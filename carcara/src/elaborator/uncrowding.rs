use super::IdHelper;
use crate::{ast::*, checker::error::CheckerError, resolution::*, utils::DedupIterator};
use std::collections::{HashMap, HashSet};

fn literal_to_term(pool: &mut dyn TermPool, (n, term): Literal) -> Rc<Term> {
    let mut term = term.clone();
    for _ in 0..n {
        term = build_term!(pool, (not { term }));
    }
    term
}

fn literals_to_clause(pool: &mut dyn TermPool, clause: &[Literal]) -> Vec<Rc<Term>> {
    clause.iter().map(|l| literal_to_term(pool, *l)).collect()
}

fn apply_naive_resolution<'a>(
    premises: &[Vec<Literal<'a>>],
    pivots: &[(Literal, bool)],
) -> Vec<Literal<'a>> {
    assert!(premises.len() >= 2);
    assert_eq!(pivots.len(), premises.len() - 1);

    let mut current = premises[0].clone();

    for (premise, &(pivot, polarity)) in premises[1..].iter().zip(pivots) {
        let negated_pivot = (pivot.0 + 1, pivot.1);
        let (pivot_in_current, pivot_in_next) = if polarity {
            (pivot, negated_pivot)
        } else {
            (negated_pivot, pivot)
        };

        let pos = current.iter().position(|x| x == &pivot_in_current).unwrap();
        current.remove(pos);

        let mut found = false;
        for &t in premise {
            if !found && t == pivot_in_next {
                found = true;
            } else {
                current.push(t);
            }
        }
        assert!(found);
    }

    current
}

#[allow(unused)]
#[allow(clippy::unnecessary_wraps)]
pub fn uncrowd_resolution(
    pool: &mut PrimitivePool,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    let target_conclusion: HashSet<_> = step.clause.iter().map(Rc::remove_all_negations).collect();

    let premise_clauses: Vec<Vec<_>> = step
        .premises
        .iter()
        .map(|p| p.clause().iter().map(Rc::remove_all_negations).collect())
        .collect();
    let pivots: Vec<_> = step
        .args
        .chunks(2)
        .map(|chunk| {
            let pivot = chunk[0].as_term().unwrap().remove_all_negations();
            let polarity = chunk[1].as_term().unwrap().is_bool_true();
            (pivot, polarity)
        })
        .collect();
    let naive_conclusion = apply_naive_resolution(&premise_clauses, &pivots);

    let crowding_literals = find_crowding_literals(
        &naive_conclusion,
        &target_conclusion,
        &premise_clauses,
        &pivots,
    );
    let mut contractions = find_needed_contractions(crowding_literals);
    if contractions.last() != Some(&step.premises.len()) {
        contractions.push(step.premises.len());
    }

    let mut previous_cut = 0;
    let mut previous_node = None;
    let mut previous_clause = None;
    let mut pivots = pivots.into_iter();
    let mut ids = IdHelper::new(&step.id);

    for cut in contractions {
        let premise_nodes: Vec<_> = previous_node
            .iter()
            .chain(&step.premises[previous_cut..cut])
            .cloned()
            .collect();
        let clauses: Vec<_> = previous_clause
            .into_iter()
            .chain(premise_clauses[previous_cut..cut].iter().cloned())
            .collect();
        let pivots: Vec<_> = (&mut pivots).take(premise_nodes.len() - 1).collect();
        let (node, clause) =
            add_partial_resolution_step(pool, &mut ids, step.depth, premise_nodes, clauses, pivots);
        previous_cut = cut;
        previous_node = Some(node);
        previous_clause = Some(clause);
    }

    Ok(previous_node.unwrap())
}

fn add_partial_resolution_step<'a>(
    pool: &mut dyn TermPool,
    ids: &mut IdHelper,
    depth: usize,
    premises: Vec<Rc<ProofNode>>,
    premise_clauses: Vec<Vec<Literal<'a>>>,
    pivots: Vec<(Literal<'a>, bool)>,
) -> (Rc<ProofNode>, Vec<Literal<'a>>) {
    let conclusion = apply_naive_resolution(&premise_clauses, &pivots);
    let contracted_conclusion = conclusion.iter().dedup().copied().collect();

    let args = pivots
        .into_iter()
        .flat_map(|(literal, polarity)| {
            [literal_to_term(pool, literal), pool.bool_constant(polarity)]
        })
        .map(ProofArg::Term)
        .collect();

    let clause = literals_to_clause(pool, &conclusion);
    let contracted_clause = clause.iter().dedup().cloned().collect();

    let resolution_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth,
        clause,
        rule: "resolution".to_owned(),
        premises,
        args,
        discharge: Vec::new(),
        previous_step: None,
    }));

    let contraction_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth,
        clause: contracted_clause,
        rule: "contraction".to_owned(),
        premises: vec![resolution_step],
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    }));

    (contraction_step, contracted_conclusion)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CrowdingLiteralInfo {
    last_inclusion: usize,
    eliminator: usize,
}

fn find_crowding_literals<'a>(
    naive_conclusion: &[Literal<'a>],
    target_conclusion: &HashSet<Literal<'a>>,
    premises: &[Vec<Literal<'a>>],
    pivots: &[(Literal<'a>, bool)],
) -> HashMap<Literal<'a>, CrowdingLiteralInfo> {
    let mut crowding_lits: HashMap<Literal, CrowdingLiteralInfo> = naive_conclusion
        .iter()
        .filter(|lit| !target_conclusion.contains(lit))
        .map(|&l| (l, CrowdingLiteralInfo { last_inclusion: 0, eliminator: 0 }))
        .collect();

    for (i, clause) in premises.iter().enumerate() {
        for lit in clause {
            if let Some(info) = crowding_lits.get_mut(lit) {
                info.last_inclusion = i;
            }
        }
    }
    for (i, &(pivot, polarity)) in pivots.iter().enumerate() {
        let pivot_in_current = if polarity {
            pivot
        } else {
            (pivot.0 + 1, pivot.1)
        };
        if let Some(info) = crowding_lits.get_mut(&pivot_in_current) {
            if i + 1 > info.last_inclusion {
                info.eliminator = i + 1;
            }
        }
    }
    crowding_lits
}

fn find_needed_contractions(
    crowding_literals: HashMap<Literal, CrowdingLiteralInfo>,
) -> Vec<usize> {
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum Event {
        Elimination,
        LastInclusion,
    }

    let mut events: Vec<_> = crowding_literals
        .iter()
        .flat_map(|(lit, info)| {
            [
                (*lit, Event::LastInclusion, info.last_inclusion),
                (*lit, Event::Elimination, info.eliminator),
            ]
        })
        .collect();

    // If there are multiple events at the same index, we must process eliminations first
    events.sort_unstable_by(|(_, a_event, a_index), (_, b_event, b_index)| {
        match a_index.cmp(b_index) {
            std::cmp::Ordering::Equal => a_event.cmp(b_event),
            other => other,
        }
    });

    let mut contractions = Vec::new();
    let mut need_to_contract = HashSet::new();
    for (lit, event, index) in events {
        match event {
            Event::LastInclusion => {
                need_to_contract.insert(lit);
            }
            Event::Elimination => {
                if need_to_contract.contains(&lit) {
                    contractions.push(index);
                    need_to_contract.clear();
                }
            }
        }
    }
    contractions
}
