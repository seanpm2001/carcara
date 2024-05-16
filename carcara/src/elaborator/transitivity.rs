use crate::{ast::*, checker::error::CheckerError};

fn add_symm_step(pool: &mut PrimitivePool, node: &Rc<ProofNode>) -> Rc<ProofNode> {
    assert_eq!(node.clause().len(), 1);
    let (a, b) = match_term!((= a b) = node.clause()[0]).unwrap();
    let clause = vec![build_term!(pool, (= {b.clone()} {a.clone()}))];
    Rc::new(ProofNode::Step(StepNode {
        id: format!("{}.symm", node.id()),
        depth: node.depth(),
        clause,
        rule: "symm".into(),
        premises: vec![node.clone()],
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    }))
}

/// Similar to `find_chain`, but reorders a premises vector to match the found chain. In `trans`,
/// this is used to reorder the step premises vector; in `eq_transitive`, it is used to reorder the
/// clause. This returns a boolean indicating whether any reordering was needed, a `usize`
/// indicating how many premises are needed to prove the conclusion, and a vector of indices of the
/// premise equalities that need to be flipped.
fn find_and_trace_chain<'a, T>(
    mut conclusion: (&'a Rc<Term>, &'a Rc<Term>),
    premise_equalities: &mut [(&'a Rc<Term>, &'a Rc<Term>)],
    premises: &mut [T],
) -> Result<(bool, usize, Vec<usize>), CheckerError> {
    let mut reordered = false;
    let mut should_flip = Vec::with_capacity(premise_equalities.len());
    let mut i = 0;
    loop {
        if conclusion.0 == conclusion.1 {
            return Ok((reordered, i, should_flip));
        }

        let (found_index, next_link) = premise_equalities[i..]
            .iter()
            .enumerate()
            .find_map(|(j, &(t, u))| {
                if t == conclusion.0 {
                    Some((j + i, u))
                } else if u == conclusion.0 {
                    should_flip.push(i);
                    Some((j + i, t))
                } else {
                    None
                }
            })
            .ok_or_else(|| {
                let (a, b) = conclusion;
                CheckerError::BrokenTransitivityChain(a.clone(), b.clone())
            })?;

        if found_index != i {
            premise_equalities.swap(i, found_index);
            premises.swap(i, found_index);
            reordered = true;
        }
        conclusion = (next_link, conclusion.1);
        i += 1;
    }
}

pub fn trans(pool: &mut PrimitivePool, step: &StepNode) -> Result<Rc<ProofNode>, CheckerError> {
    assert_eq!(step.clause.len(), 1);

    let conclusion_equality = match_term_err!((= t u) = &step.clause[0])?;
    let mut premise_equalities: Vec<_> = step
        .premises
        .iter()
        .map(|premise| {
            assert_eq!(premise.clause().len(), 1);
            match_term_err!((= t u) = &premise.clause()[0])
        })
        .collect::<Result<_, _>>()?;

    let mut new_premises = step.premises.clone();
    let (_, num_needed, should_flip) = find_and_trace_chain(
        conclusion_equality,
        &mut premise_equalities,
        &mut new_premises,
    )?;

    // If there are any premises in the step which are not needed to complete the transitivity
    // chain, we simply remove them in the elaborated step.
    new_premises.truncate(num_needed);

    // If there are any premises that need flipping, we need to introduce `symm` steps to flip the
    // needed equalities
    for i in should_flip {
        new_premises[i] = add_symm_step(pool, &new_premises[i]);
    }

    Ok(Rc::new(ProofNode::Step(StepNode {
        premises: new_premises,
        ..step.clone()
    })))
}
