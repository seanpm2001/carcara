mod transitivity;

use crate::ast::*;
use std::collections::{HashMap, HashSet};

#[allow(unused)]
pub fn elaborate(pool: &mut PrimitivePool, root: &Rc<ProofNode>) -> Rc<ProofNode> {
    mutate(pool, root, |pool, node| {
        if let ProofNode::Step(s) = node.as_ref() {
            if s.rule == "trans" {
                return transitivity::trans(pool, s).unwrap();
            }
        }
        node.clone()
    })
}

fn mutate<F>(pool: &mut PrimitivePool, root: &Rc<ProofNode>, mut mutate_func: F) -> Rc<ProofNode>
where
    F: FnMut(&mut PrimitivePool, &Rc<ProofNode>) -> Rc<ProofNode>,
{
    let mut cache: HashMap<&Rc<ProofNode>, Rc<ProofNode>> = HashMap::new();
    let mut did_outbound: HashSet<&Rc<ProofNode>> = HashSet::new();
    let mut todo = vec![(root, false)];

    while let Some((node, is_done)) = todo.pop() {
        assert!(!cache.contains_key(node), "this shouldn't happen I think");

        let mutated = match node.as_ref() {
            ProofNode::Assume { .. } => mutate_func(pool, node),
            ProofNode::Step(s) if !is_done => {
                todo.push((node, true));

                let all_premises = s
                    .premises
                    .iter()
                    .chain(&s.discharge)
                    .chain(&s.previous_step)
                    .rev();
                todo.extend(
                    all_premises.filter_map(|p| (!cache.contains_key(p)).then_some((p, false))),
                );

                continue;
            }
            ProofNode::Step(s) => {
                let premises: Vec<_> = s.premises.iter().map(|p| cache[p].clone()).collect();
                let discharge: Vec<_> = s.discharge.iter().map(|p| cache[p].clone()).collect();
                let previous_step = s.previous_step.as_ref().map(|p| cache[p].clone());

                let new_node = Rc::new(ProofNode::Step(StepNode {
                    premises,
                    discharge,
                    previous_step,
                    ..s.clone()
                }));
                mutate_func(pool, &new_node)
            }
            ProofNode::Subproof(s) if !is_done => {
                if !did_outbound.contains(node) {
                    did_outbound.insert(node);
                    todo.push((node, false));
                    todo.extend(s.outbound_premises.iter().map(|premise| (premise, false)));
                    continue;
                }

                todo.push((node, true));
                todo.push((&s.last_step, false));
                continue;
            }
            ProofNode::Subproof(s) => {
                let new_node = Rc::new(ProofNode::Subproof(SubproofNode {
                    last_step: cache[&s.last_step].clone(),
                    args: s.args.clone(),
                    outbound_premises: Vec::new(), // TODO: recompute outbound premises
                }));
                mutate_func(pool, &new_node)
            }
        };
        cache.insert(node, mutated);
    }
    cache[root].clone()
}
