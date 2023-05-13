use crate::{
    ast::*,
    elaborator::{CommandDiff, Elaborator, ProofDiff, StepElaborator},
};

pub fn binarify_resolutions(pool: &mut TermPool, proof: &[ProofCommand]) -> ProofDiff {
    let mut elab = Elaborator::new();

    let mut iter = ProofIter::new(proof);
    while let Some(command) = iter.next() {
        if let ProofCommand::Subproof(s) = command {
            elab.open_subproof(s.commands.len());
            continue;
        }

        match command {
            ProofCommand::Step(s) if s.rule == "resolution" && s.premises.len() > 2 => {
                let premise_clauses = s
                    .premises
                    .iter()
                    .map(|p| iter.get_premise(*p).clause())
                    .collect();

                let step_elab = StepElaborator::new(&mut elab, s.id.clone());
                let elaboration = binarify_single_resolution(pool, step_elab, s, premise_clauses);
                elab.push_elaboration(CommandDiff::Step(elaboration));
            }
            _ => elab.unchanged(command.clause()),
        }

        if iter.is_end_step() {
            elab.close_subproof();
        }
    }
    elab.end()
}

fn binarify_single_resolution(
    pool: &mut TermPool,
    mut elaborator: StepElaborator,
    step: &ProofStep,
    premise_clauses: Vec<&[Rc<Term>]>,
) -> Vec<ProofCommand> {
    let mut args_iter = step.args.iter();
    let mut current_clause: Vec<Rc<Term>> = premise_clauses[0].to_vec();
    let mut previous_premise = step.premises[0];

    for (i, &p) in step.premises[1..].iter().enumerate() {
        // TODO: error handling
        let pivot = args_iter.next().unwrap().as_term().unwrap();
        let is_pivot_in_left = args_iter.next().unwrap().as_term().unwrap().is_bool_true();

        let negated_pivot = build_term!(pool, (not {pivot.clone()}));
        let (pivot_in_current, pivot_in_next) = if is_pivot_in_left {
            (pivot.clone(), negated_pivot)
        } else {
            (negated_pivot, pivot.clone())
        };

        let next_clause = premise_clauses[i + 1];

        current_clause.remove(
            current_clause
                .iter()
                .position(|x| *x == pivot_in_current)
                .unwrap(),
        );
        let mut found = false;
        for t in next_clause {
            if !found && *t == pivot_in_next {
                found = true;
            } else {
                current_clause.push(t.clone());
            }
        }

        let step = ProofStep {
            id: String::new(),
            clause: current_clause.clone(),
            rule: "resolution".to_owned(),
            premises: vec![previous_premise, elaborator.map_index(p)],
            args: vec![
                ProofArg::Term(pivot.clone()),
                ProofArg::Term(pool.bool_constant(is_pivot_in_left)),
            ],
            discharge: Vec::new(),
        };
        previous_premise = elaborator.add_new_step(step);
    }
    elaborator.end()
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::*,
        elaborator::apply_diff,
        parser::{parse_instance, parse_instance_with_pool},
        translation::binarify_resolutions,
    };

    #[test]
    fn test_binarify_resolutions() {
        fn run_tests(definitions: &str, cases: &[(&str, &str)]) {
            for (proof, expected) in cases.iter() {
                let (_, Proof { commands, .. }, mut pool) = parse_instance(
                    definitions.as_bytes(),
                    proof.as_bytes(),
                    false,
                    false,
                    false,
                )
                .unwrap_or_else(|_| panic!("parser error during test"));

                let got = apply_diff(binarify_resolutions(&mut pool, &commands), commands);

                let (_, Proof { commands: expected, .. }) = parse_instance_with_pool(
                    &mut pool,
                    definitions.as_bytes(),
                    expected.as_bytes(),
                    false,
                    false,
                    false,
                )
                .unwrap_or_else(|_| panic!("parser error during test"));

                assert_eq!(expected, got);
            }
        }

        let definitions = "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
            (declare-const e Bool)
            (declare-const f Bool)
        ";
        let cases = &[
            (
                "(step t1 (cl a b) :rule hole)
                (step t2 (cl (not a)) :rule hole)
                (step t3 (cl (not b)) :rule hole)
                (step t4 (cl) :rule resolution :premises (t1 t2 t3) :args (a true b true))",
                "(step t1 (cl a b) :rule hole)
                (step t2 (cl (not a)) :rule hole)
                (step t3 (cl (not b)) :rule hole)
                (step t4.t1 (cl b) :rule resolution :premises (t1 t2) :args (a true))
                (step t4.t2 (cl) :rule resolution :premises (t4.t1 t3) :args (b true))",
            ),
            (
                "(step t1 (cl a b c) :rule hole)
                (step t2 (cl (not a) d) :rule hole)
                (step t3 (cl (not c) e (not f)) :rule hole)
                (step t4 (cl f) :rule hole)
                (step t5 (cl b d e) :rule resolution :premises (t1 t2 t3 t4)
                    :args (a true c true f false))",
                "(step t1 (cl a b c) :rule hole)
                (step t2 (cl (not a) d) :rule hole)
                (step t3 (cl (not c) e (not f)) :rule hole)
                (step t4 (cl f) :rule hole)
                (step t5.t1 (cl b c d) :rule resolution :premises (t1 t2) :args (a true))
                (step t5.t2 (cl b d e (not f)) :rule resolution :premises (t5.t1 t3) :args (c true))
                (step t5.t3 (cl b d e) :rule resolution :premises (t5.t2 t4) :args (f false))",
            ),
        ];
        run_tests(definitions, cases);
    }
}
