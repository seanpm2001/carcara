use super::Elaborator;
use crate::ast::*;
use std::fmt::Write;

type Frame = Vec<ProofCommand>;

pub struct StepElaborator<'a> {
    inner: &'a mut Elaborator,
    root_id: String,
    stack: Vec<Frame>,
}

impl<'a> StepElaborator<'a> {
    pub fn new(inner: &'a mut Elaborator, root_id: String) -> Self {
        assert!(inner.accumulator.is_empty());
        let stack = vec![Vec::new()];
        Self { inner, root_id, stack }
    }

    pub fn map_index(&self, index: (usize, usize)) -> (usize, usize) {
        assert!(index.0 <= self.inner.depth());
        let (d, mut i) = self.inner.map_index(index);
        if d == self.inner.depth() && d >= self.inner.current_subproof_len() {
            i += self.offset();
        }
        (d, i)
    }

    fn offset(&self) -> usize {
        self.stack[0].len()
    }

    fn top_frame(&mut self) -> &mut Frame {
        self.stack.last_mut().unwrap()
    }

    fn depth(&self) -> usize {
        self.stack.len() - 1
    }

    fn next_id(&self) -> String {
        let mut current = self.root_id.clone();
        for f in &self.stack {
            write!(&mut current, ".t{}", f.len() + 1).unwrap();
        }
        current
    }

    pub fn add_new_command(&mut self, mut command: ProofCommand) -> (usize, usize) {
        let index = if self.depth() == 0 {
            self.inner.current_subproof_len() + self.offset()
        } else {
            self.top_frame().len()
        };
        let depth = self.inner.depth() + self.depth();
        match &mut command {
            ProofCommand::Assume { id, .. } => *id = self.next_id(),
            ProofCommand::Step(s) => s.id = self.next_id(),
            ProofCommand::Subproof(_) => panic!("cannot push subproof directly to step elaborator"),
        }
        self.top_frame().push(command);
        (depth, index)
    }

    pub fn add_new_step(&mut self, step: ProofStep) -> (usize, usize) {
        self.add_new_command(ProofCommand::Step(step))
    }

    pub fn open_subproof(&mut self) {
        self.stack.push(Vec::new());
    }

    pub fn close_subproof(
        &mut self,
        assignment_args: Vec<(String, Rc<Term>)>,
        variable_args: Vec<SortedVar>,
    ) -> ProofCommand {
        let mut commands = self.stack.pop().unwrap();

        // We overwrite the last step id to be correct in relation to the outer subproof
        match commands.last_mut().unwrap() {
            ProofCommand::Step(s) => s.id = self.next_id(),
            _ => unreachable!(),
        }

        ProofCommand::Subproof(Subproof {
            commands,
            assignment_args,
            variable_args,
        })
    }

    pub fn end(mut self) -> Vec<ProofCommand> {
        assert!(self.depth() == 0);
        self.stack.pop().unwrap()
    }
}
