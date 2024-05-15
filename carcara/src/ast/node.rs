use super::*;

/// An alternative, graph-based representation for an Alethe proof.
///
/// Instead of storing steps in a vector like [[Proof]], steps in this representaion are nodes in a
/// directed acyclic graph, and each step holds a reference-counted pointer to each of its premises.
///
/// By definition, this representation implicitly prunes the proof of unused steps. Since we
/// generally want to check all proof steps, even if they are not used to reach the proof's
/// conclusion, this representation is not appropriate for proof checking. Instead, it is better
/// suited for elaboration and other kinds of proof manipulation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofNode {
    /// An `assume` command.
    Assume { id: String, term: Rc<Term> },

    /// A `step` command.
    Step(StepNode),

    /// A subproof.
    Subproof(SubproofNode),
}

impl ProofNode {
    /// Returns the unique id of this command.
    ///
    /// For subproofs, this is the id of the last step in the subproof.
    pub fn id(&self) -> &str {
        match self {
            ProofNode::Assume { id, .. } => id,
            ProofNode::Step(s) => &s.id,
            ProofNode::Subproof(s) => s.last_step.id(),
        }
    }

    /// Returns the clause of this command.
    ///
    /// For `assume` commands, this is a unit clause containing the assumed term; for steps, it's
    /// the conclusion clause; and for subproofs, it's the conclusion clause of the last step in the
    /// subproof.
    pub fn clause(&self) -> &[Rc<Term>] {
        match self {
            ProofNode::Assume { id: _, term } => std::slice::from_ref(term),
            ProofNode::Step(StepNode { clause, .. }) => clause,
            ProofNode::Subproof(s) => s.last_step.clause(),
        }
    }

    /// Returns `true` if the node is an `assume` command.
    pub fn is_assume(&self) -> bool {
        matches!(self, ProofNode::Assume { .. })
    }

    /// Returns `true` if the node is a `step` command.
    pub fn is_step(&self) -> bool {
        matches!(self, ProofNode::Step(_))
    }

    /// Returns `true` if the node is a subproof.
    pub fn is_subproof(&self) -> bool {
        matches!(self, ProofNode::Subproof(_))
    }
}

/// A `step` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StepNode {
    /// The step id.
    pub id: String,

    /// The conclusion clause.
    pub clause: Vec<Rc<Term>>,

    /// The rule used by the step.
    pub rule: String,

    /// The premises of the step, given via the `:premises` attribute.
    ///
    /// Each premise is a reference-counted pointer to a proof node, and an integer representing
    /// that node's depth.
    pub premises: Vec<(usize, Rc<ProofNode>)>,

    /// The step arguments, given via the `:args` attribute.
    pub args: Vec<ProofArg>,

    /// The local premises that this step discharges, given via the `:discharge` attribute.
    pub discharge: Vec<(usize, Rc<ProofNode>)>,

    /// If this step is the last step in a subproof, this holds the (implicitly referenced) previous
    /// step in the subproof.
    pub previous_step: Option<Rc<ProofNode>>,
}

/// A subproof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubproofNode {
    /// The last step in the subproof.
    pub last_step: Rc<ProofNode>,

    /// The arguments of the subproof.
    ///
    /// They can be either a variable declaration, of the form `(<symbol> <sort>)`, or an
    /// assignment, of the form `(:= <symbol> <term>)`.
    pub args: Vec<AnchorArg>,

    /// The outbound premises of a subproof, that is, the premises from steps in the subproof that
    /// refer to steps outside it.
    pub outbound_premises: Vec<(usize, Rc<ProofNode>)>,
}
