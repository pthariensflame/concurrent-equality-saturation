use std::collections::*;
use super::rewriting_system;
pub use self::rewriting_system::Identifier;
use petgraph::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NodeForm {
    System,
    Operation(usize), // index into the original Vec
    Rule {
        name: Option<Identifier>,
        quantified_variables: Vec<Identifier>, // scoped
        source: NodeIndex,                     // with scope
        target: NodeIndex,                     // with scope
    },
}

#[derive(Debug, Clone)]
pub struct PEG {
    pub original_system: rewriting_system::RewritingSystem,
    pub graph: StableDiGraph<NodeForm, ()>,
}

#[derive(Debug, Clone)]
pub struct EPEG {
    pub peg: PEG,
    pub equiv_classes: HashSet<BTreeSet<NodeIndex>>,
}
