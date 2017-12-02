use std::collections::*;
use super::rewriting_system;
pub use self::rewriting_system::Identifier;
use petgraph::prelude::*;

pub enum NodeForm {
    System,
    Term(rewriting_system::Term),
    Rule(rewriting_system::Rule),
}

pub struct EPEG {
    pub original_system: rewriting_system::RewritingSystem,
    pub graph: DiGraph<NodeForm, ()>,
    pub equiv_classes: HashSet<BTreeSet<NodeIndex>>,
}
