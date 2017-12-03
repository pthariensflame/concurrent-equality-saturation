use std::collections::*;
use petgraph::prelude::*;
use super::rewriting_system;
pub use self::rewriting_system::Identifier;

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
    Composition, // of rules; manifested lazily
}

#[derive(Debug, Clone)]
pub struct PEG {
    pub original_system: rewriting_system::RewritingSystem,
    pub graph: DiGraph<NodeForm, Option<usize>>,
}

#[derive(Debug, Clone)]
pub struct EPEG {
    pub peg: PEG,
    pub equiv_classes: HashSet<BTreeSet<NodeIndex>>,
}

pub type MetaIdent = Identifier;

#[derive(Debug, Clone)]
pub enum Trigger {
    Term(rewriting_system::GenTerm<MetaIdent>),
    Subsystem(HashSet<rewriting_system::GenRule<MetaIdent>>),
}

pub type Substitution = BTreeMap<MetaIdent, NodeIndex>;

pub struct Analysis {
    trigger: Trigger,
    callback: Box<Fn(&mut EPEG, NodeIndex, Substitution) -> bool + 'static>,
}

impl EPEG {
    pub fn saturate<Analyses>(&mut self, anas: Analyses)
    where
        Analyses: IntoIterator + Clone,
        Analyses::Item: Into<Analysis>,
    {
        let mut changed = true; // have to start the loop somewhere
        while !changed {
            changed = false;
            let ixes: Vec<_> = self.peg.graph.node_indices().collect();
            for ix in ixes {
                for ana in anas.clone().into_iter().map(|x| x.into()) {
                    for subst in self.unify_with_node(ix, ana.trigger) {
                        changed |= (ana.callback)(self, ix, subst);
                    }
                }
            }
        }
    }

    pub fn unify_with_node(&self, ix: NodeIndex, trig: Trigger) -> HashSet<Substitution> {
        match trig {
            Trigger::Term(term) => unimplemented!(),
            Trigger::Subsystem(sys) => unimplemented!(),
        }
    }
}
