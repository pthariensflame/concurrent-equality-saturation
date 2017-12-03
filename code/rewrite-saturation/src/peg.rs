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
    Composition, // of rules
    Identity(Identifier), // rule; identifier is sort
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
    callback: Box<Fn(&mut EPEG, Substitution) + 'static>,
}

impl EPEG {
    pub fn saturate<Analyses>(&mut self, anas: Analyses)
    where
        Analyses: IntoIterator<Item = Analysis>,
    {
        for ana in anas {
            for subst in self.match_substs(ana.trigger) {
                (ana.callback)(self, subst);
            }
        }
    }

    pub fn match_substs(&self, trig: Trigger) -> HashSet<Substitution> {
        match trig {
            Trigger::Term(term) => unimplemented!(),
            Trigger::Subsystem(sys) => unimplemented!(),
        }
    }
}
