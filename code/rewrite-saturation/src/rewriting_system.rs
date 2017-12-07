use std::fmt;
use snowflake::ProcessUniqueId;
use super::Void;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct RewritingSystem {
    pub sorts: Vec<Sort>,
    pub ops: Vec<Operation>,
    pub eqs: Vec<Equation>,
    pub rls: Vec<Rule>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sort {
    pub name: Identifier,
    pub supersorts: Vec<Sort>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Operation {
    pub name: Identifier,
    pub arg_sorts: Vec<Identifier>,
    pub result_sort: Identifier,
    pub frozenness: Frozenness,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Equation {
    pub quantified_variables: Vec<Identifier>, // scoped
    pub left: Term, // with scope
    pub right: Term, // with scope
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenRule<Meta> {
    pub name: Option<Identifier>,
    pub quantified_variables: Vec<Identifier>, // scoped
    pub quantified_metavariables: Vec<Meta>, // scoped
    pub source: GenTerm<Meta>, // with scope
    pub target: GenTerm<Meta>, // with scope
}

pub type Rule = GenRule<Void>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenTerm<Meta> {
    Op {
        head: Identifier, // of an `Operation`
        args: Vec<GenTerm<Meta>>,
    },
    Var { name: Identifier, // of a variable in scope },
    MetaVar { id: Meta, // of a metavariable in scope },
}

pub type Term = GenTerm<Void>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Frozenness {
    Frozen,
    Unfrozen,
}

impl Default for Frozenness {
    fn default() -> Frozenness {
        Frozenness::Unfrozen
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum IdentifierImpl {
    String { id: String },
    UniqueID { id: ProcessUniqueId },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Identifier(IdentifierImpl);

impl<S: Into<String>> From<S> for Identifier {
    fn from(id: S) -> Identifier {
        Identifier(IdentifierImpl::String { id: id.into() })
    }
}

impl Identifier {
    pub fn new_unique() -> Self {
        Identifier(IdentifierImpl::UniqueID { id: ProcessUniqueId::new() })
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            IdentifierImpl::String { ref id } => fmt::Display::fmt(id, fmtr),
            IdentifierImpl::UniqueID { ref id } => {
                fmtr.write_str("~generated:")?;
                fmt::Display::fmt(id, fmtr)
            }
        }
    }
}
