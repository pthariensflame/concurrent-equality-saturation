//! The types in this module assume all identifiers used are (scope-)unique.

use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct RewritingSystem {
    pub types: Vec<Type>,
    pub ops: Vec<Operation>,
    pub eqs: Vec<Equation>,
    pub rls: Vec<Rule>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Type {
    pub name: Identifier,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Operation {
    pub name: Identifier,
    pub args: Vec<Type>,
    pub result: Type,
    pub frozenness: Frozenness,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Equation {
    pub quantified_variables: Vec<Identifier>,   // scoped
    pub left: Term,                              // with scope
    pub right: Term,                             // with scope
    pub conditions: Vec<Either<Equation, Rule>>, // with scope
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Rule {
    pub name: Option<Identifier>,
    pub quantified_variables: Vec<Identifier>,   // scoped
    pub source: Term,                            // with scope
    pub target: Term,                            // with scope
    pub conditions: Vec<Either<Equation, Rule>>, // with scope
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Op {
        head: Identifier, // of an `Operation`
        args: Vec<Term>,
    },
    Var {
        name: Identifier, // of a variable in scope
    },
}

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Identifier {
    id: String,
}

impl<S: Into<String>> From<S> for Identifier {
    fn from(id: S) -> Identifier {
        Identifier { id: id.into() }
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.id, fmtr)
    }
}
