use std::fmt;
use std::collections::*;
use snowflake::ProcessUniqueId;
use super::Void;

/// FIXME: doc
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct RewritingSystem {
    /// FIXME: doc
    pub sorts: Vec<Sort>,
    /// FIXME: doc
    pub ops: Vec<Operation>,
    /// FIXME: doc
    pub eqs: Vec<Equation>,
    /// FIXME: doc
    pub rls: Vec<Rule>,
}

/// FIXME: doc
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sort {
    /// FIXME: doc
    pub name: Identifier,
    /// FIXME: doc
    pub supersorts: Vec<Sort>,
}

/// FIXME: doc
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Operation {
    /// FIXME: doc
    pub name: Identifier,
    /// FIXME: doc
    pub arg_sorts: Vec<Identifier>,
    /// FIXME: doc
    pub result_sort: Identifier,
    /// FIXME: doc
    pub frozenness: Frozenness,
}

/// The type of (closed) equations in a rewriting system.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Equation {
    /// A list of identifiers used on either side of this equation.
    pub quantified_variables: Vec<Identifier>,
    /// The left-hand-side of this equation.
    pub left: Term,
    /// The right-hand-side of this equation.
    pub right: Term,
}

/// The type of open/closed rewrite rules in a rewriting system, parameterized
/// on a type of metavariables.
///
/// If the type of metavariables given as an argument to this type has no
/// inhabitants, then this represents the type of closed rules.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenRule<Meta> {
    /// The label associated with this rule, if any.
    pub label: Option<Identifier>,
    /// A list of variables used on either side of this rule.
    pub quantified_variables: BTreeSet<Identifier>,
    /// A list of metavariables used on either side of this rule.
    pub quantified_metavariables: BTreeSet<Meta>,
    /// The left-hand-side of this rewrite rule.
    pub source: GenTerm<Meta>,
    /// The right-hand-side of this rewrite rule.
    pub target: GenTerm<Meta>,
}

impl<Meta> GenRule<Meta> {
    /// FIXME: doc
    pub fn new(
        label: Option<Identifier>,
        source: GenTerm<Meta>,
        target: GenTerm<Meta>,
    ) -> GenRule<Meta>
    where
        Meta: Ord + Clone,
    {
        fn traverse<M>(term: &GenTerm<M>, qvs: &mut BTreeSet<Identifier>, qmvs: &mut BTreeSet<M>)
        where
            M: Ord + Clone,
        {
            match *term {
                GenTerm::Op { ref head, ref args } => {
                    for a in args {
                        traverse(a, qvs, qmvs);
                    }
                }
                GenTerm::Var { ref name } => {
                    qvs.insert(name.clone());
                }
                GenTerm::MetaVar { ref id } => {
                    qmvs.insert(id.clone());
                }
            }
        }

        let mut qvs = BTreeSet::new();
        let mut qmvs = BTreeSet::new();

        traverse(&source, &mut qvs, &mut qmvs);
        traverse(&target, &mut qvs, &mut qmvs);

        GenRule {
            label: label,
            quantified_variables: qvs,
            quantified_metavariables: qmvs,
            source: source,
            target: target,
        }
    }
}

/// FIXME: doc
pub type Rule = GenRule<Void>;

/// The type of open/closed terms in a rewriting system, parameterized on a type
/// of metavariables.
///
/// If the type of metavariables given as an argument to this type has no
/// inhabitants, then this represents the type of terms that are closed
/// relative to metavariables.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenTerm<Meta> {
    /// Construct a term that applies an operation to some arguments.
    Op {
        /// The name of the operation.
        head: Identifier,
        /// A vector of argument terms.
        args: Vec<GenTerm<Meta>>,
    },
    /// Construct a term that references a variable in scope.
    Var {
        /// The underlying identifier.
        name: Identifier,
    },
    /// Construct a term that references a metavariable in scope.
    MetaVar {
        /// The underlying identifier.
        id: Meta,
    },
}

/// FIXME: doc
pub type Term = GenTerm<Void>;

/// FIXME: doc
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Frozenness {
    /// FIXME: doc
    Frozen,
    /// FIXME: doc
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

/// FIXME: doc
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Identifier(IdentifierImpl);

impl<S: Into<String>> From<S> for Identifier {
    fn from(id: S) -> Identifier {
        Identifier(IdentifierImpl::String { id: id.into() })
    }
}

impl Identifier {
    /// FIXME: doc
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
