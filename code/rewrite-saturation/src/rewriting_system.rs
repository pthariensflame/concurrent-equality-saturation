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
    pub rules: Vec<Rule>,
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
    pub quantified: Vec<Identifier>,
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
pub struct GenRule<Label, Var> {
    /// The label associated with this rule, if any.
    pub label: Option<Label>,
    /// A list of variables used on either side of this rule.
    pub quantified: BTreeSet<Var>,
    /// The left-hand-side of this rewrite rule.
    pub source: GenTerm<Var>,
    /// The right-hand-side of this rewrite rule.
    pub target: GenTerm<Var>,
}

impl <Label, Var> GenRule<Label, Var> {
    /// FIXME: doc
    pub fn new(
        label: Option<Label>,
        source: GenTerm<Var>,
        target: GenTerm<Var>,
    ) -> GenRule<Label, Var>
    where
        Var: Ord + Clone,
    {
        fn traverse<V>(term: &GenTerm<V>, qvs: &mut BTreeSet<V>)
        where
            V: Ord + Clone,
        {
            match *term {
                GenTerm::Op { ref args, .. } => {
                    for a in args {
                        traverse(a, qvs);
                    }
                }
                GenTerm::Var { ref name } => {
                    qvs.insert(name.clone());
                }
            }
        }

        let mut qvs = BTreeSet::new();

        traverse(&source, &mut qvs);
        traverse(&target, &mut qvs);

        GenRule {
            label: label,
            quantified: qvs,
            source: source,
            target: target,
        }
    }
}

/// FIXME: doc
pub type Rule = GenRule<Identifier, Identifier>;

/// The type of open/closed terms in a rewriting system, parameterized on a type
/// of variables.
///
/// If the type of metavariables given as an argument to this type has no
/// inhabitants, then this represents the type of terms that are closed
/// relative to metavariables.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenTerm<Var> {
    /// Construct a term that applies an operation to some arguments.
    Op {
        /// The name of the operation.
        head: Identifier,
        /// A vector of argument terms.
        args: Vec<GenTerm<Var>>,
    },
    /// Construct a term that references a variable in scope.
    Var {
        /// The underlying identifier.
        name: Var,
    },
}

/// FIXME: doc
pub type Term = GenTerm<Identifier>;

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
