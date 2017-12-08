use std::collections::*;
use petgraph::prelude::*;
use super::rewriting_system as rs;
pub use self::rs::Identifier;

/// FIXME: doc
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NodeForm {
    /// FIXME: doc
    System,
    /// FIXME: doc
    Rule {
        /// The label of this rule.
        label: Option<Identifier>,
        /// The variables quantified in the source and target nodes.
        quantified: Vec<Identifier>,
    },
    /// A node representing composition of rules; these are manifested lazily.
    Composition,
    /// FIXME: doc
    Operation {
        /// FIXME: doc
        /// index into the original Vec
        index: usize,
    },
    /// FIXME: doc
    Var {
        /// FIXME: doc
        name: Identifier,
    },
}

/// FIXME: doc
#[derive(Debug, Clone)]
pub struct PEG {
    /// FIXME: doc
    pub original_system: rs::RewritingSystem,
    /// FIXME: doc
    pub graph: DiGraph<NodeForm, Option<usize>>,
}

/// FIXME: doc
#[derive(Debug, Clone)]
pub struct EPEG {
    /// FIXME: doc
    pub peg: PEG,
    /// FIXME: doc
    pub equiv_classes: HashSet<BTreeSet<NodeIndex>>,
}

/// FIXME: doc
pub type MetaIdent = Identifier;

/// FIXME: doc
#[derive(Debug, Clone)]
pub enum Trigger {
    /// FIXME: doc
    Term(rs::GenTerm<MetaIdent>),
    /// FIXME: doc
    Subsystem(HashSet<rs::GenRule<MetaIdent>>),
}

/// FIXME: doc
pub type Substitution = BTreeMap<MetaIdent, NodeIndex>;

/// FIXME: doc
pub struct Analysis {
    /// FIXME: doc
    trigger: Trigger,
    /// FIXME: doc
    callback: Box<Fn(&mut EPEG, NodeIndex, Substitution) -> bool + 'static>,
}

struct SystemNode<'a>(NodeIndex, &'a EPEG);

struct RuleNode<'a>(NodeIndex, &'a EPEG);

struct CompositionNode<'a>(NodeIndex, &'a EPEG);

struct OperationNode<'a>(NodeIndex, &'a EPEG);

struct VarNode<'a>(NodeIndex, &'a EPEG);

impl EPEG {
    /// FIXME: doc
    pub fn saturate<Analyses>(&mut self, anas: &Analyses)
    where
        Analyses: IntoIterator + Clone,
        Analyses::Item: Into<Analysis>,
    {
        let mut changed = true; // have to start the loop somewhere
        while changed {
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

    fn child_edges(&self, ix: NodeIndex) -> Vec<(Option<usize>, NodeIndex)> {
        let mut result = Vec::new();
        for edge in self.peg.graph.edges_directed(ix, Direction::Outgoing) {
            result.push((*edge.weight(), edge.target()));
        }
        result
    }

    fn match_system(&self, ix: NodeIndex) -> Option<SystemNode> {
        // FIXME: check if `ix` is a valid system node here
        Some(SystemNode(ix, &self))
    }

    fn system_rules(&self, node: SystemNode) -> Vec<NodeIndex> {
        unimplemented!()
    }

    fn match_rule(&self, ix: NodeIndex) -> Option<RuleNode> {
        // FIXME: check if `ix` is a valid rule node here
        Some(RuleNode(ix, &self))
    }

    fn rule_lhs(&self, node: RuleNode) -> NodeIndex {
        unimplemented!()
    }

    fn rule_rhs(&self, node: RuleNode) -> NodeIndex {
        unimplemented!()
    }

    fn match_composition(&self, ix: NodeIndex) -> Option<CompositionNode> {
        // FIXME: check if `ix` is a valid composition node here
        Some(CompositionNode(ix, &self))
    }

    fn composition_lhs(&self, node: CompositionNode) -> NodeIndex {
        unimplemented!()
    }

    fn composition_rhs(&self, node: CompositionNode) -> NodeIndex {
        unimplemented!()
    }

    fn match_operation(&self, ix: NodeIndex) -> Option<OperationNode> {
        unimplemented!()
    }

    fn unify_term(
        &self,
        subst: &mut Option<Substitution>,
        ix: NodeIndex,
        pat: rs::GenTerm<MetaIdent>,
    ) {
        let g = &self.peg.graph;
        let data = &g[ix];

        match pat {
            rs::GenTerm::Op { head, args } => {
                if let NodeForm::Operation { index } = *data {
                    let mut child_edge_map: BTreeMap<usize, NodeIndex> = BTreeMap::new();
                    for edge in g.edges_directed(ix, Direction::Outgoing) {
                        if let Some(w) = *edge.weight() {
                            child_edge_map.insert(w, edge.target());
                        } else {
                            panic!("An operation node should never have an unlabelled child edge!");
                        }
                    }

                    let name = &self.peg.original_system.ops[index].name;
                    if *name == head {
                        for (i, arg) in args.iter().enumerate() {
                            if let Some(target) = child_edge_map.get(&i) {
                                self.unify_term(subst, *target, arg.clone());
                            }
                        }
                    } else {
                        *subst = None;
                    }
                }
            }
            rs::GenTerm::Var { name } => {
                if let Some(ref mut s) = *subst {
                    s.insert(name, ix);
                }
            }
        }
    }

    // pub struct GenRule<Var> {
    //     /// The label associated with this rule, if any.
    //     pub label: Option<Identifier>,
    //     /// A list of variables used on either side of this rule.
    //     pub quantified: BTreeSet<Var>,
    //     /// The left-hand-side of this rewrite rule.
    //     pub source: GenTerm<Var>,
    //     /// The right-hand-side of this rewrite rule.
    //     pub target: GenTerm<Var>,
    // }

    fn unify_rule(
        &self,
        ix: NodeIndex,
        pat: rs::GenRule<MetaIdent>
    ) -> Option<Substitution> {
        let g = &self.peg.graph;
        let data = &g[ix];

        let mut result = None;

        // FIXME: should this match on Composition nodes as well?
        if let NodeForm::Rule { ref label, ref quantified } = *data {
            if pat.label == *label {
                let edges = g.edges_directed(ix, Direction::Outgoing);

            }
        }

        result
    }

    fn unify_subsystem(
        &self,
        substs: &mut HashSet<Substitution>,
        ix: NodeIndex,
        pat: HashSet<rs::GenRule<MetaIdent>>,
    ) {
        unimplemented!()
    }

    /// FIXME: doc
    pub fn unify_with_node(&self, ix: NodeIndex, trig: Trigger) -> HashSet<Substitution> {
        let mut result = HashSet::new();
        match trig {
            Trigger::Term(term) => {
                let mut subst = Some(BTreeMap::new());
                self.unify_term(&mut subst, ix, term);
                if let Some(s) = subst {
                    result.insert(s);
                }
            }
            Trigger::Subsystem(subsystem) => {
                self.unify_subsystem(&mut result, ix, subsystem);
            }
        }
        result
    }
}
