// -----------------------------------------------------------------------------

use std::collections::*;
use petgraph::prelude::*;
use super::rewriting_system as rs;
pub use self::rs::Identifier;

// -----------------------------------------------------------------------------

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

// -----------------------------------------------------------------------------

/// FIXME: doc
#[derive(Debug, Clone)]
pub struct PEG {
    /// FIXME: doc
    pub original_system: rs::RewritingSystem,
    /// FIXME: doc
    pub graph: DiGraph<NodeForm, Option<usize>>,
}

// -----------------------------------------------------------------------------

/// FIXME: doc
#[derive(Debug, Clone)]
pub struct EPEG {
    /// FIXME: doc
    pub peg: PEG,
    /// FIXME: doc
    pub equiv_classes: HashSet<BTreeSet<NodeIndex>>,
}

// -----------------------------------------------------------------------------

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

// -----------------------------------------------------------------------------

struct SystemNode<'a>(NodeIndex, &'a EPEG);

impl <'a> SystemNode<'a> {
    fn rules(&self) -> HashSet<NodeIndex> {
        self.1.child_edges(self.0)
            .into_iter()
            .map(|(_, c)| c)
            .collect()
    }
}

struct RuleNode<'a>(NodeIndex, &'a EPEG);

impl <'a> RuleNode<'a> {
    fn children(&self) -> (NodeIndex, NodeIndex) {
        let children = self.1.child_edges(self.0);
        if children[0].0 < children[1].0 {
            (children[0].1, children[1].1)
        } else {
            (children[1].1, children[0].1)
        }
    }

    fn label(&self) -> &'a Option<Identifier> {
        if let NodeForm::Rule { ref label, .. } = self.1.peg.graph[self.0] {
            label
        } else {
            panic!("RuleNode invariant violated!")
        }
    }

    fn quantified(&self) -> &'a Vec<Identifier> {
        if let NodeForm::Rule { ref quantified, .. } = self.1.peg.graph[self.0] {
            quantified
        } else {
            panic!("RuleNode invariant violated!")
        }
    }

    fn lhs(&self) -> NodeIndex {
        self.children().0
    }

    fn rhs(&self) -> NodeIndex {
        self.children().1
    }
}

struct CompositionNode<'a>(NodeIndex, &'a EPEG);

impl <'a> CompositionNode<'a> {
    fn children(&self) -> (NodeIndex, NodeIndex) {
        let children = self.1.child_edges(self.0);
        if children[0].0 < children[1].0 {
            (children[0].1, children[1].1)
        } else {
            (children[1].1, children[0].1)
        }
    }

    fn lhs(&self) -> NodeIndex {
        self.children().0
    }

    fn rhs(&self) -> NodeIndex {
        self.children().1
    }
}

struct OperationNode<'a>(NodeIndex, &'a EPEG);

impl <'a> OperationNode<'a> {
    fn operation(&self) -> &'a rs::Operation {
        if let NodeForm::Operation { index } = self.1.peg.graph[self.0] {
            &(self.1.peg.original_system.ops[index])
        } else {
            panic!("OperationNode invariant violated!")
        }
    }

    fn name(&self) -> &'a Identifier {
        &(self.operation().name)
    }

    fn signature(&self) -> (&'a Vec<Identifier>, &'a Identifier) {
        let op = self.operation();
        (&op.arg_sorts, &op.result_sort)
    }

    fn frozenness(&self) -> &'a rs::Frozenness {
        &(self.operation().frozenness)
    }

    fn args(&self) -> Vec<NodeIndex> {
        let mut children = self.1.child_edges(self.0);
        children.sort_unstable_by_key(|&(w, _)| w);
        children.into_iter().map(|(_, c)| c).collect()
    }
}

struct VarNode<'a>(NodeIndex, &'a EPEG);

impl <'a> VarNode<'a> {
    fn name(&self) -> Identifier {
        unimplemented!()
    }
}

// -----------------------------------------------------------------------------

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

    // FIXME: doc
    fn child_edges(&self, ix: NodeIndex) -> Vec<(Option<usize>, NodeIndex)> {
        let mut result = Vec::new();
        for edge in self.peg.graph.edges_directed(ix, Direction::Outgoing) {
            result.push((*edge.weight(), edge.target()));
        }
        result
    }

    // FIXME: doc
    fn match_system(&self, ix: NodeIndex) -> Option<SystemNode> {
        // FIXME: maybe change these checks to asserts?

        // The node referenced by `ix` must be a system node.
        if let NodeForm::System = self.peg.graph[ix] {
            for (weight, _child) in self.child_edges(ix) {
                // A system node should never have an outgoing weighted edge.
                if weight.is_some() {
                    return None;
                }
            }

            return Some(SystemNode(ix, self));
        }

        None
    }

    // FIXME: doc
    fn match_rule(&self, ix: NodeIndex) -> Option<RuleNode> {
        // FIXME: maybe change these checks to asserts?

        // The node referenced by `ix` must be a rule node.
        if let NodeForm::Rule { .. } = self.peg.graph[ix] {
            let children = self.child_edges(ix);

            // A rule node must have exactly two outgoing edges.
            if children.len() != 2 {
                return None;
            }

            let (c0, c1) = (children[0], children[1]);

            // The two outgoing edges of a rule node must be weighted, and their
            // weights must not be equal to one another.
            if (c0.0 == None) || (c1.0 == None) || (c0.0 == c1.0) {
                return None;
            }

            // FIXME: check if child nodes respect scope?

            return Some(RuleNode(ix, self));
        }

        None
    }

    // FIXME: doc
    fn match_composition(&self, ix: NodeIndex) -> Option<CompositionNode> {
        // FIXME: maybe change these checks to asserts?

        // The node referenced by `ix` must be a composition node.
        if let NodeForm::Composition { .. } = self.peg.graph[ix] {
            let children = self.child_edges(ix);

            // A composition node must have exactly two outgoing edges.
            if children.len() != 2 {
                return None;
            }

            let (c0, c1) = (children[0], children[1]);

            // The two outgoing edges of a rule node must be weighted, and their
            // weights must not be equal to one another.
            if (c0.0 == None) || (c1.0 == None) || (c0.0 == c1.0) {
                return None;
            }

            // FIXME: check if child nodes are compatible?

            return Some(CompositionNode(ix, self));
        }

        None
    }

    // FIXME: doc
    fn match_operation(&self, ix: NodeIndex) -> Option<OperationNode> {
        // FIXME: maybe change these checks to asserts?

        // The node referenced by `ix` must be a operation node.
        if let NodeForm::Operation { .. } = self.peg.graph[ix] {
            let children = self.child_edges(ix);

            let mut weights = HashSet::new();

            for (weight, _child) in children {
                if let Some(w) = weight {
                    // There should never be two edges coming out of the same
                    // operation node with the same weight.
                    if weights.contains(&w) {
                        return None;
                    }
                    weights.insert(w);
                } else {
                    // An operation node must only have weighted outgoing edges.
                    return None;
                }
            }

            return Some(OperationNode(ix, self));
        }

        None
    }

    // FIXME: doc
    fn match_var(&self, ix: NodeIndex) -> Option<VarNode> {
        // FIXME: maybe change these checks to asserts?

        // The node referenced by `ix` must be a variable node.
        if let NodeForm::Var { .. } = self.peg.graph[ix] {
            // A variable node must not have any outgoing edges.
            if !(self.child_edges(ix).is_empty()) {
                return None;
            }

            return Some(VarNode(ix, self));
        }

        None
    }

    // FIXME: doc
    fn unify_term(
        &self,
        subst: &mut Option<Substitution>,
        ix: NodeIndex,
        pat: rs::GenTerm<MetaIdent>,
    ) {
        // let g = &self.peg.graph;
        // let data = &g[ix];

        match pat {
            rs::GenTerm::Op { head, args } => {
                if let Some(op_node) = self.match_operation(ix) {
                    let name = op_node.name();


                    let args = op_node.args();

                }

                // if let NodeForm::Operation { index } = *data {
                //     let mut child_edge_map: BTreeMap<usize, NodeIndex> = BTreeMap::new();
                //     for edge in g.edges_directed(ix, Direction::Outgoing) {
                //         if let Some(w) = *edge.weight() {
                //             child_edge_map.insert(w, edge.target());
                //         } else {
                //             panic!("An operation node should never have an unlabelled child edge!");
                //         }
                //     }
                //
                //     let name = &self.peg.original_system.ops[index].name;
                //     if *name == head {
                //         for (i, arg) in args.iter().enumerate() {
                //             if let Some(target) = child_edge_map.get(&i) {
                //                 self.unify_term(subst, *target, arg.clone());
                //             }
                //         }
                //     } else {
                //         *subst = None;
                //     }
                // }
            }
            rs::GenTerm::Var { name } => {
                if let Some(ref mut s) = *subst {
                    s.insert(name, ix);
                }
            }
        }
    }

    // FIXME: doc
    fn unify_rule(
        &self,
        ix: NodeIndex,
        pat: rs::GenRule<MetaIdent>
    ) -> Option<Substitution> {
        let g = &self.peg.graph;
        let data = &g[ix];

        let mut result = None;

        // FIXME: should this match on Composition nodes as well?
        if let NodeForm::Rule { ref label, .. } = *data {
            if pat.label == *label {
                let edges = g.edges_directed(ix, Direction::Outgoing);
                unimplemented!()
            }
        }

        result
    }

    // FIXME: doc
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

// -----------------------------------------------------------------------------
