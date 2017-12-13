// -----------------------------------------------------------------------------

use std::collections::*;
use std::iter::FromIterator;
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
        if let NodeForm::Var { ref name } = self.1.peg.graph[self.0] {
            name.clone()
        } else {
            panic!("VarNode invariant violated!")
        }
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
        // A helper function that takes all the same arguments as unify_term
        // but returns a boolean representing whether or not the match
        // succeeded (this avoids repeatedly having to write `*subst = None`
        // every time we need to fail the pattern match).
        fn helper(
            epeg: &EPEG,
            subst: &mut Option<Substitution>,
            ix: NodeIndex,
            pat: rs::GenTerm<MetaIdent>,
        ) -> bool {
            // Match against the given pattern.
            match pat {
                // Check if the pattern is an operation pattern.
                rs::GenTerm::Op { head: pat_head, args: pat_args } => {
                    // Check if the graph node is an operation node.
                    // If it isn't, we fail.
                    if let Some(op_node) = epeg.match_operation(ix) {
                        // Get the head and arguments of the operation node.
                        let graph_head = op_node.name();
                        let graph_args = op_node.args();

                        // If the operation name is different between the
                        // pattern and the node, we fail.
                        if pat_head != graph_head.clone() {
                            return false;
                        }

                        // If the number of arguments is different between the
                        // pattern and the node, we fail.
                        if pat_args.len() != graph_args.len() {
                            return false;
                        }

                        // Iterate over the zipped-together pattern arguments
                        // and graph arguments, unifying them.
                        for (p, g) in pat_args.iter().zip(graph_args.iter()) {
                            epeg.unify_term(subst, *g, p.clone());
                        }
                    } else {
                        return false;
                    }
                }
                // Check if the pattern is a metavariable pattern.
                rs::GenTerm::Var { name: metavar } => {
                    // If the pattern match has not yet failed, we insert a
                    // substitution from `metavar` to `ix`, since a
                    // metavariable will match against any graph node.
                    if let Some(ref mut s) = *subst {
                        s.insert(metavar, ix);
                    }
                }
            }

            true
        }

        // If `false` was returned when running `helper`, we mutate `subst`
        // to be `None`.
        if helper(self, subst, ix, pat) {
            *subst = None;
        }
    }

    // FIXME: doc
    fn unify_rule(
        &self,
        ix: NodeIndex,
        pat: rs::GenRule<MetaIdent>
    ) -> Option<Substitution> {
        let mut result = None;

        // FIXME: should this match on Composition nodes as well?
        if let Some(ref rule_node) = self.match_rule(ix) {
            // Get the label, left-hand-side, and right-hand-side of the
            // rule node and pattern.
            let graph_label = rule_node.label().clone();
            let (graph_lhs, graph_rhs) = rule_node.children();
            let pat_label = pat.label;
            let (pat_lhs, pat_rhs) = (pat.source, pat.target);

            // If the pattern (optional) label is not the same as the graph
            // node label, return `None`.
            if pat_label != graph_label {
                return None;
            }

            // Match the LHS pattern against the LHS node.
            // If this match fails, we return `None`.
            let lhs_subst = {
                let mut opt_lhs_subst = Some(Substitution::new());
                self.unify_term(&mut opt_lhs_subst, graph_lhs, pat_lhs);
                if let Some(subst) = opt_lhs_subst {
                    subst
                } else {
                    return None;
                }
            };

            // Match the RHS pattern against the RHS node.
            // If this match fails, we return `None`.
            let rhs_subst = {
                let mut opt_rhs_subst = Some(Substitution::new());
                self.unify_term(&mut opt_rhs_subst, graph_rhs, pat_rhs);
                if let Some(subst) = opt_rhs_subst {
                    subst
                } else {
                    return None;
                }
            };

            // Get `BTreeSet`s corresponding to the set of metavariables in the
            // left- and right-hand-side substitutions.
            let lhs_keys = BTreeSet::from_iter(lhs_subst.keys());
            let rhs_keys = BTreeSet::from_iter(rhs_subst.keys());

            // Create the result substitution map.
            let mut subst = Substitution::new();

            // If there are metavariables repeated between the left-hand-side
            // pattern and the right-hand-side pattern, the resultant
            // substitutions must map the same keys to the same values.
            for shared in lhs_keys.intersection(&rhs_keys) {
                if lhs_subst[shared] != rhs_subst[shared] {
                    return None;
                }
            }

            for &key in lhs_keys.union(&rhs_keys) {
                if let Some(&v) = lhs_subst.get(key) {
                    subst.insert(key.clone(), v);
                    continue;
                }
                if let Some(&v) = rhs_subst.get(key) {
                    subst.insert(key.clone(), v);
                    continue;
                }
            }

            result = Some(subst);
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
                let mut subst = Some(Substitution::new());
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
