// -----------------------------------------------------------------------------

use std::fmt;
use std::collections::*;
use std::iter::*;
use itertools::Either;
use petgraph::prelude::*;
use super::rewriting_system as rs;
pub use self::rs::Identifier;

// -----------------------------------------------------------------------------

/// FIXME: doc
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PEGNode {
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

impl fmt::Display for PEGNode {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            PEGNode::System => {
                write!(formatter, "\\\\star")
            },
            PEGNode::Rule { ref label, .. } => {
                if let Some(ref l) = *label {
                    write!(formatter, "\\\\to_{{{}}}", l)
                } else {
                    write!(formatter, "\\\\to")
                }
            },
            PEGNode::Composition => {
                write!(formatter, "\\\\mathbb{{C}}")
            },
            PEGNode::Operation { ref index } => {
                write!(formatter, "\\\\mathrm{{op}}_{{{}}}", index)
            },
            PEGNode::Var { ref name } => {
                write!(formatter, "\\\\mathrm{{{}}}", name)
            },
        }
    }
}

// -----------------------------------------------------------------------------

/// FIXME: doc
#[derive(Debug, Clone)]
pub struct PEGEdge(Option<usize>);

impl fmt::Display for PEGEdge {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        if let PEGEdge(Some(ref x)) = *self {
            write!(formatter, "{}", x)
        } else {
            write!(formatter, "")
        }
    }
}

// -----------------------------------------------------------------------------

/// FIXME: doc
#[derive(Debug, Clone)]
pub struct PEG {
    /// FIXME: doc
    pub system: rs::RewritingSystem,
    /// FIXME: doc
    pub graph: DiGraph<PEGNode, PEGEdge>,
}

impl PEG {
    // FIXME: doc
    fn add_term(&mut self, term: &rs::Term) -> NodeIndex {
        match *term {
            rs::GenTerm::Op { ref head, ref args } => {
                let index: usize = {
                    let mut temp: i64 = -1;
                    for (i, op) in self.system.ops.iter().enumerate() {
                        if op.name == *head {
                            temp = i as i64;
                            break;
                        }
                    }
                    if temp < 0 {
                        panic!("Invalid operation name in term!");
                    }
                    temp as usize
                };
                let op_node_data = PEGNode::Operation { index };
                let op_node = self.graph.add_node(op_node_data);
                for (i, arg) in args.iter().enumerate() {
                    let child = self.add_term(arg);
                    self.graph.add_edge(op_node, child, PEGEdge(Some(i)));
                }
                op_node
            },
            rs::GenTerm::Var { ref name } => {
                let var_node_data = PEGNode::Var { name: name.clone() };
                let var_node = self.graph.add_node(var_node_data);
                var_node
            },
        }
    }

    // FIXME: doc
    fn add_rule(&mut self, rule: &rs::Rule) -> NodeIndex {
        let rule_node_data = PEGNode::Rule {
            label: rule.label.clone(),
            quantified: Vec::from_iter(rule.quantified.iter().cloned()),
        };
        let rule_node = self.graph.add_node(rule_node_data);
        let lhs_node = self.add_term(&(rule.source));
        let rhs_node = self.add_term(&(rule.target));
        self.graph.add_edge(rule_node, lhs_node, PEGEdge(Some(1)));
        self.graph.add_edge(rule_node, rhs_node, PEGEdge(Some(2)));
        rule_node
    }

    // FIXME: doc
    fn add_system(&mut self, system: &rs::RewritingSystem) -> NodeIndex {
        let sys_node = self.graph.add_node(PEGNode::System);
        for rule in system.rules.clone() {
            let rule_node = self.add_rule(&rule);
            self.graph.add_edge(sys_node, rule_node, PEGEdge(None));
        }
        sys_node
    }

    /// FIXME: doc
    pub fn new(sys: &rs::RewritingSystem) -> PEG {
        let mut result = PEG {
            system: sys.clone(),
            graph: DiGraph::<PEGNode, PEGEdge>::new(),
        };
        result.add_system(sys);
        result
    }
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

impl EPEG {
    /// FIXME: doc
    pub fn new(peg: &PEG) -> EPEG {
        EPEG {
            peg: peg.clone(),
            equiv_classes: HashSet::new(),
        }
    }
}

// -----------------------------------------------------------------------------

/// FIXME: doc
pub type MetaIdent = Identifier;

/// FIXME: doc
pub type TermPattern = rs::GenTerm<MetaIdent>;

/// FIXME: doc
pub type LabelPattern = Either<Identifier, MetaIdent>;

/// FIXME: doc
pub type RulePattern = rs::GenRule<LabelPattern, MetaIdent>;

/// FIXME: doc
#[derive(Debug, Clone)]
pub enum Trigger {
    /// FIXME: doc
    Term(TermPattern),
    /// FIXME: doc
    Subsystem(HashSet<RulePattern>),
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
        if let PEGNode::Rule { ref label, .. } = self.1.peg.graph[self.0] {
            label
        } else {
            panic!("RuleNode invariant violated!")
        }
    }

    fn quantified(&self) -> &'a Vec<Identifier> {
        if let PEGNode::Rule { ref quantified, .. } = self.1.peg.graph[self.0] {
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
        if let PEGNode::Operation { index } = self.1.peg.graph[self.0] {
            &(self.1.peg.system.ops[index])
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
        if let PEGNode::Var { ref name } = self.1.peg.graph[self.0] {
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
            let PEGEdge(w) = *edge.weight();
            result.push((w, edge.target()));
        }
        result
    }

    // FIXME: doc
    fn match_system(&self, ix: NodeIndex) -> Option<SystemNode> {
        // FIXME: maybe change these checks to asserts?

        // The node referenced by `ix` must be a system node.
        if let PEGNode::System = self.peg.graph[ix] {
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
        if let PEGNode::Rule { .. } = self.peg.graph[ix] {
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
        if let PEGNode::Composition { .. } = self.peg.graph[ix] {
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
        if let PEGNode::Operation { .. } = self.peg.graph[ix] {
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
        if let PEGNode::Var { .. } = self.peg.graph[ix] {
            // A variable node must not have any outgoing edges.
            if !(self.child_edges(ix).is_empty()) {
                return None;
            }

            // FIXME: maybe the variable should have an outgoing edge to the
            // node that binds the variable's scope (e.g.: the rule node)?

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
        if !helper(self, subst, ix, pat) {
            *subst = None;
        }
    }

    // FIXME: doc
    fn unify_rule(
        &self,
        ix: NodeIndex,
        pat: RulePattern,
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

            // Match the label pattern against the graph node label.
            match pat_label {
                // If the label pattern is a label literal, check if the label
                // matches the one on the graph node.
                Some(Either::Left(ident)) => {
                    if graph_label != Some(ident) {
                        return None;
                    }
                }
                // If the label pattern is a label metavariable, it will
                // match iff the graph node has a label.
                Some(Either::Right(mvar)) => {
                    if graph_label == None {
                        return None;
                    }
                    // FIXME: maybe the result substitution should contain
                    // a mapping from the label metavariable?
                    // This would require that the PEG graph contain nodes
                    // for rule labels.
                }
                // If the label pattern is `None`, it will match iff the graph
                // node is unlabelled.
                None => {
                    if graph_label != None {
                        return None;
                    }
                }
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

            // Create the result substitution map.
            let mut subst = Substitution::new();

            // Get `BTreeSet`s corresponding to the set of metavariables in the
            // left- and right-hand-side substitutions.
            let lhs_keys = BTreeSet::from_iter(lhs_subst.keys());
            let rhs_keys = BTreeSet::from_iter(rhs_subst.keys());

            // If there are metavariables repeated between the left-hand-side
            // pattern and the right-hand-side pattern, the resultant
            // substitutions must map the same keys to the same values.
            for shared in lhs_keys.intersection(&rhs_keys) {
                if lhs_subst[shared] != rhs_subst[shared] {
                    return None;
                }
            }

            // Create the union of `lhs_subst` and `rhs_subst`.
            // If `lhs_subst` and `rhs_subst` share a key, they are guaranteed
            // by the previous code to have the same value for that key, so
            // this is well-defined.
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
        substs: &mut Option<HashSet<Substitution>>,
        ix: NodeIndex,
        pats: HashSet<RulePattern>,
    ) {
        fn search(
            epeg: &EPEG,
            rules: &[NodeIndex],
            pats: &[RulePattern],
        ) -> Option<HashSet<Substitution>> {
            let mut all = BTreeSet::new();
            for rule in rules {
                let mut matches = BTreeSet::new();
                for (i, pat) in pats.iter().enumerate() {
                    if let Some(s) = epeg.unify_rule(*rule, pat.clone()) {
                        matches.insert((i, s));
                    }
                }
                all.insert(matches);
            }

            fn foo(
                remaining: &[BTreeSet<(usize, Substitution)>],
                allowed: BTreeSet<usize>,
            ) -> HashSet<Substitution> {
                unimplemented!()
            }

            // all :: Vec<BTreeSet<(usize, Substitution)>>
            // req :: BTreeSet<usize>

            // we need to find the set of all sections of `all` that have every
            // `usize` in `req` such that no
            unimplemented!()
        }

        if let Some(system_node) = self.match_system(ix) {
            let mut rule_nodes = Vec::new();
            for n in system_node.rules() {
                if let Some(rule_node) = self.match_rule(n) {
                    rule_nodes.push(rule_node.0);
                } else if let Some(_comp_node) = self.match_composition(n) {
                    // We can't match against a composition node, for now...
                } else {
                    panic!("Child of a system node is not a rule or composition node!");
                }
            }
            let mut patterns = Vec::new();
            for pat in pats {
                patterns.push(pat);
            }
            *substs = search(self, &rule_nodes, &patterns);
        } else {
            *substs = None;
        }
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
                // self.unify_subsystem(&mut result, ix, subsystem);
                unimplemented!()
            }
        }
        result
    }
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    enum UTerm {
        UVar(String),
        UApply(String, Vec<UTerm>),
    }

    fn uvar(name: &str) -> UTerm {
        UTerm::UVar(name.to_string())
    }

    fn uconst(name: &str) -> UTerm {
        UTerm::UApply(name.to_string(), vec![])
    }

    fn uapply(name: &str, args: Vec<UTerm>) -> UTerm {
        UTerm::UApply(name.to_string(), args)
    }

    impl UTerm {
        fn infer_vars(&self) -> BTreeSet<Identifier> {
            match *self {
                UTerm::UVar(ref v) => {
                    let mut result = BTreeSet::new();
                    result.insert(Identifier::from(v.clone()));
                    result
                },
                UTerm::UApply(_, ref args) => {
                    let mut result = BTreeSet::new();
                    for arg in args {
                        for var in arg.infer_vars() {
                            result.insert(var);
                        }
                    }
                    result
                },
            }
        }

        fn infer_ops(&self) -> BTreeSet<(Identifier, usize)> {
            match *self {
                UTerm::UVar(_) => BTreeSet::new(),
                UTerm::UApply(ref f, ref args) => {
                    let mut result = BTreeSet::new();
                    result.insert((Identifier::from(f.clone()), args.len()));
                    for arg in args {
                        for op in arg.infer_ops() {
                            result.insert(op);
                        }
                    }
                    result
                },
            }
        }

        fn to_term(&self) -> rs::Term {
            match *self {
                UTerm::UVar(ref v) => {
                    rs::GenTerm::Var {
                        name: Identifier::from(v.clone())
                    }
                },
                UTerm::UApply(ref f, ref args) => {
                    rs::GenTerm::Op {
                        head: Identifier::from(f.clone()),
                        args: args.iter().map(|a| a.to_term()).collect(),
                    }
                },
            }
        }
    }

    struct URule(Option<String>, UTerm, UTerm);

    impl URule {
        fn infer_ops(&self) -> BTreeSet<(Identifier, usize)> {
            let mut result = BTreeSet::new();

            for lhs_op in self.1.infer_ops() {
                result.insert(lhs_op);
            }

            for rhs_op in self.2.infer_ops() {
                result.insert(rhs_op);
            }

            result
        }

        fn to_rule(&self) -> rs::Rule {
            rs::GenRule::new(
                self.0.clone().map(|x| Identifier::from(x)),
                self.1.to_term(),
                self.2.to_term(),
            )
        }
    }

    fn make_simple_rs(rules_vec: &[URule]) -> rs::RewritingSystem {
        let u = rs::Sort {
            name: Identifier::from("U"),
            supersorts: vec![],
        };

        let ops = {
            let ops_set: BTreeSet<(Identifier, usize)> = {
                let mut temp = BTreeSet::new();

                for rule in rules_vec {
                    for op in rule.infer_ops() {
                        temp.insert(op);
                    }
                }

                temp
            };

            let mut temp = Vec::new();

            for (name, arity) in ops_set {
                temp.push(rs::Operation {
                    name: Identifier::from(name),
                    arg_sorts: repeat(u.name.clone()).take(arity).collect(),
                    result_sort: u.name.clone(),
                    frozenness: rs::Frozenness::Unfrozen,
                });
            }

            temp
        };

        let rules = rules_vec.iter().map(|x| x.to_rule()).collect();

        rs::RewritingSystem {
            sorts: vec![u],
            ops: ops,
            eqs: vec![],
            rules: rules,
        }
    }

    #[test]
    fn monoid_example() {
        let rewriting_system = make_simple_rs(&[
            // A useless rule that can be deleted.
            URule(None,
                  uapply("succ", vec![uvar("x")]),
                  uapply("succ", vec![uvar("x")])),
            URule(Some("+-0-left-identity".to_string()),
                  uapply("_+_", vec![uconst("0"), uvar("x")]),
                  uvar("x")),
            URule(Some("+-0-right-identity".to_string()),
                  uapply("_+_", vec![uvar("x"), uconst("0")]),
                  uvar("x")),
            URule(Some("+-commutativity".to_string()),
                  uapply("_+_", vec![uvar("x"), uvar("y")]),
                  uapply("_+_", vec![uvar("y"), uvar("x")])),
            URule(Some("+-associativity".to_string()),
                  uapply("_+_", vec![
                      uapply("_+_", vec![uvar("x"), uvar("y")]),
                      uvar("z")]),
                  uapply("_+_", vec![
                      uvar("x"),
                      uapply("_+_", vec![uvar("y"), uvar("z")])])),
            URule(None,
                  uapply("_+_", vec![
                      uvar("x"),
                      uapply("succ", vec![uvar("y")])]),
                  uapply("succ", vec![
                      uapply("_+_", vec![uvar("x"), uvar("y")])]))
        ]);

        let peg = PEG::new(&rewriting_system);

        let epeg = EPEG::new(&peg);

        let pattern: RulePattern = ({
            URule(None,
                  uapply("_+_", vec![uvar("X"), uvar("Y")]),
                  uvar("Z"))
        }).to_rule().map_label(&|ref x| Either::Left((*x).clone()));

        for node in epeg.peg.graph.node_indices() {
            if let Some(subst) = epeg.unify_rule(node, pattern.clone()) {
                println!("Matched:");
                for sub in subst {
                    println!("  {:?}", sub);
                }
            }
        }

        use petgraph::dot::{Dot};
        println!("{}", Dot::with_config(&peg.graph, &[]));
    }
}

// -----------------------------------------------------------------------------
