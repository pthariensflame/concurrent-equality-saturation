// -----------------------------------------------------------------------------

use std::fmt;
use std::collections::*;
use std::iter::*;
use itertools::Either;
use petgraph::prelude::*;
use super::rewriting_system as rs;
pub use self::rs::Identifier;

// -----------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct BGraphInternal<A, B, W> {
    graph: UnGraph<Either<A, B>, W>,
    a_map: BTreeMap<A, NodeIndex>,
    b_map: BTreeMap<B, NodeIndex>,
}

/// FIXME: doc
#[derive(Debug, Clone)]
pub struct BGraph<A, B, W>(BGraphInternal<A, B, W>);

pub type Matching = BTreeSet<EdgeIndex>;

impl<A, B, W> BGraph<A, B, W> {
    /// FIXME: doc
    pub fn get_graph(&self) -> &UnGraph<Either<A, B>, W> {
        &self.0.graph
    }

    /// FIXME: doc
    pub fn get_a_map(&self) -> &BTreeMap<A, NodeIndex> {
        &self.0.a_map
    }

    /// FIXME: doc
    pub fn get_b_map(&self) -> &BTreeMap<B, NodeIndex> {
        &self.0.b_map
    }
    
    /// FIXME: doc
    pub fn new() -> BGraph<A, B, W> where A: Ord, B: Ord {
        let graph = UnGraph::<Either<A, B>, W>::new_undirected();
        let a_map = BTreeMap::new();
        let b_map = BTreeMap::new();
        BGraph(BGraphInternal { graph, a_map, b_map })
    }

    /// FIXME: doc
    pub fn add_l_node(&mut self, a: A) -> NodeIndex where A: Ord + Clone {
        if let Some(&ix) = self.0.a_map.get(&a) {
            ix
        } else {
            let ix = self.0.graph.add_node(Either::Left(a.clone()));
            self.0.a_map.insert(a, ix);
            ix
        }
    }

    /// FIXME: doc
    pub fn add_r_node(&mut self, b: B) -> NodeIndex where B: Ord + Clone {
        if let Some(&ix) = self.0.b_map.get(&b) {
            ix
        } else {
            let ix = self.0.graph.add_node(Either::Right(b.clone()));
            self.0.b_map.insert(b, ix);
            ix
        }
    }

    /// FIXME: doc
    pub fn add_edge(&mut self, a: A, b: B, weight: W) -> EdgeIndex
        where A: Ord + Clone, B: Ord + Clone
    {
        let a_node = self.add_l_node(a);
        let b_node = self.add_r_node(b);
        self.0.graph.add_edge(a_node, b_node, weight)
    }
    
    // FIXME: implement this algorithm
    // described in this paper by Takeaki Uno:
    // http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.107.8179
    /// FIXME: doc
    pub fn enum_perfect_matchings(&self) -> BTreeSet<Matching>
        where A: Ord + Clone, B: Ord + Clone
    {
        unimplemented!()
    }
}



// -----------------------------------------------------------------------------
