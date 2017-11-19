extern crate itertools;
extern crate petgraph;
#[macro_use] extern crate quickcheck;
#[macro_use] extern crate quickcheck_derive;
use itertools::{Itertools, PeekingNext};
use petgraph::prelude::*;
use quickcheck::Arbitrary;

pub mod rewriting_system;
