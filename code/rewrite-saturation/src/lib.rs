extern crate itertools;
extern crate petgraph;
use std::fmt;
use itertools::{Either, Itertools, PeekingNext};
use petgraph::prelude::*;

pub mod rewriting_system;

pub mod peg;

pub mod simple_peg;
