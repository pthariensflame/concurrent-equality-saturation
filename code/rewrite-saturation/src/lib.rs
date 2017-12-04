//! The types in this crate assume all identifiers used are (scope-)unique.

extern crate itertools;
extern crate petgraph;
extern crate snowflake;
use std::fmt;

#[derive(Copy, Clone, Hash, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Void {}

impl Void {
    fn absurd(self) -> ! {
        match self {}
    }
}

impl fmt::Display for Void {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
        self.absurd()
    }
}

pub mod rewriting_system;

pub mod peg;

// pub mod simple_peg;
