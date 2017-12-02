use std::fmt;

// -----------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Name(String);

impl<S: Into<String>> From<S> for Name {
    fn from(id: S) -> Name {
        Name(id.into())
    }
}

impl fmt::Display for Name {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Name(ref string) => fmt::Display::fmt(string, formatter)
        }
    }
}

pub fn mk_name<X: ?Sized + ToString>(value: &X) -> Name {
    Name(value.to_string())
}

// -----------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Statement {
    Seq(Vec<Statement>),
    Assign(Name, Expression),
    If(Expression, Box<Statement>, Box<Statement>),
    While(Expression, Box<Statement>),
}

impl fmt::Display for Statement {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Seq(ref statements) => {
                if statements.is_empty() {
                    write!(formatter, "{}", "{}")
                } else if statements.len() == 1 {
                    write!(formatter, "{}", statements[0])
                } else {
                    write!(formatter, "{}", statements[0])?;
                    for s in &statements[1..] {
                        write!(formatter, "; {}", s)?;
                    }
                    write!(formatter, "")
                }
            },
            Statement::Assign(ref name, ref expr) => {
                write!(formatter, "{} := {}", name, expr)
            },
            Statement::If(ref cond, ref then_statement, ref else_statement) => {
                write!(formatter, "if({}) {{ {} }} else {{ {} }}",
                       cond, *then_statement, *else_statement)
            },
            Statement::While(ref cond, ref body_statement) => {
                write!(formatter, "while({}) {{ {} }}",
                       cond, *body_statement)
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expression {
    Ref(Name),
    Apply(Name, Vec<Expression>),
}

impl fmt::Display for Expression {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Expression::Ref(ref name) => {
                write!(formatter, "{}", name)
            },
            Expression::Apply(ref func, ref args) => {
                if args.is_empty() {
                    write!(formatter, "{}()", func)
                } else if args.len() == 1 {
                    write!(formatter, "{}({})", func, args[0])
                } else {
                    write!(formatter, "{}({}", func, args[0])?;
                    for arg in &args[1..] {
                        write!(formatter, ", {}", arg)?;
                    }
                    write!(formatter, ")")
                }
            }
        }
    }
}

// -----------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CFG {

}

// -----------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PEG {
    Index { // "eval" in the thesis
        sequence: Box<PEG>,
        index:    Box<PEG>,
    },
    Until { // "pass" in the thesis
        sequence: Box<PEG>,
    },
    Iterate { // "θ" in the thesis
        initial:  Box<PEG>,
        function: Box<PEG>,
    },
}

// -----------------------------------------------------------------------------

// pub fn optimize(cfg : CFG) -> CFG {
//     // FIXME
// }

// -----------------------------------------------------------------------------

// `eval : ∀a. [a] × Int → a`
// | `eval(s, n)` gets the `n`th element of sequence `s`
//
// `pass : [Bool] → Int`
// | `pass(s)` returns the index of the first true element of `s`
//
// `θ : ∀a. a × (a → a) → [a]`
// | `θ(i, f)` returns the sequence resulting from repeatedly applying `f`
// | to itself, starting at `i`.
//
//

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use super::Statement::{Seq, Assign, If, While};
    use super::Expression::{Ref, Apply};

    #[test]
    fn expression_format_ref() {
        // check that formatting a `Ref` works
        let expression = Ref(mk_name("foobar"));
        assert_eq!("foobar", format!("{}", expression));
    }
    
    #[test]
    fn expression_format_apply() {
        { // check that formatting an empty `Apply` works
            assert_eq!("f()", format!("{}", Apply(mk_name("f"), vec![])));
        }

        { // check that formatting an `Apply` with 1 argument works
            let expression = Apply(mk_name("f"), vec![Ref(mk_name("a"))]);
            assert_eq!("f(a)", format!("{}", expression));
        }

        { // check that formatting an `Apply` with 2 arguments works
            let expression = Apply(
                mk_name("f"),
                vec![Ref(mk_name("a")), Ref(mk_name("b"))]);
            assert_eq!("f(a, b)", format!("{}", expression));
        }
        
        { // check that formatting an `Apply` with 3 arguments works
            let expression = Apply(
                mk_name("f"),
                vec![Ref(mk_name("a")), Ref(mk_name("b")), Ref(mk_name("c"))]);
            assert_eq!("f(a, b, c)", format!("{}", expression));
        }
    }
    
    #[test]
    fn statement_format_assign() {
        // check that formatting an `Assign` works
        assert_eq!("a := b",
                   format!("{}", Assign(mk_name("a"), Ref(mk_name("b")))));
    }

    #[test]
    fn statement_format_seq() {
        { // check that formatting an empty `Seq` works
            assert_eq!("{}", format!("{}", Seq(vec![])));
        }

        { // check that formatting a `Seq` with 1 substatement works
            let statement = Seq(vec![Assign(mk_name("a"), Ref(mk_name("b")))]);
            assert_eq!("a := b", format!("{}", statement));
        }

        { // check that formatting a `Seq` with 2 substatements works
            let statement = Seq(vec![
                Assign(mk_name("x2"), Ref(mk_name("x1"))),
                Assign(mk_name("x3"), Ref(mk_name("x2"))),
            ]);
            assert_eq!("x2 := x1; x3 := x2",
                       format!("{}", statement));
        }
        
        { // check that formatting a `Seq` with 3 substatements works
            let statement = Seq(vec![
                Assign(mk_name("x2"), Ref(mk_name("x1"))),
                Assign(mk_name("x3"), Ref(mk_name("x2"))),
                Assign(mk_name("x4"), Ref(mk_name("x3"))),
            ]);
            assert_eq!("x2 := x1; x3 := x2; x4 := x3",
                       format!("{}", statement));
        }
    }
    
    #[test]
    fn statement_format_if() {
        // check that formatting an `If` works
        let statement = If(
            Ref(mk_name("c")),
            Box::new(Assign(mk_name("y"),
                            Apply(mk_name("f"), vec![Ref(mk_name("x"))]))),
            Box::new(Assign(mk_name("y"),
                            Apply(mk_name("g"), vec![Ref(mk_name("x"))]))));
        assert_eq!("if(c) { y := f(x) } else { y := g(x) }",
                   format!("{}", statement));
    }
    
    #[test]
    fn statement_format_while() {
        // check that formatting a `While` works
        let statement = While(
            Apply(mk_name("p"), vec![Ref(mk_name("x"))]),
            Box::new(Assign(mk_name("x"),
                            Apply(mk_name("f"), vec![Ref(mk_name("x"))]))));
        assert_eq!("while(p(x)) { x := f(x) }",
                   format!("{}", statement));
    }
}

// -----------------------------------------------------------------------------
