use crate::syntax::{
    Predicate,
    Constant,
};
use crate::semantic::{
    Sort,
};

pub type Identifier = u32;

#[derive(Clone)]
pub enum Proposition {
    False,
    True,
    And(Box<(Proposition, Proposition)>),
    Implies(Box<(Proposition, Proposition)>),
    Forall(Identifier, Sort, Box<Proposition>),
    Call(Predicate, Vec<Expression>),
    Equal(Expression, Expression),
}

impl Proposition {
    pub fn substitute(&mut self, expr: &Expression, id: Identifier) {
        match self {
            Proposition::False => {},
            Proposition::True => {},
            Proposition::And(args) => {
                args.0.substitute(expr, id);
                args.1.substitute(expr, id);
            },
            Proposition::Implies(args) => {
                args.0.substitute(expr, id);
                args.1.substitute(expr, id);
            },
            Proposition::Forall(forall_id, sort, prop) => {
                if *forall_id != id {
                    prop.substitute(expr, id);
                }
            },
            Proposition::Call(pred, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute(expr, id);
                });
            },
            Proposition::Equal(left, right) => {
                left.substitute(expr, id);
                right.substitute(expr, id);
            },
        }
    }
}

#[derive(Clone)]
pub enum Expression {
    Variable(Identifier),
    Call(Constant, Vec<Expression>),
    Tuple(Box<(Expression, Expression)>),
    Abstraction(Identifier, Box<Expression>),
    Application(Box<(Expression, Expression)>),
    First(Box<Expression>),
    Second(Box<Expression>),
}

impl Expression {
    pub fn substitute(&mut self, expr: &Expression, id: Identifier) {
        match self {
            Expression::Variable(var) => {
                if *var == id {
                    *self = expr.clone();
                }
            },
            Expression::Call(constant, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute(expr, id);
                });
            },
            Expression::Tuple(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            },
            Expression::Abstraction(arg, body) => {
                if *arg != id {
                    body.substitute(expr, id);
                }
            },
            Expression::Application(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            },
            Expression::First(arg) => {
                arg.substitute(expr, id);
            },
            Expression::Second(arg) => {
                arg.substitute(expr, id);
            },
        }
    }
}
