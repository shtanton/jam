use crate::logic::{Expression as LExpression, LPredicate, Proposition as LProposition, Sort};
use crate::syntax::{Constant, Predicate};

type FnIdentifier = u32;

type Identifier = u32;

#[derive(Debug)]
pub struct Function {
    id: FnIdentifier,
    parameters: Vec<(Identifier, Sort)>,
    body: Expression,
}

#[derive(Debug)]
pub enum Expression {
    Ast,
    Variable(Identifier),
    Function(FnIdentifier),
    Call(Constant, Vec<Expression>),
    Tuple(Box<(Expression, Expression)>),
    Application(Box<(Expression, Expression)>),
    First(Box<Expression>),
    Second(Box<Expression>),
}

#[derive(Debug)]
pub enum Proposition {
    False,
    True,
    And(Box<(Proposition, Proposition)>),
    Implies(Box<(Proposition, Proposition)>),
    Forall(Identifier, Sort, Box<Proposition>),
    Call(Predicate, Vec<Expression>),
    CallLogic(LPredicate, Vec<Expression>),
    Equal(Expression, Expression),
}

pub struct LambdaLifter {
    _next_fn_id: u32,
}

impl LambdaLifter {
    pub fn new() -> LambdaLifter {
        LambdaLifter { _next_fn_id: 0 }
    }

    fn next_fn_id(&mut self) -> FnIdentifier {
        let id = self._next_fn_id;
        self._next_fn_id += 1;
        id
    }

    fn lambda_lift_proposition(
        &mut self,
        prop: &LProposition,
        fns: &mut Vec<Function>,
    ) -> Proposition {
        match prop {
            LProposition::False => Proposition::False,
            LProposition::True => Proposition::True,
            LProposition::And(contents) => {
                let left = self.lambda_lift_proposition(&contents.0, fns);
                let right = self.lambda_lift_proposition(&contents.1, fns);
                Proposition::And(Box::new((left, right)))
            }
            LProposition::Implies(contents) => {
                let left = self.lambda_lift_proposition(&contents.0, fns);
                let right = self.lambda_lift_proposition(&contents.1, fns);
                Proposition::Implies(Box::new((left, right)))
            }
            LProposition::Forall(id, sort, forall_prop) => Proposition::Forall(
                *id,
                sort.clone(),
                Box::new(self.lambda_lift_proposition(&forall_prop, fns)),
            ),
            LProposition::Call(pred, args) => {
                let args = args
                    .into_iter()
                    .map(|arg| self.lambda_lift_expression(arg, fns))
                    .collect::<Vec<_>>();
                Proposition::Call(*pred, args)
            }
            LProposition::CallLogic(pred, args) => {
                let args = args
                    .into_iter()
                    .map(|arg| self.lambda_lift_expression(arg, fns))
                    .collect::<Vec<_>>();
                Proposition::CallLogic(*pred, args)
            }
            LProposition::Equal(left, right) => Proposition::Equal(
                self.lambda_lift_expression(left, fns),
                self.lambda_lift_expression(right, fns),
            ),
        }
    }

    fn lambda_lift_expression(
        &mut self,
        expr: &LExpression,
        fns: &mut Vec<Function>,
    ) -> Expression {
        match expr {
            LExpression::Abstraction(id, sort, body) => {
                let fn_id = self.next_fn_id();
                let body = self.lambda_lift_expression(body, fns);
                fns.push(Function {
                    id: fn_id,
                    parameters: vec![(*id, sort.clone())],
                    body,
                });
                Expression::Function(fn_id)
            }
            LExpression::Application(contents) => Expression::Application(Box::new((
                self.lambda_lift_expression(&contents.0, fns),
                self.lambda_lift_expression(&contents.1, fns),
            ))),
            LExpression::Call(constant, args) => {
                let args = args
                    .into_iter()
                    .map(|arg| self.lambda_lift_expression(arg, fns))
                    .collect::<Vec<_>>();
                Expression::Call(*constant, args)
            }
            LExpression::First(arg) => {
                Expression::First(Box::new(self.lambda_lift_expression(&arg, fns)))
            }
            LExpression::Second(arg) => {
                Expression::Second(Box::new(self.lambda_lift_expression(&arg, fns)))
            }
            LExpression::Tuple(contents) => Expression::Tuple(Box::new((
                self.lambda_lift_expression(&contents.0, fns),
                self.lambda_lift_expression(&contents.1, fns),
            ))),
            LExpression::Variable(id) => Expression::Variable(*id),
            LExpression::Ast => Expression::Ast,
        }
    }

    pub fn lambda_lift(&mut self, prop: &LProposition) -> (Proposition, Vec<Function>) {
        let mut fns = Vec::new();
        let prop = self.lambda_lift_proposition(prop, &mut fns);
        (prop, fns)
    }
}
