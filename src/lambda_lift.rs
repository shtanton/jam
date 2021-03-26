use crate::logic::{
    Expression as LExpression, ExpressionKind as LExpressionKind, LPredicate,
    Proposition as LProposition, Sort,
};
use crate::syntax::{Constant, Predicate};

pub type FnIdentifier = u32;

pub type Identifier = u32;

#[derive(Debug)]
pub struct Function {
    pub id: FnIdentifier,
    pub parameters: Vec<(Identifier, Sort)>,
    pub body: Expression,
}

impl Function {
    pub fn substitute_fn(&mut self, expr: &Expression, fn_id: FnIdentifier) {
        self.body.substitute_fn(expr, fn_id);
    }
}

#[derive(Clone, Debug)]
pub enum Expression {
    Ast,
    Variable(Identifier, Sort),
    Function(FnIdentifier, Sort),
    Call(Constant, Vec<Expression>),
    Tuple(Box<(Expression, Expression)>),
    Application(Box<(Expression, Expression)>),
    First(Box<Expression>),
    Second(Box<Expression>),
}

impl Expression {
    pub fn typ(&self) -> Result<Sort, ()> {
        Ok(match self {
            Expression::Variable(_, typ) | Expression::Function(_, typ) => typ.clone(),
            Expression::Application(contents) => contents.0.typ()?.after_application()?,
            Expression::Ast | Expression::Call(_, _) => Sort::Value,
            Expression::First(arg) => {
                if let Sort::Product(pcontents) = arg.typ()? {
                    pcontents.0
                } else {
                    return Err(());
                }
            }
            Expression::Second(arg) => {
                if let Sort::Product(pcontents) = arg.typ()? {
                    pcontents.1
                } else {
                    return Err(());
                }
            }
            Expression::Tuple(contents) => {
                Sort::Product(Box::new((contents.0.typ()?, contents.1.typ()?)))
            }
        })
    }

    pub fn substitute_fn(&mut self, expr: &Expression, fn_id: FnIdentifier) {
        match self {
            Expression::Ast | Expression::Variable(_, _) => {}
            Expression::Function(id, _) => {
                if *id == fn_id {
                    *self = expr.clone();
                }
            }
            Expression::Call(_, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute_fn(expr, fn_id);
                });
            }
            Expression::Tuple(contents) => {
                contents.0.substitute_fn(expr, fn_id);
                contents.1.substitute_fn(expr, fn_id);
            }
            Expression::Application(contents) => {
                contents.0.substitute_fn(expr, fn_id);
                contents.1.substitute_fn(expr, fn_id);
            }
            Expression::First(arg) => {
                arg.substitute_fn(expr, fn_id);
            }
            Expression::Second(arg) => {
                arg.substitute_fn(expr, fn_id);
            }
        }
    }

    pub fn substitute(&mut self, expr: &Expression, var_id: Identifier) {
        match self {
            Expression::Ast | Expression::Function(_, _) => {}
            Expression::Variable(id, _) => {
                if *id == var_id {
                    *self = expr.clone();
                }
            }
            Expression::Call(_, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute_fn(expr, var_id);
                });
            }
            Expression::Tuple(contents) => {
                contents.0.substitute_fn(expr, var_id);
                contents.1.substitute_fn(expr, var_id);
            }
            Expression::Application(contents) => {
                contents.0.substitute_fn(expr, var_id);
                contents.1.substitute_fn(expr, var_id);
            }
            Expression::First(arg) => {
                arg.substitute_fn(expr, var_id);
            }
            Expression::Second(arg) => {
                arg.substitute_fn(expr, var_id);
            }
        }
    }
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

impl Proposition {
    pub fn substitute_fn(&mut self, expr: &Expression, fn_id: FnIdentifier) {
        match self {
            Proposition::False | Proposition::True => {}
            Proposition::And(contents) | Proposition::Implies(contents) => {
                contents.0.substitute_fn(expr, fn_id);
                contents.1.substitute_fn(expr, fn_id);
            }
            Proposition::Forall(_, _, prop) => {
                prop.substitute_fn(expr, fn_id);
            }
            Proposition::Call(_, args) | Proposition::CallLogic(_, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute_fn(expr, fn_id);
                });
            }
            Proposition::Equal(left, right) => {
                left.substitute_fn(expr, fn_id);
                right.substitute_fn(expr, fn_id);
            }
        }
    }

    pub fn substitute(&mut self, expr: &Expression, fn_id: FnIdentifier) {
        match self {
            Proposition::False | Proposition::True => {}
            Proposition::And(contents) | Proposition::Implies(contents) => {
                contents.0.substitute(expr, fn_id);
                contents.1.substitute(expr, fn_id);
            }
            Proposition::Forall(_, _, prop) => {
                prop.substitute(expr, fn_id);
            }
            Proposition::Call(_, args) | Proposition::CallLogic(_, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute(expr, fn_id);
                });
            }
            Proposition::Equal(left, right) => {
                left.substitute(expr, fn_id);
                right.substitute(expr, fn_id);
            }
        }
    }
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
        match &expr.kind {
            LExpressionKind::Abstraction(id, param_sort, body) => {
                let fn_id = self.next_fn_id();
                let body = self.lambda_lift_expression(body, fns);
                fns.push(Function {
                    id: fn_id,
                    parameters: vec![(*id, param_sort.clone())],
                    body,
                });
                Expression::Function(fn_id, expr.sort.clone())
            }
            LExpressionKind::Application(contents) => Expression::Application(Box::new((
                self.lambda_lift_expression(&contents.0, fns),
                self.lambda_lift_expression(&contents.1, fns),
            ))),
            LExpressionKind::Call(constant, args) => {
                let args = args
                    .into_iter()
                    .map(|arg| self.lambda_lift_expression(arg, fns))
                    .collect::<Vec<_>>();
                Expression::Call(*constant, args)
            }
            LExpressionKind::First(arg) => {
                Expression::First(Box::new(self.lambda_lift_expression(&arg, fns)))
            }
            LExpressionKind::Second(arg) => {
                Expression::Second(Box::new(self.lambda_lift_expression(&arg, fns)))
            }
            LExpressionKind::Tuple(contents) => Expression::Tuple(Box::new((
                self.lambda_lift_expression(&contents.0, fns),
                self.lambda_lift_expression(&contents.1, fns),
            ))),
            LExpressionKind::Variable(id) => Expression::Variable(*id, expr.sort.clone()),
            LExpressionKind::Ast => Expression::Ast,
        }
    }

    pub fn lambda_lift(&mut self, prop: &LProposition) -> (Proposition, Vec<Function>) {
        let mut fns = Vec::new();
        let prop = self.lambda_lift_proposition(prop, &mut fns);
        (prop, fns)
    }
}
