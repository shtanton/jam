use crate::lambda_lift::{FnIdentifier, Identifier};
use crate::logic::LPredicate;
use crate::remove_pairs::{
    Expression as RPExpression, Function as RPFunction, Proposition as RPProposition, Type,
};
use crate::syntax::{Constant, Predicate};

pub struct Function {
    id: FnIdentifier,
    parameters: Vec<Identifier>,
    body: Expression,
}

pub enum Expression {
    Ast,
    Variable(Identifier),
    Call(Constant, Vec<Expression>),
    Application(FnIdentifier, Vec<Expression>),
}

impl Expression {
    /*pub fn count_parameters(&self) -> Result<u32, ()> {
        Ok(match self {
            Expression::Application(contents) => {
                let fun_count = contents.0.count_parameters()?;
                if fun_count > 0 {
                    fun_count - 1
                } else {
                    return Err(());
                }
            }
            Expression::Ast | Expression::Call(_, _) | Expression::Variable(_) => 0,
            Expression::Function(_, n) => *n,
        })
    }*/
}

pub enum Proposition {
    False,
    True,
    And(Box<(Proposition, Proposition)>),
    Implies(Box<(Proposition, Proposition)>),
    Forall(Identifier, Type, Box<Proposition>),
    Call(Predicate, Vec<Expression>),
    CallLogic(LPredicate, Vec<Expression>),
    Equal(Expression, Expression),
}

fn rewrite_expression(expr: RPExpression) -> Result<Expression, ()> {
    Ok(match expr {
        RPExpression::Application(contents) => {
            let ((fun_id, _), mut args) = deconstruct_applications(contents.0)?;
            args.push(contents.1);
            let args = args
                .into_iter()
                .map(rewrite_expression)
                .collect::<Result<Vec<_>, ()>>()?;
            Expression::Application(fun_id, args)
        }
        RPExpression::Ast => Expression::Ast,
        RPExpression::Call(constant, args) => Expression::Call(
            constant,
            args.into_iter()
                .map(rewrite_expression)
                .collect::<Result<Vec<_>, ()>>()?,
        ),
        RPExpression::Function(id, _) => Expression::Application(id, Vec::new()),
        RPExpression::Variable(id, _) => Expression::Variable(id),
    })
}

fn rewrite_proposition(prop: RPProposition) -> Result<Proposition, ()> {
    Ok(match prop {
        RPProposition::And(contents) => Proposition::And(Box::new((
            rewrite_proposition(contents.0)?,
            rewrite_proposition(contents.1)?,
        ))),
        RPProposition::Implies(contents) => Proposition::Implies(Box::new((
            rewrite_proposition(contents.0)?,
            rewrite_proposition(contents.1)?,
        ))),
        RPProposition::Call(pred, args) => Proposition::Call(
            pred,
            args.into_iter()
                .map(rewrite_expression)
                .collect::<Result<Vec<_>, ()>>()?,
        ),
        RPProposition::CallLogic(pred, args) => Proposition::CallLogic(
            pred,
            args.into_iter()
                .map(rewrite_expression)
                .collect::<Result<Vec<_>, ()>>()?,
        ),
        RPProposition::Equal(left, right) => {
            Proposition::Equal(rewrite_expression(left)?, rewrite_expression(right)?)
        }
        RPProposition::False => Proposition::False,
        RPProposition::Forall(id, typ, body) => {
            Proposition::Forall(id, typ, Box::new(rewrite_proposition(*body)?))
        }
        RPProposition::True => Proposition::True,
    })
}

fn deconstruct_applications(
    mut expr: RPExpression,
) -> Result<((FnIdentifier, Type), Vec<RPExpression>), ()> {
    let mut reversed_args = Vec::new();
    while let RPExpression::Application(contents) = expr {
        let (fun, arg) = *contents;
        reversed_args.push(arg);
        expr = fun;
    }
    if let RPExpression::Function(id, typ) = expr {
        Ok(((id, typ), reversed_args.into_iter().rev().collect()))
    } else {
        Err(())
    }
}

fn construct_applications(mut fun: RPExpression, args: Vec<RPExpression>) -> RPExpression {
    for arg in args.into_iter() {
        fun = RPExpression::Application(Box::new((fun, arg)));
    }
    fun
}

pub struct Specializer {
    _next_fn_id: u32,
    _next_id: u32,
}

impl Specializer {
    pub fn next_fn_id(&mut self) -> FnIdentifier {
        let id = self._next_fn_id;
        self._next_fn_id += 1;
        id
    }

    pub fn next_id(&mut self) -> Identifier {
        let id = self._next_id;
        self._next_id += 1;
        id
    }

    fn specialize_expression(
        &mut self,
        expr: RPExpression,
        fns: &mut Vec<RPFunction>,
    ) -> Result<RPExpression, ()> {
        Ok(match expr {
            RPExpression::Application(contents) => {
                let (fun, arg) = *contents;
                let fun = self.specialize_expression(fun, fns)?;
                let arg = self.specialize_expression(arg, fns)?;
                if let Type::Function(_) = arg.typ()? {
                    let (original_arg_fn, arg_args) = deconstruct_applications(arg)?;
                    let (original_fn, fn_args) = deconstruct_applications(fun)?;
                    let mut fun_defn = fns
                        .iter()
                        .find(|fun| fun.id == original_fn.0)
                        .ok_or(())?
                        .clone();
                    fun_defn.id = self.next_fn_id();
                    let new_param_ids = (0..arg_args.len())
                        .into_iter()
                        .map(|_| self.next_id())
                        .collect::<Vec<_>>();
                    let sub = construct_applications(
                        RPExpression::Function(original_arg_fn.0, original_arg_fn.1),
                        new_param_ids
                            .iter()
                            .map(|id| RPExpression::Variable(*id, Type::Value))
                            .collect::<Vec<_>>(),
                    );
                    let (old_param_id, _) = fun_defn
                        .parameters
                        .splice(
                            fn_args.len()..(fn_args.len() + 1),
                            new_param_ids.into_iter().map(|id| (id, Type::Value)),
                        )
                        .next()
                        .ok_or(())?;
                    fun_defn.body.substitute(&sub, old_param_id);
                    let new_fn_expr = RPExpression::Function(fun_defn.id, fun_defn.typ()?);
                    fns.push(fun_defn);
                    construct_applications(construct_applications(new_fn_expr, fn_args), arg_args)
                } else {
                    RPExpression::Application(Box::new((fun, arg)))
                }
            }
            RPExpression::Ast | RPExpression::Variable(_, _) | RPExpression::Function(_, _) => expr,
            RPExpression::Call(constant, args) => RPExpression::Call(
                constant,
                args.into_iter()
                    .map(|arg| self.specialize_expression(arg, fns))
                    .collect::<Result<Vec<_>, ()>>()?,
            ),
        })
    }

    fn specialize_proposition(
        &mut self,
        prop: RPProposition,
        fns: &mut Vec<RPFunction>,
    ) -> Result<RPProposition, ()> {
        Ok(match prop {
            RPProposition::And(contents) => RPProposition::And(Box::new((
                self.specialize_proposition(contents.0, fns)?,
                self.specialize_proposition(contents.1, fns)?,
            ))),
            RPProposition::Implies(contents) => RPProposition::Implies(Box::new((
                self.specialize_proposition(contents.0, fns)?,
                self.specialize_proposition(contents.1, fns)?,
            ))),
            RPProposition::Call(pred, args) => RPProposition::Call(
                pred,
                args.into_iter()
                    .map(|arg| self.specialize_expression(arg, fns))
                    .collect::<Result<Vec<_>, ()>>()?,
            ),
            RPProposition::CallLogic(pred, args) => RPProposition::CallLogic(
                pred,
                args.into_iter()
                    .map(|arg| self.specialize_expression(arg, fns))
                    .collect::<Result<Vec<_>, ()>>()?,
            ),
            RPProposition::Equal(left, right) => RPProposition::Equal(
                self.specialize_expression(left, fns)?,
                self.specialize_expression(right, fns)?,
            ),
            RPProposition::False | RPProposition::True => prop,
        })
    }

    pub fn specialize(
        &mut self,
        prop: RPProposition,
        mut fns: Vec<RPFunction>,
    ) -> Result<(Proposition, Vec<Function>), ()> {
        let reversed_new_fns = Vec::new();
        let prop = self.specialize_proposition(prop, &mut fns)?;
        while let Some(fun) = fns.pop() {
            let is_specialized =
                fun.parameters
                    .iter()
                    .all(|(_, typ)| if let Type::Value = typ { true } else { false });
            if is_specialized {
                reversed_new_fns.push(Function {
                    body: rewrite_expression(self.specialize_expression(fun.body, &mut fns)?)?,
                    id: fun.id,
                    parameters: fun.parameters.into_iter().map(|(id, _)| id).collect(),
                });
            }
        }
        let new_fns = reversed_new_fns.into_iter().rev().collect();
        Ok((rewrite_proposition(prop)?, new_fns))
    }
}
