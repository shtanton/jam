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
    /// The id of the function being referenced and how many parameters it takes
    Function(FnIdentifier, u32),
    Call(Constant, Vec<Expression>),
    Application(Box<(Expression, Expression)>),
}

impl Expression {
    /// How many arguments this expression is expecting
    pub fn count_parameters(&self) -> Result<u32, ()> {
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
    }
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

fn deconstruct_applications(
    mut expr: RPExpression,
) -> Result<((FnIdentifier, Type), Vec<RPExpression>), ()> {
    let mut args = Vec::new();
    while let RPExpression::Application(contents) = expr {
        let (fun, arg) = *contents;
        args.push(arg);
        expr = fun;
    }
    if let RPExpression::Function(id, typ) = expr {
        Ok(((id, typ), args))
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
}

impl Specializer {
    pub fn next_fn_id(&mut self) -> FnIdentifier {
        let id = self._next_fn_id;
        self._next_fn_id += 1;
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
                    let new_fn_id = self.next_fn_id();
                    let new_fn_expr = RPExpression::Function(
                        self.next_fn_id(),
                        original_arg_fn.1 + original_fn.1 - 1,
                    );
                    construct_applications(construct_applications(new_fn_expr, fn_args), arg_args)
                } else {
                }
            }
        })
    }

    pub fn specialize(
        &mut self,
        prop: RPProposition,
        fns: Vec<RPFunction>,
    ) -> (Proposition, Vec<Function>) {
    }
}
