use crate::lambda_lift::{
    Expression as LLExpression, FnIdentifier, Function as LLFunction, Identifier,
    Proposition as LLProposition,
};
use crate::logic::{LPredicate, Sort};
use crate::syntax::{Constant, Predicate};
use std::fmt;

fn remove_pair_returns_from_sort(sort: Sort) -> Sort {
    match sort {
        Sort::Function(contents) => {
            let param_type = remove_pair_returns_from_sort(contents.0);
            let return_type = remove_pair_returns_from_sort(contents.1);
            if let Sort::Product(pcontents) = return_type {
                Sort::Product(Box::new((
                    Sort::Function(Box::new((param_type.clone(), pcontents.0))),
                    Sort::Function(Box::new((param_type, pcontents.1))),
                )))
            } else {
                Sort::Function(Box::new((param_type, return_type)))
            }
        }
        Sort::Product(contents) => Sort::Product(Box::new((
            remove_pair_returns_from_sort(contents.0),
            remove_pair_returns_from_sort(contents.1),
        ))),
        Sort::Value => Sort::Value,
    }
}

fn function_type(parameters: &Vec<(Identifier, Sort)>, ret_type: &Sort) -> Sort {
    let mut typ = ret_type.clone();
    for (_, param_type) in parameters.iter().rev() {
        typ = Sort::Function(Box::new((param_type.clone(), typ)));
    }
    typ
}

fn param_tree_to_expression(tree: &Tree<(Identifier, Sort)>) -> LLExpression {
    match tree {
        Tree::Leaf((id, sort)) => LLExpression::Variable(*id, sort.clone()),
        Tree::Branch(contents) => {
            let first = param_tree_to_expression(&contents.0);
            let second = param_tree_to_expression(&contents.1);
            LLExpression::Tuple(Box::new((first, second)))
        }
    }
}

fn remove_pair_parameters_from_sort(sort: Sort) -> Sort {
    match sort {
        Sort::Function(contents) => {
            let param_type = remove_pair_parameters_from_sort(contents.0);
            let return_type = remove_pair_parameters_from_sort(contents.1);
            if let Sort::Product(pcontents) = param_type {
                Sort::Function(Box::new((
                    pcontents.0,
                    Sort::Function(Box::new((pcontents.1, return_type))),
                )))
            } else {
                Sort::Function(Box::new((param_type, return_type)))
            }
        }
        Sort::Product(contents) => Sort::Product(Box::new((
            remove_pair_parameters_from_sort(contents.0),
            remove_pair_parameters_from_sort(contents.1),
        ))),
        Sort::Value => Sort::Value,
    }
}

fn generate_arg_tree(arg: LLExpression) -> Result<Tree<LLExpression>, ()> {
    Ok(match arg.typ()? {
        Sort::Product(_) => Tree::Branch(Box::new((
            generate_arg_tree(LLExpression::First(Box::new(arg.clone())))?,
            generate_arg_tree(LLExpression::Second(Box::new(arg)))?,
        ))),
        Sort::Value | Sort::Function(_) => Tree::Leaf(arg),
    })
}

fn generate_pairless_application(
    fun: LLExpression,
    args: Vec<LLExpression>,
) -> Result<LLExpression, ()> {
    let mut application = fun;
    for arg in args.into_iter() {
        application = LLExpression::Application(Box::new((application, arg)));
    }
    Ok(application)
}

fn remove_pair_parameters_from_expression(expr: LLExpression) -> Result<LLExpression, ()> {
    Ok(match expr {
        LLExpression::Application(contents) => {
            let fun = remove_pair_parameters_from_expression(contents.0)?;
            let arg = remove_pair_parameters_from_expression(contents.1)?;
            let arg_tree = generate_arg_tree(arg)?;
            generate_pairless_application(fun, arg_tree.to_vec())?
        }
        LLExpression::Ast | LLExpression::Variable(_, _) => expr,
        LLExpression::Function(id, typ) => {
            LLExpression::Function(id, remove_pair_parameters_from_sort(typ))
        }
        LLExpression::Call(constant, args) => LLExpression::Call(
            constant,
            args.into_iter()
                .map(|arg| remove_pair_parameters_from_expression(arg))
                .collect::<Result<Vec<_>, ()>>()?,
        ),
        LLExpression::First(arg) => {
            let arg = remove_pair_parameters_from_expression(*arg)?;
            LLExpression::First(Box::new(arg))
        }
        LLExpression::Second(arg) => {
            let arg = remove_pair_parameters_from_expression(*arg)?;
            LLExpression::Second(Box::new(arg))
        }
        LLExpression::Tuple(contents) => {
            let first = remove_pair_parameters_from_expression(contents.0)?;
            let second = remove_pair_parameters_from_expression(contents.1)?;
            LLExpression::Tuple(Box::new((first, second)))
        }
    })
}

fn generate_pairless_forall(body: LLProposition, vars: Vec<(Identifier, Sort)>) -> LLProposition {
    let mut forall = body;
    for var in vars.into_iter() {
        forall = LLProposition::Forall(var.0, var.1, Box::new(forall));
    }
    forall
}

/// Replace all <t_1, t_2>t' with <t_1 t', t_2 t'> and all pi_i(t) t' with pi_i(t t')
fn remove_applied_pairs_from_expression(expr: LLExpression) -> Result<LLExpression, ()> {
    Ok(match expr {
        LLExpression::Application(contents) => {
            let fun = remove_applied_pairs_from_expression(contents.0)?;
            let arg = remove_applied_pairs_from_expression(contents.1)?;
            match fun {
                LLExpression::Tuple(tcontents) => LLExpression::Tuple(Box::new((
                    LLExpression::Application(Box::new((tcontents.0, arg.clone()))),
                    LLExpression::Application(Box::new((tcontents.1, arg))),
                ))),
                LLExpression::First(parg) => {
                    LLExpression::First(Box::new(LLExpression::Application(Box::new((*parg, arg)))))
                }
                LLExpression::Second(parg) => LLExpression::Second(Box::new(
                    LLExpression::Application(Box::new((*parg, arg))),
                )),
                _ => LLExpression::Application(Box::new((fun, arg))),
            }
        }
        LLExpression::Ast | LLExpression::Function(_, _) | LLExpression::Variable(_, _) => expr,
        LLExpression::Call(constant, args) => LLExpression::Call(
            constant,
            args.into_iter()
                .map(|arg| remove_applied_pairs_from_expression(arg))
                .collect::<Result<Vec<_>, ()>>()?,
        ),
        LLExpression::First(arg) => {
            LLExpression::First(Box::new(remove_applied_pairs_from_expression(*arg)?))
        }
        LLExpression::Second(arg) => {
            LLExpression::Second(Box::new(remove_applied_pairs_from_expression(*arg)?))
        }
        LLExpression::Tuple(contents) => LLExpression::Tuple(Box::new((
            remove_applied_pairs_from_expression(contents.0)?,
            remove_applied_pairs_from_expression(contents.1)?,
        ))),
    })
}

fn remove_applied_pairs_from_proposition(prop: LLProposition) -> Result<LLProposition, ()> {
    Ok(match prop {
        LLProposition::True | LLProposition::False => prop,
        LLProposition::And(contents) => LLProposition::And(Box::new((
            remove_applied_pairs_from_proposition(contents.0)?,
            remove_applied_pairs_from_proposition(contents.1)?,
        ))),
        LLProposition::Implies(contents) => LLProposition::Implies(Box::new((
            remove_applied_pairs_from_proposition(contents.0)?,
            remove_applied_pairs_from_proposition(contents.1)?,
        ))),
        LLProposition::Call(pred, args) => LLProposition::Call(
            pred,
            args.into_iter()
                .map(|arg| remove_applied_pairs_from_expression(arg))
                .collect::<Result<Vec<_>, ()>>()?,
        ),
        LLProposition::CallLogic(pred, args) => LLProposition::CallLogic(
            pred,
            args.into_iter()
                .map(|arg| remove_applied_pairs_from_expression(arg))
                .collect::<Result<Vec<_>, ()>>()?,
        ),
        LLProposition::Equal(left, right) => LLProposition::Equal(
            remove_applied_pairs_from_expression(left)?,
            remove_applied_pairs_from_expression(right)?,
        ),
        LLProposition::Forall(id, typ, body) => LLProposition::Forall(
            id,
            typ,
            Box::new(remove_applied_pairs_from_proposition(*body)?),
        ),
    })
}

fn fn_tree_to_expression(tree: &Tree<LLFunction>) -> Result<LLExpression, ()> {
    Ok(match tree {
        Tree::Leaf(LLFunction {
            id,
            parameters,
            body,
        }) => LLExpression::Function(*id, function_type(parameters, &body.typ()?)),
        Tree::Branch(contents) => LLExpression::Tuple(Box::new((
            fn_tree_to_expression(&contents.0)?,
            fn_tree_to_expression(&contents.1)?,
        ))),
    })
}

#[derive(Clone)]
pub enum Type {
    Value,
    Function(Box<(Type, Type)>),
}

impl fmt::Debug for Type {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Value => write!(formatter, "v"),
            Type::Function(contents) => write!(formatter, "({:?}->{:?})", contents.0, contents.1),
        }
    }
}

impl Type {
    pub fn args(mut self) -> Vec<Type> {
        let mut args = Vec::new();
        while let Type::Function(contents) = self {
            args.push(contents.0);
            self = contents.1;
        }
        args
    }
}

#[derive(Clone)]
pub enum Expression {
    Ast,
    Variable(Identifier, Type),
    Function(FnIdentifier, Type),
    Call(Constant, Vec<Expression>),
    Application(Box<(Expression, Expression)>),
}

impl fmt::Debug for Expression {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Ast => write!(formatter, "*"),
            Expression::Variable(id, typ) => write!(formatter, "(x{}:{:?})", id, typ),
            Expression::Function(id, typ) => write!(formatter, "(f{}:{:?})", id, typ),
            Expression::Call(constant, args) => write!(formatter, "({:?} {:?})", constant, args),
            Expression::Application(contents) => {
                write!(formatter, "({:?} {:?})", contents.0, contents.1)
            }
        }
    }
}

impl Expression {
    pub fn typ(&self) -> Result<Type, ()> {
        Ok(match self {
            Expression::Application(contents) => {
                if let Type::Function(fcontents) = contents.0.typ()? {
                    fcontents.1
                } else {
                    return Err(());
                }
            }
            Expression::Ast | Expression::Call(_, _) => Type::Value,
            Expression::Function(_, typ) | Expression::Variable(_, typ) => typ.clone(),
        })
    }

    pub fn substitute(&mut self, expr: &Expression, target: Identifier) {
        match self {
            Expression::Variable(id, _) => {
                if *id == target {
                    *self = expr.clone();
                }
            }
            Expression::Application(contents) => {
                contents.0.substitute(expr, target);
                contents.1.substitute(expr, target);
            }
            Expression::Ast | Expression::Function(_, _) => {}
            Expression::Call(_, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute(expr, target);
                });
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Function {
    pub id: FnIdentifier,
    pub parameters: Vec<(Identifier, Type)>,
    pub body: Expression,
}

impl Function {
    pub fn typ(&self) -> Result<Type, ()> {
        let mut typ = self.body.typ()?;
        for (_, param_type) in self.parameters.iter().rev() {
            typ = Type::Function(Box::new((param_type.clone(), typ)));
        }
        Ok(typ)
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

impl fmt::Debug for Proposition {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Proposition::False => write!(formatter, "false"),
            Proposition::True => write!(formatter, "true"),
            Proposition::And(contents) => {
                write!(formatter, "({:?} and {:?})", contents.0, contents.1)
            }
            Proposition::Implies(contents) => {
                write!(formatter, "({:?} => {:?})", contents.0, contents.1)
            }
            Proposition::Forall(id, typ, body) => {
                write!(formatter, "(forall x{} in {:?} . {:?})", id, typ, body)
            }
            Proposition::Call(pred, args) => write!(formatter, "({:?} {:?})", pred, args),
            Proposition::CallLogic(pred, args) => write!(formatter, "({:?} {:?})", pred, args),
            Proposition::Equal(left, right) => write!(formatter, "({:?} = {:?})", left, right),
        }
    }
}

/// Returns an equivalent expression without pi_i expressions
fn remove_pair_literals_from_expression(expr: LLExpression) -> Result<LLExpression, ()> {
    Ok(match expr {
        LLExpression::First(arg) => {
            let arg = remove_pair_literals_from_expression(*arg)?;
            if let LLExpression::Tuple(contents) = arg {
                contents.0
            } else {
                return Err(());
            }
        }
        LLExpression::Second(arg) => {
            let arg = remove_pair_literals_from_expression(*arg)?;
            if let LLExpression::Tuple(contents) = arg {
                contents.1
            } else {
                return Err(());
            }
        }
        LLExpression::Ast | LLExpression::Function(_, _) | LLExpression::Variable(_, _) => expr,
        LLExpression::Tuple(contents) => LLExpression::Tuple(Box::new((
            remove_pair_literals_from_expression(contents.0)?,
            remove_pair_literals_from_expression(contents.1)?,
        ))),
        LLExpression::Application(contents) => LLExpression::Application(Box::new((
            remove_pair_literals_from_expression(contents.0)?,
            remove_pair_literals_from_expression(contents.1)?,
        ))),
        LLExpression::Call(constant, args) => LLExpression::Call(
            constant,
            args.into_iter()
                .map(|arg| remove_pair_literals_from_expression(arg))
                .collect::<Result<Vec<_>, ()>>()?,
        ),
    })
}

fn remove_pair_literals_from_proposition(prop: LLProposition) -> Result<LLProposition, ()> {
    Ok(match prop {
        LLProposition::True | LLProposition::False => prop,
        LLProposition::And(contents) => LLProposition::And(Box::new((
            remove_pair_literals_from_proposition(contents.0)?,
            remove_pair_literals_from_proposition(contents.1)?,
        ))),
        LLProposition::Implies(contents) => LLProposition::Implies(Box::new((
            remove_pair_literals_from_proposition(contents.0)?,
            remove_pair_literals_from_proposition(contents.1)?,
        ))),
        LLProposition::Call(pred, args) => LLProposition::Call(
            pred,
            args.into_iter()
                .map(|arg| remove_pair_literals_from_expression(arg))
                .collect::<Result<Vec<_>, ()>>()?,
        ),
        LLProposition::CallLogic(pred, args) => LLProposition::CallLogic(
            pred,
            args.into_iter()
                .map(|arg| remove_pair_literals_from_expression(arg))
                .collect::<Result<Vec<_>, ()>>()?,
        ),
        LLProposition::Equal(left, right) => LLProposition::Equal(
            remove_pair_literals_from_expression(left)?,
            remove_pair_literals_from_expression(right)?,
        ),
        LLProposition::Forall(id, typ, body) => LLProposition::Forall(
            id,
            typ,
            Box::new(remove_pair_literals_from_proposition(*body)?),
        ),
    })
}

/// Translates an expression that already doesn't contain any use of tuples from LLExpresion to Expression
fn pairless_expression(expr: LLExpression) -> Result<Expression, ()> {
    Ok(match expr {
        LLExpression::Application(contents) => Expression::Application(Box::new((
            pairless_expression(contents.0)?,
            pairless_expression(contents.1)?,
        ))),
        LLExpression::Ast => Expression::Ast,
        LLExpression::Call(constant, args) => Expression::Call(
            constant,
            args.into_iter()
                .map(pairless_expression)
                .collect::<Result<Vec<_>, ()>>()?,
        ),
        LLExpression::First(_) | LLExpression::Second(_) | LLExpression::Tuple(_) => return Err(()),
        LLExpression::Function(id, typ) => Expression::Function(id, pairless_type(typ)?),
        LLExpression::Variable(id, typ) => Expression::Variable(id, pairless_type(typ)?),
    })
}

/// Translates a type without any use of products from Sort to Type
fn pairless_type(typ: Sort) -> Result<Type, ()> {
    Ok(match typ {
        Sort::Value => Type::Value,
        Sort::Function(contents) => Type::Function(Box::new((
            pairless_type(contents.0)?,
            pairless_type(contents.1)?,
        ))),
        Sort::Product(_) => return Err(()),
    })
}

/// Translates a proposition without any use of pairs from LLProposition to Proposition
fn pairless_proposition(prop: LLProposition) -> Result<Proposition, ()> {
    Ok(match prop {
        LLProposition::And(contents) => Proposition::And(Box::new((
            pairless_proposition(contents.0)?,
            pairless_proposition(contents.1)?,
        ))),
        LLProposition::Implies(contents) => Proposition::Implies(Box::new((
            pairless_proposition(contents.0)?,
            pairless_proposition(contents.1)?,
        ))),
        LLProposition::Call(pred, args) => Proposition::Call(
            pred,
            args.into_iter()
                .map(pairless_expression)
                .collect::<Result<Vec<_>, ()>>()?,
        ),
        LLProposition::CallLogic(pred, args) => Proposition::CallLogic(
            pred,
            args.into_iter()
                .map(pairless_expression)
                .collect::<Result<Vec<_>, ()>>()?,
        ),
        LLProposition::Equal(left, right) => {
            Proposition::Equal(pairless_expression(left)?, pairless_expression(right)?)
        }
        LLProposition::False => Proposition::False,
        LLProposition::True => Proposition::True,
        LLProposition::Forall(id, typ, body) => Proposition::Forall(
            id,
            pairless_type(typ)?,
            Box::new(pairless_proposition(*body)?),
        ),
    })
}

fn remove_pair_returns_from_proposition(prop: LLProposition) -> LLProposition {
    match prop {
        LLProposition::Forall(id, typ, body) => LLProposition::Forall(
            id,
            remove_pair_returns_from_sort(typ),
            Box::new(remove_pair_returns_from_proposition(*body)),
        ),
        LLProposition::And(contents) => LLProposition::And(Box::new((
            remove_pair_returns_from_proposition(contents.0),
            remove_pair_returns_from_proposition(contents.1),
        ))),
        LLProposition::Implies(contents) => LLProposition::Implies(Box::new((
            remove_pair_returns_from_proposition(contents.0),
            remove_pair_returns_from_proposition(contents.1),
        ))),
        LLProposition::Call(_, _)
        | LLProposition::CallLogic(_, _)
        | LLProposition::False
        | LLProposition::True
        | LLProposition::Equal(_, _) => prop,
    }
}

enum Tree<T> {
    Leaf(T),
    Branch(Box<(Tree<T>, Tree<T>)>),
}

impl<T> Tree<T> {
    fn add_to_vec(self, target: &mut Vec<T>) {
        match self {
            Tree::Leaf(v) => target.push(v),
            Tree::Branch(contents) => {
                contents.0.add_to_vec(target);
                contents.1.add_to_vec(target);
            }
        }
    }

    fn to_vec(self) -> Vec<T> {
        let mut target = Vec::new();
        self.add_to_vec(&mut target);
        target
    }
}

pub struct PairRemover {
    _next_fn_id: u32,
    _next_id: u32,
}

impl PairRemover {
    pub fn new(_next_id: u32, _next_fn_id: u32) -> PairRemover {
        PairRemover {
            _next_fn_id,
            _next_id,
        }
    }

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

    fn generate_pairless_returns(&mut self, fun: LLFunction) -> Result<Tree<LLFunction>, ()> {
        let LLFunction {
            id,
            parameters,
            body,
        } = fun;
        Ok(match body.typ()? {
            Sort::Product(contents) => {
                let first_id = self.next_fn_id();
                let second_id = self.next_fn_id();
                Tree::Branch(Box::new((
                    self.generate_pairless_returns(LLFunction {
                        id: first_id,
                        parameters: parameters.clone(),
                        body: LLExpression::First(Box::new(body.clone())),
                    })?,
                    self.generate_pairless_returns(LLFunction {
                        id: second_id,
                        parameters,
                        body: LLExpression::Second(Box::new(body)),
                    })?,
                )))
            }
            _ => Tree::Leaf(LLFunction {
                id,
                parameters,
                body,
            }),
        })
    }

    /// Returns an equivalent program where none of the functions return tuples
    fn remove_pair_returns(
        &mut self,
        mut prop: LLProposition,
        fns: Vec<LLFunction>,
    ) -> Result<(LLProposition, Vec<LLFunction>), ()> {
        let mut new_fns = Vec::new();
        let mut reversed_fns = fns.into_iter().rev().collect::<Vec<_>>();
        while let Some(fun) = reversed_fns.pop() {
            let LLFunction {
                id,
                parameters,
                body,
            } = fun;
            let parameters = parameters
                .into_iter()
                .map(|(id, sort)| (id, remove_pair_returns_from_sort(sort)))
                .collect::<Vec<_>>();
            let fn_tree = self.generate_pairless_returns(LLFunction {
                id,
                parameters,
                body,
            })?;
            let sub = fn_tree_to_expression(&fn_tree)?;
            reversed_fns.iter_mut().for_each(|fun| {
                fun.body.substitute_fn(&sub, id);
            });
            prop.substitute_fn(&sub, id);
            fn_tree.add_to_vec(&mut new_fns);
        }
        Ok((remove_pair_returns_from_proposition(prop), new_fns))
    }

    fn generate_pairless_parameters(
        &mut self,
        param: (Identifier, Sort),
    ) -> Tree<(Identifier, Sort)> {
        let (id, sort) = param;
        if let Sort::Product(contents) = sort {
            let first_id = self.next_id();
            let second_id = self.next_id();
            Tree::Branch(Box::new((
                self.generate_pairless_parameters((first_id, contents.0)),
                self.generate_pairless_parameters((second_id, contents.1)),
            )))
        } else {
            Tree::Leaf((id, sort))
        }
    }

    fn remove_pair_parameters_from_proposition(
        &mut self,
        prop: LLProposition,
    ) -> Result<LLProposition, ()> {
        Ok(match prop {
            LLProposition::Forall(id, typ, mut body) => {
                let var_tree =
                    self.generate_pairless_parameters((id, remove_pair_parameters_from_sort(typ)));
                body.substitute(&param_tree_to_expression(&var_tree), id);
                generate_pairless_forall(
                    self.remove_pair_parameters_from_proposition(*body)?,
                    var_tree.to_vec(),
                )
            }
            LLProposition::And(contents) => LLProposition::And(Box::new((
                self.remove_pair_parameters_from_proposition(contents.0)?,
                self.remove_pair_parameters_from_proposition(contents.1)?,
            ))),
            LLProposition::Implies(contents) => LLProposition::Implies(Box::new((
                self.remove_pair_parameters_from_proposition(contents.0)?,
                self.remove_pair_parameters_from_proposition(contents.1)?,
            ))),
            LLProposition::Call(pred, args) => LLProposition::Call(
                pred,
                args.into_iter()
                    .map(|arg| remove_pair_parameters_from_expression(arg))
                    .collect::<Result<Vec<_>, ()>>()?,
            ),
            LLProposition::CallLogic(pred, args) => LLProposition::CallLogic(
                pred,
                args.into_iter()
                    .map(|arg| remove_pair_parameters_from_expression(arg))
                    .collect::<Result<Vec<_>, ()>>()?,
            ),
            LLProposition::Equal(left, right) => LLProposition::Equal(
                remove_pair_parameters_from_expression(left)?,
                remove_pair_parameters_from_expression(right)?,
            ),
            LLProposition::False => LLProposition::False,
            LLProposition::True => LLProposition::True,
        })
    }

    /// Produces an equivalent program where no function takes a pair as an argument
    fn remove_pair_parameters(
        &mut self,
        prop: LLProposition,
        fns: Vec<LLFunction>,
    ) -> Result<(LLProposition, Vec<LLFunction>), ()> {
        let new_fns = fns
            .into_iter()
            .map(|fun| {
                let LLFunction {
                    id,
                    parameters,
                    mut body,
                } = fun;
                let mut new_params = Vec::new();
                parameters
                    .into_iter()
                    .map(|(id, sort)| (id, remove_pair_parameters_from_sort(sort)))
                    .map(|param| (param.0, self.generate_pairless_parameters(param)))
                    .for_each(|(id, param_tree)| {
                        body.substitute(&param_tree_to_expression(&param_tree), id);
                        param_tree.add_to_vec(&mut new_params);
                    });
                Ok(LLFunction {
                    id,
                    parameters: new_params,
                    body: remove_pair_parameters_from_expression(body)?,
                })
            })
            .collect::<Result<Vec<_>, ()>>()?;
        Ok((self.remove_pair_parameters_from_proposition(prop)?, new_fns))
    }

    pub fn remove_pairs(
        &mut self,
        prop: LLProposition,
        fns: Vec<LLFunction>,
    ) -> Result<(Proposition, Vec<Function>), ()> {
        let (prop, fns) = self.remove_pair_returns(prop, fns)?;
        let (prop, fns) = self.remove_pair_parameters(prop, fns)?;
        let prop = remove_applied_pairs_from_proposition(prop)?;
        let fns = fns
            .into_iter()
            .map(|fun| {
                Ok(LLFunction {
                    body: remove_applied_pairs_from_expression(fun.body)?,
                    ..fun
                })
            })
            .collect::<Result<Vec<_>, ()>>()?;
        let prop = remove_pair_literals_from_proposition(prop)?;
        let fns = fns
            .into_iter()
            .map(|fun| {
                Ok(LLFunction {
                    body: remove_pair_literals_from_expression(fun.body)?,
                    ..fun
                })
            })
            .collect::<Result<Vec<_>, ()>>()?;
        Ok((
            pairless_proposition(prop)?,
            fns.into_iter()
                .map(|fun| {
                    let LLFunction {
                        id,
                        parameters,
                        body,
                    } = fun;
                    Ok(Function {
                        id: id,
                        parameters: parameters
                            .into_iter()
                            .map(|(id, typ)| Ok((id, pairless_type(typ)?)))
                            .collect::<Result<Vec<_>, ()>>()?,
                        body: pairless_expression(body)?,
                    })
                })
                .collect::<Result<Vec<_>, ()>>()?,
        ))
    }
}
