use crate::lambda_lift::LambdaLifter;
use crate::logic::ToLogic;
use crate::remove_pairs::PairRemover;
use crate::syntax::{
    Constant, Expression as SExpression, Predicate, Proposition as SProposition, Type as SType,
};
use im::{HashMap as ImHashMap, Vector as ImVec};
use std::collections::HashMap;

pub type Identifier = u32;
#[derive(Clone, Copy, Debug)]
pub struct IdentifierGenerator {
    next: Identifier,
}
impl IdentifierGenerator {
    fn next(&mut self) -> Identifier {
        let n = self.next;
        self.next += 1;
        n
    }
}
impl Default for IdentifierGenerator {
    fn default() -> IdentifierGenerator {
        IdentifierGenerator { next: 0 }
    }
}

#[derive(Clone, Debug)]
pub enum Proposition {
    False,
    Implies(Box<(Proposition, Proposition)>),
    Forall(Identifier, Box<(Type, Proposition)>),
    Call(Predicate, Vec<Expression>),
    Equal(Box<(Type, Expression, Expression)>),
    Supertype(Box<(Type, Type)>),
}

impl Proposition {
    pub fn substitute(&mut self, expr: &ExpressionKind, id: Identifier) {
        match self {
            Proposition::False => {}
            Proposition::Implies(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            }
            Proposition::Forall(_, contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            }
            Proposition::Call(_, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute(expr, id);
                });
            }
            Proposition::Equal(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
                contents.2.substitute(expr, id);
            }
            Proposition::Supertype(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum ExpressionKind {
    Ast,
    Variable(Identifier),
    Call(Constant, Vec<Expression>),
    Tuple(Box<(Expression, Expression)>),
    Abstraction(Identifier, Type, Box<Expression>),
    Application(Box<(Expression, Expression)>),
    First(Box<Expression>),
    Second(Box<Expression>),
}

#[derive(Clone, Debug)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub typ: UnrefinedType,
}

impl Expression {
    pub fn substitute(&mut self, expr: &ExpressionKind, id: Identifier) {
        match &mut self.kind {
            ExpressionKind::Ast => {}
            ExpressionKind::Variable(var) => {
                if *var == id {
                    self.kind = expr.clone();
                }
            }
            ExpressionKind::Call(_, args) => {
                args.iter_mut().for_each(|arg| arg.substitute(expr, id));
            }
            ExpressionKind::Tuple(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            }
            ExpressionKind::Abstraction(arg_id, arg_type, body) => {
                arg_type.substitute(expr, id);
                if *arg_id != id {
                    body.substitute(expr, id);
                }
            }
            ExpressionKind::Application(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            }
            ExpressionKind::First(arg) => {
                arg.substitute(expr, id);
            }
            ExpressionKind::Second(arg) => {
                arg.substitute(expr, id);
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum UnrefinedType {
    One,
    Bool,
    Nat,
    Product(Box<(UnrefinedType, UnrefinedType)>),
    Function(Box<(UnrefinedType, UnrefinedType)>),
}

#[derive(Clone)]
pub struct Variable {
    typ: UnrefinedType,
    id: Identifier,
    symbol: String,
}

#[derive(Clone, Debug)]
pub enum Type {
    One,
    Bool,
    Nat,
    Product(Identifier, Box<(Type, Type)>),
    Function(Identifier, Box<(Type, Type)>),
    Refinement(Identifier, Box<Type>, Proposition),
}

impl Type {
    pub fn substitute(&mut self, expr: &ExpressionKind, id: Identifier) {
        match self {
            Type::One | Type::Bool | Type::Nat => {}
            Type::Product(left_id, contents) => {
                contents.0.substitute(expr, id);
                if *left_id != id {
                    contents.1.substitute(expr, id);
                }
            }
            Type::Function(arg_id, contents) => {
                contents.0.substitute(expr, id);
                if *arg_id != id {
                    contents.1.substitute(expr, id);
                }
            }
            Type::Refinement(arg_id, supertype, prop) => {
                supertype.substitute(expr, id);
                if *arg_id != id {
                    prop.substitute(expr, id);
                }
            }
        }
    }

    pub fn unrefine(&self) -> UnrefinedType {
        match self {
            Type::One => UnrefinedType::One,
            Type::Bool => UnrefinedType::Bool,
            Type::Nat => UnrefinedType::Nat,
            Type::Product(_, contents) => {
                UnrefinedType::Product(Box::new((contents.0.unrefine(), contents.1.unrefine())))
            }
            Type::Function(_, contents) => {
                UnrefinedType::Function(Box::new((contents.0.unrefine(), contents.1.unrefine())))
            }
            Type::Refinement(_, supertype, _) => supertype.unrefine(),
        }
    }
}

pub type Context = ImVec<(Identifier, Type)>;

#[derive(Clone, Default)]
pub struct Environment {
    symbols: ImHashMap<String, Identifier>,
    context: Context,
}

fn constant_unrefined_return_type(constant: &Constant) -> UnrefinedType {
    match constant {
        Constant::Succ => UnrefinedType::Nat,
        Constant::Zero => UnrefinedType::Nat,
        Constant::True => UnrefinedType::Bool,
        Constant::False => UnrefinedType::Bool,
    }
}

fn add_applications_to_vec(
    expr: &Expression,
    mut context: Context,
    applications: &mut Vec<(Context, Expression, Expression)>,
) {
    match &expr.kind {
        ExpressionKind::Ast => {}
        ExpressionKind::Variable(_) => {}
        ExpressionKind::Abstraction(id, typ, body) => {
            context.push_back((*id, typ.clone()));
            add_applications_to_vec(&body, context, applications);
        }
        ExpressionKind::Application(contents) => {
            add_applications_to_vec(&contents.0, context.clone(), applications);
            add_applications_to_vec(&contents.1, context.clone(), applications);
            applications.push((context, contents.0.clone(), contents.1.clone()));
        }
        ExpressionKind::Call(_, args) => {
            args.into_iter().for_each(|arg| {
                add_applications_to_vec(&arg, context.clone(), applications);
            });
        }
        ExpressionKind::First(arg) => {
            add_applications_to_vec(&arg, context, applications);
        }
        ExpressionKind::Second(arg) => {
            add_applications_to_vec(&arg, context, applications);
        }
        ExpressionKind::Tuple(contents) => {
            add_applications_to_vec(&contents.0, context.clone(), applications);
            add_applications_to_vec(&contents.1, context, applications);
        }
    };
}

fn find_applications(expr: &Expression) -> Vec<(Context, Expression, Expression)> {
    let mut applications = Vec::new();
    add_applications_to_vec(expr, ImVec::new(), &mut applications);
    applications
}

fn arg_type(
    expr: &Expression,
    mut context: Context,
    mut args: ImVec<Expression>,
) -> Result<Type, ()> {
    Ok(match &expr.kind {
        ExpressionKind::Abstraction(id, typ, body) => {
            if let Some(arg) = args.pop_back() {
                let mut body = body.clone();
                body.substitute(&arg.kind, *id);
                arg_type(&body, context, args)?
            } else {
                typ.clone()
            }
        }
        ExpressionKind::Application(contents) => {
            args.push_back(contents.1.clone());
            arg_type(&contents.0, context, args)?
        }
        ExpressionKind::Variable(id) => {
            let (i, (_, var_type)) = context
                .iter_mut()
                .enumerate()
                .rfind(|(_, (el_id, _))| *el_id == *id)
                .ok_or(())?;
            match &var_type {
                Type::Refinement(_, typ, _) => {
                    *var_type = *typ.clone();
                    arg_type(expr, context, args)?
                }
                Type::Function(arg_id, contents) => {
                    if let Some(arg) = args.pop_back() {
                        let mut var_type = var_type.clone();
                        var_type.substitute(&arg.kind, *arg_id);
                        context.set(i, (*id, var_type.clone()));
                        arg_type(expr, context, args)?
                    } else {
                        contents.0.clone()
                    }
                }
                _ => return Err(()),
            }
        }
        _ => return Err(()),
    })
}

#[derive(Default)]
struct Analyzer {
    ident_gen: IdentifierGenerator,
    symbol_table: HashMap<Identifier, Variable>,
}

impl Analyzer {
    /// Label a proposition
    fn label_proposition(
        &mut self,
        prop: &SProposition,
        mut env: ImHashMap<String, Identifier>,
    ) -> Result<Proposition, ()> {
        Ok(match prop {
            SProposition::Call(pred, args) => {
                let args = args
                    .into_iter()
                    .map(|arg| self.label_expression(arg, env.clone()))
                    .collect::<Result<Vec<_>, ()>>()?;
                Proposition::Call(*pred, args)
            }
            SProposition::Equal(typ, left, right) => Proposition::Equal(Box::new((
                self.label_type(typ, env.clone())?,
                self.label_expression(left, env.clone())?,
                self.label_expression(right, env)?,
            ))),
            SProposition::False => Proposition::False,
            SProposition::Forall(symbol, typ, forall_prop) => {
                let typ = self.label_type(typ, env.clone())?;
                let id = self.ident_gen.next();
                env.insert(symbol.clone(), id);
                self.symbol_table.insert(
                    id,
                    Variable {
                        typ: typ.unrefine(),
                        id: id,
                        symbol: symbol.clone(),
                    },
                );
                let forall_prop = self.label_proposition(forall_prop, env)?;
                Proposition::Forall(id, Box::new((typ, forall_prop)))
            }
            SProposition::Implies(left, right) => {
                let left = self.label_proposition(left, env.clone())?;
                let right = self.label_proposition(right, env)?;
                Proposition::Implies(Box::new((left, right)))
            }
            // TODO change to supertype
            SProposition::Subtype(subtype, supertype) => {
                let subtype = self.label_type(subtype, env.clone())?;
                let supertype = self.label_type(supertype, env)?;
                Proposition::Supertype(Box::new((supertype, subtype)))
            }
        })
    }

    /// Label a Type
    fn label_type(
        &mut self,
        typ: &SType,
        mut env: ImHashMap<String, Identifier>,
    ) -> Result<Type, ()> {
        Ok(match typ {
            SType::One => Type::One,
            SType::Bool => Type::Bool,
            SType::Nat => Type::Nat,
            SType::Product(symbol, first, second) => {
                let first = self.label_type(first, env.clone())?;
                let id = self.ident_gen.next();
                env.insert(symbol.clone(), id);
                self.symbol_table.insert(
                    id,
                    Variable {
                        id: id,
                        symbol: symbol.clone(),
                        typ: first.unrefine(),
                    },
                );
                let second = self.label_type(second, env)?;
                Type::Product(id, Box::new((first, second)))
            }
            SType::Function(symbol, param, ret) => {
                let param = self.label_type(param, env.clone())?;
                let id = self.ident_gen.next();
                env.insert(symbol.clone(), id);
                self.symbol_table.insert(
                    id,
                    Variable {
                        id: id,
                        symbol: symbol.clone(),
                        typ: param.unrefine(),
                    },
                );
                let ret = self.label_type(ret, env)?;
                Type::Function(id, Box::new((param, ret)))
            }
            SType::Refinement(symbol, supertype, prop) => {
                let supertype = self.label_type(supertype, env.clone())?;
                let id = self.ident_gen.next();
                env.insert(symbol.clone(), id);
                self.symbol_table.insert(
                    id,
                    Variable {
                        id: id,
                        symbol: symbol.clone(),
                        typ: supertype.unrefine(),
                    },
                );
                let prop = self.label_proposition(prop, env)?;
                Type::Refinement(id, Box::new(supertype), prop)
            }
        })
    }

    /// Label an Expression
    fn label_expression(
        &mut self,
        expr: &SExpression,
        mut env: ImHashMap<String, Identifier>,
    ) -> Result<Expression, ()> {
        Ok(match expr {
            SExpression::Ast => Expression {
                kind: ExpressionKind::Ast,
                typ: UnrefinedType::One,
            },
            SExpression::Abstraction(param_symbol, param_type, expr) => {
                let param_type = self.label_type(param_type, env.clone())?;
                let id = self.ident_gen.next();
                env.insert(param_symbol.clone(), id);
                self.symbol_table.insert(
                    id,
                    Variable {
                        id,
                        symbol: param_symbol.clone(),
                        typ: param_type.unrefine(),
                    },
                );
                let body = self.label_expression(expr, env)?;
                let unrefined_arg_type = param_type.unrefine();
                let body_typ = body.typ.clone();
                Expression {
                    kind: ExpressionKind::Abstraction(id, param_type, Box::new(body)),
                    typ: UnrefinedType::Function(Box::new((unrefined_arg_type, body_typ))),
                }
            }
            SExpression::Application(fun, arg) => {
                let labelled_fun = self.label_expression(fun, env.clone())?;
                let labelled_arg = self.label_expression(arg, env)?;
                if let UnrefinedType::Function(type_contents) = &labelled_fun.typ {
                    let typ = type_contents.1.clone();
                    Expression {
                        kind: ExpressionKind::Application(Box::new((labelled_fun, labelled_arg))),
                        typ: typ,
                    }
                } else {
                    return Err(());
                }
            }
            SExpression::Call(constant, args) => {
                let args = args
                    .into_iter()
                    .map(|arg| self.label_expression(arg, env.clone()))
                    .collect::<Result<Vec<_>, ()>>()?;
                Expression {
                    kind: ExpressionKind::Call(*constant, args),
                    typ: constant_unrefined_return_type(&constant),
                }
            }
            SExpression::First(arg) => {
                let arg = self.label_expression(arg, env)?;
                if let UnrefinedType::Product(type_contents) = &arg.typ {
                    let typ = type_contents.0.clone();
                    Expression {
                        kind: ExpressionKind::First(Box::new(arg)),
                        typ: typ,
                    }
                } else {
                    return Err(());
                }
            }
            SExpression::Second(arg) => {
                let arg = self.label_expression(arg, env)?;
                if let UnrefinedType::Product(type_contents) = &arg.typ {
                    let typ = type_contents.1.clone();
                    Expression {
                        kind: ExpressionKind::Second(Box::new(arg)),
                        typ,
                    }
                } else {
                    return Err(());
                }
            }
            SExpression::Tuple(first, second) => {
                let first = self.label_expression(first, env.clone())?;
                let second = self.label_expression(second, env)?;
                let typ = UnrefinedType::Product(Box::new((first.typ.clone(), second.typ.clone())));
                Expression {
                    kind: ExpressionKind::Tuple(Box::new((first, second))),
                    typ,
                }
            }
            SExpression::Variable(symbol) => {
                let id = env.get(symbol).ok_or(())?;
                let variable = self.symbol_table.get(id).ok_or(())?;
                Expression {
                    kind: ExpressionKind::Variable(*id),
                    typ: variable.typ.clone(),
                }
            }
        })
    }
}

pub fn check(ast: SExpression) -> Result<Expression, String> {
    let env = ImHashMap::default();
    let mut analyzer = Analyzer::default();
    let ast = analyzer
        .label_expression(&ast, env)
        .map_err(|_| "labelling error".to_string())?;
    let mut next_id = analyzer.ident_gen.next();
    let mut next_fn_id = 0;
    let applications = find_applications(&ast);
    let mut judgements = applications
        .into_iter()
        .map(
            |(context, fun, arg)| -> Result<(Context, Expression, Type), ()> {
                let typ = arg_type(&fun, context.clone(), ImVec::default())?;
                Ok((context, arg, typ))
            },
        )
        .collect::<Result<Vec<_>, ()>>()
        .map_err(|_| "error generating typing judgements".to_string())?;
    judgements.push((ImVec::new(), ast.clone(), Type::Nat));
    let propositions = judgements
        .into_iter()
        .map(|(context, expr, typ)| {
            let mut to_logic = ToLogic::new(analyzer.ident_gen.next());
            let prop = to_logic.type_judgement_to_logic(&expr, &typ, context)?;
            Ok((to_logic.next_id(), prop))
        })
        .collect::<Result<Vec<_>, ()>>()
        .map_err(|_| "error generating first order calculus propositions".to_string())?;
    let lambda_lifted_propositions = propositions
        .into_iter()
        .map(|(next_id, prop)| {
            let mut lambda_lifter = LambdaLifter::new();
            let prop = lambda_lifter.lambda_lift(&prop);
            (next_id, lambda_lifter.next_fn_id(), prop)
        })
        .collect::<Vec<_>>();
    let pairless_propositions = lambda_lifted_propositions
        .into_iter()
        .map(|(next_id, next_fn_id, (prop, fns))| {
            let mut pair_remover = PairRemover::new(next_id, next_fn_id);
            let prop = pair_remover.remove_pairs(prop, fns)?;
            Ok((pair_remover.next_id(), pair_remover.next_fn_id(), prop))
        })
        .collect::<Result<Vec<_>, ()>>()
        .map_err(|_| "error removing pairs".to_string())?;
    for prop in pairless_propositions.iter() {
        println!("{:#?}", prop.2);
    }
    Ok(ast)
}
