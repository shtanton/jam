use crate::lambda_lift::lift;
use crate::smt::translate_judgement_to_smt;
use crate::syntax::{
    Constant, Expression as SExpression, Predicate, Proposition as SProposition, Type as SType,
};
use crate::to_z3::{run_smt, SmtResult};
use im::{hashmap as im_hashmap, HashMap as ImHashMap, Vector as ImVec};
use std::collections::HashMap;
use std::fmt;

pub type Identifier = u32;
#[derive(Clone, Copy, Debug)]
pub struct IdentifierGenerator {
    next: Identifier,
}
impl IdentifierGenerator {
    pub fn next(&mut self) -> Identifier {
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

#[derive(Debug)]
pub struct Judgement {
    pub context: Vec<(Identifier, Type)>,
    pub expression: Expression,
    pub typ: Type,
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
    pub fn substitute(
        &mut self,
        expr: &ExpressionKind,
        env: &ImHashMap<Identifier, UnrefinedType>,
        id: Identifier,
    ) {
        match self {
            Proposition::False => {}
            Proposition::Implies(contents) => {
                contents.0.substitute(expr, env, id);
                contents.1.substitute(expr, env, id);
            }
            Proposition::Forall(_, contents) => {
                contents.0.substitute(expr, env, id);
                contents.1.substitute(expr, env, id);
            }
            Proposition::Call(_, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute(expr, env, id);
                });
            }
            Proposition::Equal(contents) => {
                contents.0.substitute(expr, env, id);
                contents.1.substitute(expr, env, id);
                contents.2.substitute(expr, env, id);
            }
            Proposition::Supertype(contents) => {
                contents.0.substitute(expr, env, id);
                contents.1.substitute(expr, env, id);
            }
        }
    }

    fn env(&self) -> ImHashMap<Identifier, UnrefinedType> {
        match self {
            Proposition::False => ImHashMap::new(),
            Proposition::Implies(contents) => contents.0.env().union(contents.1.env()),
            Proposition::Forall(id, contents) => {
                contents.1.env().without(id).union(contents.0.env())
            }
            Proposition::Call(_, args) => ImHashMap::unions(args.iter().map(|arg| arg.env.clone())),
            Proposition::Equal(contents) => contents
                .0
                .env()
                .union(contents.1.env.clone())
                .union(contents.2.env.clone()),
            Proposition::Supertype(contents) => contents.0.env().union(contents.1.env()),
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
    U8Rec(Identifier, Type, Box<(Expression, Expression, Expression)>),
}

#[derive(Clone, Debug)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub typ: UnrefinedType,
    pub env: ImHashMap<Identifier, UnrefinedType>,
}

impl Expression {
    pub fn substitute(
        &mut self,
        expr: &ExpressionKind,
        env: &ImHashMap<Identifier, UnrefinedType>,
        id: Identifier,
    ) {
        if let Some(_) = self.env.remove(&id) {
            self.env = self.env.clone().union(env.clone());
        }
        match &mut self.kind {
            ExpressionKind::Ast => {}
            ExpressionKind::Variable(var) => {
                if *var == id {
                    self.kind = expr.clone();
                }
            }
            ExpressionKind::Call(_, args) => {
                args.iter_mut()
                    .for_each(|arg| arg.substitute(expr, env, id));
            }
            ExpressionKind::Tuple(contents) => {
                contents.0.substitute(expr, env, id);
                contents.1.substitute(expr, env, id);
            }
            ExpressionKind::Abstraction(arg_id, arg_type, body) => {
                arg_type.substitute(expr, env, id);
                if *arg_id != id {
                    body.substitute(expr, env, id);
                }
            }
            ExpressionKind::Application(contents) => {
                contents.0.substitute(expr, env, id);
                contents.1.substitute(expr, env, id);
            }
            ExpressionKind::First(arg) => {
                arg.substitute(expr, env, id);
            }
            ExpressionKind::Second(arg) => {
                arg.substitute(expr, env, id);
            }
            ExpressionKind::U8Rec(_, typ, contents) => {
                typ.substitute(expr, env, id);
                contents.0.substitute(expr, env, id);
                contents.1.substitute(expr, env, id);
                contents.2.substitute(expr, env, id);
            }
        }
    }
}

#[derive(Clone, Debug, Hash)]
pub enum UnrefinedType {
    One,
    Bool,
    U8,
    Product(Box<(UnrefinedType, UnrefinedType)>),
    Function(Box<(UnrefinedType, UnrefinedType)>),
}

impl fmt::Display for UnrefinedType {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UnrefinedType::One => write!(fmt, "1")?,
            UnrefinedType::Bool => write!(fmt, "B")?,
            UnrefinedType::U8 => write!(fmt, "u8")?,
            UnrefinedType::Product(contents) => write!(fmt, "<{}x{}>", contents.0, contents.1)?,
            UnrefinedType::Function(contents) => write!(fmt, "({}->{})", contents.0, contents.1)?,
        }
        Ok(())
    }
}

impl PartialEq for UnrefinedType {
    fn eq(&self, other: &UnrefinedType) -> bool {
        match (self, other) {
            (UnrefinedType::One, UnrefinedType::One)
            | (UnrefinedType::Bool, UnrefinedType::Bool)
            | (UnrefinedType::U8, UnrefinedType::U8) => true,
            (UnrefinedType::Product(left_contents), UnrefinedType::Product(right_contents)) => {
                left_contents.0 == right_contents.0 && left_contents.1 == right_contents.1
            }
            (UnrefinedType::Function(left_contents), UnrefinedType::Function(right_contents)) => {
                left_contents.0 == right_contents.0 && left_contents.1 == right_contents.1
            }
            _ => false,
        }
    }
}

impl Eq for UnrefinedType {}

#[derive(Clone)]
pub struct Variable {
    typ: Type,
    id: Identifier,
    symbol: String,
}

#[derive(Clone, Debug)]
pub enum Type {
    One,
    Bool,
    U8,
    Product(Identifier, Box<(Type, Type)>),
    Function(Identifier, Box<(Type, Type)>),
    Refinement(Identifier, Box<Type>, Proposition),
}

impl Type {
    pub fn substitute(
        &mut self,
        expr: &ExpressionKind,
        env: &ImHashMap<Identifier, UnrefinedType>,
        id: Identifier,
    ) {
        match self {
            Type::One | Type::Bool | Type::U8 => {}
            Type::Product(left_id, contents) => {
                contents.0.substitute(expr, env, id);
                if *left_id != id {
                    contents.1.substitute(expr, env, id);
                }
            }
            Type::Function(arg_id, contents) => {
                contents.0.substitute(expr, env, id);
                if *arg_id != id {
                    contents.1.substitute(expr, env, id);
                }
            }
            Type::Refinement(arg_id, supertype, prop) => {
                supertype.substitute(expr, env, id);
                if *arg_id != id {
                    prop.substitute(expr, env, id);
                }
            }
        }
    }

    pub fn unrefine(&self) -> UnrefinedType {
        match self {
            Type::One => UnrefinedType::One,
            Type::Bool => UnrefinedType::Bool,
            Type::U8 => UnrefinedType::U8,
            Type::Product(_, contents) => {
                UnrefinedType::Product(Box::new((contents.0.unrefine(), contents.1.unrefine())))
            }
            Type::Function(_, contents) => {
                UnrefinedType::Function(Box::new((contents.0.unrefine(), contents.1.unrefine())))
            }
            Type::Refinement(_, supertype, _) => supertype.unrefine(),
        }
    }

    fn env(&self) -> ImHashMap<Identifier, UnrefinedType> {
        match self {
            Type::One | Type::Bool | Type::U8 => ImHashMap::new(),
            Type::Product(id, contents) => {
                let first_env = contents.0.env();
                let second_env = contents.1.env();
                second_env.without(id).union(first_env)
            }
            Type::Function(id, contents) => {
                let param_env = contents.0.env();
                let body_env = contents.1.env();
                body_env.without(id).union(param_env)
            }
            Type::Refinement(id, supertype, prop) => prop.env().without(id).union(supertype.env()),
        }
    }
}

pub type Context = ImVec<(Identifier, Type)>;

#[derive(Clone, Default)]
pub struct Environment {
    symbols: ImHashMap<String, Identifier>,
    context: Context,
}

enum Application {
    U8Rec(Expression, Expression, Expression),
    UserFunction(Expression, Expression),
}

fn add_applications_to_vec(
    expr: &Expression,
    mut context: Context,
    applications: &mut Vec<(Context, Application)>,
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
            applications.push((
                context,
                Application::UserFunction(contents.0.clone(), contents.1.clone()),
            ));
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
        ExpressionKind::U8Rec(_, _, contents) => {
            add_applications_to_vec(&contents.0, context.clone(), applications);
            add_applications_to_vec(&contents.1, context.clone(), applications);
            add_applications_to_vec(&contents.2, context.clone(), applications);
            applications.push((
                context,
                Application::U8Rec(contents.0.clone(), contents.1.clone(), contents.2.clone()),
            ));
        }
    };
}

fn find_applications(expr: &Expression) -> Vec<(Context, Application)> {
    let mut applications = Vec::new();
    add_applications_to_vec(expr, ImVec::new(), &mut applications);
    applications
}

/// Assuming variable expr_id of type typ is operated on with args, what is the param type?
fn arg_type_of_type(typ: &Type, mut args: Vec<FnProcess>) -> Result<Type, ()> {
    Ok(match typ {
        Type::Refinement(_, typ, _) => arg_type_of_type(typ, args)?,
        Type::Function(id, contents) => match args.pop() {
            Some(FnProcess::Arg(arg)) => {
                let mut new_type = contents.1.clone();
                new_type.substitute(&arg.kind, &arg.env, *id);
                arg_type_of_type(&new_type, args)?
            }
            None => contents.0.clone(),
            Some(FnProcess::First) | Some(FnProcess::Second(_)) => {
                return Err(());
            }
        },
        Type::Product(id, contents) => match args.pop() {
            Some(FnProcess::First) => arg_type_of_type(&contents.0, args)?,
            Some(FnProcess::Second(arg)) => {
                let mut typ = arg_type_of_type(&contents.1, args)?;
                let env = arg.env.clone();
                typ.substitute(&ExpressionKind::First(Box::new(arg)), &env, *id);
                typ
            }
            Some(FnProcess::Arg(_)) | None => {
                return Err(());
            }
        },
        Type::Bool | Type::One | Type::U8 => return Err(()),
    })
}

enum FnProcess {
    First,
    Second(Expression),
    Arg(Expression),
}

fn arg_type(
    expr: &Expression,
    mut context: HashMap<Identifier, Type>,
    mut args: Vec<FnProcess>,
) -> Result<Type, ()> {
    Ok(match &expr.kind {
        ExpressionKind::Abstraction(id, typ, body) => match args.pop() {
            Some(FnProcess::Arg(arg)) => {
                let mut body = body.clone();
                body.substitute(&arg.kind, &arg.env, *id);
                arg_type(&body, context, args)?
            }
            Some(_) => {
                return Err(());
            }
            None => typ.clone(),
        },
        ExpressionKind::Application(contents) => {
            args.push(FnProcess::Arg(contents.1.clone()));
            arg_type(&contents.0, context, args)?
        }
        ExpressionKind::Variable(id) => {
            let var_type = context.get(id).ok_or(())?;
            arg_type_of_type(var_type, args.into())?
        }
        ExpressionKind::U8Rec(id, typ, contents) => {
            let mut typ = typ.clone();
            typ.substitute(&contents.2.kind, &contents.2.env, *id);
            let res = arg_type_of_type(&typ, args)?;
            context.insert(*id, typ);
            res
        }
        ExpressionKind::First(arg) => {
            args.push(FnProcess::First);
            arg_type(&arg, context, args)?
        }
        ExpressionKind::Second(arg) => {
            args.push(FnProcess::Second(*arg.clone()));
            arg_type(&arg, context, args)?
        }
        ExpressionKind::Tuple(contents) => match args.pop() {
            Some(FnProcess::First) => arg_type(&contents.0, context, args)?,
            Some(FnProcess::Second(_)) => arg_type(&contents.1, context, args)?,
            None | Some(FnProcess::Arg(_)) => {
                return Err(());
            }
        },
        ExpressionKind::Ast | ExpressionKind::Call(_, _) => return Err(()),
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
                if !pred.accepts_args(&args) {
                    return Err(());
                }
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
                        typ: typ.clone(),
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
            SType::U8 => Type::U8,
            SType::Product(symbol, first, second) => {
                let first = self.label_type(first, env.clone())?;
                let id = self.ident_gen.next();
                env.insert(symbol.clone(), id);
                self.symbol_table.insert(
                    id,
                    Variable {
                        id: id,
                        symbol: symbol.clone(),
                        typ: first.clone(),
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
                        typ: param.clone(),
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
                        typ: supertype.clone(),
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
                env: ImHashMap::new(),
            },
            SExpression::Abstraction(param_symbol, param_type, expr) => {
                let param_type = self.label_type(param_type, env.clone())?;
                let unrefined_arg_type = param_type.unrefine();
                let id = self.ident_gen.next();
                env.insert(param_symbol.clone(), id);
                self.symbol_table.insert(
                    id,
                    Variable {
                        id,
                        symbol: param_symbol.clone(),
                        typ: param_type.clone(),
                    },
                );
                let body = self.label_expression(expr, env)?;
                let body_typ = body.typ.clone();
                Expression {
                    env: body.env.without(&id).union(param_type.env()),
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
                        env: labelled_fun.env.clone().union(labelled_arg.env.clone()),
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
                if !constant.accepts_args(&args) {
                    return Err(());
                }
                Expression {
                    env: ImHashMap::unions(args.iter().map(|arg| arg.env.clone())),
                    kind: ExpressionKind::Call(*constant, args),
                    typ: constant.return_type(),
                }
            }
            SExpression::First(arg) => {
                let arg = self.label_expression(arg, env)?;
                if let UnrefinedType::Product(type_contents) = &arg.typ {
                    let typ = type_contents.0.clone();
                    Expression {
                        env: arg.env.clone(),
                        kind: ExpressionKind::First(Box::new(arg)),
                        typ,
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
                        env: arg.env.clone(),
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
                    env: first.env.clone().union(second.env.clone()),
                    kind: ExpressionKind::Tuple(Box::new((first, second))),
                    typ,
                }
            }
            SExpression::U8Rec(init, iter, count) => {
                let count = self.label_expression(count, env.clone())?;
                if let UnrefinedType::U8 = &count.typ {
                    let init = self.label_expression(init, env.clone())?;
                    let iter = self.label_expression(iter, env.clone())?;
                    let n_id = self.ident_gen.next();
                    let n = Expression {
                        kind: ExpressionKind::Variable(n_id),
                        env: ImHashMap::new().update(n_id, UnrefinedType::U8),
                        typ: UnrefinedType::U8,
                    };
                    let typ = arg_type(
                        &iter,
                        self.symbol_table
                            .clone()
                            .into_iter()
                            .map(|(id, var)| (id, var.typ))
                            .collect(),
                        vec![FnProcess::Arg(n)],
                    )?;
                    Expression {
                        env: init
                            .env
                            .clone()
                            .union(iter.env.clone())
                            .union(count.env.clone()),
                        typ: init.typ.clone(),
                        kind: ExpressionKind::U8Rec(n_id, typ, Box::new((init, iter, count))),
                    }
                } else {
                    return Err(());
                }
            }
            SExpression::Variable(symbol) => {
                let id = env.get(symbol).ok_or(())?;
                let variable = self.symbol_table.get(id).ok_or(())?;
                let mut var_env = ImHashMap::new();
                var_env.insert(*id, variable.typ.unrefine());
                Expression {
                    kind: ExpressionKind::Variable(*id),
                    typ: variable.typ.unrefine(),
                    env: var_env,
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
    if ast.typ != UnrefinedType::U8 {
        return Err("labelling error".to_string());
    }
    let applications = find_applications(&ast);
    let judgements = applications
        .into_iter()
        .flat_map(|(context, application)| match application {
            Application::UserFunction(fun, arg) => {
                if let Ok(typ) = arg_type(&fun, context.clone().into_iter().collect(), Vec::new()) {
                    vec![Ok(Judgement {
                        context: context.into_iter().collect(),
                        expression: arg,
                        typ,
                    })]
                } else {
                    vec![Err(())]
                }
            }
            Application::U8Rec(init, iter, _) => {
                let n = analyzer.ident_gen.next();
                let var_n = Expression {
                    kind: ExpressionKind::Variable(n),
                    env: ImHashMap::new().update(n, UnrefinedType::U8),
                    typ: UnrefinedType::U8,
                };
                if let Ok(type_n) = arg_type(
                    &iter,
                    context.clone().into_iter().collect(),
                    vec![FnProcess::Arg(var_n.clone())],
                ) {
                    let not_255 = {
                        let id = analyzer.ident_gen.next();
                        Type::Refinement(
                            id,
                            Box::new(Type::U8),
                            Proposition::Implies(Box::new((
                                Proposition::Equal(Box::new((
                                    Type::U8,
                                    Expression {
                                        kind: ExpressionKind::Variable(id),
                                        typ: UnrefinedType::U8,
                                        env: im_hashmap! {id => UnrefinedType::U8},
                                    },
                                    Expression {
                                        kind: ExpressionKind::Call(Constant::U8(255), vec![]),
                                        typ: UnrefinedType::U8,
                                        env: ImHashMap::new(),
                                    },
                                ))),
                                Proposition::False,
                            ))),
                        )
                    };
                    let mut type_succ_n = type_n.clone();
                    type_succ_n.substitute(
                        &ExpressionKind::Call(Constant::Succ, vec![var_n.clone()]),
                        &var_n.env,
                        n,
                    );
                    let mut type_zero = type_n.clone();
                    type_zero.substitute(
                        &ExpressionKind::Call(Constant::U8(0), Vec::new()),
                        &ImHashMap::new(),
                        n,
                    );
                    vec![
                        Ok(Judgement {
                            context: context.clone().into_iter().collect(),
                            expression: init,
                            typ: type_zero,
                        }),
                        Ok(Judgement {
                            context: context.into_iter().collect(),
                            expression: iter,
                            typ: Type::Function(
                                n,
                                Box::new((
                                    not_255,
                                    Type::Function(
                                        analyzer.ident_gen.next(),
                                        Box::new((type_n, type_succ_n)),
                                    ),
                                )),
                            ),
                        }),
                    ]
                } else {
                    vec![Err(())]
                }
            }
        })
        .collect::<Result<Vec<_>, ()>>()
        .map_err(|_| "error generating typing judgements".to_string())?;
    let judgements = judgements
        .into_iter()
        .map(|judgement| lift(judgement, &mut analyzer.ident_gen))
        .collect::<Vec<_>>();
    let smt_programs = judgements
        .into_iter()
        .map(|judgement| translate_judgement_to_smt(judgement, &mut analyzer.ident_gen))
        .collect::<Result<Vec<_>, ()>>()
        .map_err(|_| "error generating smt program".to_string())?;
    for (i, smt) in smt_programs.into_iter().enumerate() {
        println!("Program {}:", i);
        //println!("{}", smt);
        match run_smt(smt).map_err(|_| "error running SMT solver".to_string())? {
            SmtResult::Pass => {
                println!("PASS");
            }
            _ => {
                println!("FAIL");
                return Err("Type error".to_string());
            }
        }
    }
    Ok(ast)
}
