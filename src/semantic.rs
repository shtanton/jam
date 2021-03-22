use std::collections::HashMap;
use im::{
    HashMap as ImHashMap,
    Vector as ImVec,
};
use crate::syntax::{
    Predicate,
    Constant,
    Expression as SExpression,
    Type as SType,
    Proposition as SProposition,
};
use crate::logic::{
    Proposition as LProposition,
    Expression as LExpression,
};

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
        IdentifierGenerator {next: 0}
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
    fn substitute(&mut self, expr: &ExpressionKind, id: Identifier) {
        match self {
            Proposition::False => {},
            Proposition::Implies(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            },
            Proposition::Forall(forall_id, contents) => {
                contents.0.substitute(expr, id);
                if *forall_id != id {
                    contents.1. substitute(expr, id);
                }
            },
            Proposition::Call(pred, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute(expr, id);
                });
            },
            Proposition::Equal(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
                contents.2.substitute(expr, id);
            },
            Proposition::Subtype(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            },
        }
    }
}

#[derive(Clone, Debug)]
pub enum ExpressionKind {
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
    kind: ExpressionKind,
    typ: UnrefinedType,
}

impl Expression {
    fn substitute(&mut self, expr: &ExpressionKind, id: Identifier) {
        match &mut self.kind {
            ExpressionKind::Variable(var) => {
                if *var == id {
                    self.kind = expr.clone();
                }
            },
            ExpressionKind::Call(constant, args) => {
                args.iter_mut().for_each(|arg| arg.substitute(expr, id));
            },
            ExpressionKind::Tuple(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            },
            ExpressionKind::Abstraction(arg_id, arg_type, body) => {
                arg_type.substitute(expr, id);
                if *arg_id != id {
                    body.substitute(expr, id);
                }
            },
            ExpressionKind::Application(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            },
        }
    }
}

#[derive(Clone, Debug)]
pub enum UnrefinedType {
    Bool,
    Nat,
    Product(Box<(UnrefinedType, UnrefinedType)>),
    Function(Box<(UnrefinedType, UnrefinedType)>),
}

#[derive(Clone, Debug)]
pub enum Sort {
    Bool,
    Nat,
    Product(Box<(Sort, Sort)>),
    Function(Box<(Sort, Sort)>),
}

#[derive(Clone)]
pub struct Variable {
    typ: UnrefinedType,
    id: Identifier,
    symbol: String,
}

#[derive(Clone, Debug)]
pub enum Type {
    Bool,
    Nat,
    Product(Identifier, Box<(Type, Type)>),
    Function(Identifier, Box<(Type, Type)>),
    Refinement(Identifier, Box<Type>, Proposition),
}

impl Type {
    fn substitute(&mut self, expr: &ExpressionKind, id: Identifier) {
        match self {
            Type::Bool => {},
            Type::Nat => {},
            Type::Product(left_id, contents) => {
                contents.0.substitute(expr, id);
                if *left_id != id {
                    contents.1.substitute(expr, id);
                }
            },
            Type::Function(arg_id, contents) => {
                contents.0.substitute(expr, id);
                if *arg_id != id {
                    contents.1.substitute(expr, id);
                }
            },
            Type::Refinement(arg_id, supertype, prop) => {
                supertype.substitute(expr, id);
                if *arg_id != id {
                    prop.substitute(expr, id);
                }
            },
        }
    }

    fn unrefine(&self) -> UnrefinedType {
        match self {
            Type::Bool => UnrefinedType::Bool,
            Type::Nat => UnrefinedType::Nat,
            Type::Product(_, contents) => UnrefinedType::Product(Box::new((contents.0.unrefine(), contents.1.unrefine()))),
            Type::Function(_, contents) => UnrefinedType::Function(Box::new((contents.0.unrefine(), contents.1.unrefine()))),
            Type::Refinement(_, supertype, _) => supertype.unrefine(),
        }
    }
}

#[derive(Clone)]
pub enum ContextElement {
    Proposition(Proposition),
    Variable(Variable),
}

pub type Context = ImVec<ContextElement>;

#[derive(Clone, Default)]
pub struct Environment {
    symbols: ImHashMap<String, Identifier>,
    context: Context,
}

fn constantUnrefinedReturnType(constant: &Constant) -> UnrefinedType {
    match constant {
        Constant::Succ => UnrefinedType::Nat,
        Constant::Zero => UnrefinedType::Nat,
        Constant::True => UnrefinedType::Bool,
        Constant::False => UnrefinedType::Bool,
    }
}

#[derive(Default)]
struct Analyzer {
    ident_gen: IdentifierGenerator,
    symbol_table: HashMap<Identifier, Variable>,
}

impl Analyzer {
    /// Create a new Identifier for the symbol and with the Type given and return it
    fn insert_symbol(&mut self, symbol: &str, typ: Type) -> Identifier {
        let ident = self.ident_gen.next();
        let var = Variable {
            typ,
            id: ident,
            symbol: symbol.to_string(),
        };
        self.symbols.insert(ident, var);
        ident
    }

    /// Lookup a symbol in the symbol table
    fn lookup_symbol(&self, symbol: Identifier) -> Result<&Variable, ()> {
        self.symbols.get(&symbol).ok_or(())
    }

    /// Create a new Type with the given TypeKind and return it
    fn insert_type(&mut self, kind: TypeKind) -> Type {
        let typ = self.type_gen.next();
        let type_data = TypeData {
            kind,
            id: typ,
        };
        self.types.insert(typ, type_data);
        typ
    }

    /// Get TypeData of a Type
    fn type_data(&self, typ: Type) -> Option<&TypeData> {
        self.types.get(&typ)
    }

    fn substitute_expression(&self, expr: &Expression, target: &Expression, source: Identifier) -> Result<Expression, ()> {
    }

    fn substitute_proposition(&self, prop: &Proposition, expr: &Expression, ident: Identifier) -> Result<Proposition, ()> {
        match prop {
            Proposition::Call(pred, args) => {
                let subbed_args = args.into_iter().map(|arg| self.substitute_expression(arg, expr, ident)).collect::<Result<Vec<_>, ()>>()?;
                Ok(Proposition::Call(*pred, subbed_args))
            }
            Proposition::Equal(typ, left, right) => {
                let subbed_left = self.substitute_expression(left, expr, ident)?;
                let subbed_right = self.substitute_expression(right, expr, ident)?;
                let subbed_typ = self.substitute_type(*typ, expr, ident)?;
                Ok(Proposition::Equal(subbed_typ, subbed_left, subbed_right))
            }
            Proposition::False => {
                Ok(Proposition::False)
            }
            Proposition::Forall(forall_ident, typ, forall_prop) => {
                let subbed_typ = self.substitute_type(*typ, expr, ident)?;
                let subbed_prop = self.substitute_proposition(forall_prop, expr, ident)?;
                Ok(Proposition::Forall(*forall_ident, subbed_typ, Box::new(subbed_prop)))
            }
            Proposition::Implies(left, right) => {
                let subbed_left = self.substitute_proposition(left, expr, ident)?;
                let subbed_right = self.substitute_proposition(right, expr, ident)?;
                Ok(Proposition::Implies(Box::new(subbed_left), Box::new(subbed_right)))
            }
            Proposition::Subtype(subtype, supertype) => {
                let subbed_subtype = self.substitute_type(*subtype, expr, ident)?;
                let subbed_supertype = self.substitute_type(*supertype, expr, ident)?;
                Ok(Proposition::Subtype(subbed_subtype, subbed_supertype))
            }
        }
    }

    fn substitute_type(&self, typ: Type, expr: &Expression, ident: Identifier) -> Result<Type, ()> {
        let type_data = self.type_data(typ).ok_or(())?;
        match &type_data.kind {
            TypeKind::Bool => Ok(typ),
            TypeKind::Function(param_ident, param_type, ret_type) => {
                let subbed_param_type = self.substitute_type(*param_type, expr, ident)?;
                let subbed_ret_type = self.substitute_type(*ret_type, expr, ident)?;
                if subbed_param_type == *param_type && subbed_ret_type == *ret_type {
                    Ok(typ)
                } else {
                    let typ = self.insert_type(TypeKind::Function(
                        *param_ident,
                        subbed_param_type,
                        subbed_ret_type,
                    ));
                    Ok(typ)
                }
            }
            TypeKind::Nat => Ok(typ),
            TypeKind::Product(first_ident, first, second) => {
                let subbed_first = self.substitute_type(*first, expr, ident)?;
                let subbed_second = self.substitute_type(*second, expr, ident)?;
                if subbed_first == *first && subbed_second == *second {
                    Ok(typ)
                } else {
                    Ok(self.insert_type(TypeKind::Product(
                        *first_ident,
                        subbed_first,
                        subbed_second,
                    )))
                }
            }
            TypeKind::Refinement(ident, typ, prop) => {
                let subbed_typ = self.substitute_type(*typ, expr, *ident)?;
                let subbed_prop = self.substitute_proposition(prop, expr, *ident)?;
                Ok(self.insert_type(TypeKind::Refinement(*ident, subbed_typ, subbed_prop)))
            }
        }
    }

    /// Return true if the first argument is a subtype of the second
    /// has_type(t, phi, gamma) <=> gamma |- t : phi
    fn has_type(&self, expr: &Expression, typ: Type, env: Environment) -> Result<bool, ()> {
        let type_data = self.type_data(typ).ok_or(())?;
        match (expr.kind, type_data.kind) {
            (ExpressionKind::Tuple(first, second), TypeKind::Product(ident, first_type, second_type)) => {
                Ok(
                    self.has_type(&first, first_type, env)?
                    && self.has_type(&second, self.substitute_type(second_type, &first, ident)?, env)?
                    // TODO update env to include the ident
                    && self.type_wf(second_type, env)
                )
            }
        }
    }

    /// Label a proposition
    fn label_proposition(&mut self, prop: &SProposition, env: ImHashMap<String, Identifier>) -> Result<Proposition, ()> {
        Ok(match prop {
            SProposition::Call(pred, args) => {
                let args = args
                    .into_iter()
                    .map(|arg| self.label_expression(arg, env.clone()))
                    .collect::<Result<Vec<_>, ()>>()?;
                Proposition::Call(*pred, args)
            },
            SProposition::Equal(typ, left, right) => {
                Proposition::Equal(Box::new((
                    self.label_type(typ, env.clone())?,
                    self.label_expression(left, env.clone())?,
                    self.label_expression(right, env)?,
                )))
            },
            SProposition::False => Proposition::False,
            SProposition::Forall(symbol, typ, forall_prop) => {
                let typ = self.label_type(typ, env.clone())?;
                let id = self.ident_gen.next();
                env.insert(symbol.clone(), id);
                self.symbol_table.insert(id, Variable {
                    typ: typ.unrefine(),
                    id: id,
                    symbol: symbol.clone(),
                });
                let forall_prop = self.label_proposition(forall_prop, env)?;
                Proposition::Forall(id, Box::new((typ, forall_prop)))
            },
            SProposition::Implies(left, right) => {
                let left = self.label_proposition(left, env.clone())?;
                let right = self.label_proposition(right, env)?;
                Proposition::Implies(Box::new((left, right)))
            },
            // TODO change to supertype
            SProposition::Subtype(subtype, supertype) => {
                let subtype = self.label_type(subtype, env.clone())?;
                let supertype = self.label_type(supertype, env)?;
                Proposition::Supertype(Box::new((supertype, subtype)))
            },
        })
    }

    /// Label a Type
    fn label_type(&mut self, typ: &SType, env: ImHashMap<String, Identifier>) -> Result<Type, ()> {
        Ok(match typ {
            SType::Bool => Type::Bool,
            SType::Nat => Type::Nat,
            SType::Product(symbol, first, second) => {
                let first = self.label_type(first, env.clone())?;
                let id = self.ident_gen.next();
                env.insert(symbol.clone(), id);
                self.symbol_table.insert(id, Variable {
                    id: id,
                    symbol: symbol.clone(),
                    typ: first.unrefine(),
                });
                let second = self.label_type(second, env)?;
                Type::Product(
                    id,
                    Box::new((first, second))
                )
            },
            SType::Function(symbol, param, ret) => {
                let param = self.label_type(param, env.clone())?;
                let id = self.ident_gen.next();
                env.insert(symbol.clone(), id);
                self.symbol_table.insert(id, Variable {
                    id: id,
                    symbol: symbol.clone(),
                    typ: param.unrefine(),
                });
                let ret = self.label_type(ret, env)?;
                Type::Function(id, Box::new((param, ret)))
            },
            SType::Refinement(symbol, supertype, prop) => {
                let supertype = self.label_type(supertype, env.clone())?;
                let id = self.ident_gen.next();
                env.insert(symbol.clone(), id);
                self.symbol_table.insert(id, Variable {
                    id: id,
                    symbol: symbol.clone(),
                    typ: supertype.unrefine(),
                });
                let prop = self.label_proposition(prop, env)?;
                Type::Refinement(id, Box::new(supertype), prop)
            },
        })
    }

    /// Label an Expression
    fn label_expression(&mut self, expr: &SExpression, env: ImHashMap<String, Identifier>) -> Result<Expression, ()> {
        Ok(match expr {
            SExpression::Abstraction(param_symbol, param_type, expr) => {
                let param_type = self.label_type(param_type, env.clone())?;
                let id = self.ident_gen.next();
                env.insert(param_symbol.clone(), id);
                self.symbol_table.insert(id, Variable{
                    id,
                    symbol: param_symbol.clone(),
                    typ: param_type.unrefine(),
                });
                let body = self.label_expression(expr, env)?;
                Expression {
                    kind: ExpressionKind::Abstraction(id, param_type, Box::new(body)),
                    typ: UnrefinedType::Function(Box::new((param_type.unrefine(), body.typ))),
                }
            },
            SExpression::Application(fun, arg) => {
                let labelled_fun = self.label_expression(fun, env.clone())?;
                let labelled_arg = self.label_expression(arg, env)?;
                if let UnrefinedType::Function(type_contents) = labelled_fun.typ {
                    Expression {
                        kind: ExpressionKind::Application(Box::new((labelled_fun, labelled_arg))),
                        typ: type_contents.1.clone(),
                    }
                } else {
                    return Err(())
                }
            },
            SExpression::Call(constant, args) => {
                let args = args.into_iter().map(|arg| self.label_expression(arg, env)).collect::<Result<Vec<_>, ()>>()?;
                Expression {
                    kind: ExpressionKind::Call(*constant, args),
                    typ: constantUnrefinedReturnType(&constant),
                }
            },
            SExpression::First(arg) => {
                let arg = self.label_expression(arg, env)?;
                if let UnrefinedType::Product(type_contents) = arg.typ {
                    Expression {
                        kind: ExpressionKind::First(Box::new(arg)),
                        typ: type_contents.0,
                    }
                } else {
                    return Err(())
                }
            },
            SExpression::Second(arg) => {
                let arg = self.label_expression(arg, env)?;
                if let UnrefinedType::Product(type_contents) = arg.typ {
                    Expression {
                        kind: ExpressionKind::Second(Box::new(arg)),
                        typ: type_contents.1,
                    }
                } else {
                    return Err(())
                }
            },
            SExpression::Tuple(first, second) => {
                let first = self.label_expression(first, env)?;
                let second = self.label_expression(second, env)?;
                Expression {
                    kind: ExpressionKind::Tuple(Box::new((first, second))),
                    typ: UnrefinedType::Product(Box::new((first.typ, second.typ))),
                }
            },
            SExpression::Variable(symbol) => {
                let id = env.get(symbol).ok_or(())?;
                let variable = self.symbol_table.get(id).ok_or(())?;
                Expression {
                    kind: ExpressionKind::Variable(*id),
                    typ: variable.typ,
                }
            },
        })
    }

    /// Translate an expression type judgement to logic
    fn expression_type_judgement_to_logic(&mut self, expr: &Expression, typ: &Type, context: Context) -> Result<LProposition, ()> {
        match context.pop_front() {
            Some(ContextElement::Variable(Variable{
                typ: var_type,
                id,
                symbol,
            })) => {
                let (arg, sort, mut prop) = self.type_to_logic(&var_type)?;
                prop.substitute(&LExpression::Variable(id), arg);
                Ok(LProposition::Forall(
                    id,
                    sort,
                    Box::new(LProposition::Implies(Box::new((
                        prop,
                        self.expression_type_judgement_to_logic(expr, typ, context)?,
                    )))),
                ))
            },
            Some(ContextElement::Proposition(p)) => {
                Ok(LProposition::Implies(Box::new((
                    self.proposition_to_logic(&p)?,
                    self.expression_type_judgement_to_logic(expr, typ, context)?,
                ))))
            },
            None => {
                let (arg, sort, mut prop) = self.type_to_logic(typ)?;
                prop.substitute(&self.expression_to_logic(expr)?, arg);
                Ok(prop)
            },
        }
    }

    /// Translate a type to logic
    fn type_to_logic(&mut self, typ: &Type) -> Result<(Identifier, Sort, LProposition), ()> {
        match typ {
            Type::Bool => Ok((self.ident_gen.next(), Sort::Bool, LProposition::True)),
            Type::Nat => Ok((self.ident_gen.next(), Sort::Nat, LProposition::True)),
            Type::Product(id, contents) => {
                let (left_arg, left_sort, mut left_prop) = self.type_to_logic(&contents.0)?;
                let (right_arg, right_sort, mut right_prop) = self.type_to_logic(&contents.1)?;
                let id = self.ident_gen.next();
                left_prop.substitute(
                    &LExpression::First(Box::new(LExpression::Variable(id))),
                    left_arg,
                );
                right_prop.substitute(
                    &LExpression::First(Box::new(LExpression::Variable(id))),
                    left_arg,
                );
                right_prop.substitute(
                    &LExpression::Second(Box::new(LExpression::Variable(id))),
                    right_arg,
                );
                Ok((
                    id,
                    Sort::Product(Box::new((left_sort, right_sort))),
                    LProposition::And(Box::new((left_prop, right_prop))),
                ))
            },
            Type::Function(arg, contents) => {
                let (param_arg, param_sort, mut param_prop) = self.type_to_logic(&contents.0)?;
                let (ret_arg, ret_sort, mut ret_prop) = self.type_to_logic(&contents.1)?;
                let id = self.ident_gen.next();
                param_prop.substitute(&LExpression::Variable(*arg), param_arg);
                ret_prop.substitute(
                    &LExpression::Application(Box::new((
                        LExpression::Variable(id),
                        LExpression::Variable(*arg),
                    ))),
                    ret_arg,
                );
                Ok((
                    id,
                    Sort::Function(Box::new((param_sort, ret_sort))),
                    LProposition::Forall(
                        *arg,
                        param_sort,
                        Box::new(LProposition::Implies(Box::new((
                            param_prop,
                            ret_prop,
                        )))),
                    ),
                ))
            },
            Type::Refinement(arg, supertype, prop) => {
                let (super_arg, sort, mut super_prop) = self.type_to_logic(supertype)?;
                super_prop.substitute(&LExpression::Variable(*arg), super_arg);
                Ok((*arg, sort, LProposition::And(Box::new((self.proposition_to_logic(prop)?, super_prop)))))
            },
        }
    }

    fn proposition_to_logic(&mut self, prop: &Proposition) -> Result<LProposition, ()> {
        match prop {
            Proposition::False => Ok(LProposition::False),
            Proposition::Implies(contents) => Ok(LProposition::Implies(Box::new((
                self.proposition_to_logic(&contents.0)?,
                self.proposition_to_logic(&contents.1)?,
            )))),
            Proposition::Call(pred, args) => Ok(LProposition::Call(
                *pred,
                args.into_iter().map(|arg| self.expression_to_logic(arg)).collect::<Result<Vec<_>, ()>>()?,
            )),
            Proposition::Equal(contents) => {
                let (ref typ, ref left, ref right) = **contents;
                Ok(match typ {
                    Type::Bool => LProposition::Equal(
                        self.expression_to_logic(left)?,
                        self.expression_to_logic(right)?,
                    ),
                    Type::Nat => LProposition::Equal(
                        self.expression_to_logic(left)?,
                        self.expression_to_logic(right)?,
                    ),
                    Type::Product(arg_id, contents) => {
                        let sort = left.sort;
                        LProposition::And(Box::new((
                            self.proposition_to_logic(&Proposition::Equal(Box::new((
                                contents.0,
                                Expression{
                                    kind: ExpressionKind::First(Box::new(left.clone())),
                                    sort,
                                },
                                Expression{
                                    kind: ExpressionKind::First(Box::new(right.clone())),
                                    sort,
                                },
                            ))))?,
                            self.proposition_to_logic(&Proposition::Equal(Box::new((
                                {
                                    let mut right_type = contents.1;
                                    right_type.substitute(
                                        &ExpressionKind::First(Box::new(left.clone())),
                                        *arg_id,
                                    );
                                    right_type
                                },
                                Expression{
                                    kind: ExpressionKind::Second(Box::new(left.clone())),
                                    sort,
                                },
                                Expression{
                                    kind: ExpressionKind::Second(Box::new(right.clone())),
                                    sort,
                                },
                            ))))?,
                        )))
                    },
                    Type::Function(arg_id, contents) => {
                        let (left_id, left_sort, left_prop) = self.type_to_logic(&contents.0)?;
                        let right_sort = self.type_to_logic(&contents.1)?.1;
                        LProposition::Forall(
                            *arg_id,
                            left_sort,
                            Box::new(LProposition::Implies(Box::new((
                                left_prop,
                                self.proposition_to_logic(&Proposition::Equal(Box::new((
                                    contents.1,
                                    Expression{
                                        kind: ExpressionKind::Application(Box::new((
                                            left.clone(),
                                            Expression{
                                                kind: ExpressionKind::Variable(*arg_id),
                                                sort: left_sort,
                                            },
                                        ))),
                                        sort: right_sort,
                                    },
                                    Expression{
                                        kind: ExpressionKind::Application(Box::new((
                                            right.clone(),
                                            Expression{
                                                kind: ExpressionKind::Variable(*arg_id),
                                                sort: left_sort,
                                            },
                                        ))),
                                        sort: right_sort,
                                    },
                                ))))?,
                            )))),
                        )
                    },
                    Type::Refinement(arg_id, supertype, prop) => {
                        LProposition::And(Box::new((
                            self.proposition_to_logic(&Proposition::Equal(Box::new((
                                *supertype.clone(),
                                left.clone(),
                                right.clone(),
                            ))))?,
                            LProposition::And(Box::new((
                                self.proposition_to_logic(&{
                                    let p = prop.clone();
                                    p.substitute(&left.kind, *arg_id);
                                    p
                                })?,
                                self.proposition_to_logic(&{
                                    let p = prop.clone();
                                    p.substitute(&right.kind, *arg_id);
                                    p
                                })?,
                            ))),
                        )))
                    },
                })
            },
            Proposition::Supertype(contents) => {
                let (left_arg, left_sort, left_prop) = self.type_to_logic(&contents.0)?;
                let (right_arg, right_sort, right_prop) = self.type_to_logic(&contents.1)?;
                right_prop.substitute(&LExpression::Variable(left_arg), right_arg);
                Ok(LProposition::Forall(
                    left_arg,
                    left_sort,
                    Box::new(LProposition::Implies(Box::new((
                        right_prop,
                        left_prop,
                    )))),
                ))
            },
        }
    }

    fn expression_to_logic(&mut self, expr: &Expression) -> Result<LExpression, ()> {
        Ok(match expr.kind {
            ExpressionKind::Variable(id) => LExpression::Variable(id),
            ExpressionKind::Call(constant, args) => LExpression::Call(
                constant,
                args.iter().map(|arg| self.expression_to_logic(arg)).collect::<Result<Vec<_>, ()>>()?,
            ),
            ExpressionKind::Tuple(contents) => {
                let (ref left, ref right) = *contents;
                LExpression::Tuple(Box::new((
                    self.expression_to_logic(left)?,
                    self.expression_to_logic(right)?,
                )))
            },
            ExpressionKind::Abstraction(param, param_type, body) => {
                LExpression::Abstraction(param, Box::new(self.expression_to_logic(&body)?))
            },
            ExpressionKind::Application(contents) => {
                let (ref left, ref right) = *contents;
                LExpression::Application(Box::new((
                    self.expression_to_logic(left)?,
                    self.expression_to_logic(right)?,
                )))
            },
            ExpressionKind::First(arg) => LExpression::First(Box::new(self.expression_to_logic(&arg)?)),
            ExpressionKind::Second(arg) => LExpression::Second(Box::new(self.expression_to_logic(&arg)?)),
        })
    }
}

pub fn check(ast: SExpression) -> Result<Expression, String> {
    let mut env = Environment::default();
    let mut analyzer = Analyzer::default();
    analyzer.expression(ast, env).map_err(|_| "semantic error".to_string())
}
