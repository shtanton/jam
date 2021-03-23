use crate::semantic::{
    Context as SContext, Expression as SExpression, ExpressionKind as SExpressionKind,
    Proposition as SProposition, Type as SType, UnrefinedType as SUnrefinedType,
};
use crate::syntax::{Constant, Predicate};
use im::Vector as ImVec;

pub type Identifier = u32;

#[derive(Clone, Debug)]
pub enum Sort {
    Value,
    Function(Box<(Sort, Sort)>),
    Product(Box<(Sort, Sort)>),
}

impl Sort {
    fn from_type(typ: &SType) -> Sort {
        match typ {
            SType::Bool => Sort::Value,
            SType::Nat => Sort::Value,
            SType::Product(_, contents) => Sort::Product(Box::new((
                Sort::from_type(&contents.0),
                Sort::from_type(&contents.1),
            ))),
            SType::Function(_, contents) => Sort::Function(Box::new((
                Sort::from_type(&contents.0),
                Sort::from_type(&contents.1),
            ))),
            SType::Refinement(_, supertype, _) => Sort::from_type(supertype),
        }
    }
}

#[derive(Clone, Debug)]
pub enum LPredicate {
    Is1,
    IsNat,
    IsBool,
}

#[derive(Clone, Debug)]
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
    pub fn substitute(&mut self, expr: &Expression, id: Identifier) {
        match self {
            Proposition::False => {}
            Proposition::True => {}
            Proposition::And(args) => {
                args.0.substitute(expr, id);
                args.1.substitute(expr, id);
            }
            Proposition::Implies(args) => {
                args.0.substitute(expr, id);
                args.1.substitute(expr, id);
            }
            Proposition::Forall(forall_id, sort, prop) => {
                if *forall_id != id {
                    prop.substitute(expr, id);
                }
            }
            Proposition::Call(pred, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute(expr, id);
                });
            }
            Proposition::CallLogic(_, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute(expr, id);
                });
            }
            Proposition::Equal(left, right) => {
                left.substitute(expr, id);
                right.substitute(expr, id);
            }
        };
    }
}

#[derive(Clone, Debug)]
pub enum Expression {
    Variable(Identifier),
    Call(Constant, Vec<Expression>),
    Tuple(Box<(Expression, Expression)>),
    Abstraction(Identifier, Sort, Box<Expression>),
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
            }
            Expression::Call(constant, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute(expr, id);
                });
            }
            Expression::Tuple(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            }
            Expression::Abstraction(arg, _, body) => {
                if *arg != id {
                    body.substitute(expr, id);
                }
            }
            Expression::Application(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            }
            Expression::First(arg) => {
                arg.substitute(expr, id);
            }
            Expression::Second(arg) => {
                arg.substitute(expr, id);
            }
        }
    }
}

pub struct ToLogic {
    _next_id: u32,
}

impl ToLogic {
    pub fn new(_next_id: u32) -> ToLogic {
        ToLogic { _next_id }
    }

    fn next_id(&mut self) -> u32 {
        let id = self._next_id;
        self._next_id += 1;
        id
    }

    pub fn type_judgement_to_logic(
        &mut self,
        expr: &SExpression,
        typ: &SType,
        mut context: SContext,
    ) -> Result<Proposition, ()> {
        Ok(if let Some((var_id, var_type)) = context.pop_front() {
            Proposition::Forall(
                var_id,
                Sort::from_type(&var_type),
                Box::new(Proposition::Implies(Box::new((
                    self.type_judgement_to_logic(
                        &SExpression {
                            kind: SExpressionKind::Variable(var_id),
                            typ: var_type.unrefine(),
                        },
                        &var_type,
                        ImVec::new(),
                    )?,
                    self.type_judgement_to_logic(expr, typ, context)?,
                )))),
            )
        } else {
            match typ {
                SType::Bool => Proposition::CallLogic(
                    LPredicate::IsBool,
                    vec![self.expression_to_logic(expr)?],
                ),
                SType::Nat => {
                    Proposition::CallLogic(LPredicate::IsNat, vec![self.expression_to_logic(expr)?])
                }
                SType::Product(id, contents) => {
                    let (first_unrefined, second_unrefined) =
                        if let SUnrefinedType::Product(contents) = expr.typ.clone() {
                            (contents.0, contents.1)
                        } else {
                            return Err(());
                        };
                    let first = SExpression {
                        kind: SExpressionKind::First(Box::new(expr.clone())),
                        typ: first_unrefined,
                    };
                    let left_prop =
                        self.type_judgement_to_logic(&first, &contents.0, ImVec::new())?;
                    let mut right_type = contents.1.clone();
                    right_type.substitute(&first.kind, *id);
                    Proposition::And(Box::new((
                        left_prop,
                        self.type_judgement_to_logic(
                            &SExpression {
                                kind: SExpressionKind::Second(Box::new(expr.clone())),
                                typ: second_unrefined,
                            },
                            &right_type,
                            ImVec::new(),
                        )?,
                    )))
                }
                SType::Function(id, contents) => {
                    let var = SExpression {
                        kind: SExpressionKind::Variable(*id),
                        typ: contents.0.unrefine(),
                    };
                    let left_prop =
                        self.type_judgement_to_logic(&var, &contents.0, ImVec::new())?;
                    let right_expr = SExpression {
                        kind: SExpressionKind::Application(Box::new((expr.clone(), var))),
                        typ: contents.1.unrefine(),
                    };
                    Proposition::Forall(
                        *id,
                        Sort::from_type(&contents.0),
                        Box::new(Proposition::Implies(Box::new((
                            left_prop,
                            self.type_judgement_to_logic(&right_expr, &contents.1, ImVec::new())?,
                        )))),
                    )
                }
                SType::Refinement(id, supertype, prop) => {
                    let mut prop = prop.clone();
                    prop.substitute(&expr.kind, *id);
                    Proposition::And(Box::new((
                        self.type_judgement_to_logic(expr, &supertype, ImVec::new())?,
                        self.proposition_to_logic(&prop)?,
                    )))
                }
            }
        })
    }

    fn proposition_to_logic(&mut self, prop: &SProposition) -> Result<Proposition, ()> {
        Ok(match prop {
            SProposition::False => Proposition::False,
            SProposition::Implies(contents) => Proposition::Implies(Box::new((
                self.proposition_to_logic(&contents.0)?,
                self.proposition_to_logic(&contents.1)?,
            ))),
            SProposition::Forall(id, contents) => Proposition::Forall(
                *id,
                Sort::from_type(&contents.0),
                Box::new(Proposition::Implies(Box::new((
                    self.type_judgement_to_logic(
                        &SExpression {
                            kind: SExpressionKind::Variable(*id),
                            typ: contents.0.unrefine(),
                        },
                        &contents.0,
                        ImVec::new(),
                    )?,
                    self.proposition_to_logic(&contents.1)?,
                )))),
            ),
            SProposition::Call(pred, args) => Proposition::Call(
                *pred,
                args.into_iter()
                    .map(|arg| self.expression_to_logic(arg))
                    .collect::<Result<Vec<_>, ()>>()?,
            ),
            SProposition::Equal(contents) => {
                let typ = contents.0.clone();
                let left = contents.1.clone();
                let right = contents.2.clone();
                match typ {
                    SType::Bool | SType::Nat => Proposition::And(Box::new((
                        self.type_judgement_to_logic(&left, &typ, ImVec::new())?,
                        Proposition::Equal(
                            self.expression_to_logic(&left)?,
                            self.expression_to_logic(&right)?,
                        ),
                    ))),
                    SType::Product(id, mut contents) => {
                        contents.1.substitute(&left.kind, id);
                        let first_type = contents.0.unrefine();
                        let second_type = contents.1.unrefine();
                        Proposition::And(Box::new((
                            self.proposition_to_logic(&SProposition::Equal(Box::new((
                                contents.0,
                                SExpression {
                                    kind: SExpressionKind::First(Box::new(left.clone())),
                                    typ: first_type.clone(),
                                },
                                SExpression {
                                    kind: SExpressionKind::First(Box::new(right.clone())),
                                    typ: first_type,
                                },
                            ))))?,
                            self.proposition_to_logic(&SProposition::Equal(Box::new((
                                contents.1,
                                SExpression {
                                    kind: SExpressionKind::Second(Box::new(left)),
                                    typ: second_type.clone(),
                                },
                                SExpression {
                                    kind: SExpressionKind::Second(Box::new(right)),
                                    typ: second_type,
                                },
                            ))))?,
                        )))
                    }
                    SType::Function(id, contents) => {
                        let var = SExpression {
                            kind: SExpressionKind::Variable(id),
                            typ: contents.0.unrefine(),
                        };
                        let return_type = contents.1.unrefine();
                        Proposition::Forall(
                            id,
                            Sort::from_type(&contents.0),
                            Box::new(Proposition::Implies(Box::new((
                                self.type_judgement_to_logic(&var, &contents.0, ImVec::new())?,
                                self.proposition_to_logic(&SProposition::Equal(Box::new((
                                    contents.1,
                                    SExpression {
                                        kind: SExpressionKind::Application(Box::new((
                                            left,
                                            var.clone(),
                                        ))),
                                        typ: return_type.clone(),
                                    },
                                    SExpression {
                                        kind: SExpressionKind::Application(Box::new((
                                            right,
                                            var.clone(),
                                        ))),
                                        typ: return_type,
                                    },
                                ))))?,
                            )))),
                        )
                    }
                    SType::Refinement(id, supertype, prop) => {
                        let mut left_prop = prop.clone();
                        left_prop.substitute(&left.kind, id);
                        let mut right_prop = prop;
                        right_prop.substitute(&right.kind, id);
                        Proposition::And(Box::new((
                            Proposition::And(Box::new((
                                self.proposition_to_logic(&SProposition::Equal(Box::new((
                                    *supertype, left, right,
                                ))))?,
                                self.proposition_to_logic(&left_prop)?,
                            ))),
                            self.proposition_to_logic(&right_prop)?,
                        )))
                    }
                }
            }
            SProposition::Supertype(contents) => {
                let id = self.next_id();
                let var = SExpression {
                    kind: SExpressionKind::Variable(id),
                    typ: contents.1.unrefine(),
                };
                Proposition::Forall(
                    id,
                    Sort::from_type(&contents.1),
                    Box::new(Proposition::Implies(Box::new((
                        self.type_judgement_to_logic(&var, &contents.1, ImVec::new())?,
                        self.type_judgement_to_logic(&var, &contents.0, ImVec::new())?,
                    )))),
                )
            }
        })
    }

    fn expression_to_logic(&mut self, expr: &SExpression) -> Result<Expression, ()> {
        Ok(match &expr.kind {
            SExpressionKind::Variable(id) => Expression::Variable(*id),
            SExpressionKind::Call(constant, args) => Expression::Call(
                *constant,
                args.into_iter()
                    .map(|arg| self.expression_to_logic(&arg))
                    .collect::<Result<Vec<_>, ()>>()?,
            ),
            SExpressionKind::Tuple(contents) => Expression::Tuple(Box::new((
                self.expression_to_logic(&contents.0)?,
                self.expression_to_logic(&contents.1)?,
            ))),
            SExpressionKind::Abstraction(id, typ, body) => Expression::Abstraction(
                *id,
                Sort::from_type(&typ),
                Box::new(self.expression_to_logic(&body)?),
            ),
            SExpressionKind::First(arg) => {
                Expression::First(Box::new(self.expression_to_logic(&arg)?))
            }
            SExpressionKind::Second(arg) => {
                Expression::Second(Box::new(self.expression_to_logic(&arg)?))
            }
            SExpressionKind::Application(contents) => Expression::Application(Box::new((
                self.expression_to_logic(&contents.0)?,
                self.expression_to_logic(&contents.1)?,
            ))),
        })
    }
}

/*
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
}*/
