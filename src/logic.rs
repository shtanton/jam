use crate::semantic::{
    Context as SContext, Expression as SExpression, ExpressionKind as SExpressionKind,
    Proposition as SProposition, Type as SType, UnrefinedType as SUnrefinedType, UnrefinedType,
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
            SType::One => Sort::Value,
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

    fn from_unrefined_type(typ: &UnrefinedType) -> Sort {
        match typ {
            UnrefinedType::One | UnrefinedType::Bool | UnrefinedType::Nat => Sort::Value,
            UnrefinedType::Product(contents) => Sort::Product(Box::new((
                Sort::from_unrefined_type(&contents.0),
                Sort::from_unrefined_type(&contents.1),
            ))),
            UnrefinedType::Function(contents) => Sort::Function(Box::new((
                Sort::from_unrefined_type(&contents.0),
                Sort::from_unrefined_type(&contents.1),
            ))),
        }
    }

    pub fn after_application(self) -> Result<Sort, ()> {
        Ok(match self {
            Sort::Function(contents) => contents.1,
            Sort::Product(contents) => Sort::Product(Box::new((
                contents.0.after_application()?,
                contents.1.after_application()?,
            ))),
            Sort::Value => return Err(()),
        })
    }
}

#[derive(Clone, Copy, Debug)]
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

#[derive(Clone, Debug)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub sort: Sort,
}

#[derive(Clone, Debug)]
pub enum ExpressionKind {
    Ast,
    Variable(Identifier),
    Call(Constant, Vec<Expression>),
    Tuple(Box<(Expression, Expression)>),
    Abstraction(Identifier, Sort, Box<Expression>),
    Application(Box<(Expression, Expression)>),
    First(Box<Expression>),
    Second(Box<Expression>),
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
                SType::One => {
                    Proposition::CallLogic(LPredicate::Is1, vec![self.expression_to_logic(expr)?])
                }
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
                    SType::One => Proposition::And(Box::new((
                        self.type_judgement_to_logic(&left, &SType::One, ImVec::new())?,
                        self.type_judgement_to_logic(&right, &SType::One, ImVec::new())?,
                    ))),
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
        Ok(Expression {
            kind: match &expr.kind {
                SExpressionKind::Ast => ExpressionKind::Ast,
                SExpressionKind::Variable(id) => ExpressionKind::Variable(*id),
                SExpressionKind::Call(constant, args) => ExpressionKind::Call(
                    *constant,
                    args.into_iter()
                        .map(|arg| self.expression_to_logic(&arg))
                        .collect::<Result<Vec<_>, ()>>()?,
                ),
                SExpressionKind::Tuple(contents) => ExpressionKind::Tuple(Box::new((
                    self.expression_to_logic(&contents.0)?,
                    self.expression_to_logic(&contents.1)?,
                ))),
                SExpressionKind::Abstraction(id, typ, body) => ExpressionKind::Abstraction(
                    *id,
                    Sort::from_type(&typ),
                    Box::new(self.expression_to_logic(&body)?),
                ),
                SExpressionKind::First(arg) => {
                    ExpressionKind::First(Box::new(self.expression_to_logic(&arg)?))
                }
                SExpressionKind::Second(arg) => {
                    ExpressionKind::Second(Box::new(self.expression_to_logic(&arg)?))
                }
                SExpressionKind::Application(contents) => ExpressionKind::Application(Box::new((
                    self.expression_to_logic(&contents.0)?,
                    self.expression_to_logic(&contents.1)?,
                ))),
            },
            sort: Sort::from_unrefined_type(&expr.typ),
        })
    }
}
