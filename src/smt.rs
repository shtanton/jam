use crate::lambda_lift::{Expression as LExpression, Judgement, Proposition as LProposition, Type};
use crate::semantic::{Identifier, IdentifierGenerator, UnrefinedType};
use crate::syntax::{Constant, Predicate};
use std::fmt;

pub struct Smt {
    pub declarations: Vec<Declaration>,
    pub assertions: Vec<Expression>,
    pub types: Vec<UnrefinedType>,
}

impl fmt::Display for Smt {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        for decl in self.declarations.iter() {
            writeln!(fmt, "(declare-const x!{} {})", decl.id, decl.typ)?;
        }
        for assertion in self.assertions.iter() {
            writeln!(fmt, "(assert {})", assertion)?;
        }
        Ok(())
    }
}

pub struct Declaration {
    pub id: Identifier,
    pub typ: UnrefinedType,
}

#[derive(Clone)]
pub enum Expression {
    False,
    True,
    Ast,
    Variable(Identifier),
    Call(Function, Vec<Expression>),
    Forall(Identifier, UnrefinedType, Box<Expression>),
}

impl Expression {
    fn substitute(&mut self, expr: &Expression, target: Identifier) {
        match self {
            Expression::Variable(id) => {
                if *id == target {
                    *self = expr.clone();
                }
            }
            Expression::False | Expression::True | Expression::Ast => {}
            Expression::Call(_, args) => {
                for arg in args.iter_mut() {
                    arg.substitute(expr, target);
                }
            }
            Expression::Forall(_, _, body) => {
                body.substitute(expr, target);
            }
        }
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::False => write!(fmt, "false")?,
            Expression::True => write!(fmt, "true")?,
            Expression::Ast => write!(fmt, "*")?,
            Expression::Variable(id) => write!(fmt, "x!{}", id)?,
            Expression::Call(fun, args) => {
                write!(fmt, "({}", fun)?;
                for arg in args.iter() {
                    write!(fmt, " {}", arg)?;
                }
                write!(fmt, ")")?;
            }
            Expression::Forall(id, typ, body) => {
                write!(fmt, "(forall ((x!{} {})) {})", id, typ, body)?;
            }
        }
        Ok(())
    }
}

#[derive(Clone)]
pub enum Function {
    Implies,
    Equal,
    Not,
    First(UnrefinedType, UnrefinedType),
    Second(UnrefinedType, UnrefinedType),
    Pair(UnrefinedType, UnrefinedType),
    And,
    Predicate(Predicate),
    Constant(Constant),
    Apply(UnrefinedType, UnrefinedType),
}

impl fmt::Display for Function {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Function::Implies => write!(fmt, "=>")?,
            Function::Equal => write!(fmt, "=")?,
            Function::Not => write!(fmt, "not")?,
            Function::First(_, _) => write!(fmt, "first")?,
            Function::Second(_, _) => write!(fmt, "second")?,
            Function::Pair(_, _) => write!(fmt, "pair")?,
            Function::And => write!(fmt, "and")?,
            Function::Predicate(pred) => write!(fmt, "{}", pred)?,
            Function::Constant(constant) => write!(fmt, "{}", constant)?,
            Function::Apply(param_type, body_type) => write!(fmt, "apply_{}->{}", param_type, body_type)?,
        }
        Ok(())
    }
}

struct ToSmt<'a> {
    ident_gen: &'a mut IdentifierGenerator,
    types: Vec<UnrefinedType>,
}

impl<'a> ToSmt<'a> {
    fn next_id(&mut self) -> Identifier {
        self.ident_gen.next()
    }

    fn register_type(&mut self, typ: &UnrefinedType) {
        if typ == &UnrefinedType::One || typ == &UnrefinedType::Bool || self.types.iter().any(|t| t==typ) {
            println!("Type: {}", typ);
            return;
        }
        match typ {
            UnrefinedType::One | UnrefinedType::Bool => {},
            UnrefinedType::Product(contents) | UnrefinedType::Function(contents) => {
                self.register_type(&contents.0);
                self.register_type(&contents.1);
                self.types.push(typ.clone());
            },
        }
    }

    fn simplify(&mut self, typ: Type) -> Result<(Identifier, UnrefinedType, Expression), ()> {
        Ok(match typ {
            Type::One => (self.next_id(), UnrefinedType::One, Expression::True),
            Type::Bool => (self.next_id(), UnrefinedType::Bool, Expression::True),
            Type::Product(id, contents) => {
                let tuple_id = self.next_id();
                let (first_id, first_type, mut first_prop) = self.simplify(contents.0)?;
                let (second_id, second_type, mut second_prop) = self.simplify(contents.1)?;
                let first_call =
                    Expression::Call(Function::First(first_type.clone(), second_type.clone()), vec![Expression::Variable(tuple_id)]);
                first_prop.substitute(&first_call, first_id);
                second_prop.substitute(&first_call, id);
                second_prop.substitute(
                    &Expression::Call(Function::Second(first_type.clone(), second_type.clone()), vec![Expression::Variable(tuple_id)]),
                    second_id,
                );
                (
                    tuple_id,
                    UnrefinedType::Product(Box::new((first_type, second_type))),
                    Expression::Call(Function::And, vec![first_prop, second_prop]),
                )
            }
            Type::Function(id, contents) => {
                let function_id = self.next_id();
                let (param_id, param_type, mut param_prop) = self.simplify(contents.0)?;
                let (body_id, body_type, mut body_prop) = self.simplify(contents.1)?;
                let typ = UnrefinedType::Function(Box::new((param_type.clone(), body_type.clone())));
                param_prop.substitute(&Expression::Variable(id), param_id);
                body_prop.substitute(
                    &Expression::Call(
                        Function::Apply(param_type.clone(), body_type),
                        vec![Expression::Variable(function_id), Expression::Variable(id)],
                    ),
                    body_id,
                );
                (
                    function_id,
                    typ,
                    Expression::Forall(
                        id,
                        param_type,
                        Box::new(Expression::Call(
                            Function::Implies,
                            vec![param_prop, body_prop],
                        )),
                    ),
                )
            }
            Type::Refinement(id, supertype, prop) => {
                let prop = self.translate_proposition(prop)?;
                let (super_id, typ, mut superprop) = self.simplify(*supertype)?;
                superprop.substitute(&Expression::Variable(id), super_id);
                (
                    id,
                    typ,
                    Expression::Call(Function::And, vec![prop, superprop]),
                )
            }
        })
    }

    fn translate_expression(&mut self, expr: LExpression) -> Result<Expression, ()> {
        Ok(match expr {
            LExpression::Ast => Expression::Ast,
            LExpression::Variable(id, _) => Expression::Variable(id),
            LExpression::Call(constant, args) => Expression::Call(
                Function::Constant(constant),
                args.into_iter()
                    .map(|arg| self.translate_expression(arg))
                    .collect::<Result<_, ()>>()?,
            ),
            LExpression::Tuple(contents) => {
                let (first_type, second_type) = (contents.0.unrefined_type()?, contents.1.unrefined_type()?);
                self.register_type(&first_type);
                self.register_type(&second_type);
                Expression::Call(
                    Function::Pair(
                        first_type,
                        second_type,
                    ),
                    vec![
                        self.translate_expression(contents.0)?,
                        self.translate_expression(contents.1)?,
                    ],
                )
            },
            LExpression::First(arg) => {
                let (first_type, second_type) = if let UnrefinedType::Product(contents) = arg.unrefined_type()? {
                    (contents.0, contents.1)
                } else {
                    return Err(());
                };
                self.register_type(&first_type);
                self.register_type(&second_type);
                Expression::Call(Function::First(first_type, second_type), vec![self.translate_expression(*arg)?])
            }
            LExpression::Second(arg) => {
                let (first_type, second_type) = if let UnrefinedType::Product(contents) = arg.unrefined_type()? {
                    (contents.0, contents.1)
                } else {
                    return Err(());
                };
                self.register_type(&first_type);
                self.register_type(&second_type);
                Expression::Call(Function::Second(first_type, second_type), vec![self.translate_expression(*arg)?])
            }
            LExpression::Application(contents) => {
                let (param_type, body_type) = if let UnrefinedType::Function(contents) = contents.0.unrefined_type()? {
                    (contents.0, contents.1)
                } else {
                    return Err(());
                };
                self.register_type(&param_type);
                self.register_type(&body_type);
                Expression::Call(
                    Function::Apply(param_type, body_type),
                    vec![
                        self.translate_expression(contents.0)?,
                        self.translate_expression(contents.1)?,
                    ],
                )
            },
        })
    }

    fn translate_proposition(&mut self, prop: LProposition) -> Result<Expression, ()> {
        Ok(match prop {
            LProposition::False => Expression::False,
            LProposition::Implies(contents) => Expression::Call(
                Function::Implies,
                vec![
                    self.translate_proposition(contents.0)?,
                    self.translate_proposition(contents.1)?,
                ],
            ),
            LProposition::Forall(id, contents) => {
                let (typ_id, typ, mut prop) = self.simplify(contents.0)?;
                self.register_type(&typ);
                prop.substitute(&Expression::Variable(id), typ_id);
                Expression::Forall(
                    id,
                    typ,
                    Box::new(Expression::Call(
                        Function::Implies,
                        vec![prop, self.translate_proposition(contents.1)?],
                    )),
                )
            }
            LProposition::Call(pred, args) => Expression::Call(
                Function::Predicate(pred),
                args.into_iter()
                    .map(|arg| self.translate_expression(arg))
                    .collect::<Result<_, ()>>()?,
            ),
            LProposition::Equal(contents) => {
                let left = contents.1;
                let right = contents.2;
                let left_type = left.unrefined_type()?;
                let right_type = right.unrefined_type()?;
                self.register_type(&left_type);
                self.register_type(&right_type);
                self.register_type(&contents.0.unrefine());
                match contents.0 {
                    Type::One => {
                        if let UnrefinedType::One = left_type {
                            if let UnrefinedType::One = right_type {
                                Expression::True
                            } else {
                                Expression::False
                            }
                        } else {
                            Expression::False
                        }
                    }
                    Type::Bool => {
                        if let UnrefinedType::Bool = left_type {
                            if let UnrefinedType::Bool = right_type {
                                Expression::Call(
                                    Function::Equal,
                                    vec![
                                        self.translate_expression(left)?,
                                        self.translate_expression(right)?,
                                    ],
                                )
                            } else {
                                Expression::False
                            }
                        } else {
                            Expression::False
                        }
                    }
                    Type::Product(id, mut contents) => {
                        let prop1 = self.translate_proposition(LProposition::Equal(Box::new((
                            contents.0,
                            LExpression::First(Box::new(left.clone())),
                            LExpression::First(Box::new(right.clone())),
                        ))))?;
                        contents.1.substitute(&left, id);
                        let prop2 = self.translate_proposition(LProposition::Equal(Box::new((
                            contents.1,
                            LExpression::Second(Box::new(left)),
                            LExpression::Second(Box::new(right)),
                        ))))?;
                        Expression::Call(Function::And, vec![prop1, prop2])
                    }
                    Type::Function(id, contents) => {
                        let (type_id, typ, mut prop1) = self.simplify(contents.0)?;
                        prop1.substitute(&Expression::Variable(id), type_id);
                        let prop2 = self.translate_proposition(LProposition::Equal(Box::new((
                            contents.1,
                            LExpression::Application(Box::new((
                                left,
                                LExpression::Variable(id, typ.clone()),
                            ))),
                            LExpression::Application(Box::new((
                                right,
                                LExpression::Variable(id, typ.clone()),
                            ))),
                        ))))?;
                        Expression::Forall(
                            id,
                            typ,
                            Box::new(Expression::Call(Function::Implies, vec![prop1, prop2])),
                        )
                    }
                    Type::Refinement(id, supertype, prop) => {
                        let mut prop1 = self.translate_proposition(prop)?;
                        let mut prop2 = prop1.clone();
                        let smt_left = self.translate_expression(left.clone())?;
                        let smt_right = self.translate_expression(right.clone())?;
                        prop1.substitute(&smt_left, id);
                        prop2.substitute(&smt_right, id);
                        Expression::Call(
                            Function::And,
                            vec![
                                Expression::Call(Function::And, vec![prop1, prop2]),
                                self.translate_proposition(LProposition::Equal(Box::new((
                                    *supertype, left, right,
                                ))))?,
                            ],
                        )
                    }
                }
            }
            LProposition::Supertype(contents) => {
                let (super_id, supertype, super_prop) = self.simplify(contents.0)?;
                let (sub_id, subtype, mut sub_prop) = self.simplify(contents.1)?;
                self.register_type(&supertype);
                self.register_type(&subtype);
                if supertype != subtype {
                    return Ok(Expression::False);
                }
                sub_prop.substitute(&Expression::Variable(super_id), sub_id);
                Expression::Forall(
                    super_id,
                    supertype,
                    Box::new(Expression::Call(
                        Function::Implies,
                        vec![sub_prop, super_prop],
                    )),
                )
            }
        })
    }

    fn translate_judgement_to_smt(mut self, judgement: Judgement) -> Result<Smt, ()> {
        let Judgement {
            context,
            expression,
            typ,
        } = judgement;
        let mut declarations = Vec::new();
        let mut assertions = Vec::new();
        for defn in context.into_iter() {
            let (id, typ, mut prop) = self.simplify(defn.1)?;
            self.register_type(&typ);
            prop.substitute(&Expression::Variable(defn.0), id);
            declarations.push(Declaration {
                id: defn.0,
                typ,
            });
            assertions.push(prop);
        }
        let (id, _, mut prop) = self.simplify(typ)?;
        prop.substitute(&self.translate_expression(expression)?, id);
        assertions.push(Expression::Call(Function::Not, vec![prop]));
        Ok(Smt {
            declarations,
            assertions,
            types: self.types,
        })
    }
}

pub fn translate_judgement_to_smt(
    judgement: Judgement,
    ident_gen: &mut IdentifierGenerator,
) -> Result<Smt, ()> {
    let translater = ToSmt {
        ident_gen,
        types: Vec::new(),
    };
    translater.translate_judgement_to_smt(judgement)
}
