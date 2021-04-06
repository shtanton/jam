use crate::lambda_lift::{Expression as LExpression, Judgement, Proposition as LProposition, Type};
use crate::semantic::{Identifier, IdentifierGenerator, UnrefinedType};
use crate::syntax::{Constant, Predicate};
use std::collections::HashMap;
use std::fmt;

#[derive(Clone, Eq, Hash, PartialEq)]
enum Sort {
    Pair(Box<(Sort, Sort)>),
    Id(TypeIdentifier),
    One,
    Bool,
}

impl fmt::Display for Sort {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Sort::One => write!(fmt, "1")?,
            Sort::Bool => write!(fmt, "B")?,
            Sort::Id(id) => write!(fmt, "T!{}", id)?,
            Sort::Pair(contents) => write!(fmt, "<{}x{}>", contents.0, contents.1)?,
        }
        Ok(())
    }
}

struct TypeMap {
    sorts: HashMap<UnrefinedType, Sort>,
    types: HashMap<Sort, UnrefinedType>,
    next_id: TypeIdentifier,
}

impl Default for TypeMap {
    fn default() -> TypeMap {
        TypeMap {
            sorts: HashMap::new(),
            types: HashMap::new(),
            next_id: 0,
        }
    }
}

impl TypeMap {
    fn get_sort(&mut self, typ: &UnrefinedType) -> Sort {
        if let Some(sort) = self.sorts.get(typ) {
            sort.clone()
        } else {
            match typ {
                UnrefinedType::One => Sort::One,
                UnrefinedType::Bool => Sort::Bool,
                UnrefinedType::Product(contents) => Sort::Pair(Box::new((
                    self.get_sort(&contents.0),
                    self.get_sort(&contents.1),
                ))),
                UnrefinedType::Function(contents) => {
                    let sort = Sort::Id(self.next_id);
                    self.next_id += 1;
                    self.sorts.insert(typ.clone(), sort.clone());
                    self.types.insert(sort.clone(), typ.clone());
                    sort
                }
            }
        }
    }
}

pub type TypeIdentifier = u32;

pub struct Smt {
    declarations: Vec<Declaration>,
    assertions: Vec<Expression>,
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
    id: Identifier,
    typ: Sort,
}

#[derive(Clone)]
pub enum Expression {
    False,
    True,
    Ast,
    Variable(Identifier),
    Call(Function, Vec<Expression>),
    Forall(Identifier, Sort, Box<Expression>),
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
    First,
    Second,
    Pair,
    And,
    Predicate(Predicate),
    Constant(Constant),
    Apply(Sort),
}

impl fmt::Display for Function {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Function::Implies => write!(fmt, "=>")?,
            Function::Equal => write!(fmt, "=")?,
            Function::Not => write!(fmt, "not")?,
            Function::First => write!(fmt, "first")?,
            Function::Second => write!(fmt, "second")?,
            Function::Pair => write!(fmt, "pair")?,
            Function::And => write!(fmt, "and")?,
            Function::Predicate(pred) => write!(fmt, "{}", pred)?,
            Function::Constant(constant) => write!(fmt, "{}", constant)?,
            Function::Apply(typ) => write!(fmt, "apply_{}", typ)?,
        }
        Ok(())
    }
}

struct ToSmt<'a> {
    ident_gen: &'a mut IdentifierGenerator,
    type_map: TypeMap,
}

impl<'a> ToSmt<'a> {
    fn next_id(&mut self) -> Identifier {
        self.ident_gen.next()
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
                    Expression::Call(Function::First, vec![Expression::Variable(tuple_id)]);
                first_prop.substitute(&first_call, first_id);
                second_prop.substitute(&first_call, id);
                second_prop.substitute(
                    &Expression::Call(Function::Second, vec![Expression::Variable(tuple_id)]),
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
                let typ = UnrefinedType::Function(Box::new((param_type.clone(), body_type)));
                let type_id = self.type_map.get_sort(&typ);
                param_prop.substitute(&Expression::Variable(id), param_id);
                body_prop.substitute(
                    &Expression::Call(
                        Function::Apply(type_id),
                        vec![Expression::Variable(function_id), Expression::Variable(id)],
                    ),
                    body_id,
                );
                (
                    function_id,
                    typ,
                    Expression::Forall(
                        id,
                        self.type_map.get_sort(&param_type),
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
            LExpression::Tuple(contents) => Expression::Call(
                Function::Pair,
                vec![
                    self.translate_expression(contents.0)?,
                    self.translate_expression(contents.1)?,
                ],
            ),
            LExpression::First(arg) => {
                Expression::Call(Function::First, vec![self.translate_expression(*arg)?])
            }
            LExpression::Second(arg) => {
                Expression::Call(Function::Second, vec![self.translate_expression(*arg)?])
            }
            LExpression::Application(contents) => Expression::Call(
                Function::Apply(self.type_map.get_sort(&contents.0.unrefined_type()?)),
                vec![
                    self.translate_expression(contents.0)?,
                    self.translate_expression(contents.1)?,
                ],
            ),
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
                prop.substitute(&Expression::Variable(id), typ_id);
                Expression::Forall(
                    id,
                    self.type_map.get_sort(&typ),
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
                            self.type_map.get_sort(&typ),
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
                if supertype != subtype {
                    return Ok(Expression::False);
                }
                sub_prop.substitute(&Expression::Variable(super_id), sub_id);
                Expression::Forall(
                    super_id,
                    self.type_map.get_sort(&supertype),
                    Box::new(Expression::Call(
                        Function::Implies,
                        vec![sub_prop, super_prop],
                    )),
                )
            }
        })
    }

    fn translate_judgement_to_smt(&mut self, judgement: Judgement) -> Result<Smt, ()> {
        let Judgement {
            context,
            expression,
            typ,
        } = judgement;
        let mut declarations = Vec::new();
        let mut assertions = Vec::new();
        for defn in context.into_iter() {
            let (id, typ, mut prop) = self.simplify(defn.1)?;
            prop.substitute(&Expression::Variable(defn.0), id);
            declarations.push(Declaration {
                id: defn.0,
                typ: self.type_map.get_sort(&typ),
            });
            assertions.push(prop);
        }
        let (id, _, mut prop) = self.simplify(typ)?;
        prop.substitute(&self.translate_expression(expression)?, id);
        assertions.push(Expression::Call(Function::Not, vec![prop]));
        Ok(Smt {
            declarations,
            assertions,
        })
    }
}

pub fn translate_judgement_to_smt(
    judgement: Judgement,
    ident_gen: &mut IdentifierGenerator,
) -> Result<Smt, ()> {
    let mut translater = ToSmt {
        ident_gen,
        type_map: TypeMap::default(),
    };
    translater.translate_judgement_to_smt(judgement)
}
