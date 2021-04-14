use crate::semantic::{
    Expression as SExpression, ExpressionKind as SExpressionKind, Identifier, IdentifierGenerator,
    Judgement as SJudgement, Proposition as SProposition, Type as SType, UnrefinedType,
};
use crate::syntax::{Constant, Predicate};

#[derive(Debug)]
pub struct Judgement {
    pub context: Vec<(Identifier, Type)>,
    pub expression: Expression,
    pub typ: Type,
}

#[derive(Clone, Debug)]
pub enum Type {
    One,
    Bool,
    Product(Identifier, Box<(Type, Type)>),
    Function(Identifier, Box<(Type, Type)>),
    Refinement(Identifier, Box<Type>, Proposition),
}

impl Type {
    pub fn unrefine(&self) -> UnrefinedType {
        match self {
            Type::One => UnrefinedType::One,
            Type::Bool => UnrefinedType::Bool,
            Type::Product(_, contents) => {
                UnrefinedType::Product(Box::new((contents.0.unrefine(), contents.1.unrefine())))
            }
            Type::Function(_, contents) => {
                UnrefinedType::Function(Box::new((contents.0.unrefine(), contents.1.unrefine())))
            }
            Type::Refinement(_, typ, _) => typ.unrefine(),
        }
    }

    pub fn substitute(&mut self, expr: &Expression, target: Identifier) {
        match self {
            Type::One | Type::Bool => {}
            Type::Product(_, contents) => {
                contents.0.substitute(expr, target);
                contents.1.substitute(expr, target);
            }
            Type::Function(_, contents) => {
                contents.0.substitute(expr, target);
                contents.1.substitute(expr, target);
            }
            Type::Refinement(_, supertype, prop) => {
                supertype.substitute(expr, target);
                prop.substitute(expr, target);
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum Expression {
    Ast,
    Variable(Identifier, UnrefinedType),
    Call(Constant, Vec<Expression>),
    Tuple(Box<(Expression, Expression)>),
    Application(Box<(Expression, Expression)>),
    First(Box<Expression>),
    Second(Box<Expression>),
}

impl Expression {
    pub fn unrefined_type(&self) -> Result<UnrefinedType, ()> {
        Ok(match self {
            Expression::Ast => UnrefinedType::One,
            Expression::Variable(_, typ) => typ.clone(),
            Expression::Call(constant, _) => constant.return_type(),
            Expression::Tuple(contents) => UnrefinedType::Product(Box::new((
                contents.0.unrefined_type()?,
                contents.1.unrefined_type()?,
            ))),
            Expression::Application(contents) => {
                if let UnrefinedType::Function(fcontents) = contents.0.unrefined_type()? {
                    fcontents.1
                } else {
                    return Err(());
                }
            }
            Expression::First(arg) => {
                if let UnrefinedType::Product(pcontents) = arg.unrefined_type()? {
                    pcontents.0
                } else {
                    return Err(());
                }
            }
            Expression::Second(arg) => {
                if let UnrefinedType::Product(pcontents) = arg.unrefined_type()? {
                    pcontents.1
                } else {
                    return Err(());
                }
            }
        })
    }

    pub fn substitute(&mut self, expr: &Expression, target: Identifier) {
        match self {
            Expression::Ast => {}
            Expression::Variable(id, _) => {
                if *id == target {
                    *self = expr.clone();
                }
            }
            Expression::Application(contents) => {
                contents.0.substitute(expr, target);
                contents.1.substitute(expr, target);
            }
            Expression::Call(_, args) => {
                for arg in args.iter_mut() {
                    arg.substitute(expr, target);
                }
            }
            Expression::First(arg) => {
                arg.substitute(expr, target);
            }
            Expression::Second(arg) => {
                arg.substitute(expr, target);
            }
            Expression::Tuple(contents) => {
                contents.0.substitute(expr, target);
                contents.1.substitute(expr, target);
            }
        }
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
    pub fn substitute(&mut self, expr: &Expression, target: Identifier) {
        match self {
            Proposition::False => {}
            Proposition::Implies(contents) => {
                contents.0.substitute(expr, target);
                contents.1.substitute(expr, target);
            }
            Proposition::Forall(_, contents) => {
                contents.0.substitute(expr, target);
                contents.1.substitute(expr, target);
            }
            Proposition::Call(_, args) => {
                for arg in args.iter_mut() {
                    arg.substitute(expr, target);
                }
            }
            Proposition::Equal(contents) => {
                contents.0.substitute(expr, target);
                contents.1.substitute(expr, target);
                contents.2.substitute(expr, target);
            }
            Proposition::Supertype(contents) => {
                contents.0.substitute(expr, target);
                contents.1.substitute(expr, target);
            }
        }
    }
}

struct LambdaLifter<'a> {
    ident_gen: &'a mut IdentifierGenerator,
    context: Vec<(Identifier, Type)>,
}

impl<'a> LambdaLifter<'a> {
    fn next_id(&mut self) -> Identifier {
        self.ident_gen.next()
    }

    fn refine_type(&mut self, typ: &UnrefinedType) -> Type {
        match typ {
            UnrefinedType::One => Type::One,
            UnrefinedType::Bool => Type::Bool,
            UnrefinedType::Product(contents) => Type::Product(
                self.next_id(),
                Box::new((self.refine_type(&contents.0), self.refine_type(&contents.1))),
            ),
            UnrefinedType::Function(contents) => Type::Function(
                self.next_id(),
                Box::new((self.refine_type(&contents.0), self.refine_type(&contents.1))),
            ),
        }
    }

    fn lift_expression(&mut self, expr: SExpression) -> Expression {
        match expr.kind {
            SExpressionKind::Abstraction(param, param_type, body) => {
                let environment: Vec<_> = expr.env.into_iter().collect();
                let new_fn = self.next_id();
                let refinement_id = self.next_id();
                let refined_body_type = self.refine_type(&body.typ);
                let mut typ = Type::Function(
                    param,
                    Box::new((
                        self.lift_type(param_type),
                        Type::Refinement(
                            refinement_id,
                            Box::new(refined_body_type.clone()),
                            Proposition::Equal(Box::new((
                                refined_body_type,
                                Expression::Variable(refinement_id, body.typ.clone()),
                                self.lift_expression(*body),
                            ))),
                        ),
                    )),
                );
                for (param_id, param_type) in environment.iter().rev() {
                    typ = Type::Function(*param_id, Box::new((self.refine_type(param_type), typ)));
                }
                let mut expr = Expression::Variable(new_fn, typ.unrefine());
                for (param_id, param_type) in environment.into_iter() {
                    expr = Expression::Application(Box::new((
                        expr,
                        Expression::Variable(param_id, param_type),
                    )));
                }
                self.context.push((new_fn, typ));
                expr
            }
            SExpressionKind::Application(contents) => Expression::Application(Box::new((
                self.lift_expression(contents.0),
                self.lift_expression(contents.1),
            ))),
            SExpressionKind::Ast => Expression::Ast,
            SExpressionKind::Call(constant, args) => Expression::Call(
                constant,
                args.into_iter()
                    .map(|arg| self.lift_expression(arg))
                    .collect(),
            ),
            SExpressionKind::First(arg) => Expression::First(Box::new(self.lift_expression(*arg))),
            SExpressionKind::Second(arg) => {
                Expression::Second(Box::new(self.lift_expression(*arg)))
            }
            SExpressionKind::Tuple(contents) => Expression::Tuple(Box::new((
                self.lift_expression(contents.0),
                self.lift_expression(contents.1),
            ))),
            SExpressionKind::Variable(id) => Expression::Variable(id, expr.typ),
        }
    }

    fn lift_proposition(&mut self, prop: SProposition) -> Proposition {
        match prop {
            SProposition::False => Proposition::False,
            SProposition::Implies(contents) => Proposition::Implies(Box::new((
                self.lift_proposition(contents.0),
                self.lift_proposition(contents.1),
            ))),
            SProposition::Call(pred, args) => Proposition::Call(
                pred,
                args.into_iter()
                    .map(|arg| self.lift_expression(arg))
                    .collect(),
            ),
            SProposition::Forall(id, contents) => Proposition::Forall(
                id,
                Box::new((
                    self.lift_type(contents.0),
                    self.lift_proposition(contents.1),
                )),
            ),
            SProposition::Equal(contents) => Proposition::Equal(Box::new((
                self.lift_type(contents.0),
                self.lift_expression(contents.1),
                self.lift_expression(contents.2),
            ))),
            SProposition::Supertype(contents) => Proposition::Supertype(Box::new((
                self.lift_type(contents.0),
                self.lift_type(contents.1),
            ))),
        }
    }

    fn lift_type(&mut self, typ: SType) -> Type {
        match typ {
            SType::One => Type::One,
            SType::Bool => Type::Bool,
            SType::Product(id, contents) => {
                let first = self.lift_type(contents.0);
                let second = self.lift_type(contents.1);
                Type::Product(id, Box::new((first, second)))
            }
            SType::Function(id, contents) => {
                let param = self.lift_type(contents.0);
                let body = self.lift_type(contents.1);
                Type::Function(id, Box::new((param, body)))
            }
            SType::Refinement(id, supertype, prop) => {
                let supertype = self.lift_type(*supertype);
                let prop = self.lift_proposition(prop);
                Type::Refinement(id, Box::new(supertype), prop)
            }
        }
    }

    fn lift_defn(&mut self, (id, typ): (Identifier, SType)) -> (Identifier, Type) {
        (id, self.lift_type(typ))
    }

    fn lift(&mut self, judgement: SJudgement) -> (Expression, Type) {
        for defn in judgement.context.into_iter() {
            let new_defn = self.lift_defn(defn);
            self.context.push(new_defn);
        }
        let expression = self.lift_expression(judgement.expression);
        let typ = self.lift_type(judgement.typ);
        (expression, typ)
    }
}

pub fn lift(judgement: SJudgement, ident_gen: &mut IdentifierGenerator) -> Judgement {
    let mut lifter = LambdaLifter {
        ident_gen,
        context: Vec::new(),
    };
    let (expression, typ) = lifter.lift(judgement);
    Judgement {
        context: lifter.context,
        expression,
        typ,
    }
}
