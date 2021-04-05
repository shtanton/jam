use crate::semantic::{
    Expression as SExpression, ExpressionKind as SExpressionKind,
    Proposition as SProposition, Identifier, Type as SType, UnrefinedType,
    IdentifierGenerator, Judgement as SJudgement,
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
    fn unrefine(&self) -> UnrefinedType {
        match self {
            Type::One => UnrefinedType::One,
            Type::Bool => UnrefinedType::Bool,
            Type::Product(_, contents) => UnrefinedType::Product(Box::new((contents.0.unrefine(), contents.1.unrefine()))),
            Type::Function(_, contents) => UnrefinedType::Function(Box::new((contents.0.unrefine(), contents.1.unrefine()))),
            Type::Refinement(_, typ, _) => typ.unrefine(),
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

#[derive(Clone, Debug)]
pub enum Proposition {
    False,
    Implies(Box<(Proposition, Proposition)>),
    Forall(Identifier, Box<(Type, Proposition)>),
    Call(Predicate, Vec<Expression>),
    Equal(Box<(Type, Expression, Expression)>),
    Supertype(Box<(Type, Type)>),
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
                let new_fn = self.next_id();
                let refinement_id = self.next_id();
                let refined_body_type = self.refine_type(&body.typ);
                let typ = Type::Function(self.next_id(), Box::new((
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
                )));
                let unrefined_type = typ.unrefine();
                self.context.push((new_fn, typ));
                Expression::Variable(new_fn, unrefined_type)
            },
            SExpressionKind::Application(contents) => Expression::Application(Box::new((
                self.lift_expression(contents.0),
                self.lift_expression(contents.1),
            ))),
            SExpressionKind::Ast => Expression::Ast,
            SExpressionKind::Call(constant, args) => Expression::Call(
                constant,
                args.into_iter().map(|arg| self.lift_expression(arg)).collect(),
            ),
            SExpressionKind::First(arg) => Expression::First(Box::new(self.lift_expression(*arg))),
            SExpressionKind::Second(arg) => Expression::Second(Box::new(self.lift_expression(*arg))),
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
                args.into_iter().map(|arg| self.lift_expression(arg)).collect(),
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
            },
            SType::Function(id, contents) => {
                let param = self.lift_type(contents.0);
                let body = self.lift_type(contents.1);
                Type::Function(id, Box::new((param, body)))
            },
            SType::Refinement(id, supertype, prop) => {
                let supertype = self.lift_type(*supertype);
                let prop = self.lift_proposition(prop);
                Type::Refinement(id, Box::new(supertype), prop)
            },
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
