use crate::syntax::{
    Predicate,
    Constant,
};
use crate::semantic::{
    Sort,
};

pub type Identifier = u32;

#[derive(Clone)]
pub enum Proposition {
    False,
    True,
    And(Box<(Proposition, Proposition)>),
    Implies(Box<(Proposition, Proposition)>),
    Forall(Identifier, Sort, Box<Proposition>),
    Call(Predicate, Vec<Expression>),
    Equal(Expression, Expression),
}

impl Proposition {
    pub fn substitute(&mut self, expr: &Expression, id: Identifier) {
        match self {
            Proposition::False => {},
            Proposition::True => {},
            Proposition::And(args) => {
                args.0.substitute(expr, id);
                args.1.substitute(expr, id);
            },
            Proposition::Implies(args) => {
                args.0.substitute(expr, id);
                args.1.substitute(expr, id);
            },
            Proposition::Forall(forall_id, sort, prop) => {
                if *forall_id != id {
                    prop.substitute(expr, id);
                }
            },
            Proposition::Call(pred, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute(expr, id);
                });
            },
            Proposition::Equal(left, right) => {
                left.substitute(expr, id);
                right.substitute(expr, id);
            },
        }
    }
}

#[derive(Clone)]
pub enum Expression {
    Variable(Identifier),
    Call(Constant, Vec<Expression>),
    Tuple(Box<(Expression, Expression)>),
    Abstraction(Identifier, Box<Expression>),
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
            },
            Expression::Call(constant, args) => {
                args.iter_mut().for_each(|arg| {
                    arg.substitute(expr, id);
                });
            },
            Expression::Tuple(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            },
            Expression::Abstraction(arg, body) => {
                if *arg != id {
                    body.substitute(expr, id);
                }
            },
            Expression::Application(contents) => {
                contents.0.substitute(expr, id);
                contents.1.substitute(expr, id);
            },
            Expression::First(arg) => {
                arg.substitute(expr, id);
            },
            Expression::Second(arg) => {
                arg.substitute(expr, id);
            },
        }
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
