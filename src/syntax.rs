extern crate nom;
use crate::semantic::{Expression as SExpression, UnrefinedType};
use nom::{
    alt, char,
    character::complete::{alphanumeric0, multispace0 as ws0, multispace1 as ws1},
    complete, do_parse,
    error::{Error, ErrorKind},
    many0, map, named, preceded, separated_list0, separated_list1, tag, Err, IResult, Needed,
};
use std::fmt;

#[derive(Debug)]
pub enum Type {
    One,
    Bool,
    Product(Identifier, Box<Type>, Box<Type>),
    Function(Identifier, Box<Type>, Box<Type>),
    Refinement(Identifier, Box<Type>, Proposition),
}

pub type Identifier = String;

#[derive(Debug)]
pub enum Proposition {
    False,
    Implies(Box<Proposition>, Box<Proposition>),
    Forall(Identifier, Box<Type>, Box<Proposition>),
    Call(Predicate, Vec<Expression>),
    Equal(Box<Type>, Expression, Expression),
    Subtype(Box<Type>, Box<Type>),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Predicate {
    Prop,
}

impl fmt::Display for Predicate {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Predicate::Prop => write!(fmt, "prop")?,
        }
        Ok(())
    }
}

impl Predicate {
    pub fn accepts_args(&self, args: &Vec<SExpression>) -> bool {
        match self {
            Predicate::Prop => args.len() == 1 && args[0].typ == UnrefinedType::Bool,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Constant {
    True,
    False,
}

impl Constant {
    pub fn return_type(&self) -> UnrefinedType {
        match self {
            Constant::True | Constant::False => UnrefinedType::Bool,
        }
    }

    pub fn accepts_args(&self, args: &Vec<SExpression>) -> bool {
        match self {
            Constant::False | Constant::True => args.len() == 0,
        }
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Constant::True => write!(fmt, "true")?,
            Constant::False => write!(fmt, "false")?,
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum Expression {
    Ast,
    Variable(Identifier),
    Call(Constant, Vec<Expression>),
    Tuple(Box<Expression>, Box<Expression>),
    Abstraction(Identifier, Box<Type>, Box<Expression>),
    Application(Box<Expression>, Box<Expression>),
    First(Box<Expression>),
    Second(Box<Expression>),
}

named!(typ_bool(&str) -> Type, map!(tag!("bool"), |_| Type::Bool));

named!(typ_one(&str) -> Type, map!(char!('1'), |_| Type::One));

named!(typ_product(&str) -> Type, do_parse!(
    char!('<') >> ws0 >>
    id: identifier >> ws0 >> char!(':') >> ws0 >>
    first: typ >> ws1 >>
    second: typ >> ws0 >> char!('>') >>
    (Type::Product(id, Box::new(first), Box::new(second)))
));

named!(typ_function(&str) -> Type, do_parse!(
    char!('(') >> ws0 >> tag!("fn") >> ws1 >>
    id: identifier >> ws0 >> char!(':') >> ws0 >>
    argtyp: typ >> ws1 >>
    bodytyp: typ >> ws0 >> char!(')') >>
    (Type::Function(id, Box::new(argtyp), Box::new(bodytyp)))
));

named!(typ_refinement(&str) -> Type, do_parse!(
    id: identifier >> ws0 >> char!(':') >> ws0 >>
    t: typ >> ws0 >> char!('{') >> ws0 >>
    prop: proposition >> ws0 >> char!('}') >>
    (Type::Refinement(id, Box::new(t), prop))
));

named!(typ(&str) -> Type, alt!(typ_bool |  typ_product | typ_function | typ_refinement | typ_one));

fn identifier(input: &str) -> IResult<&str, Identifier> {
    if let Some(c) = input.chars().nth(0) {
        if c.is_ascii_alphabetic() {
            let (input, ident) = alphanumeric0(input)?;
            Ok((input, ident.to_string()))
        } else {
            Err(Err::Error(Error {
                code: ErrorKind::Alpha,
                input: input,
            }))
        }
    } else {
        Err(Err::Incomplete(Needed::Unknown))
    }
}

named!(proposition_false(&str) -> Proposition, map!(tag!("false"), |_| Proposition::False));

named!(proposition_implies(&str) -> Proposition, do_parse!(
    char!('(') >> ws0 >> tag!("=>") >> ws1 >>
    assumption: proposition >> ws1 >>
    deduction: proposition >> ws0 >> char!(')') >>
    (Proposition::Implies(Box::new(assumption), Box::new(deduction)))
));

named!(proposition_forall(&str) -> Proposition, do_parse!(
    char!('(') >> ws0 >> tag!("forall") >> ws1 >>
    id: identifier >> ws0 >> char!(':') >> ws0 >>
    t: typ >> ws1 >>
    p: proposition >> ws0 >> char!(')') >>
    (Proposition::Forall(id, Box::new(t), Box::new(p)))
));

named!(proposition_equal(&str) -> Proposition, do_parse!(
    char!('(') >> ws0 >> char!('=') >> ws1 >>
    t: typ >> ws1 >>
    left: expression >> ws1 >>
    right: expression >> ws0 >> char!(')') >>
    (Proposition::Equal(Box::new(t), left, right))
));

named!(proposition_subtype(&str) -> Proposition, do_parse!(
    char!('(') >> ws0 >> tag!("<:") >> ws1 >>
    left: typ >> ws1 >>
    right: typ >> ws0 >> char!(')') >>
    (Proposition::Subtype(Box::new(left), Box::new(right)))
));

named!(proposition_call(&str) -> Proposition, do_parse!(
    char!('(') >> ws0 >>
    pred: predicate >> ws1 >>
    args: separated_list0!(ws1, complete!(expression)) >> char!(')') >>
    (Proposition::Call(pred, args))
));

named!(proposition(&str) -> Proposition, alt!(
    proposition_false |
    proposition_implies |
    proposition_forall |
    proposition_equal |
    proposition_subtype |
    proposition_call
));

named!(predicate(&str) -> Predicate, alt!(
    map!(tag!("prop"), |_| Predicate::Prop)
));

named!(constant(&str) -> Constant, alt!(
    map!(tag!("true"), |_| Constant::True) |
    map!(tag!("false"), |_| Constant::False)
));

named!(expression_variable(&str) -> Expression, map!(identifier, Expression::Variable));

named!(expression_tuple(&str) -> Expression, do_parse!(
    char!('<') >> ws0 >>
    first: expression >> ws1 >>
    second: expression >> ws0 >>
    char!('>') >>
    (Expression::Tuple(Box::new(first), Box::new(second)))
));

named!(expression_call(&str) -> Expression, do_parse!(
    char!('(') >> ws0 >>
    c: constant >>
    args: many0!(preceded!(ws1, complete!(expression))) >>
    ws0 >> char!(')') >>
    (Expression::Call(c, args))
));

named!(expression_abstraction(&str) -> Expression, do_parse!(
    char!('(') >> ws0 >> tag!("fn") >> ws1 >>
    id: identifier >> ws0 >> char!(':') >> ws0 >>
    t: typ >> ws1 >>
    body: expression >> ws0 >> char!(')') >>
    (Expression::Abstraction(id, Box::new(t), Box::new(body)))
));

named!(expression_application(&str) -> Expression, do_parse!(
    char!('(') >> ws0 >>
    f: expression >> ws1 >>
    arg: expression >> ws0 >> char!(')') >>
    (Expression::Application(Box::new(f), Box::new(arg)))
));

named!(expression_first(&str) -> Expression, do_parse!(
    char!('(') >> ws0 >> tag!("first") >> ws1 >>
    arg: expression >> ws0 >> char!(')') >>
    (Expression::First(Box::new(arg)))
));

named!(expression_second(&str) -> Expression, do_parse!(
    char!('(') >> ws0 >> tag!("second") >> ws1 >>
    arg: expression >> ws0 >> char!(')') >>
    (Expression::Second(Box::new(arg)))
));

named!(expression_ast(&str) -> Expression, do_parse!(
    char!('*') >>
    (Expression::Ast)
));

named!(definition(&str) -> (Identifier, Type, Expression), do_parse!(
    char!('(') >> ws0 >>
    id: identifier >> ws0 >> char!(':') >> ws0 >>
    t: typ >> ws0 >> char!('=') >> ws0 >>
    e: expression >> ws0 >> char!(')') >>
    ((id, t, e))
));

named!(expression_let(&str) -> Expression, do_parse!(
    char!('(') >> ws0 >> tag!("let") >> ws1 >>
    defns: separated_list1!(ws1, definition) >> ws1 >> tag!("in") >> ws1 >>
    e: expression >> ws0 >> char!(')') >>
    ({
        let mut expr = e;
        for (id, t, value) in defns.into_iter().rev() {
            expr = Expression::Application(
                Box::new(Expression::Abstraction(id, Box::new(t), Box::new(expr))),
                Box::new(value),
            );
        }
        expr
    })
));

named!(expression(&str) -> Expression, alt!(
    expression_abstraction |
    expression_first |
    expression_second |
    expression_call |
    expression_ast |
    expression_application |
    expression_variable |
    expression_tuple |
    expression_let
));

named!(program(&str) -> Expression, do_parse!(
    ws0 >>
    e: expression >> ws0 >>
    (e)
));

pub fn parse(input: &str) -> Result<Expression, String> {
    let (remaining, ast) = program(input).map_err(|_| "parse error".to_string())?;
    if remaining.len() == 0 {
        Ok(ast)
    } else {
        Err("parse error".to_string())
    }
}
