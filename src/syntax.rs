extern crate nom;
use nom::{
    alt, char,
    character::complete::{alphanumeric0, multispace0 as ws0, multispace1 as ws1},
    complete,
    error::{Error, ErrorKind},
    many0, map, named, preceded, separated_list0, tag, take_while, tuple, Err, IResult, Needed,
};

#[derive(Debug)]
pub enum Type {
    Bool,
    Nat,
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

#[derive(Debug)]
pub enum Predicate {}

#[derive(Debug)]
pub enum Constant {
    Succ,
    First,
    Second,
}

#[derive(Debug)]
pub enum Expression {
    Variable(Identifier),
    Call(Constant, Vec<Expression>),
    Tuple(Box<Expression>, Box<Expression>),
    Abstraction(Identifier, Box<Type>, Box<Expression>),
    Application(Box<Expression>, Box<Expression>),
}

named!(typ_bool(&str) -> Type, map!(tag!("bool"), |_| Type::Bool));

named!(typ_nat(&str) -> Type, map!(tag!("nat"), |_| Type::Nat));

named!(typ_product(&str) -> Type, map!(tuple!(
    char!('<'), ws0, identifier, ws0, char!(':'), ws0, typ, ws1, typ, ws0, char!('>')
), |tup| Type::Product(tup.2, Box::new(tup.6), Box::new(tup.8))));

named!(typ_function(&str) -> Type, map!(tuple!(
    char!('('), ws0, tag!("fn"), ws1, identifier, ws0, char!(':'), ws0, typ, ws1, typ, ws0, char!(')')
), |tup| Type::Function(tup.4, Box::new(tup.8), Box::new(tup.10))));

named!(typ_refinement(&str) -> Type, map!(tuple!(
    identifier, ws0, char!(':'), ws0, typ, ws0, char!('{'), ws0, proposition, ws0, char!('}')
), |tup| Type::Refinement(tup.0, Box::new(tup.4), tup.8)));

named!(typ(&str) -> Type, alt!(typ_bool | typ_nat | typ_product | typ_function | typ_refinement));

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

named!(proposition(&str) -> Proposition, map!(tag!("false"), |_| Proposition::False));

named!(constant(&str) -> Constant, alt!(
    map!(tag!("succ"), |_| Constant::Succ)
        | map!(tag!("first"), |_| Constant::First)
        | map!(tag!("second"), |_| Constant::Second)
));

fn expression_variable(input: &str) -> IResult<&str, Expression> {
    let (input, v) = identifier(input)?;
    Ok((input, Expression::Variable(v)))
}

fn expression_tuple(input: &str) -> IResult<&str, Expression> {
    let (input, (_, _, e1, _, e2, _, _)) = tuple!(
        input,
        char!('<'),
        ws0,
        expression,
        ws1,
        expression,
        ws0,
        char!('>')
    )?;
    Ok((input, Expression::Tuple(Box::new(e1), Box::new(e2))))
}

fn expression_call(input: &str) -> IResult<&str, Expression> {
    let (input, (_, _, c, _, args, _, _)) = tuple!(
        input,
        char!('('),
        ws0,
        constant,
        ws1,
        separated_list0!(ws1, complete!(expression)),
        ws0,
        char!(')')
    )?;
    Ok((input, Expression::Call(c, args)))
}

fn expression_abstraction(input: &str) -> IResult<&str, Expression> {
    let (input, (_, _, _, _, ident, _, _, _, t, _, body, _, _)) = tuple!(
        input,
        char!('('),
        ws0,
        tag!("fn"),
        ws1,
        identifier,
        ws0,
        char!(':'),
        ws0,
        typ,
        ws1,
        expression,
        ws0,
        char!(')')
    )?;
    Ok((
        input,
        Expression::Abstraction(ident, Box::new(t), Box::new(body)),
    ))
}

named!(expression_application(&str) -> Expression, map!(tuple!(char!('('), ws0, expression, ws1, expression, ws0, char!(')')), |tup| Expression::Application(Box::new(tup.2), Box::new(tup.4))));

pub fn expression(input: &str) -> IResult<&str, Expression> {
    alt!(
        input,
        expression_abstraction
            | expression_call
            | expression_application
            | expression_variable
            | expression_tuple
    )
}
