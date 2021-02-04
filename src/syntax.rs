extern crate nom;
use nom::{
    IResult,
    Err,
    Needed,
    error::{Error, ErrorKind},
    character::{
        complete::{multispace0, multispace1, alphanumeric0},
    },
    alt,
    char,
    complete,
    many0,
    map,
    preceded,
    separated_list0,
    take_while,
    tag,
    tuple,
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
pub enum Predicate {
}

#[derive(Debug)]
pub enum Constant {
    Succ,
}

#[derive(Debug)]
pub enum Expression {
    Variable(Identifier),
    Call(Constant, Vec<Expression>),
    Tuple(Box<Expression>, Box<Expression>),
    Abstraction(Identifier, Box<Type>, Box<Expression>),
    Extraction(bool, Box<Expression>),
    Application(Box<Expression>, Box<Expression>),
}

fn identifier(input: &str) -> IResult<&str, Identifier> {
    if let Some(c) = input.chars().nth(0) {
        if c.is_ascii_alphabetic() {
            let (input, ident) = alphanumeric0(input)?;
            Ok((input, ident.to_string()))
        } else {
            Err(Err::Error(Error {code: ErrorKind::Alpha, input: input}))
        }
    } else {
        Err(Err::Incomplete(Needed::Unknown))
    }
}

fn constant(input: &str) -> IResult<&str, Constant> {
    alt!(
        input,
        map!(tag!("succ"), |_| Constant::Succ)
    )
}

fn expression_variable(input: &str) -> IResult<&str, Expression> {
    let (input, v) = identifier(input)?;
    Ok((input, Expression::Variable(v)))
}

fn expression_tuple(input: &str) -> IResult<&str, Expression> {
    let (input, (_, _, e1, _, e2, _, _)) = tuple!(input, char!('<'), multispace0, expression, multispace1, expression, multispace0, char!('>'))?;
    Ok((input, Expression::Tuple(Box::new(e1), Box::new(e2))))
}

fn expression_call(input: &str) -> IResult<&str, Expression> {
    let (input, (_, _, c, _, args, _, _)) = tuple!(input, char!('('), multispace0, constant, multispace1, separated_list0!(multispace1, complete!(expression)), multispace0, char!(')'))?;
    Ok((input, Expression::Call(c, args)))
}

pub fn expression(input: &str) -> IResult<&str, Expression> {
    alt!(
        input,
        expression_call |
        expression_variable |
        expression_tuple
    )
}
