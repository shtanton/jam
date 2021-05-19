extern crate nom;
use crate::semantic::{Expression as SExpression, UnrefinedType};
use nom::{
    alt, char,
    character::complete::{digit1, multispace0 as ws0, multispace1 as ws1},
    complete, do_parse,
    error::{Error, ErrorKind},
    many0, map, map_res, named, preceded, separated_list0, separated_list1, tag, tuple, Err,
    IResult, Needed,
};
use std::fmt;

#[derive(Debug)]
pub enum Type {
    One,
    Bool,
    U8,
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
    Supertype(Box<Type>, Box<Type>),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Predicate {
    Prop,
    LessThan,
    LessThanEq,
    GreaterThan,
    GreaterThanEq,
}

impl fmt::Display for Predicate {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Predicate::Prop => write!(fmt, "prop")?,
            Predicate::LessThan => write!(fmt, "<")?,
            Predicate::LessThanEq => write!(fmt, "<=")?,
            Predicate::GreaterThan => write!(fmt, ">")?,
            Predicate::GreaterThanEq => write!(fmt, ">=")?,
        }
        Ok(())
    }
}

impl Predicate {
    pub fn accepts_args(&self, args: &Vec<SExpression>) -> bool {
        match self {
            Predicate::Prop => args.len() == 1 && args[0].typ == UnrefinedType::Bool,
            Predicate::LessThan
            | Predicate::LessThanEq
            | Predicate::GreaterThan
            | Predicate::GreaterThanEq => {
                args.len() == 2
                    && args[0].typ == UnrefinedType::U8
                    && args[1].typ == UnrefinedType::U8
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Constant {
    True,
    False,
    And,
    Or,
    Implies,
    DblImplies,
    Not,
    U8(u8),
    Succ,
    Pred,
    Add,
    Sub,
    LessThan,
    LessThanEq,
    GreaterThan,
    GreaterThanEq,
}

impl Constant {
    pub fn return_type(&self) -> UnrefinedType {
        match self {
            Constant::True
            | Constant::False
            | Constant::And
            | Constant::Or
            | Constant::Implies
            | Constant::DblImplies
            | Constant::Not
            | Constant::LessThan
            | Constant::LessThanEq
            | Constant::GreaterThan
            | Constant::GreaterThanEq => UnrefinedType::Bool,
            Constant::U8(_) | Constant::Succ | Constant::Pred | Constant::Add | Constant::Sub => {
                UnrefinedType::U8
            }
        }
    }

    pub fn accepts_args(&self, args: &Vec<SExpression>) -> bool {
        match self {
            Constant::False | Constant::True | Constant::U8(_) => args.len() == 0,
            Constant::And | Constant::Or | Constant::Implies | Constant::DblImplies => {
                if args.len() != 2 {
                    return false;
                }
                match (&args[0].typ, &args[1].typ) {
                    (UnrefinedType::Bool, UnrefinedType::Bool) => true,
                    _ => false,
                }
            }
            Constant::Not => {
                if args.len() != 1 {
                    return false;
                }
                args[0].typ == UnrefinedType::Bool
            }
            Constant::Succ | Constant::Pred => {
                if args.len() != 1 {
                    return false;
                }
                args[0].typ == UnrefinedType::U8
            }
            Constant::Add
            | Constant::Sub
            | Constant::LessThan
            | Constant::LessThanEq
            | Constant::GreaterThan
            | Constant::GreaterThanEq => {
                if args.len() != 2 {
                    return false;
                }
                args[0].typ == UnrefinedType::U8 && args[1].typ == UnrefinedType::U8
            }
        }
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Constant::True => write!(fmt, "true"),
            Constant::False => write!(fmt, "false"),
            Constant::And => write!(fmt, "and"),
            Constant::Or => write!(fmt, "or"),
            Constant::Implies => write!(fmt, "=>"),
            Constant::DblImplies => write!(fmt, "<=>"),
            Constant::Not => write!(fmt, "not"),
            Constant::U8(v) => write!(fmt, "{}", v),
            Constant::Succ => write!(fmt, "succ"),
            Constant::Pred => write!(fmt, "pred"),
            Constant::Add => write!(fmt, "+"),
            Constant::Sub => write!(fmt, "-"),
            Constant::LessThan => write!(fmt, "<"),
            Constant::LessThanEq => write!(fmt, "<="),
            Constant::GreaterThan => write!(fmt, ">"),
            Constant::GreaterThanEq => write!(fmt, ">="),
        }
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
    U8Rec(Box<Expression>, Box<Expression>, Box<Expression>),
    Ite(Box<Expression>, Box<Expression>, Box<Expression>),
}

named!(typ_bool(&str) -> Type, map!(tag!("bool"), |_| Type::Bool));

named!(typ_u8(&str) -> Type, map!(tag!("u8"), |_| Type::U8));

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
    params: parameter_list >> ws1 >>
    bodytyp: typ >> ws0 >> char!(')') >>
    ({
        let mut t = bodytyp;
        for (id, typ) in params.into_iter().rev() {
            t = Type::Function(id, Box::new(typ), Box::new(t));
        }
        t
    })
));

named!(typ_refinement(&str) -> Type, do_parse!(
    id: identifier >> ws0 >> char!(':') >> ws0 >>
    t: typ >> ws0 >> char!('{') >> ws0 >>
    prop: proposition >> ws0 >> char!('}') >>
    (Type::Refinement(id, Box::new(t), prop))
));

named!(typ(&str) -> Type, alt!(typ_bool |  typ_product | typ_function | typ_refinement | typ_one | typ_u8));

fn identifier_chars(input: &str) -> IResult<&str, &str> {
    for (i, c) in input.chars().enumerate() {
        if !(c.is_ascii_alphanumeric() || c == '\'' || c == '_' || c == '-') {
            let (ident, input) = input.split_at(i);
            return Ok((input, ident));
        }
    }
    let (ident, input) = input.split_at(input.len());
    Ok((input, ident))
}

fn identifier(input: &str) -> IResult<&str, Identifier> {
    if let Some(c) = input.chars().nth(0) {
        if c.is_ascii_alphabetic() {
            let (input, ident) = identifier_chars(input)?;
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
    char!('(') >> ws0 >> tag!(":>") >> ws1 >>
    left: typ >> ws1 >>
    right: typ >> ws0 >> char!(')') >>
    (Proposition::Supertype(Box::new(left), Box::new(right)))
));

named!(proposition_call(&str) -> Proposition, do_parse!(
    char!('(') >> ws0 >>
    pred: predicate >> ws1 >>
    args: separated_list0!(ws1, complete!(expression)) >> char!(')') >>
    (Proposition::Call(pred, args))
));

named!(proposition_and(&str) -> Proposition, do_parse!(
    char!('(') >> ws0 >> tag!("and") >> ws1 >>
    left: proposition >> ws1 >>
    right: proposition >> ws0 >> char!(')') >>
    (Proposition::Implies(
        Box::new(Proposition::Implies(
            Box::new(left),
            Box::new(Proposition::Implies(
                Box::new(right),
                Box::new(Proposition::False),
            )),
        )),
        Box::new(Proposition::False),
    ))
));

named!(proposition_or(&str) -> Proposition, do_parse!(
    char!('(') >> ws0 >> tag!("or") >> ws1 >>
    left: proposition >> ws1 >>
    right: proposition >> ws0 >> char!(')') >>
    (Proposition::Implies(
        Box::new(Proposition::Implies(
            Box::new(left),
            Box::new(Proposition::False),
        )),
        Box::new(right),
    ))
));

named!(proposition_not(&str) -> Proposition, do_parse!(
    char!('(') >> ws0 >> tag!("not") >> ws1 >>
    arg: proposition >> ws0 >> char!(')') >>
    (Proposition::Implies(
        Box::new(arg),
        Box::new(Proposition::False),
    ))
));

named!(proposition(&str) -> Proposition, alt!(
    proposition_false |
    proposition_implies |
    proposition_forall |
    proposition_equal |
    proposition_subtype |
    proposition_call |
    proposition_and |
    proposition_or |
    proposition_not
));

named!(predicate(&str) -> Predicate, alt!(
    map!(tag!("bool"), |_| Predicate::Prop) |
    map!(tag!("<="), |_| Predicate::LessThanEq) |
    map!(tag!(">="), |_| Predicate::GreaterThanEq) |
    map!(tag!("<"), |_| Predicate::LessThan) |
    map!(tag!(">"), |_| Predicate::GreaterThan)
));

named!(parse_u8(&str) -> u8, map_res!(
    digit1,
    |s: &str| s.parse::<u8>()
));

named!(constant(&str) -> Constant, alt!(
    map!(tag!("true"), |_| Constant::True) |
    map!(tag!("false"), |_| Constant::False) |
    map!(tag!("and"), |_| Constant::And) |
    map!(tag!("or"), |_| Constant::Or) |
    map!(tag!("=>"), |_| Constant::Implies) |
    map!(tag!("<=>"), |_| Constant::DblImplies) |
    map!(tag!("not"), |_| Constant::Not) |
    map!(parse_u8, |v| Constant::U8(v)) |
    map!(tag!("succ"), |_| Constant::Succ) |
    map!(tag!("pred"), |_| Constant::Pred) |
    map!(tag!("+"), |_| Constant::Add) |
    map!(tag!("-"), |_| Constant::Sub) |
    map!(tag!("<"), |_| Constant::LessThan) |
    map!(tag!("<="), |_| Constant::LessThanEq) |
    map!(tag!(">"), |_| Constant::GreaterThan) |
    map!(tag!(">="), |_| Constant::GreaterThanEq)
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

named!(parameter(&str) -> (Identifier, Type), do_parse!(
    id: identifier >> ws0 >> char!(':') >> ws0 >>
    t: typ >>
    ((id, t))
));

named!(parameter_list(&str) -> Vec<(Identifier, Type)>, separated_list1!(
    tuple!(ws0, char!(','), ws0),
    parameter
));

named!(expression_abstraction(&str) -> Expression, do_parse!(
    char!('(') >> ws0 >> tag!("fn") >> ws1 >>
    params: parameter_list >> ws1 >>
    body: expression >> ws0 >> char!(')') >>
    ({
        let mut expr = body;
        for (id, typ) in params.into_iter().rev() {
            expr = Expression::Abstraction(id, Box::new(typ), Box::new(expr));
        }
        expr
    })
));

named!(expression_application(&str) -> Expression, do_parse!(
    char!('(') >> ws0 >>
    f: expression >> ws1 >>
    args: separated_list1!(ws1, expression) >> ws0 >> char!(')') >>
    ({
        let mut expr = f;
        for arg in args.into_iter() {
            expr = Expression::Application(Box::new(expr), Box::new(arg));
        }
        expr
    })
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
    id: identifier >> ws0 >> char!(':') >> ws0 >>
    t: typ >> ws0 >> char!('=') >> ws0 >>
    e: expression >>
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

named!(expression_u8rec(&str) -> Expression, do_parse!(
    char!('(') >> ws0 >> tag!("u8rec") >> ws1 >>
    init: expression >> ws1 >>
    iter: expression >> ws1 >>
    count: expression >> ws0 >> char!(')') >>
    (Expression::U8Rec(Box::new(init), Box::new(iter), Box::new(count)))
));

named!(expression_ite(&str) -> Expression, do_parse!(
    char!('(') >> ws0 >> tag!("ite") >> ws1 >>
    cond: expression >> ws1 >>
    if_branch: expression >> ws1 >>
    else_branch: expression >> ws0 >> char!(')') >>
    (Expression::Ite(Box::new(cond), Box::new(if_branch), Box::new(else_branch)))
));

named!(expression(&str) -> Expression, alt!(
    expression_ite |
    expression_u8rec |
    expression_let |
    expression_abstraction |
    expression_first |
    expression_second |
    expression_call |
    expression_ast |
    expression_application |
    expression_variable |
    expression_tuple
));

named!(program(&str) -> Expression, do_parse!(
    ws0 >>
    e: expression >> ws0 >>
    (e)
));

pub fn parse(input: &str) -> Result<Expression, String> {
    let (remaining, ast) = program(input).map_err(|err| match err {
        Err::Incomplete(needed) => format!("Parsing error: Needed {:?}", needed),
        Err::Error(err) | Err::Failure(err) => format!(
            "Parsing error: input: {}, error code: {:?}",
            err.input, err.code
        ),
    })?;
    if remaining.len() == 0 {
        Ok(ast)
    } else {
        Err("Parsing error, reached EOF too early".to_string())
    }
}
