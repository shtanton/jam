named!(typ_refinement(&str) -> Type, do_parse!(
    id: identifier >> ws0 >> char!(':') >> ws0 >>
    t: typ >> ws0 >> char!('{') >> ws0 >>
    prop: proposition >> ws0 >> char!('}') >>
    (Type::Refinement(id, Box::new(t), prop))
));

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

named!(expression_variable(&str) -> Expression, map!(identifier, Expression::Variable));

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
