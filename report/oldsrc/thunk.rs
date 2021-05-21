fn thunk_function_types(typ: UnrefinedType) -> UnrefinedType {
  match typ {
    UnrefinedType::One => UnrefinedType::One,
    UnrefinedType::Bool => UnrefinedType::Bool,
    UnrefinedType::U8 => UnrefinedType::U8,
    UnrefinedType::Product(contents) => UnrefinedType::Product(Box::new((
      thunk_function_types(contents.0),
      thunk_function_types(contents.1),
    ))),
    UnrefinedType::Function(contents) => UnrefinedType::Function(Box::new((
      thunk_type(contents.0),
      thunk_function_types(contents.1),
    ))),
  }
}

fn thunk_type(typ: UnrefinedType) -> UnrefinedType {
  UnrefinedType::Function(Box::new((
    UnrefinedType::One,
    thunk_function_types(typ),
  )))
}

impl<'a> Thunker<'a> {
  fn thunk_expression(&mut self, expr: Expression) -> Expression {
    let env: ImHashMap<Identifier, UnrefinedType> = expr
      .env
      .into_iter()
      .map(|(id, typ)| (id, thunk_type(typ)))
      .collect();
    let kind = match expr.kind {
      ExpressionKind::Variable(id) => ExpressionKind::Application(Box::new((
        Expression {
          kind: ExpressionKind::Variable(id),
          typ: thunk_type(expr.typ.clone()),
          env: env.clone(),
        },
        Expression {
          kind: ExpressionKind::Ast,
          typ: UnrefinedType::One,
          env: ImHashMap::new(),
        },
      ))),
      ExpressionKind::Application(contents) => {
        let (fun, arg) = *contents;
        let fun = self.thunk_expression(fun);
        let arg = self.thunk_expression(arg);
        let thunk = Expression {
          env: arg.env.clone(),
          typ: UnrefinedType::Function(Box::new((
            UnrefinedType::One,
            arg.typ.clone(),
          ))),
          kind: ExpressionKind::Abstraction(
            self.next_id(),
            Type::One,
            Box::new(arg),
          ),
        };
        ExpressionKind::Application(Box::new((fun, thunk)))
      }
    };
    let typ = thunk_function_types(expr.typ);
    Expression { kind, typ, env }
  }
}

pub fn to_thunk(
  source: Expression,
  ident_gen: &mut IdentifierGenerator,
) -> Expression {
  let mut thunker = Thunker { ident_gen };
  thunker.thunk_expression(source)
}
