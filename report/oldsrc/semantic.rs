#[derive(Debug)]
pub struct Judgement {
  pub context: Vec<(Identifier, Type)>,
  pub expression: Expression,
  pub typ: Type,
}

fn add_applications_to_vec(
  expr: &Expression,
  mut context: Context,
  applications: &mut Vec<(Context, Application)>,
) {
  match &expr.kind {
    ExpressionKind::Ast => {}
    ExpressionKind::Variable(_) => {}
    ExpressionKind::Abstraction(id, typ, body) => {
      context.push_back((*id, typ.clone()));
      add_applications_to_vec(&body, context, applications);
    }
    ExpressionKind::Application(contents) => {
      add_applications_to_vec(&contents.0, context.clone(), applications);
      add_applications_to_vec(&contents.1, context.clone(), applications);
      applications.push((
        context,
        Application::UserFunction(contents.0.clone(), contents.1.clone()),
      ));
    }
    ExpressionKind::Call(_, args) => {
      args.into_iter().for_each(|arg| {
        add_applications_to_vec(&arg, context.clone(), applications);
      });
    }
    ExpressionKind::First(arg) => {
      add_applications_to_vec(&arg, context, applications);
    }
    ExpressionKind::Second(arg) => {
      add_applications_to_vec(&arg, context, applications);
    }
    ExpressionKind::Tuple(contents) => {
      add_applications_to_vec(&contents.0, context.clone(), applications);
      add_applications_to_vec(&contents.1, context, applications);
    }
    ExpressionKind::U8Rec(_, _, contents) => {
      add_applications_to_vec(&contents.0, context.clone(), applications);
      add_applications_to_vec(&contents.1, context.clone(), applications);
      add_applications_to_vec(&contents.2, context.clone(), applications);
      applications.push((
        context,
        Application::U8Rec(
          contents.0.clone(),
          contents.1.clone(),
          contents.2.clone(),
        ),
      ));
    }
    ExpressionKind::Ite(contents) => {
      add_applications_to_vec(&contents.0, context.clone(), applications);
      add_applications_to_vec(&contents.1, context, applications);
    }
  };
}

fn find_applications(expr: &Expression) -> Vec<(Context, Application)> {
  let mut applications = Vec::new();
  add_applications_to_vec(expr, ImVec::new(), &mut applications);
  applications
}

/// Assuming variable expr_id of type typ is operated on with args, what is the param type?
fn arg_type_of_type(typ: &Type, mut args: Vec<FnProcess>) -> Result<Type, ()> {
  Ok(match typ {
    Type::Refinement(_, typ, _) => arg_type_of_type(typ, args)?,
    Type::Function(id, contents) => match args.pop() {
      Some(FnProcess::Arg(arg)) => {
        let mut new_type = contents.1.clone();
        new_type.substitute(&arg.kind, &arg.env, *id);
        arg_type_of_type(&new_type, args)?
      }
      None => contents.0.clone(),
      Some(FnProcess::First) | Some(FnProcess::Second(_)) => {
        return Err(());
      }
    },
    Type::Product(id, contents) => match args.pop() {
      Some(FnProcess::First) => arg_type_of_type(&contents.0, args)?,
      Some(FnProcess::Second(arg)) => {
        let mut typ = arg_type_of_type(&contents.1, args)?;
        let env = arg.env.clone();
        typ.substitute(&ExpressionKind::First(Box::new(arg)), &env, *id);
        typ
      }
      Some(FnProcess::Arg(_)) | None => {
        return Err(());
      }
    },
    Type::Bool | Type::One | Type::U8 => return Err(()),
  })
}

enum FnProcess {
  First,
  Second(Expression),
  Arg(Expression),
}

fn arg_type(
  expr: &Expression,
  mut context: HashMap<Identifier, Type>,
  mut args: Vec<FnProcess>,
) -> Result<Type, ()> {
  Ok(match &expr.kind {
    ExpressionKind::Abstraction(id, typ, body) => match args.pop() {
      Some(FnProcess::Arg(arg)) => {
        let mut body = body.clone();
        body.substitute(&arg.kind, &arg.env, *id);
        arg_type(&body, context, args)?
      }
      Some(_) => {
        return Err(());
      }
      None => typ.clone(),
    },
    ExpressionKind::Application(contents) => {
      args.push(FnProcess::Arg(contents.1.clone()));
      arg_type(&contents.0, context, args)?
    }
    ExpressionKind::Variable(id) => {
      let var_type = context.get(id).ok_or(())?;
      arg_type_of_type(var_type, args.into())?
    }
    ExpressionKind::U8Rec(id, typ, contents) => {
      let mut typ = typ.clone();
      typ.substitute(&contents.2.kind, &contents.2.env, *id);
      let res = arg_type_of_type(&typ, args)?;
      context.insert(*id, typ);
      res
    }
    ExpressionKind::First(arg) => {
      args.push(FnProcess::First);
      arg_type(&arg, context, args)?
    }
    ExpressionKind::Second(arg) => {
      args.push(FnProcess::Second(*arg.clone()));
      arg_type(&arg, context, args)?
    }
    ExpressionKind::Tuple(contents) => match args.pop() {
      Some(FnProcess::First) => arg_type(&contents.0, context, args)?,
      Some(FnProcess::Second(_)) => arg_type(&contents.1, context, args)?,
      None | Some(FnProcess::Arg(_)) => {
        return Err(());
      }
    },
    ExpressionKind::Ite(contents) => arg_type(&contents.1, context, args)?,
    ExpressionKind::Ast | ExpressionKind::Call(_, _) => return Err(()),
  })
}

impl Analyzer {
  /// Label an Expression
  fn label_expression(
    &mut self,
    expr: &SExpression,
    mut env: ImHashMap<String, Identifier>,
  ) -> Result<Expression, ()> {
    Ok(match expr {
      SExpression::Abstraction(param_symbol, param_type, expr) => {
        let param_type = self.label_type(param_type, env.clone())?;
        let unrefined_arg_type = param_type.unrefine();
        let id = self.ident_gen.next();
        env.insert(param_symbol.clone(), id);
        self.symbol_table.insert(
          id,
          Variable {
            id,
            symbol: param_symbol.clone(),
            typ: param_type.clone(),
          },
        );
        let body = self.label_expression(expr, env)?;
        let body_typ = body.typ.clone();
        Expression {
          env: body.env.without(&id).union(param_type.env()),
          kind: ExpressionKind::Abstraction(id, param_type, Box::new(body)),
          typ: UnrefinedType::Function(Box::new((
            unrefined_arg_type,
            body_typ,
          ))),
        }
      }
      SExpression::Application(fun, arg) => {
        let labelled_fun = self.label_expression(fun, env.clone())?;
        let labelled_arg = self.label_expression(arg, env)?;
        if let UnrefinedType::Function(type_contents) = &labelled_fun.typ {
          let typ = type_contents.1.clone();
          Expression {
            env: labelled_fun.env.clone().union(labelled_arg.env.clone()),
            kind: ExpressionKind::Application(Box::new((
              labelled_fun,
              labelled_arg,
            ))),
            typ: typ,
          }
        } else {
          return Err(());
        }
      }
      SExpression::U8Rec(init, iter, count) => {
        let count = self.label_expression(count, env.clone())?;
        if let UnrefinedType::U8 = &count.typ {
          let init = self.label_expression(init, env.clone())?;
          let iter = self.label_expression(iter, env.clone())?;
          let n_id = self.ident_gen.next();
          let n = Expression {
            kind: ExpressionKind::Variable(n_id),
            env: ImHashMap::new().update(n_id, UnrefinedType::U8),
            typ: UnrefinedType::U8,
          };
          let typ = arg_type(
            &iter,
            self
              .symbol_table
              .clone()
              .into_iter()
              .map(|(id, var)| (id, var.typ))
              .collect(),
            vec![FnProcess::Arg(n)],
          )?;
          Expression {
            env: init
              .env
              .clone()
              .union(iter.env.clone())
              .union(count.env.clone()),
            typ: init.typ.clone(),
            kind: ExpressionKind::U8Rec(
              n_id,
              typ,
              Box::new((init, iter, count)),
            ),
          }
        } else {
          return Err(());
        }
      }
      SExpression::Variable(symbol) => {
        let id = env.get(symbol).ok_or(())?;
        let variable = self.symbol_table.get(id).ok_or(())?;
        let mut var_env = ImHashMap::new();
        var_env.insert(*id, variable.typ.unrefine());
        Expression {
          kind: ExpressionKind::Variable(*id),
          typ: variable.typ.unrefine(),
          env: var_env,
        }
      }
    })
  }
}

pub fn check(ast: SExpression) -> Result<Expression, String> {
  let env = ImHashMap::default();
  let mut analyzer = Analyzer::default();
  let ast = analyzer
    .label_expression(&ast, env)
    .map_err(|_| "labelling error".to_string())?;
  if ast.typ != UnrefinedType::U8 {
    return Err("labelling error".to_string());
  }
  let applications = find_applications(&ast);
  let judgements = applications
    .into_iter()
    .flat_map(|(context, application)| match application {
      Application::UserFunction(fun, arg) => {
        if let Ok(typ) =
          arg_type(&fun, context.clone().into_iter().collect(), Vec::new())
        {
          vec![Ok(Judgement {
            context: context.into_iter().collect(),
            expression: arg,
            typ,
          })]
        } else {
          vec![Err(())]
        }
      }
      Application::U8Rec(init, iter, _) => {
        let n = analyzer.ident_gen.next();
        let var_n = Expression {
          kind: ExpressionKind::Variable(n),
          env: ImHashMap::new().update(n, UnrefinedType::U8),
          typ: UnrefinedType::U8,
        };
        if let Ok(type_n) = arg_type(
          &iter,
          context.clone().into_iter().collect(),
          vec![FnProcess::Arg(var_n.clone())],
        ) {
          let not_255 = {
            let id = analyzer.ident_gen.next();
            Type::Refinement(
              id,
              Box::new(Type::U8),
              Proposition::Implies(Box::new((
                Proposition::Equal(Box::new((
                  Type::U8,
                  Expression {
                    kind: ExpressionKind::Variable(id),
                    typ: UnrefinedType::U8,
                    env: im_hashmap! {id => UnrefinedType::U8},
                  },
                  Expression {
                    kind: ExpressionKind::Call(Constant::U8(255), vec![]),
                    typ: UnrefinedType::U8,
                    env: ImHashMap::new(),
                  },
                ))),
                Proposition::False,
              ))),
            )
          };
          let mut type_succ_n = type_n.clone();
          type_succ_n.substitute(
            &ExpressionKind::Call(Constant::Succ, vec![var_n.clone()]),
            &var_n.env,
            n,
          );
          let mut type_zero = type_n.clone();
          type_zero.substitute(
            &ExpressionKind::Call(Constant::U8(0), Vec::new()),
            &ImHashMap::new(),
            n,
          );
          vec![
            Ok(Judgement {
              context: context.clone().into_iter().collect(),
              expression: init,
              typ: type_zero,
            }),
            Ok(Judgement {
              context: context.into_iter().collect(),
              expression: iter,
              typ: Type::Function(
                n,
                Box::new((
                  not_255,
                  Type::Function(
                    analyzer.ident_gen.next(),
                    Box::new((type_n, type_succ_n)),
                  ),
                )),
              ),
            }),
          ]
        } else {
          vec![Err(())]
        }
      }
    })
    .collect::<Result<Vec<_>, ()>>()
    .map_err(|_| "error generating typing judgements".to_string())?;
  let judgements = judgements
    .into_iter()
    .map(|judgement| lift(judgement, &mut analyzer.ident_gen))
    .collect::<Vec<_>>();
  let smt_programs = judgements
    .into_iter()
    .map(|judgement| {
      translate_judgement_to_smt(judgement, &mut analyzer.ident_gen)
    })
    .collect::<Result<Vec<_>, ()>>()
    .map_err(|_| "error generating smt program".to_string())?;
  for (i, smt) in smt_programs.into_iter().enumerate() {
    println!("Program {}:", i);
    match run_smt(smt).map_err(|_| "error running SMT solver".to_string())? {
      SmtResult::Pass => {
        println!("PASS");
      }
      _ => {
        println!("FAIL");
        return Err("Type error".to_string());
      }
    }
  }
  Ok(to_thunk(ast, &mut analyzer.ident_gen))
}
