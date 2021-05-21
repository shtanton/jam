struct Z3Translater<'a> {
  fn_map: HashMap<(UnrefinedType, UnrefinedType), FnData<'a>>,
  pair_map: HashMap<(UnrefinedType, UnrefinedType), PairData<'a>>,
  ctx: &'a Context,
  one: ZSort<'a>,
  ast: FuncDecl<'a>,
  bool: ZSort<'a>,
  u8: ZSort<'a>,
  variables: HashMap<Identifier, FuncDecl<'a>>,
}

impl<'a> Z3Translater<'a> {
  fn translate_expression(
    &mut self,
    expr: Expression,
  ) -> Result<Dynamic<'a>, ()> {
    Ok(match expr {
      Expression::Call(fun, args) => match fun {
        Function::Apply(param_type, body_type) => {
          let zargs = self.translate_expressions(args)?;
          let zargs_ref: Vec<_> = zargs.iter().collect();
          let FnData { apply, .. } = self
            .fn_map
            .get(&(param_type, body_type))
            .as_ref()
            .ok_or(())?;
          apply.apply(zargs_ref.as_slice())
        }
        Function::First(first_type, second_type) => {
          let zargs = self.translate_expressions(args)?;
          let zargs_ref: Vec<_> = zargs.iter().collect();
          let PairData { first, .. } = self
            .pair_map
            .get(&(first_type, second_type))
            .as_ref()
            .ok_or(())?;
          first.apply(zargs_ref.as_slice())
        }
        Function::Not => {
          let zargs: Vec<_> =
            self.translate_expressions_to_bools(args)?;
          Dynamic::from_ast(&zargs[0].not())
        }
      },
    })
  }

  fn run_smt(mut self, smt: Smt) -> Result<SmtResult, ()> {
    let Smt {
      declarations,
      assertions,
      types,
    } = smt;
    for typ in types.into_iter() {
      match &typ {
        UnrefinedType::One
        | UnrefinedType::Bool
        | UnrefinedType::U8 => {}
        UnrefinedType::Function(contents) => {
          let (param_type, body_type) = &**contents;
          let symbol = Symbol::String(format!(
            "({}->{})",
            param_type, body_type
          ));
          let zsort = ZSort::uninterpreted(self.ctx, symbol);
          let param_zsort = self.get_zsort(param_type).unwrap();
          let body_zsort = self.get_zsort(body_type).unwrap();
          let apply = FuncDecl::new(
            self.ctx,
            format!("apply_{}->{}", param_type, body_type),
            &[&zsort, param_zsort],
            body_zsort,
          );
          self
            .fn_map
            .insert(*contents.clone(), FnData { zsort, apply });
        }
        UnrefinedType::Product(contents) => {
          let (first, second) = &**contents;
          let first_zsort = self.get_zsort(first).unwrap();
          let second_zsort = self.get_zsort(second).unwrap();
          let DatatypeSort {
            sort: zsort,
            mut variants,
            ..
          } = DatatypeBuilder::new(self.ctx, "Pair")
            .variant(
              "pair",
              vec![
                ("first", DatatypeAccessor::Sort(first_zsort)),
                ("second", DatatypeAccessor::Sort(second_zsort)),
              ],
            )
            .finish();
          let DatatypeVariant {
            constructor: pair_fn,
            mut accessors,
            ..
          } = variants.pop().unwrap();
          let second_fn = accessors.pop().unwrap();
          let first_fn = accessors.pop().unwrap();
          self.pair_map.insert(
            *contents.clone(),
            PairData {
              zsort,
              pair: pair_fn,
              first: first_fn,
              second: second_fn,
            },
          );
        }
      }
    }
    for declaration in declarations.into_iter() {
      self.define_var(declaration.id, declaration.typ)?;
    }
    let solver = Solver::new(self.ctx);
    for assertion in assertions.into_iter() {
      if let Some(bool_ast) =
        self.translate_expression(assertion)?.as_bool()
      {
        solver.assert(&bool_ast);
      } else {
        return Ok(SmtResult::Fail);
      }
    }
    let res = solver.check();
    Ok(match res {
      SatResult::Sat => {
        let model = solver.get_model().unwrap();
        println!("Model: {}", model);
        SmtResult::Fail
      }
      SatResult::Unknown => SmtResult::Unknown,
      SatResult::Unsat => SmtResult::Pass,
    })
  }
}

pub fn run_smt(smt: Smt) -> Result<SmtResult, ()> {
  let cfg = Config::new();
  let ctx = Context::new(&cfg);
  let (one, mut ast_vec, _) = ZSort::enumeration(
    &ctx,
    Symbol::String(String::from("1")),
    &[Symbol::String(String::from("*"))],
  );
  let bool_zsort = ZSort::bool(&ctx);
  let u8_zsort = ZSort::bitvector(&ctx, 8);
  let translater = Z3Translater {
    fn_map: HashMap::new(),
    pair_map: HashMap::new(),
    ctx: &ctx,
    one,
    ast: ast_vec.pop().unwrap(),
    bool: bool_zsort,
    u8: u8_zsort,
    variables: HashMap::new(),
  };
  translater.run_smt(smt)
}
