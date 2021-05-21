impl<'a> ToSmt<'a> {
  fn simplify(
    &mut self,
    typ: Type,
  ) -> Result<(Identifier, UnrefinedType, Expression), ()> {
    Ok(match typ {
      Type::Refinement(id, supertype, prop) => {
        let prop = self.translate_proposition(prop)?;
        let (super_id, typ, mut superprop) =
          self.simplify(*supertype)?;
        superprop.substitute(&Expression::Variable(id), super_id);
        (
          id,
          typ,
          Expression::Call(Function::And, vec![prop, superprop]),
        )
      }
    })
  }

  fn translate_expression(
    &mut self,
    expr: LExpression,
  ) -> Result<Expression, ()> {
    Ok(match expr {
      LExpression::Application(contents) => {
        let (param_type, body_type) =
          if let UnrefinedType::Function(contents) =
            contents.0.unrefined_type()?
          {
            (contents.0, contents.1)
          } else {
            return Err(());
          };
        self.register_type(&param_type);
        self.register_type(&body_type);
        Expression::Call(
          Function::Apply(param_type, body_type),
          vec![
            self.translate_expression(contents.0)?,
            self.translate_expression(contents.1)?,
          ],
        )
      }
    })
  }

  fn translate_proposition(
    &mut self,
    prop: LProposition,
  ) -> Result<Expression, ()> {
    Ok(match prop {
      LProposition::Equal(contents) => {
        let left = contents.1;
        let right = contents.2;
        let left_type = left.unrefined_type()?;
        let right_type = right.unrefined_type()?;
        self.register_type(&left_type);
        self.register_type(&right_type);
        self.register_type(&contents.0.unrefine());
        match contents.0 {
          Type::Function(id, contents) => {
            let (type_id, typ, mut prop1) =
              self.simplify(contents.0)?;
            prop1.substitute(&Expression::Variable(id), type_id);
            let prop2 = self.translate_proposition(
              LProposition::Equal(Box::new((
                contents.1,
                LExpression::Application(Box::new((
                  left,
                  LExpression::Variable(id, typ.clone()),
                ))),
                LExpression::Application(Box::new((
                  right,
                  LExpression::Variable(id, typ.clone()),
                ))),
              ))),
            )?;
            Expression::Forall(
              id,
              typ,
              Box::new(Expression::Call(
                Function::Implies,
                vec![prop1, prop2],
              )),
            )
          }
        }
      }
    })
  }

  fn translate_judgement_to_smt(
    mut self,
    judgement: Judgement,
  ) -> Result<Smt, ()> {
    let Judgement {
      context,
      expression,
      typ,
    } = judgement;
    let mut declarations = Vec::new();
    let mut assertions = Vec::new();
    for defn in context.into_iter() {
      let (id, typ, mut prop) = self.simplify(defn.1)?;
      self.register_type(&typ);
      prop.substitute(&Expression::Variable(defn.0), id);
      declarations.push(Declaration { id: defn.0, typ });
      assertions.push(prop);
    }
    let (id, unrefined_type, mut prop) = self.simplify(typ)?;
    self.register_type(&unrefined_type);
    prop.substitute(&self.translate_expression(expression)?, id);
    assertions.push(Expression::Call(Function::Not, vec![prop]));
    Ok(Smt {
      declarations,
      assertions,
      types: self.types,
    })
  }
}

pub fn translate_judgement_to_smt(
  judgement: Judgement,
  ident_gen: &mut IdentifierGenerator,
) -> Result<Smt, ()> {
  let translater = ToSmt {
    ident_gen,
    types: Vec::new(),
  };
  translater.translate_judgement_to_smt(judgement)
}
