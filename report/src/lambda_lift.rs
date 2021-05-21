impl<'a> LambdaLifter<'a> {
  fn lift_expression(&mut self, expr: SExpression) -> Expression {
    match expr.kind {
      SExpressionKind::U8Rec(id, iter_type, contents) => {
        let environment = iter_type
          .env()
          .clone()
          .without(&id)
          .into_iter()
          .collect::<Vec<_>>();
        let iter_type = self.lift_type(iter_type);
        let mut typ =
          Type::Function(id, Box::new((Type::U8, iter_type)));
        for (param_id, param_type) in environment.iter().rev() {
          typ = Type::Function(
            *param_id,
            Box::new((self.refine_type(param_type), typ)),
          );
        }
        let count = self.lift_expression(contents.2);
        let var = self.next_id();
        let mut expr = Expression::Variable(var, typ.unrefine());
        for (param_id, param_type) in environment.into_iter() {
          expr = Expression::Application(Box::new((
            expr,
            Expression::Variable(param_id, param_type),
          )));
        }
        expr = Expression::Application(Box::new((expr, count)));
        self.context.push((var, typ));
        expr
      }
      SExpressionKind::Abstraction(param, param_type, body) => {
        let environment: Vec<_> = expr.env.into_iter().collect();
        let new_fn = self.next_id();
        let refinement_id = self.next_id();
        let refined_body_type = self.refine_type(&body.typ);
        let mut typ = Type::Function(
          param,
          Box::new((
            self.lift_type(param_type),
            Type::Refinement(
              refinement_id,
              Box::new(refined_body_type.clone()),
              Proposition::Equal(Box::new((
                refined_body_type,
                Expression::Variable(refinement_id, body.typ.clone()),
                self.lift_expression(*body),
              ))),
            ),
          )),
        );
        for (param_id, param_type) in environment.iter().rev() {
          typ = Type::Function(
            *param_id,
            Box::new((self.refine_type(param_type), typ)),
          );
        }
        let mut expr = Expression::Variable(new_fn, typ.unrefine());
        for (param_id, param_type) in environment.into_iter() {
          expr = Expression::Application(Box::new((
            expr,
            Expression::Variable(param_id, param_type),
          )));
        }
        self.context.push((new_fn, typ));
        expr
      }
    }
  }

  fn lift(&mut self, judgement: SJudgement) -> (Expression, Type) {
    for defn in judgement.context.into_iter() {
      let new_defn = self.lift_defn(defn);
      self.context.push(new_defn);
    }
    let expression = self.lift_expression(judgement.expression);
    let typ = self.lift_type(judgement.typ);
    (expression, typ)
  }
}

pub fn lift(
  judgement: SJudgement,
  ident_gen: &mut IdentifierGenerator,
) -> Judgement {
  let mut lifter = LambdaLifter {
    ident_gen,
    context: Vec::new(),
  };
  let (expression, typ) = lifter.lift(judgement);
  Judgement {
    context: lifter.context,
    expression,
    typ,
  }
}
