use crate::lambda_lift::Identifier;
use crate::remove_pairs::{Expression, Function, Proposition, Type};

pub struct Uncurryer {
    _next_id: u32,
}

impl Uncurryer {
    pub fn new(_next_id: u32) -> Uncurryer {
        Uncurryer { _next_id }
    }

    pub fn next_id(&mut self) -> Identifier {
        let id = self._next_id;
        self._next_id += 1;
        id
    }

    fn uncurry_function(&mut self, fun: Function) -> Result<Function, ()> {
        let Function {
            id,
            mut parameters,
            mut body,
        } = fun;
        let mut body_type = body.typ()?;
        while let Type::Function(fcontents) = body_type {
            let new_param = (self.next_id(), fcontents.0);
            parameters.push(new_param.clone());
            body = Expression::Application(Box::new((
                body,
                Expression::Variable(new_param.0, new_param.1),
            )));
            body_type = fcontents.1;
        }
        Ok(Function {
            id,
            parameters,
            body,
        })
    }

    pub fn uncurry(
        &mut self,
        prop: Proposition,
        fns: Vec<Function>,
    ) -> Result<(Proposition, Vec<Function>), ()> {
        let fns = fns
            .into_iter()
            .map(|fun| self.uncurry_function(fun))
            .collect::<Result<Vec<_>, ()>>()?;
        Ok((prop, fns))
    }
}
