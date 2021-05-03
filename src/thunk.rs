use crate::semantic::{
    Expression, ExpressionKind, Identifier, IdentifierGenerator, Type, UnrefinedType,
};
use im::HashMap as ImHashMap;

struct Thunker<'a> {
    ident_gen: &'a mut IdentifierGenerator,
}

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
    UnrefinedType::Function(Box::new((UnrefinedType::One, thunk_function_types(typ))))
}

impl<'a> Thunker<'a> {
    fn next_id(&mut self) -> Identifier {
        self.ident_gen.next()
    }

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
                    typ: UnrefinedType::Function(Box::new((UnrefinedType::One, arg.typ.clone()))),
                    kind: ExpressionKind::Abstraction(self.next_id(), Type::One, Box::new(arg)),
                };
                ExpressionKind::Application(Box::new((fun, thunk)))
            }
            ExpressionKind::Abstraction(id, typ, body) => {
                let body = self.thunk_expression(*body);
                let typ = thunk_type(typ.unrefine()).refine(self.ident_gen);
                ExpressionKind::Abstraction(id, typ, Box::new(body))
            }
            ExpressionKind::Ast => ExpressionKind::Ast,
            ExpressionKind::Call(constant, args) => ExpressionKind::Call(
                constant,
                args.into_iter()
                    .map(|arg| self.thunk_expression(arg))
                    .collect(),
            ),
            ExpressionKind::First(arg) => {
                ExpressionKind::First(Box::new(self.thunk_expression(*arg)))
            }
            ExpressionKind::Second(arg) => {
                ExpressionKind::Second(Box::new(self.thunk_expression(*arg)))
            }
            ExpressionKind::Tuple(contents) => ExpressionKind::Tuple(Box::new((
                self.thunk_expression(contents.0),
                self.thunk_expression(contents.1),
            ))),
            ExpressionKind::U8Rec(id, typ, contents) => ExpressionKind::U8Rec(
                id,
                thunk_function_types(typ.unrefine()).refine(self.ident_gen),
                Box::new((
                    self.thunk_expression(contents.0),
                    self.thunk_expression(contents.1),
                    self.thunk_expression(contents.2),
                )),
            ),
        };
        let typ = thunk_function_types(expr.typ);
        Expression { kind, typ, env }
    }
}

pub fn to_thunk(source: Expression, ident_gen: &mut IdentifierGenerator) -> Expression {
    println!("Pre thunk:\n{}", source);
    let mut thunker = Thunker { ident_gen };
    thunker.thunk_expression(source)
}
