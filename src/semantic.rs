use std::collections::HashMap;
use im::HashMap as ImHashMap;
use crate::syntax::{
    Predicate,
    Constant,
    Expression as SExpression,
    Type as SType,
};

pub type Type = u32;
#[derive(Clone, Copy, Debug)]
pub struct TypeGenerator {
    next: Type,
}
impl TypeGenerator {
    fn next(&mut self) -> Type {
        let n = self.next;
        self.next += 1;
        n
    }
}
impl Default for TypeGenerator {
    fn default() -> TypeGenerator {
        TypeGenerator {next: 0}
    }
}

pub type Identifier = u32;
#[derive(Clone, Copy, Debug)]
pub struct IdentifierGenerator {
    next: Identifier,
}
impl IdentifierGenerator {
    fn next(&mut self) -> Identifier {
        let n = self.next;
        self.next += 1;
        n
    }
}
impl Default for IdentifierGenerator {
    fn default() -> IdentifierGenerator {
        IdentifierGenerator {next: 0}
    }
}

#[derive(Debug)]
pub enum Proposition {
    False,
    Implies(Box<Proposition>, Box<Proposition>),
    Forall(Identifier, Type, Box<Proposition>),
    Call(Predicate, Vec<Expression>),
    Equal(Type, Expression, Expression),
    Subtype(Type, Type),
}

#[derive(Debug)]
pub enum ExpressionKind {
    Variable(Identifier),
    Call(Constant, Vec<Expression>),
    Tuple(Box<Expression>, Box<Expression>),
    Abstraction(Identifier, Type, Box<Expression>),
    Application(Box<Expression>, Box<Expression>),
}

#[derive(Debug)]
pub struct Expression {
    kind: ExpressionKind,
    typ: Type,
}

pub struct Variable {
    typ: Type,
    id: Identifier,
    symbol: String,
}

pub type SymbolTable = HashMap<Identifier, Variable>;

pub struct TypeData {
    kind: TypeKind,
    id: Type,
}

pub enum TypeKind {
    Bool,
    Nat,
    Product(Identifier, Type, Type),
    Function(Identifier, Type, Type),
    Refinement(Identifier, Type, Proposition),
}

pub type TypeTable = HashMap<Type, TypeData>;

pub type Environment = ImHashMap<String, Identifier>;

#[derive(Default)]
struct Analyzer {
    symbols: SymbolTable,
    types: TypeTable,

    ident_gen: IdentifierGenerator,
    typ_gen: TypeGenerator,
}

impl Analyzer {
    fn insert_symbol(&mut self, symbol: &str, typ: Type) -> Identifier {
        let ident = self.ident_gen.next();
        let var = Variable {
            typ,
            id: ident,
            symbol: symbol.to_string(),
        };
        self.symbols.insert(ident, var);
        ident
    }

    fn insert_typ(&mut self, kind: TypeKind) -> Type {
        let typ = self.typ_gen.next();
        let typ_data = TypeData {
            kind,
            id: typ,
        };
        self.types.insert(typ, typ_data);
        typ
    }

    fn typ(&mut self, typ: SType, env: Environment) -> Result<Type, ()> {
    }

    fn expression(&mut self, expr: SExpression, env: Environment) -> Result<Expression, ()> {
        match expr {
            SExpression::Abstraction(sym, typ, expr) => {
                let param_typ = self.typ(*typ, env)?;
                let ident = self.insert_symbol(&sym, param_typ);
                let body = self.expression(*expr, env.update(sym.clone(), ident))?;
                let ret_typ = body.typ;
                let typ_kind = TypeKind::Function(ident, param_typ, ret_typ);
                let typ = self.insert_typ(typ_kind);
                Ok(Expression {
                    kind: ExpressionKind::Abstraction(ident, param_typ, Box::new(body)),
                    typ: typ,
                })
            }
        }
    }
}

pub fn label(ast: SExpression) -> Result<Expression, String> {
    let mut env = Environment::default();
    let mut analyzer = Analyzer::default();
    analyzer.expression(ast, env).map_err(|_| "semantic error".to_string())
}
