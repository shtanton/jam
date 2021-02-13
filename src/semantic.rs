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
    type_gen: TypeGenerator,
}

impl Analyzer {
    /// Create a new Identifier for the symbol and with the Type given and return it
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

    /// Create a new Type with the given TypeKind and return it
    fn insert_type(&mut self, kind: TypeKind) -> Type {
        let typ = self.type_gen.next();
        let type_data = TypeData {
            kind,
            id: typ,
        };
        self.types.insert(typ, type_data);
        typ
    }

    /// Get TypeData of a Type
    fn type_data(&self, typ: Type) -> Option<&TypeData> {
        self.types.get(&typ)
    }

    /// Return true if the first argument is a subtype of the second
    fn is_subtype(&self, expected_subtype: Type, expected_supertype: Type) -> bool {
    }

    /// Check types passed to a constant call and return the returned type of the call
    fn constant_call(&mut self, constant: Constant, args: Vec<Type>, env: Environment) -> Result<Type, ()> {
    }

    /// Label a Type
    fn typ(&mut self, typ: SType, env: Environment) -> Result<Type, ()> {
    }

    /// Label an Expression
    fn expression(&mut self, expr: SExpression, env: Environment) -> Result<Expression, ()> {
        match expr {
            SExpression::Abstraction(sym, typ, expr) => {
                let param_type = self.typ(*typ, env)?;
                let ident = self.insert_symbol(&sym, param_type);
                let body = self.expression(*expr, env.update(sym.clone(), ident))?;
                let ret_type = body.typ;
                let type_kind = TypeKind::Function(ident, param_type, ret_type);
                let typ = self.insert_type(type_kind);
                Ok(Expression {
                    kind: ExpressionKind::Abstraction(ident, param_type, Box::new(body)),
                    typ: typ,
                })
            }
            SExpression::Application(fun, arg) => {
                let labelled_fun = self.expression(*fun, env)?;
                let labelled_arg = self.expression(*arg, env)?;
                let fun_type_data = self.type_data(labelled_fun.typ).ok_or(())?;
                if let TypeKind::Function(ident, expected_arg_type, ret_type) = fun_type_data.kind {
                    if !self.is_subtype(labelled_arg.typ, expected_arg_type) {
                        Err(())
                    } else {
                        Ok(Expression {
                            kind: ExpressionKind::Application(Box::new(labelled_fun), Box::new(labelled_arg)),
                            typ: ret_type,
                        })
                    }
                } else {
                    Err(())
                }
            }
            SExpression::Call(constant, args) => {
                let args = args.into_iter().map(|e| self.expression(e, env)).collect::<Result<Vec<_>, ()>>()?;
                let ret_type = self.constant_call(constant, args.iter().map(|e| e.typ).collect::<Vec<_>>(), env)?;
                Ok(Expression {
                    kind: ExpressionKind::Call(constant, args),
                    typ: ret_type,
                })
            }
            SExpression::Tuple(first, second) => {
                let first = self.expression(*first, env)?;
                let second = self.expression(*second, env)?;
                Ok(Expression {
                    kind: ExpressionKind::Tuple(Box::new(first), Box::new(second)),
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
