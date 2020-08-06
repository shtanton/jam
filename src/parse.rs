use std::iter::Peekable;

use im::HashMap;

use crate::lex::Token;
use crate::stdlib::I32_TYPE_ID;

#[derive(Debug)]
pub enum ExprKind {
    Identifier(u64),
    IntegerLiteral(i64),
    FunctionCall {
        function: u64,
        params: Vec<Expr>,
    },
    Let {
        defs: Vec<(u64, Expr)>,
        body: Box<Expr>,
    },
    Fn {
        params: Vec<u64>,
        body: Box<Expr>,
    },
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub typ: Type,
}

#[derive(Clone, Debug)]
pub enum Variable {
    Value { id: u64, typ: Type },
    Type(Type),
}

impl Variable {
    pub fn typ(&self) -> Result<&Type, String> {
        if let Variable::Type(typ) = self {
            Ok(typ)
        } else {
            Err("Variable is not a type".to_string())
        }
    }

    pub fn id(&self) -> u64 {
        match self {
            Variable::Value { id, .. } => *id,
            Variable::Type(typ) => typ.id(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Type {
    Function {
        id: u64,
        args: Vec<Type>,
        ret: Box<Type>,
    },
    Other(u64),
}

impl Type {
    /// True if the type is an integer type
    pub fn is_integer(&self) -> bool {
        if let Type::Other(id) = self {
            *id == I32_TYPE_ID
        } else {
            false
        }
    }

    /// True if typ is a 'subtype' of self, i.e. typ can be used in place of self
    pub fn accepts(&self, typ: &Type) -> bool {
        match (self, typ) {
            (
                Type::Function {
                    args: self_args,
                    ret: self_ret,
                    ..
                },
                Type::Function {
                    args: typ_args,
                    ret: typ_ret,
                    ..
                },
            ) => {
                self_ret.accepts(typ_ret)
                    && self_args.len() == typ_args.len()
                    && self_args
                        .iter()
                        .zip(typ_args.iter())
                        .fold(true, |acc, (self_arg, typ_arg)| {
                            acc && typ_arg.accepts(self_arg)
                        })
            }
            (Type::Other(self_id), Type::Other(typ_id)) => self_id == typ_id,
            _ => false,
        }
    }

    /// The id of the type, globally unique
    pub fn id(&self) -> u64 {
        match self {
            Type::Function { id, .. } => *id,
            Type::Other(id) => *id,
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct Env {
    pub variables: HashMap<String, Variable>,
}

impl Env {
    pub fn get(&self, name: &str) -> Result<&Variable, String> {
        self.variables
            .get(name)
            .ok_or(format!("Variable {} not found", name))
    }
}

pub struct Parser {
    next_variable_id: u64,
}

impl Parser {
    /// Each time this is called in a parser it generates a new unique id
    fn get_variable_id(&mut self) -> u64 {
        let id = self.next_variable_id;
        self.next_variable_id += 1;
        id
    }

    /// Parse a function definition, starting immediately after the fn keyword and ending after the )
    fn parse_fn(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = Token>>,
        typ: &Type,
        env: &Env,
    ) -> Result<Expr, String> {
        let (arg_types, return_type) = if let Type::Function { args, ret, .. } = typ {
            (args, ret.as_ref())
        } else {
            return Err("Expected some other type, found function".to_string());
        };
        if tokens.next().ok_or("Expected [ found EOF")? != Token::OpenSquare {
            return Err("Expected [ found something else".to_string());
        }
        let mut next_env = env.clone();
        let mut args = Vec::new();
        let mut arg_types_iter = arg_types.iter();
        while *tokens.peek().ok_or("Expected ] found EOF")? != Token::CloseSquare {
            match tokens.next() {
                None => {
                    return Err("Expected ( found EOF".to_string());
                }
                Some(Token::OpenBracket) => {}
                Some(token) => {
                    return Err(format!("Expected ( found {:?}", token));
                }
            }
            let identifier = if let Some(Token::Identifier(name)) = tokens.next() {
                name
            } else {
                return Err("Expected parameter identifier found something else".to_string());
            };
            let id = self.get_variable_id();
            let typ = self.parse_type(tokens, env)?;
            if tokens.next().ok_or("Expected ) found EOF")? != Token::CloseBracket {
                return Err("Expected ) found something else".to_string());
            }
            let expected_type = arg_types_iter
                .next()
                .ok_or("Function accepts too many arguments")?;
            if !typ.accepts(expected_type) {
                return Err("Parameter type mismatch".to_string());
            }
            next_env
                .variables
                .insert(identifier, Variable::Value { id, typ });
            args.push(id);
        }
        if arg_types_iter.next().is_some() {
            return Err("Function doesn't accept enough arguments".to_string());
        }
        tokens.next();
        let body = self.parse_expr(tokens, return_type, &next_env)?;
        if tokens.next() != Some(Token::CloseBracket) {
            return Err("Expected ) found something else".to_string());
        }
        Ok(Expr {
            typ: typ.clone(),
            kind: ExprKind::Fn {
                params: args,
                body: Box::new(body),
            },
        })
    }

    /// Parses a type expression, consumes the tokens for the type and returns the type
    fn parse_type(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = Token>>,
        env: &Env,
    ) -> Result<Type, String> {
        match tokens.next() {
            Some(Token::Identifier(name)) => Ok(env.get(name.as_str())?.typ()?.clone()),
            Some(Token::OpenBracket) => match tokens.peek() {
                Some(Token::OpenSquare) => {
                    tokens.next();
                    let mut arg_types = Vec::new();
                    while *tokens.peek().ok_or("Expected ] found EOF")? != Token::CloseSquare {
                        arg_types.push(self.parse_type(tokens, env)?);
                    }
                    tokens.next();
                    let ret = self.parse_type(tokens, env)?;
                    if tokens.next().ok_or("Expected ) found EOF")? != Token::CloseBracket {
                        return Err("Expected ) found something else".to_string());
                    }
                    Ok(Type::Function {
                        id: self.get_variable_id(),
                        args: arg_types,
                        ret: Box::new(ret),
                    })
                }
                _ => Err("Expected [ found something else".to_string()),
            },
            _ => Err("Expected type found something else".to_string()),
        }
    }

    /// Parses a let expression starting after the keyword let, until the closing bracket
    /// (let [(x int 5) (y int 10)] (+ x y))
    fn parse_let(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = Token>>,
        typ: &Type,
        env: &Env,
    ) -> Result<Expr, String> {
        let mut next_env = env.clone();
        let mut defs = Vec::new();
        if let Some(Token::OpenSquare) = tokens.peek() {
            tokens.next();
        } else {
            return Err(format!("Expected [ found {:?}", tokens.next()));
        }
        loop {
            if let Some(Token::CloseSquare) = tokens.peek() {
                break;
            }
            match tokens.next() {
                Some(Token::OpenBracket) => {
                    let identifier = if let Some(Token::Identifier(identifier)) = tokens.next() {
                        identifier
                    } else {
                        return Err("Expected identifier found something else".to_string());
                    };
                    let var_type = self.parse_type(tokens, env)?;
                    let var_value = self.parse_expr(tokens, &var_type, env)?;
                    match tokens.next() {
                        Some(Token::CloseBracket) => {}
                        _ => return Err("Expected ) found something else".to_string()),
                    };
                    let id = self.get_variable_id();
                    next_env
                        .variables
                        .insert(identifier, Variable::Value { id, typ: var_type });
                    defs.push((id, var_value));
                }
                None => {
                    return Err("Expected ( found EOF".to_string());
                }
                Some(token) => {
                    return Err(format!("Expected ( found {:?}", token));
                }
            }
        }
        tokens.next();
        let body = Box::new(self.parse_expr(tokens, typ, &next_env)?);
        tokens.next();
        Ok(Expr {
            typ: typ.clone(),
            kind: ExprKind::Let { defs, body },
        })
    }

    /// Parses any expression that starts with '('
    fn parse_function_call(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = Token>>,
        return_typ: &Type,
        env: &Env,
    ) -> Result<Expr, String> {
        let fn_name = match tokens
            .next()
            .ok_or("Expected a function identifier, found nothing".to_string())?
        {
            Token::Identifier(name) => Ok(name),
            Token::Let => {
                return self.parse_let(tokens, return_typ, env);
            }
            Token::Fn => {
                return self.parse_fn(tokens, return_typ, env);
            }
            _ => Err("Expected identifier or keyword, found something else".to_string()),
        }?;
        let function = env
            .variables
            .get(fn_name.as_str())
            .ok_or("Function not defined")?;
        let (param_types, actual_return_type) = match function {
            Variable::Type(_) => Err("Expected a function identifier but found a type".to_string()),
            Variable::Value { id, typ } => match typ {
                Type::Other(_) => Err("Expected a function but found something else".to_string()),
                Type::Function { args, ret, .. } => Ok((args, ret.as_ref())),
            },
        }?;
        if !return_typ.accepts(actual_return_type) {
            return Err("Function returns the wrong type".to_string());
        }
        let params: Result<Vec<Expr>, String> = param_types
            .into_iter()
            .map(|typ| self.parse_expr(tokens, &typ, env))
            .collect();
        if let Some(Token::CloseBracket) = tokens.next() {
            Ok(Expr {
                kind: ExprKind::FunctionCall {
                    function: function.id(),
                    params: params?,
                },
                typ: return_typ.clone(),
            })
        } else {
            Err("Expected ) found something else".to_string())
        }
    }

    fn parse_expr(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = Token>>,
        typ: &Type,
        env: &Env,
    ) -> Result<Expr, String> {
        match tokens.next() {
            None => Err("Tried to parse an expression from an empty token stream".to_string()),
            Some(Token::IntegerLiteral(num)) => {
                if typ.is_integer() {
                    Ok(Expr {
                        kind: ExprKind::IntegerLiteral(num),
                        typ: typ.clone(),
                    })
                } else {
                    Err("Expected integer found something else".to_string())
                }
            }
            Some(Token::OpenBracket) => self.parse_function_call(tokens, typ, env),
            Some(Token::CloseBracket) => {
                Err("Tried to parse expression from close bracket".to_string())
            }
            Some(Token::OpenSquare) => Err("Expected expression found [".to_string()),
            Some(Token::CloseSquare) => Err("Expected expression found ]".to_string()),
            Some(Token::Identifier(name)) => {
                let variable = env.get(name.as_str())?;
                if let Variable::Value { id, typ: var_typ } = variable {
                    if typ.accepts(var_typ) {
                        Ok(Expr {
                            kind: ExprKind::Identifier(*id),
                            typ: var_typ.clone(),
                        })
                    } else {
                        Err("Expected a type and found a different type".to_string())
                    }
                } else {
                    Err("Expected value found type".to_string())
                }
            }
            Some(Token::Let) => Err("let is a reserved keyword".to_string()),
            Some(Token::Fn) => Err("fn is a reserved keyword".to_string()),
        }
    }

    pub fn parse(tokens: impl Iterator<Item = Token>, env: Env) -> Result<Expr, String> {
        let next_variable_id = crate::stdlib::LOWEST_USER_VAR_ID;
        let mut parser = Parser { next_variable_id };

        parser.parse_expr(&mut tokens.peekable(), env.get("i32")?.typ()?, &env)
    }
}
