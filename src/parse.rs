use crate::lex::Token;
use crate::stdlib::INT_ID;
use im::HashMap as ImHashMap;
use std::collections::HashMap;
use std::fmt;
use std::iter::Peekable;
use std::rc::Rc;

#[derive(Debug)]
pub enum ExprKind {
    Variable(Variable),
    FunctionCall {
        function: Box<Expr>,
        params: Vec<Expr>,
    },
    Let {
        defs: Vec<(Variable, Expr)>,
        body: Box<Expr>,
    },
    Fn {
        params: Vec<Variable>,
        body: Box<Expr>,
    },
    Comptime(ComptimeExpr),
}

/// An expression with a value known at compile time
#[derive(Clone)]
pub enum ComptimeExpr {
    Int(i64),
    Type(Type),
    Bool(bool),
    Function(Rc<dyn Fn(Vec<ComptimeExpr>) -> ComptimeExpr>),
}

impl fmt::Debug for ComptimeExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ComptimeExpr::Int(val) => write!(f, "Comptime({})", val),
            ComptimeExpr::Type(typ) => write!(f, "Comptime({:?})", typ),
            ComptimeExpr::Bool(val) => write!(f, "Comptime({})", val),
            ComptimeExpr::Function(val) => write!(f, "Comptime(fn)"),
        }
    }
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub typ: Type,
    pub env: Vec<Variable>,
}

#[derive(Clone, Debug)]
pub struct Variable {
    pub id: u64,
    pub typ: Type,
}

impl PartialEq for Variable {
    fn eq(&self, rhs: &Variable) -> bool {
        self.id == rhs.id
    }
}

impl Eq for Variable {}

impl Ord for Variable {
    fn cmp(&self, rhs: &Variable) -> std::cmp::Ordering {
        self.id.cmp(&rhs.id)
    }
}

impl PartialOrd for Variable {
    fn partial_cmp(&self, rhs: &Variable) -> Option<std::cmp::Ordering> {
        Some(self.cmp(rhs))
    }
}

#[derive(Clone, Debug)]
pub enum Type {
    Function {
        args: Vec<Type>,
        ret: Box<Type>,
        env: Vec<Type>,
    },
    Primal(u64),
    Type,
}

impl Type {
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
            (Type::Primal(self_id), Type::Primal(typ_id)) => self_id == typ_id,
            (Type::Type, Type::Type) => true,
            _ => false,
        }
    }

    fn expect_accept(&self, typ: &Type) -> Result<(), String> {
        if self.accepts(typ) {
            Ok(())
        } else {
            Err(format!("Expected type {} found {}", self, typ))
        }
    }

    pub fn is_function(&self) -> bool {
        if let Type::Function { .. } = self {
            true
        } else {
            false
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Primal(id) => {
                write!(f, "Primal({})", id)?;
            }
            Type::Function { args, ret, .. } => {
                write!(f, "([")?;
                let mut iter = args.iter();
                if let Some(first) = iter.next() {
                    write!(f, "{}", first)?;
                    for arg in iter {
                        write!(f, ", {}", arg)?;
                    }
                }
                write!(f, "] {})", ret)?;
            }
            Type::Type => {
                write!(f, "Type")?;
            }
        };
        Ok(())
    }
}

#[derive(Debug, Default, Clone)]
pub struct Env {
    pub variables: ImHashMap<String, Variable>,
    pub comptime: ImHashMap<u64, ComptimeExpr>,
}

impl Env {
    fn get_variable(&self, identifier: &str) -> Result<&Variable, String> {
        self.variables
            .get(identifier)
            .ok_or(format!("Variable {} not found", identifier))
    }
}

fn expect_token(
    tokens: &mut impl Iterator<Item = Token>,
    expected_token: Token,
) -> Result<(), String> {
    if let Some(actual_token) = tokens.next() {
        if actual_token == expected_token {
            Ok(())
        } else {
            Err(format!(
                "Expected {:?} found {:?}",
                expected_token, actual_token
            ))
        }
    } else {
        Err(format!("Expected {:?} found nothing", expected_token))
    }
}

fn type_from_expr(expr: Expr) -> Result<Type, String> {
    match (&expr.typ, &expr.kind) {
        (Type::Type, ExprKind::Comptime(ComptimeExpr::Type(typ))) => Ok(typ.clone()),
        _ => Err(format!("Expected type found {:?}", expr)),
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

    /// Parse an import, starting after the keyword and ending after the )
    fn parse_import(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = Token>>,
    ) -> Result<Expr, String> {
        if let Some(Token::StringLiteral(module)) = tokens.next() {
            if module == "std" {
                if let Some(Token::CloseBracket) = tokens.next() {
                } else {
                    return Err("Expected ) found something else".to_string());
                }
                Err("Importing std not implemented yet".to_string())
            /*Ok(Expr {
                kind: ExprKind::Import(Module::Std),
                typ:
            })*/
            } else {
                Err("std is the only import available for now".to_string())
            }
        } else {
            Err("Expected a string literal, found something else".to_string())
        }
    }

    /// Parse a function definition, starting immediately after the fn keyword and ending after the )
    /// (fn [(x int) (y int)] int (+ x y))
    fn parse_fn(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = Token>>,
        env: &Env,
    ) -> Result<Expr, String> {
        expect_token(tokens, Token::OpenSquare)?;
        let mut next_env = env.clone();
        let mut args = Vec::new();
        let mut arg_types = Vec::new();
        while *tokens.peek().ok_or("Expected ] found EOF")? != Token::CloseSquare {
            expect_token(tokens, Token::OpenBracket)?;
            let identifier = if let Some(Token::Identifier(name)) = tokens.next() {
                name
            } else {
                return Err("Expected parameter identifier found something else".to_string());
            };
            let id = self.get_variable_id();
            let type_expr = self.parse_expr(tokens, &next_env)?;
            let typ = type_from_expr(type_expr)?;
            expect_token(tokens, Token::CloseBracket)?;
            arg_types.push(typ.clone());
            let var = Variable { id, typ };
            next_env.variables.insert(identifier, var.clone());
            args.push(var);
        }
        tokens.next();
        let return_type_expr = self.parse_expr(tokens, &next_env)?;
        let return_type = type_from_expr(return_type_expr)?;
        let body = self.parse_expr(tokens, &next_env)?;
        let captures: Vec<_> = body
            .env
            .iter()
            .map(|var| var.clone())
            .filter(|var| {
                for arg in args.iter() {
                    if *arg == *var {
                        return false;
                    }
                }
                true
            })
            .collect();
        return_type.expect_accept(&body.typ)?;
        expect_token(tokens, Token::CloseBracket)?;
        let capture_types: Vec<_> = captures.iter().map(|var| var.typ.clone()).collect();
        Ok(Expr {
            typ: Type::Function {
                args: arg_types,
                ret: Box::new(body.typ.clone()),
                env: capture_types,
            },
            kind: ExprKind::Fn {
                params: args,
                body: Box::new(body),
            },
            env: captures,
        })
    }

    /// Parses a type expression, consumes the tokens for the type and returns the type
    /*fn parse_type(
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
            Some(token) => Err(format!("Expected type found {:?}", token)),
            None => Err("Expected type found nothing".to_string()),
        }
    }*/

    /// Parses a let expression starting after the keyword let, until the closing bracket
    /// (let [(x int 5) (y int 10)] (+ x y))
    fn parse_let(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = Token>>,
        env: &Env,
    ) -> Result<Expr, String> {
        let mut next_env = env.clone();
        let mut defs = Vec::new();
        expect_token(tokens, Token::OpenSquare)?;
        loop {
            if let Some(Token::CloseSquare) = tokens.peek() {
                break;
            }
            expect_token(tokens, Token::OpenBracket)?;
            let identifier = if let Some(Token::Identifier(identifier)) = tokens.next() {
                identifier
            } else {
                return Err("Expected identifier found something else".to_string());
            };
            let type_expr = self.parse_expr(tokens, &next_env)?;
            let var_type = type_from_expr(type_expr)?;
            let id = self.get_variable_id();
            let var = Variable {
                id,
                typ: var_type.clone(),
            };
            if var_type.is_function() {
                next_env.variables.insert(identifier.clone(), var.clone());
            }
            let var_value = self.parse_expr(tokens, &next_env)?;
            var_type.expect_accept(&var_value.typ)?;
            expect_token(tokens, Token::CloseBracket)?;
            if !var_type.is_function() {
                next_env.variables.insert(identifier, var.clone());
            }
            defs.push((var, var_value));
        }
        tokens.next();
        let body = Box::new(self.parse_expr(tokens, &next_env)?);
        let captures: Vec<_> = body
            .env
            .iter()
            .map(|var| var.clone())
            .filter(|var| {
                for def in defs.iter() {
                    if def.0 == *var {
                        return false;
                    }
                }
                true
            })
            .collect();
        expect_token(tokens, Token::CloseBracket)?;
        Ok(Expr {
            typ: body.typ.clone(),
            kind: ExprKind::Let { defs, body },
            env: captures,
        })
    }

    /// Parses any expression that starts with '(', starts after the (
    fn parse_bracketed_expression(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = Token>>,
        env: &Env,
    ) -> Result<Expr, String> {
        match tokens
            .peek()
            .ok_or("Expected a function identifier, found nothing".to_string())?
        {
            Token::Let => {
                tokens.next();
                self.parse_let(tokens, env)
            }
            Token::Fn => {
                tokens.next();
                self.parse_fn(tokens, env)
            }
            Token::Import => {
                tokens.next();
                self.parse_import(tokens)
            }
            _ => {
                let function = self.parse_expr(tokens, env)?;
                self.parse_function_call(function, tokens, env)
            }
        }
    }

    /// Parses a call to a function, starting AFTER the function expression (i.e. the first argument)
    /// Doesn't assume the function argument is a function, just that it is an expression
    fn parse_function_call(
        &mut self,
        function: Expr,
        tokens: &mut Peekable<impl Iterator<Item = Token>>,
        env: &Env,
    ) -> Result<Expr, String> {
        if let Type::Function {
            args: arg_types,
            ret: ret_type,
            ..
        } = function.typ.clone()
        {
            let args = arg_types
                .into_iter()
                .map(|typ| {
                    let arg = self.parse_expr(tokens, env)?;
                    if !typ.accepts(&arg.typ) {
                        return Err("Argument type doesn't match expected type".to_string());
                    }
                    Ok(arg)
                })
                .collect::<Result<Vec<_>, String>>()?;
            match &function.kind {
                ExprKind::Comptime(ComptimeExpr::Function(function)) => {
                    let comptime_args = args
                        .iter()
                        .map(|arg| match &arg.kind {
                            ExprKind::Comptime(expr) => Some(expr.clone()),
                            _ => None,
                        })
                        .collect::<Option<Vec<ComptimeExpr>>>();
                    if let Some(args) = comptime_args {
                        expect_token(tokens, Token::CloseBracket)?;
                        return Ok(Expr {
                            kind: ExprKind::Comptime(function(args)),
                            typ: ret_type.as_ref().clone(),
                            env: Vec::new(),
                        });
                    }
                }
                _ => {}
            };
            let mut captures = args
                .iter()
                .flat_map(|arg| arg.env.iter())
                .map(|var| var.clone())
                .collect::<Vec<_>>();
            captures.sort();
            captures.dedup();
            expect_token(tokens, Token::CloseBracket)?;
            Ok(Expr {
                kind: ExprKind::FunctionCall {
                    function: Box::new(function),
                    params: args,
                },
                typ: ret_type.as_ref().clone(),
                env: captures,
            })
        } else {
            Err("Tried to call something that isn't a function".to_string())
        }
    }

    fn parse_expr(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = Token>>,
        env: &Env,
    ) -> Result<Expr, String> {
        match tokens.next() {
            None => Err("Tried to parse an expression from an empty token stream".to_string()),
            Some(Token::IntegerLiteral(num)) => Ok(Expr {
                kind: ExprKind::Comptime(ComptimeExpr::Int(num)),
                typ: Type::Primal(INT_ID),
                env: Vec::new(),
            }),
            Some(Token::StringLiteral(_)) => Err("Strings not yet implemented".to_string()),
            Some(Token::OpenBracket) => self.parse_bracketed_expression(tokens, env),
            Some(Token::CloseBracket) => {
                Err("Tried to parse expression from close bracket".to_string())
            }
            Some(Token::OpenSquare) => Err("Expected expression found [".to_string()),
            Some(Token::CloseSquare) => Err("Expected expression found ]".to_string()),
            Some(Token::Identifier(name)) => {
                let variable = env.get_variable(name.as_str())?;
                if let Some(comptime) = env.comptime.get(&variable.id) {
                    Ok(Expr {
                        kind: ExprKind::Comptime(comptime.clone()),
                        typ: variable.typ.clone(),
                        env: vec![variable.clone()],
                    })
                } else {
                    Ok(Expr {
                        kind: ExprKind::Variable(variable.clone()),
                        typ: variable.typ.clone(),
                        env: vec![variable.clone()],
                    })
                }
            }
            Some(Token::Let) => Err("let is a reserved keyword".to_string()),
            Some(Token::Fn) => Err("fn is a reserved keyword".to_string()),
            Some(Token::Import) => Err("import is a reserved keyword".to_string()),
            Some(Token::Type) => Err("type is a reserved keyword".to_string()),
            Some(Token::Struct) => Err("struct is a reserved keyword".to_string()),
        }
    }

    pub fn parse(tokens: impl Iterator<Item = Token>, env: Env) -> Result<Expr, String> {
        let next_variable_id = crate::stdlib::LOWEST_USER_VAR_ID;
        let mut parser = Parser { next_variable_id };

        let expr = parser.parse_expr(&mut tokens.peekable(), &env)?;
        if !Type::Primal(crate::stdlib::INT_ID).accepts(&expr.typ) {
            return Err("Expected in found something else".to_string());
        }
        Ok(expr)
    }
}
