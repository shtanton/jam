use crate::lex::Token;
use crate::stdlib::INT_ID;
use im::HashMap as ImHashMap;
use std::collections::HashMap;
use std::fmt;
use std::iter::Peekable;
use std::rc::Rc;

pub type VariableId = u64;
pub type TypeId = u64;

#[derive(Clone, Debug)]
pub enum ValueId {
    Variable(VariableId),
    Type(TypeId),
}

#[derive(Debug)]
pub enum ExprKind {
    Number(i64),
    Variable(VariableId),
    FunctionCall {
        function: Box<Expr>,
        args: Vec<Expr>,
    },
    Let {
        defs: Vec<(VariableId, Expr)>,
        body: Box<Expr>,
    },
    Fn {
        params: Vec<VariableId>,
        body: Box<Expr>,
    },
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub typ: TypeId,
    pub env: Vec<VariableId>,
}

#[derive(Clone, Debug)]
pub struct Variable {
    pub id: VariableId,
    pub typ: TypeId,
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

#[derive(Clone, Debug, PartialEq)]
pub enum SuperType {
    Int,
    Bool,
}

impl fmt::Display for SuperType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Clone, Debug)]
pub enum SMTValue {
    Call(SMTFunction, Vec<SMTValue>),
    Variable(u64),
    Type(TypeId),
    Const(SMTConst),
    This,
}

#[derive(Copy, Clone, Debug)]
pub enum SMTFunction {
    Equal,
}

#[derive(Clone, Debug)]
pub enum SMTConst {
    Number(i64),
    Bool(bool),
}

#[derive(Clone, Debug)]
pub enum Type {
    Function {
        params: Vec<TypeId>,
        ret: TypeId,
    },
    Primitive {
        // If true the value is an runtime instance of the type.
        // If false the value is a comptime subtype of the type.
        instance: bool,
        // Superest of types
        super_type: SuperType,
        assertion: SMTValue,
    },
    AnyType,
}

impl Type {
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
            Type::Function { params, ret, .. } => {
                write!(f, "([")?;
                let mut iter = params.iter();
                if let Some(first) = iter.next() {
                    write!(f, "{}", first)?;
                    for param in iter {
                        write!(f, ", {}", param)?;
                    }
                }
                write!(f, "] {})", ret)?;
            }
            Type::Primitive {
                instance,
                super_type,
                ..
            } => {
                if *instance {
                    write!(f, "{}", super_type)?;
                } else {
                    write!(f, "(subtype {})", super_type)?;
                }
            }
            Type::AnyType => {
                write!(f, "type")?;
            }
        };
        Ok(())
    }
}

#[derive(Debug, Default, Clone)]
pub struct Env {
    pub variables: ImHashMap<String, ValueId>,
}

impl Env {
    fn get_id(&self, identifier: &str) -> Result<&ValueId, String> {
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

pub struct Parser {
    next_variable_id: u64,
    next_type_id: u64,
    variables: HashMap<VariableId, Variable>,
    types: HashMap<TypeId, Type>,
}

impl Parser {
    /// Each time this is called in a parser it generates a new unique id
    fn get_variable_id(&mut self) -> VariableId {
        let id = self.next_variable_id;
        self.next_variable_id += 1;
        id
    }

    fn get_type_id(&mut self) -> TypeId {
        let id = self.next_type_id;
        self.next_type_id += 1;
        id
    }

    fn get_type(&self, typ_id: TypeId) -> Result<&Type, String> {
        self.types.get(&typ_id).ok_or("Type not found".to_string())
    }

    fn get_variable(&self, var_id: VariableId) -> Result<&Variable, String> {
        self.variables
            .get(&var_id)
            .ok_or("Variable not found".to_string())
    }

    fn flatten_SMT_value(&self, value: &SMTValue) -> Result<(Vec<SuperType>, SMTValue), String> {
    }

		/// Returns how many variables are needed and an assertion over those variables
		/// In the assertion the variables are referenced as u64 from 0 to count-1 inclusive
		/// Variable 0 is the one that can take any value the type can take
    fn construct_SMT_assertion(&self, type_id: TypeId) -> Result<(Vec<SuperType>, SMTValue), String> {
        let typ = self.get_type(type_id)?;
        let (super_type, assertion) = match typ {
            Type::Function {..} => return Err("Tried to construct an SMT assertion for a function type".to_string()),
            Type::AnyType => return Err("Tried to construct an SMT assertion for anytype".to_string()),
            Type::Primitive {
                super_type,
                assertion,
                ..
            } => (super_type, assertion),
        };
        let mut super_types = vec![*super_type];
        let final_assertion = match assertion {
            SMTValue::Call(func, args) => {
                let final_args = Vec::new();
                for arg in args.iter() {
                    let (used_for_arg, arg) = self.flatten_SMT_value(arg)?;
                }
                SMTValue::Call(*func, final_args)
            },
        };
        Ok((super_types, final_assertion))
    }

    fn SMT_accepts(&self, super_type: SuperType, target_assertion: SMTValue, subject_assertion: SMTValue) -> Result<bool, String> {
    }

    fn accepts(&self, target_id: TypeId, subject_id: TypeId) -> Result<bool, String> {
        let target = self.get_type(target_id)?;
        let subject = self.get_type(subject_id)?;
        match (target, subject) {
            (
                Type::Function {
                    params: target_params,
                    ret: target_ret,
                },
                Type::Function {
                    params: subject_params,
                    ret: subject_ret,
                },
            ) => {
                let mut param_pairs = target_params
                    .iter()
                    .copied()
                    .zip(subject_params.iter().copied());
                while let Some((target_param, subject_param)) = param_pairs.next() {
                    if !self.accepts(subject_param, target_param)? {
                        return Ok(false);
                    }
                }
                self.accepts(*target_ret, *subject_ret)
            }
            (Type::AnyType, Type::AnyType) => Ok(true),
            (
                Type::AnyType,
                Type::Primitive {
                    instance: false, ..
                },
            ) => Ok(true),
            (
                Type::Primitive {
                    instance: false,
                    super_type: target_super_type,
                    assertion: target_assertion,
                },
                Type::Primitive {
                    instance: false,
                    super_type: subject_super_type,
                    assertion: subject_assertion,
                },
            ) => {
                // TODO
                if target_super_type != subject_super_type {
                    return Ok(false);
                }
                Ok(true)
            }
            (
                Type::Primitive {
                    instance: true,
                    super_type: target_super_type,
                    assertion: target_assertion,
                },
                Type::Primitive {
                    instance: true,
                    super_type: subject_super_type,
                    assertion: subject_assertion,
                },
            ) => {
                // TODO
                if target_super_type != subject_super_type {
                    return Ok(false);
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn accepts_value(&self, target_id: TypeId, subject_id: TypeId) -> Result<bool, String> {
        let target = self.get_type(target_id)?;
        let subject = self.get_type(subject_id)?;
        match (target, subject) {
            (Type::AnyType, _) => Ok(true),
            (
                Type::Primitive {
                    instance: false,
                    super_type: target_super_type,
                    assertion: target_assertion,
                },
                Type::Primitive {
                    instance: true,
                    super_type: subject_super_type,
                    assertion: subject_assertion,
                },
            ) => {
                if target_super_type != subject_super_type {
                    return Ok(false);
                }
                // TODO
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn expect_accepts(&self, target: TypeId, subject: TypeId) -> Result<(), String> {
        if self.accepts(target, subject)? {
            Ok(())
        } else {
            Err("This type isn't valid here...".to_string())
        }
    }

    fn expect_accepts_value(&self, target: TypeId, subject: TypeId) -> Result<(), String> {
        if self.accepts_value(target, subject)? {
            Ok(())
        } else {
            Err("This value isn't valid here...".to_string())
        }
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
        let mut params = Vec::new();
        let mut param_types = Vec::new();
        while *tokens.peek().ok_or("Expected ] found EOF")? != Token::CloseSquare {
            expect_token(tokens, Token::OpenBracket)?;
            let identifier = if let Some(Token::Identifier(name)) = tokens.next() {
                name
            } else {
                return Err("Expected parameter identifier found something else".to_string());
            };
            let var_id = self.get_variable_id();
            let typ_id = self.parse_type(tokens, env)?;
            expect_token(tokens, Token::CloseBracket)?;
            self.variables.insert(
                var_id,
                Variable {
                    id: var_id,
                    typ: typ_id,
                },
            );
            next_env
                .variables
                .insert(identifier, ValueId::Variable(var_id));
            params.push(var_id);
            param_types.push(typ_id);
        }
        tokens.next();
        let return_type = self.parse_type(tokens, env)?;
        // TODO enable returning types
        let body = self.parse_expr(tokens, &next_env)?;
        expect_token(tokens, Token::CloseBracket)?;
        let captures: Vec<_> = body
            .env
            .iter()
            .map(|id| *id)
            .filter(|id| {
                for param in params.iter() {
                    if *param == *id {
                        return false;
                    }
                }
                true
            })
            .collect();
        self.expect_accepts(return_type, body.typ)?;
        let typ = self.get_type_id();
        self.types.insert(
            typ,
            Type::Function {
                params: param_types,
                ret: return_type,
            },
        );
        Ok(Expr {
            typ: typ,
            kind: ExprKind::Fn {
                params: params,
                body: Box::new(body),
            },
            env: captures,
        })
    }

    /// Parses a type expression, consumes the tokens for the type and returns the TypeId
    fn parse_type(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = Token>>,
        env: &Env,
    ) -> Result<TypeId, String> {
        match tokens.next() {
            Some(Token::Identifier(name)) => {
                if let Ok(ValueId::Type(id)) = env.get_id(name.as_str()) {
                    Ok(*id)
                } else {
                    Err("Expected type found something else".to_string())
                }
            }
            Some(Token::OpenBracket) => match tokens.next() {
                Some(Token::OpenSquare) => {
                    let mut param_types = Vec::new();
                    while *tokens.peek().ok_or("Expected ] found EOF")? != Token::CloseSquare {
                        param_types.push(self.parse_type(tokens, env)?);
                    }
                    tokens.next();
                    let ret_type = self.parse_type(tokens, env)?;
                    expect_token(tokens, Token::CloseBracket)?;
                    let typ_id = self.get_type_id();
                    self.types.insert(
                        typ_id,
                        Type::Function {
                            params: param_types,
                            ret: ret_type,
                        },
                    );
                    Ok(typ_id)
                }
                // TODO let, call, import
                _ => Err("Invalid token following (".to_string()),
            },
            Some(token) => Err(format!("Expected type found {:?}", token)),
            None => Err("Expected type found nothing".to_string()),
        }
    }

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
            let typ_id = self.parse_type(tokens, env)?;
            let typ = self.get_type(typ_id)?;
            match typ {
                Type::AnyType
                | Type::Primitive {
                    instance: false, ..
                } => {
                    // TODO recursion
                    let subtyp = self.parse_type(tokens, env)?;
                    self.expect_accepts_value(typ_id, subtyp)?;
                    next_env.variables.insert(identifier, ValueId::Type(subtyp));
                }
                _ => {
                    let var_id = self.get_variable_id();
                    let variable = Variable {
                        id: var_id,
                        typ: typ_id,
                    };
                    // TODO recursion
                    let var_value = self.parse_expr(tokens, env)?;
                    self.expect_accepts(typ_id, var_value.typ)?;
                    next_env
                        .variables
                        .insert(identifier, ValueId::Variable(var_id));
                    self.variables.insert(var_id, variable);
                    defs.push((var_id, var_value));
                }
            }
            expect_token(tokens, Token::CloseBracket)?;
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
            params: param_types,
            ret: ret_type,
        } = self.get_type(function.typ)?.clone()
        {
            let args = param_types
                .iter()
                .map(|typ| {
                    let arg = self.parse_expr(tokens, env)?;
                    self.expect_accepts(*typ, arg.typ)?;
                    Ok(arg)
                })
                .collect::<Result<Vec<_>, String>>()?;
            let mut captures = args
                .iter()
                .flat_map(|arg| arg.env.iter())
                .chain(function.env.iter())
                .map(|&var_id| var_id)
                .collect::<Vec<_>>();
            captures.sort();
            captures.dedup();
            expect_token(tokens, Token::CloseBracket)?;
            Ok(Expr {
                kind: ExprKind::FunctionCall {
                    function: Box::new(function),
                    args: args,
                },
                typ: ret_type,
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
            Some(Token::IntegerLiteral(num)) => {
                let typ_id = self.get_type_id();
                let typ = Type::Primitive {
                    instance: true,
                    super_type: SuperType::Int,
                    assertion: SMTValue::Call(
                        SMTFunction::Equal,
                        Box::new((SMTValue::This, SMTValue::Const(SMTConst::Number(num)))),
                    ),
                };
                self.types.insert(typ_id, typ);
                Ok(Expr {
                    kind: ExprKind::Number(num),
                    typ: typ_id,
                    env: Vec::new(),
                })
            }
            Some(Token::StringLiteral(_)) => Err("Strings not yet implemented".to_string()),
            Some(Token::OpenBracket) => self.parse_bracketed_expression(tokens, env),
            Some(Token::CloseBracket) => {
                Err("Tried to parse expression from close bracket".to_string())
            }
            Some(Token::OpenSquare) => Err("Expected expression found [".to_string()),
            Some(Token::CloseSquare) => Err("Expected expression found ]".to_string()),
            Some(Token::Identifier(name)) => {
                let value_id = env.get_id(name.as_str())?;
                if let ValueId::Variable(var_id) = value_id {
                    let var = self.get_variable(*var_id)?;
                    Ok(Expr {
                        kind: ExprKind::Variable(*var_id),
                        typ: var.typ,
                        env: vec![*var_id],
                    })
                } else {
                    Err("Expected expression found type".to_string())
                }
            }
            Some(Token::Let) => Err("let is a reserved keyword".to_string()),
            Some(Token::Fn) => Err("fn is a reserved keyword".to_string()),
            Some(Token::Import) => Err("import is a reserved keyword".to_string()),
            Some(Token::Type) => Err("type is a reserved keyword".to_string()),
            Some(Token::Struct) => Err("struct is a reserved keyword".to_string()),
        }
    }

    pub fn new(
        next_variable_id: VariableId,
        next_type_id: TypeId,
        variables: HashMap<VariableId, Variable>,
        types: HashMap<TypeId, Type>,
    ) -> Parser {
        Parser {
            next_variable_id,
            next_type_id,
            variables,
            types,
        }
    }

    pub fn parse(
        mut self: Parser,
        tokens: impl Iterator<Item = Token>,
        env: Env,
    ) -> Result<Expr, String> {
        let expr = self.parse_expr(&mut tokens.peekable(), &env)?;
        Ok(expr)
    }
}
