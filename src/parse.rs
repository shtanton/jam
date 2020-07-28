use std::iter::{self, Peekable};
use std::ptr;
use std::alloc::{alloc, dealloc, Layout};

use im::HashMap;

use llvm_sys::core::{
    LLVMIntTypeInContext, LLVMGetTypeKind, LLVMTypeOf, LLVMGetParamTypes, LLVMGetReturnType, LLVMCountParamTypes,
    LLVMDumpType, LLVMGetElementType,
};
use llvm_sys::{LLVMType, LLVMContext, LLVMTypeKind, LLVMValue};

use crate::lex::Token;

#[derive(Debug)]
pub enum ExprKind {
    Identifier(String),
    IntegerLiteral(i64),
    FunctionCall {
        function: *mut LLVMValue,
        params: Vec<Expr>,
    },
    //Let(Vec<(usize, Expr)>),
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub typ: *mut LLVMType,
}

#[derive(Default, Clone)]
pub struct Env<'a> {
    pub variables: HashMap<&'a str, *mut LLVMValue>,
}

pub struct Parser {
}

impl Parser {
    fn parse_function_call(&mut self, tokens: &mut impl Iterator<Item=Token>, return_typ: *mut LLVMType, env: Env) -> Result<Expr, String> {
        let fn_name = match tokens.next().ok_or("Expected a function identifier, found nothing".to_string())? {
            Token::Identifier(name) => Ok(name),
            _ => Err("Expected identifier, found something else".to_string()),
        }?;
        let function = *env.variables.get(fn_name.as_str()).ok_or("Function not defined")?;
        let param_types = unsafe {
            let function_pointer_type = LLVMTypeOf(function);
            if LLVMGetTypeKind(function_pointer_type) != LLVMTypeKind::LLVMPointerTypeKind {
                return Err("Expected a function, found something else".to_string());
            }
            let function_type = LLVMGetElementType(function_pointer_type);
            if LLVMGetTypeKind(function_type) != LLVMTypeKind::LLVMFunctionTypeKind {
                return Err("Expected a function, found something else".to_string());
            }
            if LLVMGetReturnType(function_type) != return_typ {
                return Err("Function returns the wrong type".to_string());
            }
            let param_count = LLVMCountParamTypes(function_type);
            let mut param_types: Vec<*mut LLVMType> = iter::repeat(ptr::null::<LLVMType>() as *mut _).take(param_count as usize).collect();
            LLVMGetParamTypes(function_type, param_types.as_mut_ptr());
            param_types
        };
        let params: Result<Vec<Expr>, String> = param_types.into_iter().map(|typ| {
            self.parse_expr(tokens, typ, env.clone())
        }).collect();
        if let Some(Token::CloseBracket) = tokens.next() {
            Ok(Expr {
                kind: ExprKind::FunctionCall {
                    function: function,
                    params: params?,
                },
                typ: return_typ,
            })
        } else {
            Err("Expected ) found something else".to_string())
        }
    }

    fn parse_expr(&mut self, tokens: &mut impl Iterator<Item=Token>, typ: *mut LLVMType, env: Env) -> Result<Expr, String> {
        match tokens.next() {
            None => Err("Tried to parse an expression from an empty token stream".to_string()),
            Some(Token::IntegerLiteral(num)) => {
                if unsafe {LLVMGetTypeKind(typ) == LLVMTypeKind::LLVMIntegerTypeKind} {
                    Ok(Expr {
                        kind: ExprKind::IntegerLiteral(num),
                        typ: typ,
                    })
                } else {
                    Err("Expected integer found something else".to_string())
                }
            }
            Some(Token::OpenBracket) => {
                self.parse_function_call(tokens, typ, env)
            },
            Some(Token::CloseBracket) => Err("Tried to parse expression from close bracket".to_string()),
            Some(Token::Identifier(name)) => Ok(Expr {
                kind: ExprKind::Identifier(name),
                typ: typ,
            }),
            Some(Token::Fn) => {
                Err("fn isn't implemented yet".to_string())
            },
            Some(Token::Let) => {
                Err("let isn't implemented yet".to_string())
            },
        }
    }

    pub fn parse_expr_list<S: Iterator<Item=Token>>(&mut self, tokens: &mut Peekable<S>, typ: *mut LLVMType, env: Env) -> Result<Vec<Expr>, String> {
        let mut exprs = Vec::new();
        loop {
            match tokens.peek() {
                None => break,
                Some(&Token::CloseBracket) => break,
                _ => {},
            }
            exprs.push(self.parse_expr(tokens, typ, env.clone())?);
        }
        Ok(exprs)
    }

    pub fn parse(tokens: impl Iterator<Item=Token>, env: Env, context: *mut LLVMContext) -> Result<Expr, String> {
        let mut parser = Parser {};

        let i32_type = unsafe {LLVMIntTypeInContext(context, 32)};
        parser.parse_expr(&mut tokens.peekable(), i32_type, env)
    }
}
