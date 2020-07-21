use std::iter::Peekable;

use im::HashMap;

use llvm_sys::core::{
    LLVMIntTypeInContext, LLVMGetTypeKind,
};
use llvm_sys::{LLVMType, LLVMContext, LLVMTypeKind};

use crate::lex::Token;

#[derive(Debug)]
pub enum ExprKind {
    Identifier(String),
    IntegerLiteral(i64),
    //Let(Vec<(usize, Expr)>),
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub typ: *mut LLVMType,
}

#[derive(Default)]
struct Env<'a> {
    variables: HashMap<&'a str, usize>,
}

pub struct Parser {
}

impl Parser {
    fn parse_function_call(&mut self, tokens: &mut impl Iterator<Item=Token>, typ: *mut LLVMType) -> Result<Expr, String> {
        Err("Function calls not implemented yet".to_string())
    }

    fn parse_expr(&mut self, tokens: &mut impl Iterator<Item=Token>, typ: *mut LLVMType) -> Result<Expr, String> {
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
                self.parse_function_call(tokens, typ)
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

    pub fn parse_expr_list<S: Iterator<Item=Token>>(&mut self, tokens: &mut Peekable<S>, typ: *mut LLVMType) -> Result<Vec<Expr>, String> {
        let mut exprs = Vec::new();
        loop {
            match tokens.peek() {
                None => break,
                Some(&Token::CloseBracket) => break,
                _ => {},
            }
            exprs.push(self.parse_expr(tokens, typ)?);
        }
        Ok(exprs)
    }

    pub fn parse(tokens: impl Iterator<Item=Token>, context: *mut LLVMContext) -> Result<Expr, String> {
        let mut parser = Parser {};
        let i32_type = unsafe {LLVMIntTypeInContext(context, 32)};
        parser.parse_expr(&mut tokens.peekable(), i32_type)
    }
}
