extern crate llvm_sys;
extern crate lazy_static;
extern crate im;
mod lex;
mod parse;
mod codegen;

use llvm_sys::core::{LLVMContextCreate, LLVMContextDispose};

use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();

    let tokens: Vec<lex::Token> = lex::lex(args[1].clone()).map(|res| res.unwrap()).collect();

    unsafe {
        let context = LLVMContextCreate();
        let ast = parse::Parser::parse(tokens.into_iter(), context).unwrap();
        codegen::codegen(ast, context);
        LLVMContextDispose(context);
    }
}
