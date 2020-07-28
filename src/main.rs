extern crate llvm_sys;
extern crate lazy_static;
extern crate im;
mod lex;
mod parse;
mod codegen;
mod stdlib;

use llvm_sys::core::{LLVMContextCreate, LLVMContextDispose, LLVMModuleCreateWithName, LLVMDisposeModule};

use std::env;

macro_rules! c_str {
    ($s:expr) => (
        concat!($s, "\0").as_ptr() as *const i8
    );
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let tokens: Vec<lex::Token> = lex::lex(args[1].clone()).map(|res| res.unwrap()).collect();

    unsafe {
        let context = LLVMContextCreate();
        let module = LLVMModuleCreateWithName(c_str!("main"));

        let env = stdlib::stdlib(context, module);
        let ast = parse::Parser::parse(tokens.into_iter(), env, context).unwrap();
        codegen::codegen(ast, context, module);
        LLVMDisposeModule(module);
        LLVMContextDispose(context);
    }
}
