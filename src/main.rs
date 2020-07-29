extern crate im;
extern crate lazy_static;
extern crate llvm_sys;
mod codegen;
mod lex;
mod parse;
mod stdlib;

use llvm_sys::core::{
    LLVMContextCreate, LLVMContextDispose, LLVMDisposeModule, LLVMModuleCreateWithName,
};

use std::env;

macro_rules! c_str {
    ($s:expr) => {
        concat!($s, "\0").as_ptr() as *const i8
    };
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let tokens: Vec<lex::Token> = lex::lex(args[1].clone()).map(|res| res.unwrap()).collect();
    let env = stdlib::stdlib_env();
    let ast = parse::Parser::parse(tokens.into_iter(), env).unwrap();

    unsafe {
        let context = LLVMContextCreate();
        let module = LLVMModuleCreateWithName(c_str!("main"));

        codegen::CodeGen::codegen(ast, stdlib::stdlib_vars(context, module), context, module);

        LLVMDisposeModule(module);
        LLVMContextDispose(context);
    }
}
