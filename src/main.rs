extern crate im;
extern crate lazy_static;
extern crate llvm_sys;
//mod codegen;
//mod lex;
//mod parse;
//mod stdlib;
mod syntax;
mod semantic;

//use llvm_sys::core::{
//LLVMContextCreate, LLVMContextDispose, LLVMDisposeModule, LLVMModuleCreateWithName,
//};
use std::env;
use std::fs::File;
use std::io::Read;

macro_rules! c_str {
    ($s:expr) => {
        concat!($s, "\0").as_ptr() as *const i8
    };
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let input_path = if let Some(path) = args.get(1) {
        path
    } else {
        println!("Usage:");
        println!("jam source.jam");
        return;
    };
    let mut source = String::new();
    let mut input_file = File::open(input_path).expect("Error opening file");
    input_file
        .read_to_string(&mut source)
        .expect("Error reading file");

    //let tokens: Vec<lex::Token> = lex::lex(source).map(|res| res.unwrap()).collect();
    //let ast = stdlib::stdparser()
    //.parse(tokens.into_iter(), stdlib::stdenv())
    //.unwrap();
    let ast = syntax::parse(&source).unwrap();
    println!("{:#?}", ast);

    /*unsafe {
        let context = LLVMContextCreate();
        let module = LLVMModuleCreateWithName(c_str!("main"));

        codegen::CodeGen::codegen(ast, context, module);

        LLVMDisposeModule(module);
        LLVMContextDispose(context);
    }*/
}
