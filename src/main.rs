extern crate llvm_sys;
extern crate lazy_static;
mod lex;

use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();

    let tokens: Vec<lex::Token> = lex::lex(args[1].clone()).map(|res| res.unwrap()).collect();

    println!("{:?}", tokens);
}
