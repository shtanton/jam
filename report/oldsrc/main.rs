extern crate im;
extern crate llvm_sys;
extern crate z3;
mod codegen;
mod lambda_lift;
mod semantic;
mod smt;
mod syntax;
mod thunk;
mod to_z3;

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

  let ast = syntax::parse(&source).unwrap();
  let labelled_ast = semantic::check(ast).unwrap();
  codegen::codegen(labelled_ast, c_str!("main.bc"));
}
