use crate::parse::{Expr, ExprKind, Type};
use im::HashMap;
use llvm_sys::bit_writer::LLVMWriteBitcodeToFile;
use llvm_sys::core::{
    LLVMAddFunction, LLVMAppendBasicBlockInContext, LLVMBuildCall, LLVMBuildRet, LLVMConstInt,
    LLVMCreateBuilderInContext, LLVMDisposeBuilder, LLVMFunctionType, LLVMIntTypeInContext,
    LLVMPositionBuilderAtEnd, LLVMSetTarget, LLVMGetParam, LLVMDumpType,
};
use llvm_sys::{LLVMBuilder, LLVMContext, LLVMModule, LLVMType, LLVMValue};
use std::ptr;

macro_rules! c_str {
    ($s:expr) => {
        concat!($s, "\0").as_ptr() as *const i8
    };
}

#[derive(Clone)]
pub enum Value {
    Value(*mut LLVMValue),
    Type(*mut LLVMType),
}

impl Value {
    fn typ(&self) -> Result<*mut LLVMType, String> {
        if let Value::Type(typ) = self {
            Ok(*typ)
        } else {
            Err("Value is not a type".to_string())
        }
    }

    fn value(&self) -> Result<*mut LLVMValue, String> {
        if let Value::Value(value) = self {
            Ok(*value)
        } else {
            Err("Type is not a value".to_string())
        }
    }
}

pub struct CodeGen {
    variables: HashMap<u64, Value>,
    module: *mut LLVMModule,
    context: *mut LLVMContext,
}

impl CodeGen {
    fn get_type(&self, typ: &Type) -> Result<*mut LLVMType, String> {
        match typ {
            Type::Other(id) => self.variables.get(id).ok_or("Type not found".to_string())?.typ(),
            Type::Function {id, args, ret} => {
                if let Some(typ) = self.variables.get(id) {
                    typ.typ()
                } else {
                    let llvm_args: Result<Vec<_>, _> = args.iter().map(|arg| self.get_type(arg)).collect();
                    let llvm_args = llvm_args?;
                    let llvm_ret = self.get_type(ret.as_ref())?;
                    let llvm_typ = unsafe {
                        LLVMFunctionType(llvm_ret, llvm_args.as_ptr() as *mut _, args.len() as u32, 0)
                    };
                    Ok(llvm_typ)
                }
            }
        }
    }

    fn get_variable_value(&self, value: u64) -> Result<*mut LLVMValue, String> {
        self.variables
            .get(&value)
            .ok_or("Variable not found".to_string())?
            .value()
    }

    fn gen_expr(
        &mut self,
        expr: Expr,
        builder: *mut LLVMBuilder,
    ) -> Result<*mut LLVMValue, String> {
        match expr.kind {
            ExprKind::IntegerLiteral(num) => {
                Ok(unsafe { LLVMConstInt(self.get_type(&expr.typ)?, num as u64, 1) })
            }
            ExprKind::Identifier(id) => {
                let value = self.get_variable_value(id)?;
                Ok(value)
            }
            ExprKind::FunctionCall {
                function,
                params: param_exprs,
            } => {
                let params: Result<Vec<*mut LLVMValue>, String> = param_exprs
                    .into_iter()
                    .map(|param| self.gen_expr(param, builder))
                    .collect();
                let params = params?;
                let len = params.len() as u32;
                let value = unsafe {
                    LLVMBuildCall(
                        builder,
                        self.get_variable_value(function)?,
                        params.as_ptr() as *mut _,
                        len,
                        c_str!("test"),
                    )
                };
                Ok(value)
            }
            ExprKind::Let { defs, body } => {
                for (id, expr) in defs.into_iter() {
                    let value = Value::Value(self.gen_expr(expr, builder)?);
                    self.variables.insert(id, value);
                }
                let value = self.gen_expr(*body, builder)?;
                Ok(value)
            }
            ExprKind::Fn { params, body } => {
                let typ = self.get_type(&expr.typ)?;
                let fun = unsafe {
                    let fun = LLVMAddFunction(self.module, c_str!("fun"), typ);
                    let block = LLVMAppendBasicBlockInContext(self.context, fun, c_str!("fun"));
                    let fun_builder = LLVMCreateBuilderInContext(self.context);
                    LLVMPositionBuilderAtEnd(fun_builder, block);
                    for (index, param) in params.into_iter().enumerate() {
                        let value = LLVMGetParam(fun, index as u32);
                        self.variables.insert(param, Value::Value(value));
                    }
                    let return_expr = self.gen_expr(*body, fun_builder)?;
                    LLVMBuildRet(fun_builder, return_expr);
                    fun
                };
                Ok(fun)
            }
        }
    }

    pub fn codegen(
        ast: Expr,
        variables: HashMap<u64, Value>,
        context: *mut LLVMContext,
        module: *mut LLVMModule,
    ) {
        let mut codegen = CodeGen { variables, module, context };
        unsafe {
            let builder = LLVMCreateBuilderInContext(context);

            let i32_type = LLVMIntTypeInContext(context, 32);

            //let puts_func_type = LLVMFunctionType(i32_type, [i8_pointer_type].as_ptr() as *mut _, 1, 0);
            //let puts_func = LLVMAddFunction(module, c_str!("puts"), puts_func_type);

            let main_func_type = LLVMFunctionType(i32_type, ptr::null_mut(), 0, 0);
            let main_func = LLVMAddFunction(module, c_str!("main"), main_func_type);
            let main_block = LLVMAppendBasicBlockInContext(context, main_func, c_str!("main"));
            LLVMPositionBuilderAtEnd(builder, main_block);

            //let hello_world_str = LLVMBuildGlobalStringPtr(builder, c_str!("hello world"), c_str!(""));
            //LLVMBuildCall(builder, puts_func, [hello_world_str].as_ptr() as *mut _, 1, c_str!(""));
            LLVMBuildRet(builder, codegen.gen_expr(ast, builder).unwrap());

            LLVMSetTarget(module, c_str!("x86_64-pc-linux-gnu"));
            LLVMWriteBitcodeToFile(module, c_str!("main.bc"));

            LLVMDisposeBuilder(builder);
        };
    }
}
