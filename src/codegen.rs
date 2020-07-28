use llvm_sys::core::{
    LLVMModuleCreateWithName, LLVMCreateBuilderInContext, LLVMDisposeBuilder, LLVMDisposeModule, LLVMSetTarget, LLVMVoidTypeInContext,
    LLVMFunctionType, LLVMAddFunction, LLVMAppendBasicBlockInContext, LLVMPositionBuilderAtEnd, LLVMBuildRet, LLVMIntTypeInContext, LLVMConstInt, LLVMPointerType,
    LLVMBuildGlobalStringPtr, LLVMBuildCall,
};
use llvm_sys::bit_writer::LLVMWriteBitcodeToFile;
use llvm_sys::{LLVMBuilder, LLVMContext, LLVMValue, LLVMModule};
use std::ptr;
use crate::parse::{Expr, ExprKind};

macro_rules! c_str {
    ($s:expr) => (
        concat!($s, "\0").as_ptr() as *const i8
    );
}

fn gen_expr(expr: Expr, builder: *mut LLVMBuilder) -> Result<*mut LLVMValue, String> {
    match expr.kind {
        ExprKind::IntegerLiteral(num) => {
            Ok(unsafe {LLVMConstInt(expr.typ, num as u64, 1)})
        }
        ExprKind::Identifier(_) => {
            Err("identifiers as expressions isn't implemented yet".to_string())
        }
        ExprKind::FunctionCall {
            function,
            params: param_exprs,
        } => {
            let params: Result<Vec<*mut LLVMValue>, String> = param_exprs.into_iter().map(|param| gen_expr(param, builder)).collect();
            let params = params?;
            let len = params.len() as u32;
            let value = unsafe {
                LLVMBuildCall(builder, function, params.as_ptr() as *mut _, len, c_str!("test"))
            };
            Ok(value)
        }
    }
}

pub fn codegen(ast: Expr, context: *mut LLVMContext, module: *mut LLVMModule) {
    unsafe {
        let builder = LLVMCreateBuilderInContext(context);

        //let void_type = LLVMVoidTypeInContext(context);
        //let i8_type = LLVMIntTypeInContext(context, 8);
        //let i8_pointer_type = LLVMPointerType(i8_type, 0);
        let i32_type = LLVMIntTypeInContext(context, 32);
        let zero_i32 = LLVMConstInt(i32_type, 0, 1);

        //let puts_func_type = LLVMFunctionType(i32_type, [i8_pointer_type].as_ptr() as *mut _, 1, 0);
        //let puts_func = LLVMAddFunction(module, c_str!("puts"), puts_func_type);

        let main_func_type = LLVMFunctionType(i32_type, ptr::null_mut(), 0, 0);
        let main_func = LLVMAddFunction(module, c_str!("main"), main_func_type);
        let main_block = LLVMAppendBasicBlockInContext(context, main_func, c_str!("main"));
        LLVMPositionBuilderAtEnd(builder, main_block);

        //let hello_world_str = LLVMBuildGlobalStringPtr(builder, c_str!("hello world"), c_str!(""));
        //LLVMBuildCall(builder, puts_func, [hello_world_str].as_ptr() as *mut _, 1, c_str!(""));
        LLVMBuildRet(builder, gen_expr(ast, builder).unwrap());

        LLVMSetTarget(module, c_str!("x86_64-pc-linux-gnu"));
        LLVMWriteBitcodeToFile(module, c_str!("main.bc"));

        LLVMDisposeBuilder(builder);
    };
}
