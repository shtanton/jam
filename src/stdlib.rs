use llvm_sys::{LLVMContext, LLVMModule};
use llvm_sys::core::{
    LLVMIntTypeInContext, LLVMFunctionType, LLVMAddFunction, LLVMCreateBuilderInContext, LLVMAppendBasicBlockInContext, LLVMPositionBuilderAtEnd,
    LLVMBuildRet, LLVMConstInt, LLVMBuildAdd, LLVMGetParam, LLVMBuildSub
};
use crate::parse::{Env};

macro_rules! c_str {
    ($s:expr) => (
        concat!($s, "\0").as_ptr() as *const i8
    );
}

pub fn stdlib(context: *mut LLVMContext, module: *mut LLVMModule) -> Env<'static> {
    let mut env = Env::default();

    unsafe {
        let builder = LLVMCreateBuilderInContext(context);

        let i32_type = LLVMIntTypeInContext(context, 32);

        let add_func = {
            let add_func_type = LLVMFunctionType(i32_type, [i32_type, i32_type].as_ptr() as *mut _, 2, 0);
            let add_func = LLVMAddFunction(module, c_str!("add"), add_func_type);
            let add_block = LLVMAppendBasicBlockInContext(context, add_func, c_str!("add"));
            LLVMPositionBuilderAtEnd(builder, add_block);
            let lhs = LLVMGetParam(add_func, 0);
            let rhs = LLVMGetParam(add_func, 1);
            let result = LLVMBuildAdd(builder, lhs, rhs, c_str!("test"));
            LLVMBuildRet(builder, result);
            add_func
        };
        env.variables.insert("+", add_func);

        let sub_func = {
            let sub_func_type = LLVMFunctionType(i32_type, [i32_type, i32_type].as_ptr() as *mut _, 2, 0);
            let sub_func = LLVMAddFunction(module, c_str!("sub"), sub_func_type);
            let sub_block = LLVMAppendBasicBlockInContext(context, sub_func, c_str!("sub"));
            LLVMPositionBuilderAtEnd(builder, sub_block);
            let lhs = LLVMGetParam(sub_func, 0);
            let rhs = LLVMGetParam(sub_func, 1);
            let result = LLVMBuildSub(builder, lhs, rhs, c_str!("test"));
            LLVMBuildRet(builder, result);
            sub_func
        };
        env.variables.insert("-", sub_func);
    };

    env
}
