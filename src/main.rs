extern crate llvm_sys;

use llvm_sys::core::{
    LLVMContextCreate, LLVMModuleCreateWithName, LLVMCreateBuilderInContext, LLVMDisposeBuilder, LLVMDisposeModule, LLVMContextDispose, LLVMSetTarget, LLVMVoidTypeInContext,
    LLVMFunctionType, LLVMAddFunction, LLVMAppendBasicBlockInContext, LLVMPositionBuilderAtEnd, LLVMBuildRet, LLVMIntTypeInContext, LLVMConstInt, LLVMPointerType,
    LLVMBuildGlobalStringPtr, LLVMBuildCall,
};
use llvm_sys::bit_writer::LLVMWriteBitcodeToFile;
use std::ptr;

macro_rules! c_str {
    ($s:expr) => (
        concat!($s, "\0").as_ptr() as *const i8
    );
}

fn main() {
    unsafe {
        let context = LLVMContextCreate();
        let module = LLVMModuleCreateWithName(c_str!("main"));
        let builder = LLVMCreateBuilderInContext(context);

        //let void_type = LLVMVoidTypeInContext(context);
        let i8_type = LLVMIntTypeInContext(context, 8);
        let i8_pointer_type = LLVMPointerType(i8_type, 0);
        let i32_type = LLVMIntTypeInContext(context, 32);
        let zero_i32 = LLVMConstInt(i32_type, 0, 1);

        let puts_func_type = LLVMFunctionType(i32_type, [i8_pointer_type].as_ptr() as *mut _, 1, 0);
        let puts_func = LLVMAddFunction(module, c_str!("puts"), puts_func_type);

        let main_func_type = LLVMFunctionType(i32_type, ptr::null_mut(), 0, 0);
        let main_func = LLVMAddFunction(module, c_str!("main"), main_func_type);
        let main_block = LLVMAppendBasicBlockInContext(context, main_func, c_str!("main"));
        LLVMPositionBuilderAtEnd(builder, main_block);

        let hello_world_str = LLVMBuildGlobalStringPtr(builder, c_str!("hello world"), c_str!(""));
        LLVMBuildCall(builder, puts_func, [hello_world_str].as_ptr() as *mut _, 1, c_str!(""));
        LLVMBuildRet(builder, zero_i32);

        LLVMSetTarget(module, c_str!("x86_64-pc-linux-gnu"));
        LLVMWriteBitcodeToFile(module, c_str!("main.bc"));

        LLVMDisposeBuilder(builder);
        LLVMDisposeModule(module);
        LLVMContextDispose(context);
    };
}
