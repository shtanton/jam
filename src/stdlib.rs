use crate::codegen::Value;
use crate::parse::{Env, Type, Variable};
use im::HashMap;
use llvm_sys::core::{
    LLVMAddFunction, LLVMAppendBasicBlockInContext, LLVMBuildAdd, LLVMBuildRet, LLVMBuildSub,
    LLVMCreateBuilderInContext, LLVMFunctionType, LLVMGetParam, LLVMIntTypeInContext,
    LLVMPositionBuilderAtEnd,
};
use llvm_sys::{LLVMContext, LLVMModule};

macro_rules! c_str {
    ($s:expr) => {
        concat!($s, "\0").as_ptr() as *const i8
    };
}

pub const ADD_FUNC_ID: u64 = 0;
pub const SUB_FUNC_ID: u64 = 1;
pub const INT_TYPE_ID: u64 = 2;
pub const ADD_FUNC_TYPE_ID: u64 = 3;
pub const SUB_FUNC_TYPE_ID: u64 = 4;

pub const LOWEST_USER_VAR_ID: u64 = 5;

pub fn stdlib_env() -> Env {
    let mut env = Env::default();
    env.variables.insert(
        "+".to_string(),
        Variable::Value {
            id: ADD_FUNC_ID,
            typ: Type::Function {
                id: ADD_FUNC_TYPE_ID,
                args: vec![Type::Other(INT_TYPE_ID), Type::Other(INT_TYPE_ID)],
                ret: Box::new(Type::Other(INT_TYPE_ID)),
            },
        },
    );
    env.variables.insert(
        "-".to_string(),
        Variable::Value {
            id: SUB_FUNC_ID,
            typ: Type::Function {
                id: SUB_FUNC_TYPE_ID,
                args: vec![Type::Other(INT_TYPE_ID), Type::Other(INT_TYPE_ID)],
                ret: Box::new(Type::Other(INT_TYPE_ID)),
            },
        },
    );
    env.variables
        .insert("int".to_string(), Variable::Type(Type::Other(INT_TYPE_ID)));
    env
}

pub fn stdlib_vars(context: *mut LLVMContext, module: *mut LLVMModule) -> HashMap<u64, Value> {
    let mut variables = HashMap::default();
    unsafe {
        let builder = LLVMCreateBuilderInContext(context);

        let int_type = LLVMIntTypeInContext(context, 64);
        variables.insert(INT_TYPE_ID, Value::Type(int_type));

        {
            let add_func_type =
                LLVMFunctionType(int_type, [int_type, int_type].as_ptr() as *mut _, 2, 0);
            let add_func = LLVMAddFunction(module, c_str!("add"), add_func_type);
            let add_block = LLVMAppendBasicBlockInContext(context, add_func, c_str!("add"));
            LLVMPositionBuilderAtEnd(builder, add_block);
            let lhs = LLVMGetParam(add_func, 0);
            let rhs = LLVMGetParam(add_func, 1);
            let result = LLVMBuildAdd(builder, lhs, rhs, c_str!("test"));
            LLVMBuildRet(builder, result);
            variables.insert(ADD_FUNC_ID, Value::Value(add_func));
            variables.insert(ADD_FUNC_TYPE_ID, Value::Type(add_func_type));
        };

        {
            let sub_func_type =
                LLVMFunctionType(int_type, [int_type, int_type].as_ptr() as *mut _, 2, 0);
            let sub_func = LLVMAddFunction(module, c_str!("sub"), sub_func_type);
            let sub_block = LLVMAppendBasicBlockInContext(context, sub_func, c_str!("sub"));
            LLVMPositionBuilderAtEnd(builder, sub_block);
            let lhs = LLVMGetParam(sub_func, 0);
            let rhs = LLVMGetParam(sub_func, 1);
            let result = LLVMBuildSub(builder, lhs, rhs, c_str!("test"));
            LLVMBuildRet(builder, result);
            variables.insert(SUB_FUNC_ID, Value::Value(sub_func));
            variables.insert(SUB_FUNC_TYPE_ID, Value::Type(sub_func_type));
        };
    };
    variables
}
