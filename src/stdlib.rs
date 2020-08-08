use crate::codegen::Value;
use crate::parse::{Env, Type, Variable};
use im::HashMap;
use llvm_sys::core::{
    LLVMAddFunction, LLVMAddIncoming, LLVMAppendBasicBlockInContext, LLVMBuildAdd, LLVMBuildBr,
    LLVMBuildCall, LLVMBuildCondBr, LLVMBuildICmp, LLVMBuildPhi, LLVMBuildRet, LLVMBuildSub,
    LLVMConstInt, LLVMCreateBuilderInContext, LLVMDisposeBuilder, LLVMFunctionType, LLVMGetParam,
    LLVMIntTypeInContext, LLVMMoveBasicBlockAfter, LLVMPointerType, LLVMPositionBuilderAtEnd,
};
use llvm_sys::{LLVMContext, LLVMIntPredicate, LLVMModule, LLVMType, LLVMValue};
use std::ptr;

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
pub const IF_FUNC_TYPE_ID: u64 = 5;
pub const IF_FUNC_ID: u64 = 6;
pub const IF_BRANCH_TYPE_ID: u64 = 7;
pub const BOOL_TYPE_ID: u64 = 8;
pub const TRUE_ID: u64 = 9;
pub const FALSE_ID: u64 = 10;
pub const EQUAL_FUNC_ID: u64 = 11;
pub const EQUAL_FUNC_TYPE_ID: u64 = 12;

pub const LOWEST_USER_VAR_ID: u64 = 13;

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
    env.variables.insert(
        "bool".to_string(),
        Variable::Type(Type::Other(BOOL_TYPE_ID)),
    );
    env.variables.insert(
        "if".to_string(),
        Variable::Value {
            id: IF_FUNC_ID,
            typ: Type::Function {
                id: IF_FUNC_TYPE_ID,
                args: vec![
                    Type::Other(BOOL_TYPE_ID),
                    Type::Function {
                        id: IF_BRANCH_TYPE_ID,
                        args: Vec::new(),
                        ret: Box::new(Type::Other(INT_TYPE_ID)),
                    },
                    Type::Function {
                        id: IF_BRANCH_TYPE_ID,
                        args: Vec::new(),
                        ret: Box::new(Type::Other(INT_TYPE_ID)),
                    },
                ],
                ret: Box::new(Type::Other(INT_TYPE_ID)),
            },
        },
    );
    env.variables.insert(
        "true".to_string(),
        Variable::Value {
            id: TRUE_ID,
            typ: Type::Other(BOOL_TYPE_ID),
        },
    );
    env.variables.insert(
        "false".to_string(),
        Variable::Value {
            id: FALSE_ID,
            typ: Type::Other(BOOL_TYPE_ID),
        },
    );
    env.variables.insert(
        "=".to_string(),
        Variable::Value {
            id: EQUAL_FUNC_ID,
            typ: Type::Function {
                id: EQUAL_FUNC_TYPE_ID,
                args: vec![Type::Other(INT_TYPE_ID), Type::Other(INT_TYPE_ID)],
                ret: Box::new(Type::Other(BOOL_TYPE_ID)),
            },
        },
    );
    env
}

pub fn stdlib_vars(context: *mut LLVMContext, module: *mut LLVMModule) -> HashMap<u64, Value> {
    let mut variables = HashMap::default();
    unsafe {
        let builder = LLVMCreateBuilderInContext(context);

        let int_type = LLVMIntTypeInContext(context, 64);
        let bool_type = LLVMIntTypeInContext(context, 1);
        variables.insert(INT_TYPE_ID, Value::Type(int_type));
        variables.insert(BOOL_TYPE_ID, Value::Type(bool_type));

        {
            let add_func_type =
                LLVMFunctionType(int_type, [int_type, int_type].as_ptr() as *mut _, 2, 0);
            let add_func = LLVMAddFunction(module, c_str!("add"), add_func_type);
            let add_block = LLVMAppendBasicBlockInContext(context, add_func, c_str!("add"));
            LLVMPositionBuilderAtEnd(builder, add_block);
            let lhs = LLVMGetParam(add_func, 0);
            let rhs = LLVMGetParam(add_func, 1);
            let result = LLVMBuildAdd(builder, lhs, rhs, c_str!("add"));
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
            let result = LLVMBuildSub(builder, lhs, rhs, c_str!("sub"));
            LLVMBuildRet(builder, result);
            variables.insert(SUB_FUNC_ID, Value::Value(sub_func));
            variables.insert(SUB_FUNC_TYPE_ID, Value::Type(sub_func_type));
        };

        {
            let if_branch_type =
                LLVMFunctionType(int_type, ptr::null::<LLVMType>() as *mut _, 0, 0);
            let if_branch_type_ptr = LLVMPointerType(if_branch_type, 0);
            let if_func_type = LLVMFunctionType(
                int_type,
                [bool_type, if_branch_type_ptr, if_branch_type_ptr].as_ptr() as *mut _,
                3,
                0,
            );
            let if_func = LLVMAddFunction(module, c_str!("if"), if_func_type);
            let if_block = LLVMAppendBasicBlockInContext(context, if_func, c_str!("if"));
            LLVMPositionBuilderAtEnd(builder, if_block);
            let cond = LLVMGetParam(if_func, 0);
            let if_branch_val = LLVMGetParam(if_func, 1);
            let else_branch_val = LLVMGetParam(if_func, 2);
            let if_branch = LLVMAppendBasicBlockInContext(context, if_func, c_str!("if_branch"));
            let else_branch =
                LLVMAppendBasicBlockInContext(context, if_func, c_str!("else_branch"));
            let end_block = LLVMAppendBasicBlockInContext(context, if_func, c_str!("end_block"));
            LLVMBuildCondBr(builder, cond, if_branch, else_branch);
            LLVMPositionBuilderAtEnd(builder, if_branch);
            let if_result = LLVMBuildCall(
                builder,
                if_branch_val,
                ptr::null::<LLVMValue>() as *mut _,
                0,
                c_str!("if_call"),
            );
            LLVMBuildBr(builder, end_block);
            LLVMMoveBasicBlockAfter(else_branch, if_branch);
            LLVMPositionBuilderAtEnd(builder, else_branch);
            let else_result = LLVMBuildCall(
                builder,
                else_branch_val,
                ptr::null::<LLVMValue>() as *mut _,
                0,
                c_str!("else_call"),
            );
            LLVMBuildBr(builder, end_block);
            LLVMMoveBasicBlockAfter(end_block, else_branch);
            LLVMPositionBuilderAtEnd(builder, end_block);
            let phi = LLVMBuildPhi(builder, int_type, c_str!("conditional_result"));
            LLVMAddIncoming(
                phi,
                [if_result, else_result].as_ptr() as *mut _,
                [if_branch, else_branch].as_ptr() as *mut _,
                2,
            );
            LLVMBuildRet(builder, phi);
            variables.insert(IF_FUNC_TYPE_ID, Value::Type(if_func_type));
            variables.insert(IF_FUNC_ID, Value::Value(if_func));
            variables.insert(IF_BRANCH_TYPE_ID, Value::Type(if_branch_type));
        };

        {
            let true_val = LLVMConstInt(bool_type, 1, 1);
            let false_val = LLVMConstInt(bool_type, 0, 1);
            variables.insert(TRUE_ID, Value::Value(true_val));
            variables.insert(FALSE_ID, Value::Value(false_val));
        };

        {
            let equal_func_type =
                LLVMFunctionType(bool_type, [int_type, int_type].as_ptr() as *mut _, 2, 0);
            let equal_func = LLVMAddFunction(module, c_str!("equal"), equal_func_type);
            let equal_block = LLVMAppendBasicBlockInContext(context, equal_func, c_str!("equal"));
            LLVMPositionBuilderAtEnd(builder, equal_block);
            let lhs = LLVMGetParam(equal_func, 0);
            let rhs = LLVMGetParam(equal_func, 1);
            let result = LLVMBuildICmp(
                builder,
                LLVMIntPredicate::LLVMIntEQ,
                lhs,
                rhs,
                c_str!("int_eq"),
            );
            LLVMBuildRet(builder, result);
            variables.insert(EQUAL_FUNC_ID, Value::Value(equal_func));
            variables.insert(EQUAL_FUNC_TYPE_ID, Value::Type(equal_func_type));
        };
        LLVMDisposeBuilder(builder);
    };
    variables
}
