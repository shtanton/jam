//use crate::codegen::Value;
use crate::parse::{Env, Type, Variable, TypeId, VariableId, Parser, SuperType, SMTValue, SMTConst, SMTFunction, ValueId};
use im::HashMap as ImHashMap;
use llvm_sys::core::{
    LLVMAddFunction, LLVMAddIncoming, LLVMAppendBasicBlockInContext, LLVMBuildAdd,
    LLVMBuildBitCast, LLVMBuildBr, LLVMBuildCall, LLVMBuildCondBr, LLVMBuildExtractValue,
    LLVMBuildICmp, LLVMBuildPhi, LLVMBuildRet, LLVMBuildSub, LLVMConstInt, LLVMConstNamedStruct,
    LLVMCreateBuilderInContext, LLVMDisposeBuilder, LLVMDumpType, LLVMFunctionType, LLVMGetParam,
    LLVMIntTypeInContext, LLVMMoveBasicBlockAfter, LLVMPointerType, LLVMPositionBuilderAtEnd,
    LLVMStructTypeInContext,
};
use llvm_sys::{LLVMBuilder, LLVMContext, LLVMIntPredicate, LLVMModule, LLVMType, LLVMValue};
use std::collections::HashMap;
use std::ptr;
use std::rc::Rc;

macro_rules! c_str {
    ($s:expr) => {
        concat!($s, "\0").as_ptr() as *const i8
    };
}

pub const INT_ID: TypeId = 0;
pub const BOOL_ID: TypeId = 1;
pub const ADD_TYPE_ID: TypeId = 2;
pub const NEXT_TYPE_ID: TypeId = 3;

pub const ADD_FUNC_ID: VariableId = 0;
pub const SUB_FUNC_ID: VariableId = 1;
pub const INT_TYPE_ID: VariableId = 2;
pub const IF_FUNC_ID: VariableId = 3;
pub const BOOL_TYPE_ID: VariableId = 4;
pub const TRUE_ID: VariableId = 5;
pub const FALSE_ID: VariableId = 6;
pub const EQUAL_FUNC_ID: VariableId = 7;
pub const NEXT_VARIABLE_ID: VariableId = 9;

pub fn stdparser() -> Parser {
    let mut variables = HashMap::new();
    let mut types = HashMap::new();

    types.insert(INT_ID, Type::Primitive {
        instance: true,
        super_type: SuperType::Int,
        assertion: SMTValue::Const(SMTConst::Bool(true)),
    });

    types.insert(ADD_TYPE_ID, Type::Function {
        params: vec![INT_ID, INT_ID],
        ret: INT_ID,
    });

    variables.insert(ADD_FUNC_ID, Variable {
        id: ADD_FUNC_ID,
        typ: ADD_TYPE_ID,
    });

    Parser::new(NEXT_VARIABLE_ID, NEXT_TYPE_ID, variables, types)
}

pub fn stdenv() -> Env {
    let mut env = Env::default();
    env.variables.insert("int".to_string(), ValueId::Type(INT_ID));
    env.variables.insert( "+".to_string(), ValueId::Variable(ADD_FUNC_ID), );
    env
}

/*pub fn stdlib_env() -> Env {
    let mut env = Env::default();
    env.variables.insert(
        "+".to_string(),
        Variable {
            id: ADD_FUNC_ID,
            typ: Type::Function {
                args: vec![Type::Primal(INT_ID), Type::Primal(INT_ID)],
                ret: Box::new(Type::Primal(INT_ID)),
                env: Vec::new(),
            },
        },
    );
    env.variables.insert(
        "-".to_string(),
        Variable {
            id: SUB_FUNC_ID,
            typ: Type::Function {
                args: vec![Type::Primal(INT_ID), Type::Primal(INT_ID)],
                ret: Box::new(Type::Primal(INT_ID)),
                env: Vec::new(),
            },
        },
    );
    env.variables.insert(
        "int".to_string(),
        Variable {
            id: INT_TYPE_ID,
            typ: Type::Type,
        },
    );
    env.variables.insert(
        "bool".to_string(),
        Variable {
            id: BOOL_TYPE_ID,
            typ: Type::Type,
        },
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
        Variable {
            id: TRUE_ID,
            typ: Type::Primal(BOOL_ID),
        },
    );
    env.variables.insert(
        "false".to_string(),
        Variable {
            id: FALSE_ID,
            typ: Type::Primal(BOOL_ID),
        },
    );
    env.variables.insert(
        "=".to_string(),
        Variable {
            id: EQUAL_FUNC_ID,
            typ: Type::Function {
                args: vec![Type::Primal(INT_ID), Type::Primal(INT_ID)],
                ret: Box::new(Type::Primal(BOOL_ID)),
                env: Vec::new(),
            },
        },
    );
    let comptime = stdlib_comptime();
    env.comptime = comptime;
    env
}

fn comptime_add(args: Vec<ComptimeExpr>) -> ComptimeExpr {
    let mut args_iter = args.into_iter();
    match (args_iter.next(), args_iter.next(), args_iter.next()) {
        (Some(ComptimeExpr::Int(lhs)), Some(ComptimeExpr::Int(rhs)), None) => {
            ComptimeExpr::Int(lhs + rhs)
        }
        _ => panic!("comptime_add called incorrectly"),
    }
}

fn comptime_sub(args: Vec<ComptimeExpr>) -> ComptimeExpr {
    let mut args_iter = args.into_iter();
    match (args_iter.next(), args_iter.next(), args_iter.next()) {
        (Some(ComptimeExpr::Int(lhs)), Some(ComptimeExpr::Int(rhs)), None) => {
            ComptimeExpr::Int(lhs - rhs)
        }
        _ => panic!("comptime_sub called incorrectly"),
    }
}

fn stdlib_comptime() -> ImHashMap<u64, ComptimeExpr> {
    let mut values = ImHashMap::new();
    values.insert(ADD_FUNC_ID, ComptimeExpr::Function(Rc::new(comptime_add)));
    values.insert(SUB_FUNC_ID, ComptimeExpr::Function(Rc::new(comptime_sub)));
    values.insert(INT_TYPE_ID, ComptimeExpr::Type(Type::Primal(INT_ID)));
    values
}

unsafe fn func_to_closure(
    context: *mut LLVMContext,
    malloc: *mut LLVMValue,
    builder: *mut LLVMBuilder,
    val: *mut LLVMValue,
    typ: *mut LLVMType,
) -> (*mut LLVMValue, *mut LLVMType) {
    let closure_env_type =
        LLVMStructTypeInContext(context, ptr::null::<LLVMType>() as *mut _, 0, 0);
    let closure_type = LLVMStructTypeInContext(
        context,
        [
            LLVMPointerType(typ, 0),
            LLVMPointerType(closure_env_type, 0),
        ]
        .as_ptr() as *mut _,
        2,
        0,
    );
    let closure_env = LLVMBuildCall(
        builder,
        malloc,
        [LLVMConstInt(LLVMIntTypeInContext(context, 64), 0, 1)].as_ptr() as *mut _,
        1,
        c_str!("env"),
    );
    let closure = LLVMConstNamedStruct(closure_type, [val, closure_env].as_ptr() as *mut _, 2);
    (closure, closure_type)
}*/

/*pub fn stdlib_vars(
    codegen: &crate::codegen::CodeGen,
    main_builder: *mut LLVMBuilder,
) -> ImHashMap<u64, Value> {
    let context = codegen.context;
    let module = codegen.module;
    let malloc = codegen.malloc;
    let mut variables = ImHashMap::default();
    unsafe {
        let builder = LLVMCreateBuilderInContext(context);

        let int_type = LLVMIntTypeInContext(context, 64);
        let bool_type = LLVMIntTypeInContext(context, 1);
        variables.insert(INT_TYPE_ID, Value::Type(int_type));
        variables.insert(BOOL_TYPE_ID, Value::Type(bool_type));

        let empty_env_type = LLVMPointerType(
            LLVMStructTypeInContext(context, ptr::null::<LLVMType>() as *mut _, 0, 0),
            0,
        );
        let empty_env_i8 = LLVMBuildCall(
            main_builder,
            malloc,
            [LLVMConstInt(int_type, 0, 1)].as_ptr() as *mut _,
            1,
            c_str!("env_i8"),
        );
        let empty_env = LLVMBuildBitCast(main_builder, empty_env_i8, empty_env_type, c_str!("env"));
        let byte_ptr = LLVMPointerType(LLVMIntTypeInContext(context, 8), 0);

        let closure_type = |func_type: *mut LLVMType| -> *mut LLVMType {
            LLVMStructTypeInContext(
                context,
                [LLVMPointerType(func_type, 0), byte_ptr].as_ptr() as *mut _,
                2,
                0,
            )
        };

        {
            let add_func_type = LLVMFunctionType(
                int_type,
                [int_type, int_type, empty_env_type].as_ptr() as *mut _,
                3,
                0,
            );
            let add_closure_type = closure_type(add_func_type);
            let add_func = LLVMAddFunction(module, c_str!("add"), add_func_type);
            let add_closure = LLVMConstNamedStruct(
                add_closure_type,
                [add_func, empty_env].as_ptr() as *mut _,
                2,
            );
            let add_block = LLVMAppendBasicBlockInContext(context, add_func, c_str!("add"));
            LLVMPositionBuilderAtEnd(builder, add_block);
            let lhs = LLVMGetParam(add_func, 0);
            let rhs = LLVMGetParam(add_func, 1);
            let result = LLVMBuildAdd(builder, lhs, rhs, c_str!("add"));
            LLVMBuildRet(builder, result);
            variables.insert(ADD_FUNC_ID, Value::Value(add_closure));
        };

        {
            let sub_func_type = LLVMFunctionType(
                int_type,
                [int_type, int_type, empty_env_type].as_ptr() as *mut _,
                2,
                0,
            );
            let sub_closure_type = closure_type(sub_func_type);
            let sub_func = LLVMAddFunction(module, c_str!("sub"), sub_func_type);
            let sub_closure = LLVMConstNamedStruct(
                sub_closure_type,
                [sub_func, empty_env].as_ptr() as *mut _,
                2,
            );
            let sub_block = LLVMAppendBasicBlockInContext(context, sub_func, c_str!("sub"));
            LLVMPositionBuilderAtEnd(builder, sub_block);
            let lhs = LLVMGetParam(sub_func, 0);
            let rhs = LLVMGetParam(sub_func, 1);
            let result = LLVMBuildSub(builder, lhs, rhs, c_str!("sub"));
            LLVMBuildRet(builder, result);
            variables.insert(SUB_FUNC_ID, Value::Value(sub_closure));
        };

        /*{
            let branch_func_type = LLVMFunctionType(int_type, [byte_ptr].as_ptr() as *mut _, 1, 0);
            let branch_closure_type = closure_type(branch_func_type);
            let if_func_type = LLVMFunctionType(
                int_type,
                [
                    bool_type,
                    branch_closure_type,
                    branch_closure_type,
                    empty_env_type,
                ]
                .as_ptr() as *mut _,
                4,
                0,
            );
            let if_closure_type = closure_type(if_func_type);
            let if_func = LLVMAddFunction(module, c_str!("if"), if_func_type);
            let if_closure =
                LLVMConstNamedStruct(if_closure_type, [if_func, empty_env].as_ptr() as *mut _, 2);
            let if_block = LLVMAppendBasicBlockInContext(context, if_func, c_str!("if"));
            LLVMPositionBuilderAtEnd(builder, if_block);
            let cond = LLVMGetParam(if_func, 0);
            let then_closure = LLVMGetParam(if_func, 1);
            let then_func = LLVMBuildExtractValue(builder, then_closure, 0, c_str!("then_fn"));
            let else_closure = LLVMGetParam(if_func, 2);
            let else_func = LLVMBuildExtractValue(builder, else_closure, 0, c_str!("else_fn"));
            let then_branch = LLVMAppendBasicBlockInContext(context, if_func, c_str!("if_branch"));
            let else_branch =
                LLVMAppendBasicBlockInContext(context, if_func, c_str!("else_branch"));
            let end_block = LLVMAppendBasicBlockInContext(context, if_func, c_str!("end_block"));
            LLVMBuildCondBr(builder, cond, then_branch, else_branch);
            LLVMPositionBuilderAtEnd(builder, then_branch);
            let then_env = LLVMBuildExtractValue(builder, then_closure, 1, c_str!("then_env"));
            let then_result = LLVMBuildCall(
                builder,
                then_func,
                [then_env].as_ptr() as *mut _,
                1,
                c_str!("if_call"),
            );
            LLVMBuildBr(builder, end_block);
            LLVMMoveBasicBlockAfter(else_branch, then_branch);
            LLVMPositionBuilderAtEnd(builder, else_branch);
            let else_env = LLVMBuildExtractValue(builder, else_closure, 1, c_str!("else_env"));
            let else_result = LLVMBuildCall(
                builder,
                else_func,
                [else_env].as_ptr() as *mut _,
                1,
                c_str!("else_call"),
            );
            LLVMBuildBr(builder, end_block);
            LLVMMoveBasicBlockAfter(end_block, else_branch);
            LLVMPositionBuilderAtEnd(builder, end_block);
            let phi = LLVMBuildPhi(builder, int_type, c_str!("conditional_result"));
            LLVMAddIncoming(
                phi,
                [then_result, else_result].as_ptr() as *mut _,
                [then_branch, else_branch].as_ptr() as *mut _,
                2,
            );
            LLVMBuildRet(builder, phi);
            variables.insert(IF_FUNC_TYPE_ID, Value::Type(if_closure_type));
            variables.insert(IF_FUNC_ID, Value::Value(if_closure));
            variables.insert(IF_BRANCH_TYPE_ID, Value::Type(branch_closure_type));
        };*/

        {
            let true_val = LLVMConstInt(bool_type, 1, 1);
            let false_val = LLVMConstInt(bool_type, 0, 1);
            variables.insert(TRUE_ID, Value::Value(true_val));
            variables.insert(FALSE_ID, Value::Value(false_val));
        };

        {
            let equal_func_type = LLVMFunctionType(
                bool_type,
                [int_type, int_type, empty_env_type].as_ptr() as *mut _,
                3,
                0,
            );
            let equal_closure_type = closure_type(equal_func_type);
            let equal_func = LLVMAddFunction(module, c_str!("equal"), equal_func_type);
            let equal_closure = LLVMConstNamedStruct(
                equal_closure_type,
                [equal_func, empty_env].as_ptr() as *mut _,
                2,
            );
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
            variables.insert(EQUAL_FUNC_ID, Value::Value(equal_closure));
        };
        LLVMDisposeBuilder(builder);
    };
    variables
}*/
