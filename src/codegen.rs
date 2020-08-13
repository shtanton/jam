use crate::parse::{Expr, ExprKind, Type};
use im::HashMap;
use llvm_sys::bit_writer::LLVMWriteBitcodeToFile;
use llvm_sys::core::{
    LLVMAddAttributeAtIndex, LLVMAddFunction, LLVMAppendBasicBlockInContext, LLVMBuildCall,
    LLVMBuildExtractValue, LLVMBuildInsertValue, LLVMBuildRet, LLVMConstInt, LLVMConstNamedStruct,
    LLVMCreateBuilderInContext, LLVMCreateStringAttribute, LLVMDisposeBuilder, LLVMDumpModule,
    LLVMDumpValue, LLVMFunctionType, LLVMGetElementAsConstant, LLVMGetParam, LLVMGetUndef,
    LLVMIntTypeInContext, LLVMPointerType, LLVMPositionBuilderAtEnd, LLVMSetTarget,
    LLVMStructTypeInContext, LLVMVoidTypeInContext,
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

#[derive(Clone)]
struct Env {
    variables: HashMap<u64, Value>,
}

pub struct CodeGen {
    //variables: HashMap<u64, Value>,
    pub module: *mut LLVMModule,
    pub context: *mut LLVMContext,
    pub malloc: *mut LLVMValue,
}

impl CodeGen {
    unsafe fn build_malloc(&self, builder: *mut LLVMBuilder, size: u64) -> *mut LLVMValue {
        LLVMBuildCall(
            builder,
            self.malloc,
            [LLVMConstInt(
                LLVMIntTypeInContext(self.context, 64),
                size,
                1,
            )]
            .as_ptr() as *mut _,
            1,
            c_str!("malloc"),
        )
    }

    fn get_type(&self, typ: &Type, env: &Env) -> Result<*mut LLVMType, String> {
        match typ {
            Type::Other(id) => env
                .variables
                .get(id)
                .ok_or("Type not found".to_string())?
                .typ(),
            Type::Function { id, args, ret } => {
                if let Some(typ) = env.variables.get(id) {
                    typ.typ()
                } else {
                    let llvm_args: Result<Vec<_>, String> = args
                        .iter()
                        .map(|arg| {
                            if arg.is_function() {
                                unsafe {
                                    let typ = self.get_type(arg, env)?;
                                    Ok(LLVMPointerType(typ, 0))
                                }
                            } else {
                                self.get_type(arg, env)
                            }
                        })
                        .collect();
                    let mut llvm_args = llvm_args?;
                    unsafe {
                        llvm_args.push(LLVMPointerType(LLVMIntTypeInContext(self.context, 8), 0));
                    };
                    let llvm_ret = self.get_type(ret.as_ref(), env)?;
                    let llvm_typ = unsafe {
                        LLVMFunctionType(
                            llvm_ret,
                            llvm_args.as_ptr() as *mut _,
                            args.len() as u32 + 1,
                            0,
                        )
                    };
                    Ok(llvm_typ)
                }
            }
        }
    }

    fn get_variable_value(&self, value: u64, env: &Env) -> Result<*mut LLVMValue, String> {
        env.variables
            .get(&value)
            .ok_or("Variable not found".to_string())?
            .value()
    }

    fn gen_expr(
        &mut self,
        expr: Expr,
        builder: *mut LLVMBuilder,
        env: &Env,
        my_id: Option<u64>,
    ) -> Result<*mut LLVMValue, String> {
        println!("{:?}", expr);
        match expr.kind {
            ExprKind::IntegerLiteral(num) => {
                Ok(unsafe { LLVMConstInt(self.get_type(&expr.typ, env)?, num as u64, 1) })
            }
            ExprKind::Identifier(id) => {
                let value = self.get_variable_value(id, env)?;
                Ok(value)
            }
            ExprKind::FunctionCall {
                function,
                params: param_exprs,
            } => {
                let params: Result<Vec<*mut LLVMValue>, String> = param_exprs
                    .into_iter()
                    .map(|param| self.gen_expr(param, builder, env, None))
                    .collect();
                let mut params = params?;
                let closure = self.get_variable_value(function, env)?;
                let value = unsafe {
                    LLVMDumpValue(closure);
                    println!("");
                    let function =
                        LLVMBuildExtractValue(builder, closure, 0, c_str!("fun_from_closure"));
                    println!("Extracted function");
                    let env = LLVMBuildExtractValue(builder, closure, 1, c_str!("env"));
                    params.push(env);
                    println!("About to build call");
                    LLVMBuildCall(
                        builder,
                        function,
                        params.as_ptr() as *mut _,
                        params.len() as u32,
                        c_str!("call"),
                    )
                };
                Ok(value)
            }
            ExprKind::Let { defs, body } => {
                let mut new_env = env.clone();
                for (id, expr) in defs.into_iter() {
                    let value = Value::Value(self.gen_expr(expr, builder, &new_env, Some(id))?);
                    new_env.variables.insert(id, value);
                }
                let value = self.gen_expr(*body, builder, &new_env, None)?;
                Ok(value)
            }
            ExprKind::Fn { params, body } => {
                let typ = self.get_type(&expr.typ, env)?;
                let closure = unsafe {
                    let func = LLVMAddFunction(self.module, c_str!("fn"), typ);
                    let mut env = env.clone();
                    if let Some(id) = my_id {
                        env.variables.insert(id, Value::Value(func));
                    }
                    let block = LLVMAppendBasicBlockInContext(self.context, func, c_str!("fn"));
                    let func_builder = LLVMCreateBuilderInContext(self.context);
                    LLVMPositionBuilderAtEnd(func_builder, block);
                    for (index, id) in params.into_iter().enumerate() {
                        let value = LLVMGetParam(func, index as u32);
                        env.variables.insert(id, Value::Value(value));
                    }
                    let return_expr = self.gen_expr(*body, func_builder, &env, None)?;
                    LLVMBuildRet(func_builder, return_expr);
                    LLVMDisposeBuilder(func_builder);
                    let env_type = LLVMPointerType(LLVMIntTypeInContext(self.context, 8), 0);
                    let closure_env = self.build_malloc(builder, 0);
                    let closure_type = LLVMStructTypeInContext(
                        self.context,
                        [LLVMPointerType(typ, 0), env_type].as_ptr() as *mut _,
                        2,
                        0,
                    );
                    let closure_without_env = LLVMConstNamedStruct(
                        closure_type,
                        [func, LLVMGetUndef(env_type)].as_ptr() as *mut _,
                        2,
                    );
                    let closure = LLVMBuildInsertValue(
                        builder,
                        closure_without_env,
                        closure_env,
                        1,
                        c_str!("closure"),
                    );
                    closure
                };
                Ok(closure)
            }
        }
    }

    pub fn codegen(ast: Expr, context: *mut LLVMContext, module: *mut LLVMModule) {
        unsafe {
            let builder = LLVMCreateBuilderInContext(context);

            //let puts_func_type = LLVMFunctionType(i32_type, [i8_pointer_type].as_ptr() as *mut _, 1, 0);
            //let puts_func = LLVMAddFunction(module, c_str!("puts"), puts_func_type);

            let gc_init_type =
                LLVMFunctionType(LLVMVoidTypeInContext(context), ptr::null_mut(), 0, 0);
            let gc_init = LLVMAddFunction(module, c_str!("GC_init"), gc_init_type);
            let malloc_type = LLVMFunctionType(
                LLVMPointerType(LLVMIntTypeInContext(context, 8), 0),
                [LLVMIntTypeInContext(context, 64)].as_ptr() as *mut _,
                1,
                0,
            );
            let malloc = LLVMAddFunction(module, c_str!("GC_malloc"), malloc_type);
            let noalias = LLVMCreateStringAttribute(context, c_str!("noalias"), 7, c_str!(""), 0);
            LLVMAddAttributeAtIndex(malloc, 0, noalias);

            let mut codegen = CodeGen {
                module,
                context,
                malloc,
            };

            let main_func_type =
                LLVMFunctionType(LLVMIntTypeInContext(context, 64), ptr::null_mut(), 0, 0);
            let main_func = LLVMAddFunction(module, c_str!("main"), main_func_type);
            let main_block = LLVMAppendBasicBlockInContext(context, main_func, c_str!("main"));
            LLVMPositionBuilderAtEnd(builder, main_block);
            LLVMBuildCall(builder, gc_init, ptr::null_mut(), 0, c_str!(""));
            let variables = crate::stdlib::stdlib_vars(&codegen, builder);

            //let hello_world_str = LLVMBuildGlobalStringPtr(builder, c_str!("hello world"), c_str!(""));
            //LLVMBuildCall(builder, puts_func, [hello_world_str].as_ptr() as *mut _, 1, c_str!(""));
            LLVMBuildRet(
                builder,
                codegen
                    .gen_expr(ast, builder, &Env { variables }, None)
                    .unwrap(),
            );

            LLVMSetTarget(module, c_str!("x86_64-pc-linux-gnu"));
            LLVMDumpModule(module);
            LLVMWriteBitcodeToFile(module, c_str!("main.bc"));

            LLVMDisposeBuilder(builder);
        };
    }
}
