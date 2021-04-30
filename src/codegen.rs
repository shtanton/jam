use crate::semantic::{Expression, ExpressionKind, Identifier, UnrefinedType};
use crate::syntax::Constant;
use im::HashMap;
use llvm_sys::bit_writer::LLVMWriteBitcodeToFile;
use llvm_sys::core::{
    LLVMAddAttributeAtIndex, LLVMAddFunction, LLVMAppendBasicBlockInContext, LLVMBuildAdd,
    LLVMBuildAnd, LLVMBuildBitCast, LLVMBuildCall, LLVMBuildExtractValue, LLVMBuildGEP,
    LLVMBuildInsertValue, LLVMBuildLoad, LLVMBuildNot, LLVMBuildOr, LLVMBuildRet, LLVMBuildStore,
    LLVMBuildStructGEP, LLVMBuildSub, LLVMBuildXor, LLVMConstInt, LLVMConstNamedStruct,
    LLVMConstNull, LLVMConstStructInContext, LLVMContextCreate, LLVMContextDispose,
    LLVMCreateBuilderInContext, LLVMCreateStringAttribute, LLVMDisposeBuilder, LLVMDisposeModule,
    LLVMDumpModule, LLVMDumpValue, LLVMFunctionType, LLVMGetElementAsConstant, LLVMGetParam,
    LLVMGetUndef, LLVMIntTypeInContext, LLVMModuleCreateWithName, LLVMPointerType,
    LLVMPositionBuilderAtEnd, LLVMSetTarget, LLVMStructTypeInContext, LLVMVoidTypeInContext,
};
use llvm_sys::{LLVMBuilder, LLVMContext, LLVMModule, LLVMType, LLVMValue};
use std::ptr;

macro_rules! c_str {
    ($s:expr) => {
        concat!($s, "\0").as_ptr() as *const i8
    };
}

struct CodeGen {
    env: HashMap<Identifier, *mut LLVMValue>,
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
                0,
            )]
            .as_ptr() as *mut _,
            1,
            c_str!("malloc"),
        )
    }

    /*unsafe fn get_type_size(&self, typ: *mut LLVMType, builder: *mut LLVMBuilder) -> *mut LLVMValue {
        let ptr = LLVMBuildGEP(
            builder,
            LLVMConstNull(typ),
            [1].as_ptr() as *mut _,
            1,
            c_str!("size_of_gep"),
        );
        LLVMBuildPtrToInt(
            builder,
            ptr,
            LLVMIntTypeInContext(self.context, 64),
    }*/

    fn get_type_size(&self, typ: &UnrefinedType) -> u64 {
        match typ {
            UnrefinedType::One => 0,
            UnrefinedType::Bool => 1,
            UnrefinedType::U8 => 1,
            UnrefinedType::Product(contents) => {
                self.get_type_size(&contents.0) + self.get_type_size(&contents.1)
            }
            UnrefinedType::Function(_) => 8,
        }
    }

    unsafe fn get_function_type(&self, typ: &UnrefinedType) -> Result<*mut LLVMType, ()> {
        Ok(match typ {
            UnrefinedType::Function(contents) => {
                let param_type = self.get_type(&contents.0)?;
                let body_type = self.get_type(&contents.1)?;
                LLVMFunctionType(
                    body_type,
                    [
                        LLVMPointerType(LLVMIntTypeInContext(self.context, 8), 0),
                        param_type,
                    ]
                    .as_ptr() as *mut _,
                    2,
                    0,
                )
            }
            _ => return Err(()),
        })
    }

    unsafe fn get_type(&self, typ: &UnrefinedType) -> Result<*mut LLVMType, ()> {
        Ok(match typ {
            UnrefinedType::One => LLVMVoidTypeInContext(self.context),
            UnrefinedType::Bool => LLVMIntTypeInContext(self.context, 8),
            UnrefinedType::U8 => LLVMIntTypeInContext(self.context, 8),
            UnrefinedType::Product(contents) => LLVMStructTypeInContext(
                self.context,
                [self.get_type(&contents.0)?, self.get_type(&contents.1)?].as_ptr() as *mut _,
                2,
                0,
            ),
            UnrefinedType::Function(_) => LLVMPointerType(
                LLVMStructTypeInContext(
                    self.context,
                    [LLVMPointerType(self.get_function_type(typ)?, 0)].as_ptr() as *mut _,
                    1,
                    0,
                ),
                0,
            ),
        })
        /*match typ {
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
        }*/
    }

    fn get_variable(&self, value: Identifier) -> Option<*mut LLVMValue> {
        self.env.get(&value).map(|v| *v)
    }

    fn register_variable(&mut self, id: Identifier, value: *mut LLVMValue) {
        self.env.insert(id, value);
    }

    unsafe fn gen_expr(
        &mut self,
        expr: Expression,
        builder: *mut LLVMBuilder,
    ) -> Result<*mut LLVMValue, ()> {
        Ok(match expr.kind {
            ExpressionKind::Call(constant, mut args) => match constant {
                Constant::U8(num) => LLVMConstInt(self.get_type(&expr.typ)?, num as u64, 1),
                Constant::And => {
                    let right = args.pop().ok_or(())?;
                    let left = args.pop().ok_or(())?;
                    let left = self.gen_expr(left, builder)?;
                    let right = self.gen_expr(right, builder)?;
                    LLVMBuildAnd(builder, left, right, c_str!("and"))
                }
                Constant::Or => {
                    let right = args.pop().ok_or(())?;
                    let left = args.pop().ok_or(())?;
                    let left = self.gen_expr(left, builder)?;
                    let right = self.gen_expr(right, builder)?;
                    LLVMBuildOr(builder, left, right, c_str!("or"))
                }
                Constant::Not => {
                    let arg = args.pop().ok_or(())?;
                    let arg = self.gen_expr(arg, builder)?;
                    LLVMBuildNot(builder, arg, c_str!("not"))
                }
                Constant::Implies => {
                    let right = args.pop().ok_or(())?;
                    let left = args.pop().ok_or(())?;
                    let left = self.gen_expr(left, builder)?;
                    let right = self.gen_expr(right, builder)?;
                    let not_left = LLVMBuildNot(builder, left, c_str!("imply_not"));
                    LLVMBuildOr(builder, not_left, right, c_str!("imply_or"))
                }
                Constant::DblImplies => {
                    let right = args.pop().ok_or(())?;
                    let left = args.pop().ok_or(())?;
                    let left = self.gen_expr(left, builder)?;
                    let right = self.gen_expr(right, builder)?;
                    let xor = LLVMBuildXor(builder, left, right, c_str!("dbl_imply_xor"));
                    LLVMBuildNot(builder, xor, c_str!("dbl_imply_not"))
                }
                Constant::True => LLVMConstInt(self.get_type(&expr.typ)?, 1, 0),
                Constant::False => LLVMConstInt(self.get_type(&expr.typ)?, 0, 0),
                Constant::Succ => {
                    let arg = args.pop().ok_or(())?;
                    let arg_type = self.get_type(&arg.typ)?;
                    let arg = self.gen_expr(arg, builder)?;
                    LLVMBuildAdd(builder, arg, LLVMConstInt(arg_type, 1, 0), c_str!("succ"))
                }
                Constant::Pred => {
                    let arg = args.pop().ok_or(())?;
                    let arg_type = self.get_type(&arg.typ)?;
                    let arg = self.gen_expr(arg, builder)?;
                    LLVMBuildSub(builder, arg, LLVMConstInt(arg_type, 1, 0), c_str!("pred"))
                }
            },
            ExpressionKind::Variable(id) => self.get_variable(id).ok_or(())?,
            ExpressionKind::Abstraction(id, _, body) => {
                let fun_type = self.get_function_type(&expr.typ)?;
                let env_vec = expr.env.into_iter().collect::<Vec<_>>();
                let env_size = env_vec
                    .iter()
                    .fold(8, |size, (_, typ)| size + self.get_type_size(typ));
                let mut env_type_env_members = env_vec
                    .iter()
                    .map(|(_, typ)| self.get_type(&typ))
                    .collect::<Result<Vec<_>, ()>>()?;
                let mut env_type_members = vec![LLVMPointerType(fun_type, 0)];
                env_type_members.append(&mut env_type_env_members);
                let env_type = LLVMStructTypeInContext(
                    self.context,
                    env_type_members.as_ptr() as *mut _,
                    env_type_members.len() as u32,
                    0,
                );
                let func = LLVMAddFunction(self.module, c_str!("fn"), fun_type);
                let block = LLVMAppendBasicBlockInContext(self.context, func, c_str!("fn_block"));
                let func_builder = LLVMCreateBuilderInContext(self.context);
                LLVMPositionBuilderAtEnd(func_builder, block);
                let untyped_env_param = LLVMGetParam(func, 0);
                let env_param = LLVMBuildBitCast(
                    func_builder,
                    untyped_env_param,
                    LLVMPointerType(env_type, 0),
                    c_str!("env"),
                );
                let param = LLVMGetParam(func, 1);
                self.register_variable(id, param);
                let old_env = self.env.clone();
                for (i, (id, _)) in env_vec.iter().enumerate() {
                    let env_var_ptr = LLVMBuildStructGEP(
                        func_builder,
                        env_param,
                        (i + 1) as u32,
                        c_str!("env_var_ptr"),
                    );
                    let env_var = LLVMBuildLoad(func_builder, env_var_ptr, c_str!("env_var"));
                    self.register_variable(*id, env_var);
                }
                let body = self.gen_expr(*body, func_builder)?;
                self.env = old_env;
                LLVMBuildRet(func_builder, body);
                LLVMDisposeBuilder(func_builder);
                let untyped_env_ptr = self.build_malloc(builder, env_size);
                let env_ptr = LLVMBuildBitCast(
                    builder,
                    untyped_env_ptr,
                    LLVMPointerType(env_type, 0),
                    c_str!("env"),
                );
                let env_func_ptr = LLVMBuildStructGEP(builder, env_ptr, 0, c_str!("env_func_ptr"));
                LLVMBuildStore(builder, func, env_func_ptr);
                for (i, (id, _)) in env_vec.iter().enumerate() {
                    let env_env_ptr =
                        LLVMBuildStructGEP(builder, env_ptr, (i + 1) as u32, c_str!("env_env_ptr"));
                    LLVMBuildStore(builder, self.get_variable(*id).ok_or(())?, env_env_ptr);
                }
                env_ptr
            }
            ExpressionKind::Application(contents) => {
                let (fun, arg) = *contents;
                let env = self.gen_expr(fun, builder)?;
                let arg = self.gen_expr(arg, builder)?;
                let fun_ptr = LLVMBuildStructGEP(builder, env, 0, c_str!("env_fun_ptr"));
                let fun = LLVMBuildLoad(builder, fun_ptr, c_str!("env_fun"));
                let untyped_env = LLVMBuildBitCast(
                    builder,
                    env,
                    LLVMPointerType(LLVMIntTypeInContext(self.context, 8), 0),
                    c_str!("untyped_env"),
                );
                LLVMBuildCall(
                    builder,
                    fun,
                    [untyped_env, arg].as_ptr() as *mut _,
                    2,
                    c_str!("apply"),
                )
            }
            ExpressionKind::Ast => LLVMConstNull(self.get_type(&expr.typ)?),
            ExpressionKind::Tuple(contents) => {
                let (first, second) = *contents;
                let first = self.gen_expr(first, builder)?;
                let second = self.gen_expr(second, builder)?;
                LLVMConstStructInContext(self.context, [first, second].as_ptr() as *mut _, 2, 0)
            }
            ExpressionKind::First(arg) => {
                LLVMBuildExtractValue(builder, self.gen_expr(*arg, builder)?, 0, c_str!("first"))
            }
            ExpressionKind::Second(arg) => {
                LLVMBuildExtractValue(builder, self.gen_expr(*arg, builder)?, 1, c_str!("first"))
            }
            ExpressionKind::U8Rec(_, _, _) => LLVMConstNull(self.get_type(&expr.typ)?),
        })
        /*match expr.kind {
            ExpressionKind::FunctionCall {
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
            ExpressionKind::Fn { params, body } => {
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
        }*/
    }
}

pub fn codegen(ast: Expression, file: *const i8) {
    unsafe {
        let context = LLVMContextCreate();
        let module = LLVMModuleCreateWithName(c_str!("main"));
        let builder = LLVMCreateBuilderInContext(context);

        //let puts_func_type = LLVMFunctionType(i32_type, [i8_pointer_type].as_ptr() as *mut _, 1, 0);
        //let puts_func = LLVMAddFunction(module, c_str!("puts"), puts_func_type);

        let gc_init_type = LLVMFunctionType(LLVMVoidTypeInContext(context), ptr::null_mut(), 0, 0);
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
            env: HashMap::new(),
            module,
            context,
            malloc,
        };

        let main_func_type =
            LLVMFunctionType(LLVMIntTypeInContext(context, 8), ptr::null_mut(), 0, 0);
        let main_func = LLVMAddFunction(module, c_str!("main"), main_func_type);
        let main_block = LLVMAppendBasicBlockInContext(context, main_func, c_str!("main"));
        LLVMPositionBuilderAtEnd(builder, main_block);
        LLVMBuildCall(builder, gc_init, ptr::null_mut(), 0, c_str!(""));
        //let variables = crate::stdlib::stdlib_vars(&codegen, builder);

        //let hello_world_str = LLVMBuildGlobalStringPtr(builder, c_str!("hello world"), c_str!(""));
        //LLVMBuildCall(builder, puts_func, [hello_world_str].as_ptr() as *mut _, 1, c_str!(""));
        LLVMBuildRet(builder, codegen.gen_expr(ast, builder).unwrap());
        println!("generated");

        LLVMSetTarget(module, c_str!("x86_64-pc-linux-gnu"));
        LLVMDumpModule(module);
        LLVMWriteBitcodeToFile(module, file);

        LLVMDisposeBuilder(builder);
        LLVMDisposeModule(module);
        LLVMContextDispose(context);
    };
}
