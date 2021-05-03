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
    LLVMGetIntrinsicDeclaration, LLVMBuildAlloca,
};
use llvm_sys::{LLVMBuilder, LLVMContext, LLVMModule, LLVMType, LLVMValue};
use std::ptr;

macro_rules! c_str {
    ($s:expr) => {
        concat!($s, "\0").as_ptr() as *const i8
    };
}

#[derive(Clone)]
struct Context {
    builder: *mut LLVMBuilder,
    env: *mut LLVMValue,
    env_type: *mut LLVMType,
    param: *mut LLVMValue,
    param_type: *mut LLVMType,
    param_ptr: *mut LLVMValue,
    env_indices: HashMap<Identifier, u32>,
    param_id: Identifier,
}

struct CodeGen {
    pub module: *mut LLVMModule,
    pub context: *mut LLVMContext,
    malloc: *mut LLVMValue,
    localescape: *mut LLVMValue,
    localrecover: *mut LLVMValue,
    frameaddress: *mut LLVMValue,
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

    unsafe fn thunk_type(&self, typ: *mut LLVMType) -> *mut LLVMType {
        let byte_ptr = LLVMPointerType(LLVMIntTypeInContext(self.context, 8), 0);
        LLVMStructTypeInContext(
            self.context,
            [
                LLVMPointerType(LLVMFunctionType(
                    typ,
                    [byte_ptr, byte_ptr].as_ptr() as *mut _,
                    2,
                    0,
                ), 0),
                byte_ptr,
                byte_ptr,
            ].as_ptr() as *mut _,
            3,
            0,
        )
    }

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
                let body_type = self.get_type(&contents.1)?;
                LLVMFunctionType(
                    body_type,
                    [
                        LLVMPointerType(LLVMIntTypeInContext(self.context, 8), 0),
                        LLVMPointerType(LLVMIntTypeInContext(self.context, 8), 0),
                    ]
                    .as_ptr() as *mut _,
                    2,
                    0,
                )
            }
            _ => return Err(()),
        })
    }

    unsafe fn get_parameter_type(&self, typ: &UnrefinedType) -> Result<*mut LLVMType, ()> {
        let resolved_type = self.get_type(typ)?;
        Ok(LLVMStructTypeInContext(
            self.context,
            [
                LLVMPointerType(LLVMFunctionType(
                    resolved_type,
                    [LLVMPointerType(LLVMIntTypeInContext(self.context, 8), 0)].as_ptr() as *mut _,
                    1,
                    0,
                ), 0),
                LLVMPointerType(LLVMIntTypeInContext(self.context, 8), 0),
            ].as_ptr() as *mut _,
            2,
            0,
        ))
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
    }

    unsafe fn get_thunk(&self, id: Identifier, context: &Context) -> Option<*mut LLVMValue> {
        if id == context.param_id {
            Some(context.param)
        } else {
            if let Some(&index) = context.env_indices.get(&id) {
                let thunk_ptr = LLVMBuildStructGEP(
                    context.builder,
                    context.env,
                    index,
                    c_str!("thunk_ptr"),
                );
                Some(LLVMBuildLoad(
                    context.builder,
                    thunk_ptr,
                    c_str!("thunk"),
                ))
            } else {
                None
            }
        }
    }

    unsafe fn gen_expr(
        &mut self,
        expr: Expression,
        context: Context,
    ) -> Result<*mut LLVMValue, ()> {
        println!("{:?}", expr);
        let builder = context.builder;
        Ok(match expr.kind {
            ExpressionKind::Call(constant, mut args) => match constant {
                Constant::U8(num) => LLVMConstInt(self.get_type(&expr.typ)?, num as u64, 1),
                Constant::And => {
                    let right = args.pop().ok_or(())?;
                    let left = args.pop().ok_or(())?;
                    let left = self.gen_expr(left, context.clone())?;
                    let right = self.gen_expr(right, context)?;
                    LLVMBuildAnd(builder, left, right, c_str!("and"))
                }
                Constant::Or => {
                    let right = args.pop().ok_or(())?;
                    let left = args.pop().ok_or(())?;
                    let left = self.gen_expr(left, context.clone())?;
                    let right = self.gen_expr(right, context)?;
                    LLVMBuildOr(builder, left, right, c_str!("or"))
                }
                Constant::Not => {
                    let arg = args.pop().ok_or(())?;
                    let arg = self.gen_expr(arg, context)?;
                    LLVMBuildNot(builder, arg, c_str!("not"))
                }
                Constant::Implies => {
                    let right = args.pop().ok_or(())?;
                    let left = args.pop().ok_or(())?;
                    let left = self.gen_expr(left, context.clone())?;
                    let right = self.gen_expr(right, context)?;
                    let not_left = LLVMBuildNot(builder, left, c_str!("imply_not"));
                    LLVMBuildOr(builder, not_left, right, c_str!("imply_or"))
                }
                Constant::DblImplies => {
                    let right = args.pop().ok_or(())?;
                    let left = args.pop().ok_or(())?;
                    let left = self.gen_expr(left, context.clone())?;
                    let right = self.gen_expr(right, context)?;
                    let xor = LLVMBuildXor(builder, left, right, c_str!("dbl_imply_xor"));
                    LLVMBuildNot(builder, xor, c_str!("dbl_imply_not"))
                }
                Constant::True => LLVMConstInt(self.get_type(&expr.typ)?, 1, 0),
                Constant::False => LLVMConstInt(self.get_type(&expr.typ)?, 0, 0),
                Constant::Succ => {
                    let arg = args.pop().ok_or(())?;
                    let arg_type = self.get_type(&arg.typ)?;
                    let arg = self.gen_expr(arg, context)?;
                    LLVMBuildAdd(builder, arg, LLVMConstInt(arg_type, 1, 0), c_str!("succ"))
                }
                Constant::Pred => {
                    let arg = args.pop().ok_or(())?;
                    let arg_type = self.get_type(&arg.typ)?;
                    let arg = self.gen_expr(arg, context)?;
                    LLVMBuildSub(builder, arg, LLVMConstInt(arg_type, 1, 0), c_str!("pred"))
                }
            },
            ExpressionKind::Variable(id) => {
                let thunk = self.get_thunk(id, &context).ok_or(())?;
                LLVMDumpValue(thunk);
                println!("");
                LLVMDumpValue(context.env);
                println!("");
                LLVMDumpValue(context.param);
                println!("");
                let thunk_fn_ptr = LLVMBuildStructGEP(
                    context.builder,
                    thunk,
                    0,
                    c_str!("thunk_fn_ptr"),
                );
                let thunk_fn = LLVMBuildLoad(context.builder, thunk_fn_ptr, c_str!("thunk_fn"));
                let thunk_env_ptr = LLVMBuildStructGEP(
                    context.builder,
                    thunk,
                    1,
                    c_str!("thunk_env_ptr"),
                );
                let thunk_env = LLVMBuildLoad(context.builder, thunk_env_ptr, c_str!("thunk_fn"));
                let thunk_param_ptr = LLVMBuildStructGEP(
                    context.builder,
                    thunk,
                    2,
                    c_str!("thunk_param_ptr"),
                );
                let thunk_param = LLVMBuildLoad(context.builder, thunk_param_ptr, c_str!("thunk_fn"));
                LLVMBuildCall(
                    context.builder,
                    thunk_fn,
                    [thunk_env, thunk_param].as_ptr() as *mut _,
                    2,
                    c_str!("var"),
                )
            },
            ExpressionKind::Abstraction(id, param_type, body) => {
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
                let param_type = self.get_type(&param_type.unrefine())?;
                let untyped_param = LLVMGetParam(func, 1);
                let param = LLVMBuildBitCast(
                    func_builder,
                    untyped_param,
                    LLVMPointerType(self.thunk_type(param_type), 0),
                    c_str!("param"),
                );
                let stack_param = LLVMBuildAlloca(
                    context.builder,
                    param_type,
                    c_str!("stack_param"),
                );
                LLVMBuildStore(
                    context.builder,
                    param,
                    stack_param,
                );
                let body_context = Context {
                    builder: func_builder,
                    env: env_param,
                    env_type: env_type,
                    param: param,
                    param_type: param_type,
                    param_ptr: stack_param,
                    env_indices: env_vec.iter().enumerate().map(|(i, (id, _))| (*id, (i+1) as u32)).collect(),
                    param_id: id,
                };
                let body = self.gen_expr(*body, body_context)?;
                LLVMBuildRet(func_builder, body);
                LLVMDisposeBuilder(func_builder);
                let untyped_env_ptr = self.build_malloc(context.builder, env_size);
                let env_ptr = LLVMBuildBitCast(
                    context.builder,
                    untyped_env_ptr,
                    LLVMPointerType(env_type, 0),
                    c_str!("env"),
                );
                let env_func_ptr = LLVMBuildStructGEP(context.builder, env_ptr, 0, c_str!("env_func_ptr"));
                LLVMBuildStore(context.builder, func, env_func_ptr);
                for (i, (id, _)) in env_vec.iter().enumerate() {
                    let env_env_ptr =
                        LLVMBuildStructGEP(context.builder, env_ptr, (i + 1) as u32, c_str!("env_env_ptr"));
                    LLVMBuildStore(context.builder, self.get_thunk(*id, &context).ok_or(())?, env_env_ptr);
                }
                env_ptr
            }
            ExpressionKind::Application(contents) => {
                let (fun, arg) = *contents;
                let env = self.gen_expr(fun, context.clone())?;
                let thunk_fn = LLVMAddFunction(
                    self.module,
                    c_str!("thunk"),
                    LLVMFunctionType(
                        self.get_type(&arg.typ)?,
                        [LLVMPointerType(LLVMIntTypeInContext(self.context, 8), 0), LLVMPointerType(LLVMIntTypeInContext(self.context, 8), 0)].as_ptr() as *mut _,
                        2,
                        0,
                    ),
                );
                let block = LLVMAppendBasicBlockInContext(self.context, thunk_fn, c_str!("thunk_block"));
                let thunk_builder = LLVMCreateBuilderInContext(self.context);
                LLVMPositionBuilderAtEnd(thunk_builder, block);
                let untyped_env_param = LLVMGetParam(thunk_fn, 0);
                let env_param = LLVMBuildBitCast(
                    thunk_builder,
                    untyped_env_param,
                    LLVMPointerType(context.env_type, 0),
                    c_str!("env"),
                );
                let untyped_param = LLVMGetParam(thunk_fn, 1);
                let param = LLVMBuildBitCast(
                    thunk_builder,
                    untyped_param,
                    LLVMPointerType(self.thunk_type(context.param_type), 0),
                    c_str!("param_ptr"),
                );
                let param = LLVMBuildLoad(
                    context.builder,
                    param_ptr,
                    c_str!("param"),
                );
                let thunk_context = Context {
                    builder: thunk_builder,
                    env: env_param,
                    env_type: context.env_type,
                    param: param,
                    param_type: context.param_type,
                    param_ptr: param_ptr,
                    param_id: context.param_id,
                    env_indices: context.env_indices,
                };
                LLVMBuildRet(thunk_builder, self.gen_expr(arg, thunk_context)?);
                let thunk = LLVMConstStructInContext(
                    self.context,
                    [thunk_fn, context.env, context.param_ptr].as_ptr() as *mut _,
                    3,
                    0,
                );
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
                    [untyped_env, thunk].as_ptr() as *mut _,
                    2,
                    c_str!("apply"),
                )
            }
            ExpressionKind::Ast => LLVMConstNull(self.get_type(&expr.typ)?),
            ExpressionKind::Tuple(contents) => {
                let (first, second) = *contents;
                let first = self.gen_expr(first, context.clone())?;
                let second = self.gen_expr(second, context)?;
                LLVMConstStructInContext(self.context, [first, second].as_ptr() as *mut _, 2, 0)
            }
            ExpressionKind::First(arg) => {
                LLVMBuildExtractValue(context.builder, self.gen_expr(*arg, context)?, 0, c_str!("first"))
            }
            ExpressionKind::Second(arg) => {
                LLVMBuildExtractValue(context.builder, self.gen_expr(*arg, context)?, 1, c_str!("first"))
            }
            ExpressionKind::U8Rec(_, _, _) => LLVMConstNull(self.get_type(&expr.typ)?),
        })
    }
}

pub fn codegen(ast: Expression, file: *const i8) {
    unsafe {
        let context = LLVMContextCreate();
        let module = LLVMModuleCreateWithName(c_str!("main"));
        let builder = LLVMCreateBuilderInContext(context);

        let gc_init_type = LLVMFunctionType(LLVMVoidTypeInContext(context), ptr::null_mut(), 0, 0);
        let gc_init = LLVMAddFunction(module, c_str!("GC_init"), gc_init_type);
        let malloc_type = LLVMFunctionType(
            LLVMPointerType(LLVMIntTypeInContext(context, 8), 0),
            [LLVMIntTypeInContext(context, 64)].as_ptr() as *mut _,
            1,
            0,
        );
        let malloc = LLVMAddFunction(module, c_str!("GC_malloc"), malloc_type);
        let localescape_type = LLVMFunctionType(
            LLVMVoidTypeInContext(context),
            [0].as_ptr() as *mut _,
            0,
            1,
        );
        let localescape = LLVMAddFunction(module, c_str!("llvm.localescape"), localescape_type);
        let frameaddress_type = LLVMFunctionType(
            LLVMPointerType(LLVMIntTypeInContext(context, 8), 0),
            [LLVMIntTypeInContext(context, 32)].as_ptr() as *mut _,
            1,
            0,
        );
        let frameaddress = LLVMAddFunction(module, c_str!("llvm.frameaddress"), frameaddress_type);
        let localrecover_type = LLVMFunctionType(
            LLVMPointerType(LLVMIntTypeInContext(context, 8), 0),
            [
                LLVMPointerType(LLVMIntTypeInContext(context, 8), 0),
                LLVMPointerType(LLVMIntTypeInContext(context, 8), 0),
                LLVMIntTypeInContext(context, 32),
            ].as_ptr() as *mut _,
            3,
            0,
        );
        let localrecover = LLVMAddFunction(module, c_str!("llvm.localrecover"), localrecover_type);
        let noalias = LLVMCreateStringAttribute(context, c_str!("noalias"), 7, c_str!(""), 0);
        LLVMAddAttributeAtIndex(malloc, 0, noalias);

        let mut codegen = CodeGen {
            module,
            context,
            malloc,
            localescape,
            localrecover,
            frameaddress,
        };

        let main_func_type =
            LLVMFunctionType(LLVMIntTypeInContext(context, 8), ptr::null_mut(), 0, 0);
        let main_func = LLVMAddFunction(module, c_str!("main"), main_func_type);
        let main_block = LLVMAppendBasicBlockInContext(context, main_func, c_str!("main"));
        LLVMPositionBuilderAtEnd(builder, main_block);
        LLVMBuildCall(builder, gc_init, ptr::null_mut(), 0, c_str!(""));

        let param_type = LLVMVoidTypeInContext(context);
        let param = LLVMConstNull(param_type);
        let param_ptr = LLVMConstNull(LLVMPointerType(param_type, 0));
        let env_type = LLVMVoidTypeInContext(context);
        let env = LLVMConstNull(LLVMPointerType(env_type, 0));
        let builder_context = Context {
            builder: builder,
            env: env,
            env_type: env_type,
            param: param,
            param_type: param_type,
            param_ptr: param_ptr,
            env_indices: HashMap::new(),
            param_id: u32::MAX,
        };
        LLVMBuildRet(builder, codegen.gen_expr(ast, builder_context).unwrap());

        LLVMSetTarget(module, c_str!("x86_64-pc-linux-gnu"));
        LLVMDumpModule(module);
        LLVMWriteBitcodeToFile(module, file);

        LLVMDisposeBuilder(builder);
        LLVMDisposeModule(module);
        LLVMContextDispose(context);
    };
}
