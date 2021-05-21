impl CodeGen {
  unsafe fn build_closure(
    &mut self,
    builder: *mut LLVMBuilder,
    typ: &UnrefinedType,
    env_vars: Vec<(*mut LLVMType, *mut LLVMValue, u64)>,
    body: impl FnOnce(
      &mut CodeGen,
      *mut LLVMBuilder,
      *mut LLVMValue,
      *mut LLVMValue,
    ) -> Result<*mut LLVMValue, ()>,
  ) -> Result<*mut LLVMValue, ()> {
    let fun_type = self.get_function_type(typ)?;
    let env_size =
      env_vars.iter().fold(8, |acc, (_, _, size)| acc + size);
    let env_type_env_members =
      env_vars.iter().map(|(typ, _, _)| *typ).collect::<Vec<_>>();
    let env_type = self.gen_env_type(fun_type, env_type_env_members);
    let func = LLVMAddFunction(self.module, c_str!("fn"), fun_type);
    let block = LLVMAppendBasicBlockInContext(
      self.context,
      func,
      c_str!("fn_block"),
    );
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
    let old_fun = self.fun;
    self.fun = func;
    let body = body(self, func_builder, env_param, param)?;
    self.fun = old_fun;
    LLVMBuildRet(func_builder, body);
    LLVMDisposeBuilder(func_builder);
    let untyped_env_ptr = self.build_malloc(builder, env_size);
    let env_ptr = LLVMBuildBitCast(
      builder,
      untyped_env_ptr,
      LLVMPointerType(env_type, 0),
      c_str!("env"),
    );
    let env_fun_ptr =
      LLVMBuildStructGEP(builder, env_ptr, 0, c_str!("env_func_ptr"));
    LLVMBuildStore(builder, func, env_fun_ptr);
    for (i, (_, value, _)) in env_vars.iter().enumerate() {
      let env_env_ptr = LLVMBuildStructGEP(
        builder,
        env_ptr,
        (i + 1) as u32,
        c_str!("env_env_ptr"),
      );
      LLVMBuildStore(builder, *value, env_env_ptr);
    }
    Ok(LLVMBuildBitCast(
      builder,
      env_ptr,
      self.get_type(typ)?,
      c_str!("fn_env"),
    ))
  }

  unsafe fn build_application(
    &mut self,
    builder: *mut LLVMBuilder,
    closure: *mut LLVMValue,
    arg: *mut LLVMValue,
  ) -> *mut LLVMValue {
    let fun_ptr =
      LLVMBuildStructGEP(builder, closure, 0, c_str!("fun_ptr"));
    let fun = LLVMBuildLoad(builder, fun_ptr, c_str!("fun"));
    let untyped_closure = LLVMBuildBitCast(
      builder,
      closure,
      LLVMPointerType(LLVMIntTypeInContext(self.context, 8), 0),
      c_str!("untyped_closure"),
    );
    LLVMBuildCall(
      builder,
      fun,
      [untyped_closure, arg].as_ptr() as *mut _,
      2,
      c_str!("apply"),
    )
  }

  unsafe fn gen_expr(
    &mut self,
    expr: Expression,
    builder: *mut LLVMBuilder,
  ) -> Result<*mut LLVMValue, ()> {
    Ok(match expr.kind {
      ExpressionKind::Call(constant, mut args) => match constant {
        Constant::Succ => {
          let arg = args.pop().ok_or(())?;
          let arg_type = self.get_type(&arg.typ)?;
          let arg = self.gen_expr(arg, builder)?;
          LLVMBuildAdd(
            builder,
            arg,
            LLVMConstInt(arg_type, 1, 0),
            c_str!("succ"),
          )
        }
      },
      ExpressionKind::Variable(id) => {
        self.get_variable(id).ok_or(())?
      }
      ExpressionKind::Abstraction(id, _, body) => {
        let env_vec = expr.env.into_iter().collect::<Vec<_>>();
        let env_ids =
          env_vec.iter().map(|(id, _)| *id).collect::<Vec<_>>();
        let env_vars = env_vec
          .into_iter()
          .map(|(id, typ)| {
            Ok((
              self.get_type(&typ)?,
              self.get_variable(id).ok_or(())?,
              self.get_type_size(&typ),
            ))
          })
          .collect::<Result<Vec<_>, ()>>()?;
        self.build_closure(
          builder,
          &expr.typ,
          env_vars,
          |this, func_builder, env_param, param| {
            this.register_variable(id, param);
            let old_env = this.env.clone();
            for (i, id) in env_ids.into_iter().enumerate() {
              let env_var_ptr = LLVMBuildStructGEP(
                func_builder,
                env_param,
                (i + 1) as u32,
                c_str!("env_var_ptr"),
              );
              let env_var = LLVMBuildLoad(
                func_builder,
                env_var_ptr,
                c_str!("env_var"),
              );
              this.register_variable(id, env_var);
            }
            let body = this.gen_expr(*body, func_builder)?;
            this.env = old_env;
            Ok(body)
          },
        )?
      }
      ExpressionKind::Application(contents) => {
        let (fun, arg) = *contents;
        let closure = self.gen_expr(fun, builder)?;
        let arg = self.gen_expr(arg, builder)?;
        self.build_application(builder, closure, arg)
      }
      ExpressionKind::U8Rec(_, _, contents) => {
        let entry = LLVMAppendBasicBlockInContext(
          self.context,
          self.fun,
          c_str!("u8rec_entry"),
        );
        let header = LLVMAppendBasicBlockInContext(
          self.context,
          self.fun,
          c_str!("u8rec_header"),
        );
        let body = LLVMAppendBasicBlockInContext(
          self.context,
          self.fun,
          c_str!("u8rec_body"),
        );
        let exit = LLVMAppendBasicBlockInContext(
          self.context,
          self.fun,
          c_str!("u8rec_exit"),
        );
        LLVMBuildBr(builder, entry);
        LLVMPositionBuilderAtEnd(builder, entry);
        let (init_expr, iter_expr, count_expr) = *contents;
        let initial_count = self.gen_expr(count_expr, builder)?;
        let acc_type = init_expr.typ.clone();
        let llvm_acc_type = self.get_type(&acc_type)?;
        let acc_thunk_type = self.thunk_type(llvm_acc_type);
        let initial_acc_thunk = {
          let env_vec =
            init_expr.env.clone().into_iter().collect::<Vec<_>>();
          let env_ids =
            env_vec.iter().map(|(id, _)| *id).collect::<Vec<_>>();
          let env_vars = env_vec
            .into_iter()
            .map(|(id, typ)| {
              Ok((
                self.get_type(&typ)?,
                self.get_variable(id).ok_or(())?,
                self.get_type_size(&typ),
              ))
            })
            .collect::<Result<Vec<_>, ()>>()?;
          self.build_closure(
            builder,
            &UnrefinedType::Function(Box::new((
              UnrefinedType::One,
              acc_type.clone(),
            ))),
            env_vars,
            |this, func_builder, env_param, _| {
              let old_env = this.env.clone();
              for (i, id) in env_ids.into_iter().enumerate() {
                let env_var_ptr = LLVMBuildStructGEP(
                  func_builder,
                  env_param,
                  (i + 1) as u32,
                  c_str!("env_var_ptr"),
                );
                let env_var = LLVMBuildLoad(
                  func_builder,
                  env_var_ptr,
                  c_str!("env_var"),
                );
                this.register_variable(id, env_var);
              }
              let body = this.gen_expr(init_expr, func_builder)?;
              this.env = old_env;
              Ok(body)
            },
          )?
        };
        LLVMBuildBr(builder, header);
        LLVMPositionBuilderAtEnd(builder, header);
        let prev_count = LLVMBuildPhi(
          builder,
          LLVMIntTypeInContext(self.context, 8),
          c_str!("prev_count"),
        );
        let prev_acc_thunk =
          LLVMBuildPhi(builder, acc_thunk_type, c_str!("prev_acc"));
        let prev_count_is_zero = LLVMBuildICmp(
          builder,
          LLVMIntPredicate::LLVMIntEQ,
          prev_count,
          LLVMConstInt(LLVMIntTypeInContext(self.context, 8), 0, 0),
          c_str!("prev_count_is_zero"),
        );
        LLVMBuildCondBr(builder, prev_count_is_zero, exit, body);
        LLVMPositionBuilderAtEnd(builder, body);
        let count = LLVMBuildSub(
          builder,
          prev_count,
          LLVMConstInt(LLVMIntTypeInContext(self.context, 8), 1, 0),
          c_str!("count"),
        );
        LLVMAddIncoming(
          prev_count,
          [initial_count, count].as_ptr() as *mut _,
          [entry, body].as_ptr() as *mut _,
          2,
        );
        let count_thunk_type =
          self.thunk_type(LLVMIntTypeInContext(self.context, 8));
        let count_thunk = {
          self.build_closure(
            builder,
            &UnrefinedType::Function(Box::new((
              UnrefinedType::One,
              UnrefinedType::U8,
            ))),
            vec![(LLVMIntTypeInContext(self.context, 8), count, 1)],
            |_, func_builder, env_param, _| {
              let count_ptr = LLVMBuildStructGEP(
                func_builder,
                env_param,
                1,
                c_str!("count_ptr"),
              );
              let count = LLVMBuildLoad(
                func_builder,
                count_ptr,
                c_str!("count"),
              );
              Ok(count)
            },
          )?
        };
        let acc_thunk = {
          let iter_env_vec =
            iter_expr.env.clone().into_iter().collect::<Vec<_>>();
          let iter_env_ids = iter_env_vec
            .iter()
            .map(|(id, _)| *id)
            .collect::<Vec<_>>();
          let iter_env_vars =
            iter_env_vec.into_iter().map(|(id, typ)| {
              Ok((
                self.get_type(&typ)?,
                self.get_variable(id).ok_or(())?,
                self.get_type_size(&typ),
              ))
            });
          let env_vars = vec![
            Ok((acc_thunk_type, prev_acc_thunk, 8)),
            Ok((count_thunk_type, count_thunk, 8)),
          ]
          .into_iter()
          .chain(iter_env_vars)
          .collect::<Result<Vec<_>, ()>>()?;
          self.build_closure(
            builder,
            &UnrefinedType::Function(Box::new((
              UnrefinedType::One,
              acc_type,
            ))),
            env_vars,
            |this, func_builder, env_param, _| {
              let acc_thunk_ptr = LLVMBuildStructGEP(
                func_builder,
                env_param,
                1,
                c_str!("acc_thunk_ptr"),
              );
              let acc_thunk = LLVMBuildLoad(
                func_builder,
                acc_thunk_ptr,
                c_str!("acc_thunk"),
              );
              let count_thunk_ptr = LLVMBuildStructGEP(
                func_builder,
                env_param,
                2,
                c_str!("count_thunk_ptr"),
              );
              let count_thunk = LLVMBuildLoad(
                func_builder,
                count_thunk_ptr,
                c_str!("count_thunk"),
              );
              let old_env = this.env.clone();
              for (i, id) in iter_env_ids.iter().enumerate() {
                let env_var_ptr = LLVMBuildStructGEP(
                  func_builder,
                  env_param,
                  (i + 3) as u32,
                  c_str!("env_var_ptr"),
                );
                let env_var = LLVMBuildLoad(
                  func_builder,
                  env_var_ptr,
                  c_str!("env_var"),
                );
                this.register_variable(*id, env_var);
              }
              let iter = this.gen_expr(iter_expr, func_builder)?;
              this.env = old_env;
              let partially_applied_iter = this.build_application(
                func_builder,
                iter,
                count_thunk,
              );
              let fully_applied_iter = this.build_application(
                func_builder,
                partially_applied_iter,
                acc_thunk,
              );
              Ok(fully_applied_iter)
            },
          )?
        };
        LLVMAddIncoming(
          prev_acc_thunk,
          [initial_acc_thunk, acc_thunk].as_ptr() as *mut _,
          [entry, body].as_ptr() as *mut _,
          2,
        );
        LLVMBuildBr(builder, header);
        LLVMPositionBuilderAtEnd(builder, exit);
        self.build_application(
          builder,
          prev_acc_thunk,
          LLVMConstInt(LLVMIntTypeInContext(self.context, 8), 0, 0),
        )
      }
    })
  }
}

pub fn codegen(ast: Expression, file: *const i8) {
  unsafe {
    let context = LLVMContextCreate();
    let module = LLVMModuleCreateWithName(c_str!("main"));
    let builder = LLVMCreateBuilderInContext(context);

    let gc_init_type = LLVMFunctionType(
      LLVMVoidTypeInContext(context),
      ptr::null_mut(),
      0,
      0,
    );
    let gc_init =
      LLVMAddFunction(module, c_str!("GC_init"), gc_init_type);
    let malloc_type = LLVMFunctionType(
      LLVMPointerType(LLVMIntTypeInContext(context, 8), 0),
      [LLVMIntTypeInContext(context, 64)].as_ptr() as *mut _,
      1,
      0,
    );
    let malloc =
      LLVMAddFunction(module, c_str!("GC_malloc"), malloc_type);
    let noalias = LLVMCreateStringAttribute(
      context,
      c_str!("noalias"),
      7,
      c_str!(""),
      0,
    );
    LLVMAddAttributeAtIndex(malloc, 0, noalias);

    let main_func_type = LLVMFunctionType(
      LLVMIntTypeInContext(context, 8),
      ptr::null_mut(),
      0,
      0,
    );
    let main_func =
      LLVMAddFunction(module, c_str!("main"), main_func_type);
    let main_block = LLVMAppendBasicBlockInContext(
      context,
      main_func,
      c_str!("main"),
    );
    LLVMPositionBuilderAtEnd(builder, main_block);
    LLVMBuildCall(builder, gc_init, ptr::null_mut(), 0, c_str!(""));

    let mut codegen = CodeGen {
      env: ImHashMap::new(),
      fun: main_func,
      module,
      context,
      malloc,
    };

    LLVMBuildRet(builder, codegen.gen_expr(ast, builder).unwrap());

    LLVMSetTarget(module, c_str!("x86_64-pc-linux-gnu"));
    LLVMWriteBitcodeToFile(module, file);

    LLVMDisposeBuilder(builder);
    LLVMDisposeModule(module);
    LLVMContextDispose(context);
  };
}
