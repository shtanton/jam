use crate::semantic::{Identifier, UnrefinedType};
use crate::smt::{Expression, Function, Smt};
use crate::syntax::{Constant, Predicate};
use std::collections::HashMap;
use z3::{
    ast::{forall_const, Ast, Bool, Dynamic, BV},
    Config, Context, DatatypeAccessor, DatatypeBuilder, DatatypeSort, DatatypeVariant, FuncDecl,
    SatResult, Solver, Sort as ZSort, Symbol,
};

pub enum SmtResult {
    Pass,
    Unknown,
    Fail,
}

struct PairData<'a> {
    zsort: ZSort<'a>,
    pair: FuncDecl<'a>,
    first: FuncDecl<'a>,
    second: FuncDecl<'a>,
}

struct FnData<'a> {
    zsort: ZSort<'a>,
    apply: FuncDecl<'a>,
}

struct Z3Translater<'a> {
    fn_map: HashMap<(UnrefinedType, UnrefinedType), FnData<'a>>,
    pair_map: HashMap<(UnrefinedType, UnrefinedType), PairData<'a>>,
    ctx: &'a Context,
    one: ZSort<'a>,
    ast: FuncDecl<'a>,
    bool: ZSort<'a>,
    u8: ZSort<'a>,
    variables: HashMap<Identifier, FuncDecl<'a>>,
}

impl<'a> Z3Translater<'a> {
    fn translate_constant_call(
        &self,
        constant: Constant,
        mut args: Vec<Dynamic<'a>>,
    ) -> Result<Dynamic<'a>, ()> {
        Ok(match constant {
            Constant::True => Bool::from_bool(self.ctx, true).into(),
            Constant::False => Bool::from_bool(self.ctx, false).into(),
            Constant::And => {
                let bool_args = args
                    .iter()
                    .map(|arg| arg.as_bool())
                    .collect::<Option<Vec<Bool<'a>>>>()
                    .ok_or(())?;
                Bool::and(self.ctx, bool_args.iter().collect::<Vec<_>>().as_slice()).into()
            }
            Constant::Or => {
                let bool_args = args
                    .iter()
                    .map(|arg| arg.as_bool())
                    .collect::<Option<Vec<Bool<'a>>>>()
                    .ok_or(())?;
                Bool::or(self.ctx, bool_args.iter().collect::<Vec<_>>().as_slice()).into()
            }
            Constant::Implies => {
                let bool_args = args
                    .iter()
                    .map(|arg| arg.as_bool())
                    .collect::<Option<Vec<Bool<'a>>>>()
                    .ok_or(())?;
                bool_args[0].implies(&bool_args[1]).into()
            }
            Constant::DblImplies => {
                let bool_args = args
                    .iter()
                    .map(|arg| arg.as_bool())
                    .collect::<Option<Vec<Bool<'a>>>>()
                    .ok_or(())?;
                let left = bool_args[0].implies(&bool_args[1]);
                let right = bool_args[1].implies(&bool_args[0]);
                Bool::and(self.ctx, &[&left, &right]).into()
            }
            Constant::Not => {
                let bool_arg = args.pop().ok_or(())?.as_bool().ok_or(())?;
                bool_arg.not().into()
            }
            Constant::U8(value) => BV::from_u64(self.ctx, value as u64, 8).into(),
            Constant::Succ => {
                let bv_arg = args.pop().ok_or(())?.as_bv().ok_or(())?;
                let one = BV::from_u64(self.ctx, 1, 8);
                bv_arg.bvadd(&one).into()
            }
            Constant::Pred => {
                let bv_arg = args.pop().ok_or(())?.as_bv().ok_or(())?;
                let one = BV::from_u64(self.ctx, 1, 8);
                bv_arg.bvsub(&one).into()
            }
            Constant::Add => {
                let bv_args = args
                    .iter()
                    .map(|arg| arg.as_bv())
                    .collect::<Option<Vec<_>>>()
                    .ok_or(())?;
                bv_args[0].bvadd(&bv_args[1]).into()
            }
            Constant::Sub => {
                let bv_args = args
                    .iter()
                    .map(|arg| arg.as_bv())
                    .collect::<Option<Vec<_>>>()
                    .ok_or(())?;
                bv_args[0].bvsub(&bv_args[1]).into()
            }
        })
    }

    fn translate_predicate_call(
        &self,
        predicate: Predicate,
        mut args: Vec<Dynamic<'a>>,
    ) -> Result<Dynamic<'a>, ()> {
        Ok(match predicate {
            Predicate::Prop => args.pop().ok_or(())?,
            Predicate::LessThan => {
                let bv_args = args
                    .iter()
                    .map(|arg| arg.as_bv())
                    .collect::<Option<Vec<_>>>()
                    .ok_or(())?;
                bv_args[0].bvult(&bv_args[1]).into()
            }
            Predicate::LessThanEq => {
                let bv_args = args
                    .iter()
                    .map(|arg| arg.as_bv())
                    .collect::<Option<Vec<_>>>()
                    .ok_or(())?;
                bv_args[0].bvule(&bv_args[1]).into()
            }
            Predicate::GreaterThan => {
                let bv_args = args
                    .iter()
                    .map(|arg| arg.as_bv())
                    .collect::<Option<Vec<_>>>()
                    .ok_or(())?;
                bv_args[0].bvugt(&bv_args[1]).into()
            }
            Predicate::GreaterThanEq => {
                let bv_args = args
                    .iter()
                    .map(|arg| arg.as_bv())
                    .collect::<Option<Vec<_>>>()
                    .ok_or(())?;
                bv_args[0].bvuge(&bv_args[1]).into()
            }
        })
    }

    fn get_zsort(&self, typ: &UnrefinedType) -> Option<&ZSort<'a>> {
        match typ {
            UnrefinedType::One => Some(&self.one),
            UnrefinedType::Bool => Some(&self.bool),
            UnrefinedType::U8 => Some(&self.u8),
            UnrefinedType::Function(contents) => self.fn_map.get(contents).map(|data| &data.zsort),
            UnrefinedType::Product(contents) => self.pair_map.get(contents).map(|data| &data.zsort),
        }
    }

    fn define_var(&mut self, id: Identifier, typ: UnrefinedType) -> Result<(), ()> {
        let zsort = self.get_zsort(&typ).ok_or(())?;
        let func_decl = FuncDecl::new(self.ctx, format!("x!{}", id), &[], zsort);
        self.variables.insert(id, func_decl);
        Ok(())
    }

    fn get_var(&self, id: Identifier) -> Result<Dynamic<'a>, ()> {
        let func_decl = self.variables.get(&id).ok_or(())?;
        Ok(func_decl.apply(&[]))
    }

    fn translate_expressions(&mut self, exprs: Vec<Expression>) -> Result<Vec<Dynamic<'a>>, ()> {
        exprs
            .into_iter()
            .map(|expr| self.translate_expression(expr))
            .collect()
    }

    fn translate_expressions_to_bools(
        &mut self,
        exprs: Vec<Expression>,
    ) -> Result<Vec<Bool<'a>>, ()> {
        exprs
            .into_iter()
            .map(|expr| {
                if let Ok(ast) = self.translate_expression(expr) {
                    ast.as_bool().ok_or(())
                } else {
                    Err(())
                }
            })
            .collect()
    }

    fn translate_expression(&mut self, expr: Expression) -> Result<Dynamic<'a>, ()> {
        Ok(match expr {
            Expression::Variable(id) => self.get_var(id)?,
            Expression::Forall(id, typ, body) => {
                self.define_var(id, typ)?;
                let body = self.translate_expression(*body)?;
                let x = self.get_var(id)?;
                forall_const(self.ctx, &[&x], &[], &body)
            }
            Expression::False => {
                let bool_ast = Bool::from_bool(self.ctx, false);
                Dynamic::from_ast(&bool_ast)
            }
            Expression::True => {
                let bool_ast = Bool::from_bool(self.ctx, true);
                Dynamic::from_ast(&bool_ast)
            }
            Expression::Ast => self.ast.apply(&[]),
            Expression::Call(fun, args) => match fun {
                Function::And => {
                    let zargs = self.translate_expressions_to_bools(args)?;
                    let zargs_ref: Vec<_> = zargs.iter().collect();
                    let bool_ast: Bool = Bool::and(self.ctx, zargs_ref.as_slice());
                    Dynamic::from_ast(&bool_ast)
                }
                Function::Apply(param_type, body_type) => {
                    let zargs = self.translate_expressions(args)?;
                    let zargs_ref: Vec<_> = zargs.iter().collect();
                    let FnData { apply, .. } = self
                        .fn_map
                        .get(&(param_type, body_type))
                        .as_ref()
                        .ok_or(())?;
                    apply.apply(zargs_ref.as_slice())
                }
                Function::Constant(constant) => {
                    let zargs = self.translate_expressions(args)?;
                    self.translate_constant_call(constant, zargs)?
                }
                Function::Equal => {
                    let zargs = self.translate_expressions(args)?;
                    let bool_ast = zargs[0]._safe_eq(&zargs[1]).map_err(|_| ())?;
                    Dynamic::from_ast(&bool_ast)
                }
                Function::First(first_type, second_type) => {
                    let zargs = self.translate_expressions(args)?;
                    let zargs_ref: Vec<_> = zargs.iter().collect();
                    let PairData { first, .. } = self
                        .pair_map
                        .get(&(first_type, second_type))
                        .as_ref()
                        .ok_or(())?;
                    first.apply(zargs_ref.as_slice())
                }
                Function::Implies => {
                    let zargs = self.translate_expressions_to_bools(args)?;
                    let bool_ast = zargs[0].implies(&zargs[1]);
                    Dynamic::from_ast(&bool_ast)
                }
                Function::Not => {
                    let zargs: Vec<_> = self.translate_expressions_to_bools(args)?;
                    Dynamic::from_ast(&zargs[0].not())
                }
                Function::Pair(first_type, second_type) => {
                    let zargs = self.translate_expressions(args)?;
                    let zargs_ref: Vec<_> = zargs.iter().collect();
                    let PairData { pair, .. } = self
                        .pair_map
                        .get(&(first_type, second_type))
                        .as_ref()
                        .ok_or(())?;
                    pair.apply(zargs_ref.as_slice())
                }
                Function::Predicate(pred) => {
                    let zargs = self.translate_expressions(args)?;
                    self.translate_predicate_call(pred, zargs)?
                }
                Function::Second(first_type, second_type) => {
                    let zargs = self.translate_expressions(args)?;
                    let zargs_ref: Vec<_> = zargs.iter().collect();
                    let PairData { second, .. } = self
                        .pair_map
                        .get(&(first_type, second_type))
                        .as_ref()
                        .ok_or(())?;
                    second.apply(zargs_ref.as_slice())
                }
            },
        })
    }

    fn run_smt(mut self, smt: Smt) -> Result<SmtResult, ()> {
        let Smt {
            declarations,
            assertions,
            types,
        } = smt;
        for typ in types.into_iter() {
            match &typ {
                UnrefinedType::One | UnrefinedType::Bool | UnrefinedType::U8 => {}
                UnrefinedType::Function(contents) => {
                    let (param_type, body_type) = &**contents;
                    let symbol = Symbol::String(format!("({}->{})", param_type, body_type));
                    let zsort = ZSort::uninterpreted(self.ctx, symbol);
                    let param_zsort = self.get_zsort(param_type).unwrap();
                    let body_zsort = self.get_zsort(body_type).unwrap();
                    let apply = FuncDecl::new(
                        self.ctx,
                        format!("apply_{}->{}", param_type, body_type),
                        &[&zsort, param_zsort],
                        body_zsort,
                    );
                    self.fn_map
                        .insert(*contents.clone(), FnData { zsort, apply });
                }
                UnrefinedType::Product(contents) => {
                    let (first, second) = &**contents;
                    let first_zsort = self.get_zsort(first).unwrap();
                    let second_zsort = self.get_zsort(second).unwrap();
                    let DatatypeSort {
                        sort: zsort,
                        mut variants,
                        ..
                    } = DatatypeBuilder::new(self.ctx, "Pair")
                        .variant(
                            "pair",
                            vec![
                                ("first", DatatypeAccessor::Sort(first_zsort)),
                                ("second", DatatypeAccessor::Sort(second_zsort)),
                            ],
                        )
                        .finish();
                    let DatatypeVariant {
                        constructor: pair_fn,
                        mut accessors,
                        ..
                    } = variants.pop().unwrap();
                    let second_fn = accessors.pop().unwrap();
                    let first_fn = accessors.pop().unwrap();
                    self.pair_map.insert(
                        *contents.clone(),
                        PairData {
                            zsort,
                            pair: pair_fn,
                            first: first_fn,
                            second: second_fn,
                        },
                    );
                }
            }
        }
        for declaration in declarations.into_iter() {
            self.define_var(declaration.id, declaration.typ)?;
        }
        let solver = Solver::new(self.ctx);
        for assertion in assertions.into_iter() {
            if let Some(bool_ast) = self.translate_expression(assertion)?.as_bool() {
                solver.assert(&bool_ast);
            } else {
                return Ok(SmtResult::Fail);
            }
        }
        let res = solver.check();
        Ok(match res {
            SatResult::Sat => {
                let model = solver.get_model().unwrap();
                println!("Model: {}", model);
                SmtResult::Fail
            }
            SatResult::Unknown => SmtResult::Unknown,
            SatResult::Unsat => SmtResult::Pass,
        })
    }
}

pub fn run_smt(smt: Smt) -> Result<SmtResult, ()> {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let (one, mut ast_vec, _) = ZSort::enumeration(
        &ctx,
        Symbol::String(String::from("1")),
        &[Symbol::String(String::from("*"))],
    );
    let bool_zsort = ZSort::bool(&ctx);
    let u8_zsort = ZSort::bitvector(&ctx, 8);
    let translater = Z3Translater {
        fn_map: HashMap::new(),
        pair_map: HashMap::new(),
        ctx: &ctx,
        one,
        ast: ast_vec.pop().unwrap(),
        bool: bool_zsort,
        u8: u8_zsort,
        variables: HashMap::new(),
    };
    translater.run_smt(smt)
}
