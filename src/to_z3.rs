use z3::{
    ast::{Ast, Bool, Dynamic, forall_const},
    DatatypeBuilder,
    DatatypeAccessor,
    DatatypeSort,
    DatatypeVariant,
    Config,
    Context,
    Sort as ZSort,
    Symbol,
    Solver,
    FuncDecl,
    SatResult,
};
use crate::smt::{Smt, Expression, Function};
use crate::semantic::{UnrefinedType, Identifier};
use crate::syntax::{Constant, Predicate};
use std::collections::HashMap;

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
    constants: HashMap<Constant, FuncDecl<'a>>,
    predicates: HashMap<Predicate, FuncDecl<'a>>,
    variables: HashMap<Identifier, FuncDecl<'a>>,
}

impl<'a> Z3Translater<'a> {
    fn get_zsort(&self, typ: &UnrefinedType) -> Option<&ZSort<'a>> {
        match typ {
            UnrefinedType::One => Some(&self.one),
            UnrefinedType::Bool => Some(&self.bool),
            UnrefinedType::Function(contents) => {
                self.fn_map.get(contents).map(|data| &data.zsort)
            },
            UnrefinedType::Product(contents) => {
                self.pair_map.get(contents).map(|data| &data.zsort)
            },
        }
    }

    fn define_const(&mut self, id: Identifier, typ: UnrefinedType) -> Result<(), ()> {
        let zsort = self.get_zsort(&typ).ok_or(())?;
        let func_decl = FuncDecl::new(self.ctx, format!("x!{}", id), &[], zsort);
        self.variables.insert(id, func_decl);
        Ok(())
    }

    fn get_const(&self, id: Identifier) -> Result<Dynamic<'a>, ()> {
        let func_decl = self.variables.get(&id).ok_or(())?;
        Ok(func_decl.apply(&[]))
    }

    fn translate_expressions(&mut self, exprs: Vec<Expression>) -> Result<Vec<Dynamic<'a>>, ()> {
        exprs.into_iter().map(|expr| self.translate_expression(expr)).collect()
    }

    fn translate_expressions_to_bools(&mut self, exprs: Vec<Expression>) -> Result<Vec<Bool<'a>>, ()> {
        exprs.into_iter().map(|expr| {
            if let Ok(ast) = self.translate_expression(expr) {
                ast.as_bool().ok_or(())
            } else {
                Err(())
            }
        }).collect()
    }

    fn translate_expression(&mut self, expr: Expression) -> Result<Dynamic<'a>, ()> {
        Ok(match expr {
            Expression::Variable(id) => {
                self.get_const(id)?
            },
            Expression::Forall(id, typ, body) => {
                self.define_const(id, typ)?;
                let body = self.translate_expression(*body)?;
                let x = self.get_const(id)?;
                forall_const(self.ctx, &[&x], &[], &body)
            },
            Expression::False => {
                let bool_ast = Bool::from_bool(self.ctx, false);
                Dynamic::from_ast(&bool_ast)
            },
            Expression::True => {
                let bool_ast = Bool::from_bool(self.ctx, true);
                Dynamic::from_ast(&bool_ast)
            },
            Expression::Ast => self.ast.apply(&[]),
            Expression::Call(fun, args) => {
                match fun {
                    Function::And => {
                        let zargs = self.translate_expressions_to_bools(args)?;
                        let zargs_ref: Vec<_> = zargs.iter().collect();
                        let bool_ast: Bool = Bool::and(self.ctx, zargs_ref.as_slice());
                        Dynamic::from_ast(&bool_ast)
                    },
                    Function::Apply(param_type, body_type) => {
                        let zargs = self.translate_expressions(args)?;
                        let zargs_ref: Vec<_> = zargs.iter().collect();
                        let FnData{apply, ..} = self.fn_map.get(&(param_type, body_type)).as_ref().ok_or(())?;
                        apply.apply(zargs_ref.as_slice())
                    },
                    Function::Constant(constant) => {
                        let zargs = self.translate_expressions(args)?;
                        let zargs_ref: Vec<_> = zargs.iter().collect();
                        self.constants.get(&constant).as_ref().ok_or(())?.apply(zargs_ref.as_slice())
                    },
                    Function::Equal => {
                        let zargs = self.translate_expressions(args)?;
                        let bool_ast = zargs[0]._safe_eq(&zargs[1]).map_err(|_| ())?;
                        Dynamic::from_ast(&bool_ast)
                    },
                    Function::First(first_type, second_type) => {
                        let zargs = self.translate_expressions(args)?;
                        let zargs_ref: Vec<_> = zargs.iter().collect();
                        let PairData{first, ..} = self.pair_map.get(&(first_type, second_type)).as_ref().ok_or(())?;
                        first.apply(zargs_ref.as_slice())
                    },
                    Function::Implies => {
                        let zargs = self.translate_expressions_to_bools(args)?;
                        let bool_ast = zargs[0].implies(&zargs[1]);
                        Dynamic::from_ast(&bool_ast)
                    },
                    Function::Not => {
                        let zargs: Vec<_> = self.translate_expressions_to_bools(args)?;
                        Dynamic::from_ast(&zargs[0].not())
                    },
                    Function::Pair(first_type, second_type) => {
                        let zargs = self.translate_expressions(args)?;
                        let zargs_ref: Vec<_> = zargs.iter().collect();
                        let PairData{pair, ..} = self.pair_map.get(&(first_type, second_type)).as_ref().ok_or(())?;
                        pair.apply(zargs_ref.as_slice())
                    },
                    Function::Predicate(pred) => {
                        let zargs = self.translate_expressions(args)?;
                        let zargs_ref: Vec<_> = zargs.iter().collect();
                        self.predicates.get(&pred).as_ref().ok_or(())?.apply(zargs_ref.as_slice())
                    },
                    Function::Second(first_type, second_type) => {
                        let zargs = self.translate_expressions(args)?;
                        let zargs_ref: Vec<_> = zargs.iter().collect();
                        let PairData{second, ..} = self.pair_map.get(&(first_type, second_type)).as_ref().ok_or(())?;
                        second.apply(zargs_ref.as_slice())
                    },
                }
            },
        })
    }

    fn run_smt(mut self, smt: Smt) -> Result<bool, ()> {
        // TODO declarations
        let Smt {declarations, assertions, types} = smt;
        for typ in types.into_iter() {
            match &typ {
                UnrefinedType::One | UnrefinedType::Bool => {},
                UnrefinedType::Function(contents) => {
                    let (param_type, body_type) = &**contents;
                    let symbol = Symbol::String(format!("({}->{})", param_type, body_type));
                    let zsort = ZSort::uninterpreted(self.ctx, symbol);
                    let param_zsort = self.get_zsort(param_type).unwrap();
                    let body_zsort = self.get_zsort(body_type).unwrap();
                    let apply = FuncDecl::new(
                        self.ctx,
                        "apply",
                        &[&zsort, param_zsort],
                        body_zsort,
                    );
                    self.fn_map.insert(*contents.clone(), FnData {
                        zsort,
                        apply,
                    });
                },
                UnrefinedType::Product(contents) => {
                    let (first, second) = &**contents;
                    let first_zsort = self.get_zsort(first).unwrap();
                    let second_zsort = self.get_zsort(second).unwrap();
                    let DatatypeSort {sort: zsort, mut variants, ..} = DatatypeBuilder::new(self.ctx, "Pair")
                        .variant("pair", vec![
                            ("first", DatatypeAccessor::Sort(first_zsort)),
                            ("second", DatatypeAccessor::Sort(second_zsort)),
                        ])
                        .finish();
                    let DatatypeVariant {
                        constructor: pair_fn,
                        mut accessors,
                        ..
                    } = variants.pop().unwrap();
                    let second_fn = accessors.pop().unwrap();
                    let first_fn = accessors.pop().unwrap();
                    self.pair_map.insert(*contents.clone(), PairData{
                        zsort,
                        pair: pair_fn,
                        first: first_fn,
                        second: second_fn,
                    });
                },
            }
        }
        for declaration in declarations.into_iter() {
            self.define_const(declaration.id, declaration.typ)?;
        }
        let solver = Solver::new(self.ctx);
        for assertion in assertions.into_iter() {
            if let Some(bool_ast) = self.translate_expression(assertion)?.as_bool() {
                solver.assert(&bool_ast);
            } else {
                return Ok(false);
            }
        }
        Ok(solver.check() != SatResult::Sat)
    }
}

pub fn run_smt(smt: Smt) -> bool {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let (one, mut ast_vec, _) = ZSort::enumeration(&ctx, Symbol::String(String::from("1")), &[Symbol::String(String::from("*"))]);
    let bool_zsort = ZSort::bool(&ctx);
    // TODO constants and predicates
    let translater = Z3Translater {
        fn_map: HashMap::new(),
        pair_map: HashMap::new(),
        ctx: &ctx,
        one,
        ast: ast_vec.pop().unwrap(),
        bool: bool_zsort,
        constants: HashMap::new(),
        predicates: HashMap::new(),
        variables: HashMap::new(),
    };
    translater.run_smt(smt).unwrap_or(false)
}
