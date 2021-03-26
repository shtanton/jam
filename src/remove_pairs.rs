use crate::lambda_lift::{
    Expression as LLExpression, ExpressionKind as LLExpressionKind, FnIdentifier,
    Function as LLFunction, Identifier, Proposition as LLProposition,
};
use crate::logic::Sort;

fn remove_pair_returns_from_sort(sort: Sort) -> Sort {
    match sort {
        Sort::Function(contents) => {
            let param_type = remove_pair_returns_from_sort(contents.0);
            let return_type = remove_pair_returns_from_sort(contents.1);
            if let Sort::Product(pcontents) = return_type {
                Sort::Product(Box::new((
                    Sort::Function(Box::new((param_type.clone(), pcontents.0))),
                    Sort::Function(Box::new((param_type, pcontents.1))),
                )))
            } else {
                Sort::Function(Box::new((param_type, return_type)))
            }
        }
        Sort::Product(contents) => Sort::Product(Box::new((
            remove_pair_returns_from_sort(contents.0),
            remove_pair_returns_from_sort(contents.1),
        ))),
        Sort::Value => Sort::Value,
    }
}

fn function_type(parameters: &Vec<(Identifier, Sort)>, ret_type: &Sort) -> Sort {
    let mut typ = ret_type.clone();
    for (_, param_type) in parameters.iter().rev() {
        typ = Sort::Function(Box::new((param_type.clone(), typ)));
    }
    typ
}

fn param_tree_to_expression(tree: &Tree<(Identifier, Sort)>) -> LLExpression {
    match tree {
        Tree::Leaf((id, sort)) => LLExpression {
            kind: LLExpressionKind::Variable(*id),
            typ: sort.clone(),
        },
        Tree::Branch(contents) => {
            let first = param_tree_to_expression(&contents.0);
            let second = param_tree_to_expression(&contents.1);
            let typ = Sort::Product(Box::new((first.typ.clone(), second.typ.clone())));
            LLExpression {
                kind: LLExpressionKind::Tuple(Box::new((first, second))),
                typ,
            }
        }
    }
}

fn remove_pair_parameters_from_sort(sort: Sort) -> Sort {
    match sort {
        Sort::Function(contents) => {
            let param_type = remove_pair_parameters_from_sort(contents.0);
            let return_type = remove_pair_parameters_from_sort(contents.1);
            if let Sort::Product(pcontents) = param_type {
                Sort::Function(Box::new((
                    pcontents.0,
                    Sort::Function(Box::new((pcontents.1, return_type))),
                )))
            } else {
                Sort::Function(Box::new((param_type, return_type)))
            }
        }
        Sort::Product(contents) => Sort::Product(Box::new((
            remove_pair_parameters_from_sort(contents.0),
            remove_pair_parameters_from_sort(contents.1),
        ))),
        Sort::Value => Sort::Value,
    }
}

fn generate_arg_tree(arg: LLExpression) -> Tree<LLExpression> {
    match &arg.typ {
        Sort::Product(contents) => {
            let second_type = contents.1.clone();
            Tree::Branch(Box::new((
                generate_arg_tree(LLExpression {
                    kind: LLExpressionKind::First(Box::new(arg.clone())),
                    typ: contents.0.clone(),
                }),
                generate_arg_tree(LLExpression {
                    kind: LLExpressionKind::Second(Box::new(arg)),
                    typ: second_type,
                }),
            )))
        }
        Sort::Value | Sort::Function(_) => Tree::Leaf(arg),
    }
}

fn generate_pairless_application(
    fun: LLExpression,
    args: Vec<LLExpression>,
) -> Result<LLExpression, ()> {
    let mut application = fun;
    for arg in args.into_iter() {
        let typ = if let Sort::Function(contents) = &application.typ {
            contents.1.clone()
        } else {
            return Err(());
        };
        application = LLExpression {
            kind: LLExpressionKind::Application(Box::new((application, arg))),
            typ,
        };
    }
    Ok(application)
}

fn remove_pair_parameters_from_expression(expr: LLExpression) -> Result<LLExpression, ()> {
    Ok(match expr.kind {
        LLExpressionKind::Application(contents) => {
            let fun = remove_pair_parameters_from_expression(contents.0)?;
            let arg = remove_pair_parameters_from_expression(contents.1)?;
            let arg_tree = generate_arg_tree(arg);
            generate_pairless_application(fun, arg_tree.to_vec())?
        }
        LLExpressionKind::Ast | LLExpressionKind::Variable(_) => expr,
        LLExpressionKind::Function(id) => LLExpression {
            kind: LLExpressionKind::Function(id),
            typ: remove_pair_parameters_from_sort(expr.typ),
        },
        LLExpressionKind::Call(constant, args) => LLExpression {
            kind: LLExpressionKind::Call(
                constant,
                args.into_iter()
                    .map(|arg| remove_pair_parameters_from_expression(arg))
                    .collect::<Result<Vec<_>, ()>>()?,
            ),
            typ: expr.typ,
        },
        LLExpressionKind::First(arg) => {
            let arg = remove_pair_parameters_from_expression(*arg)?;
            let typ = if let Sort::Product(contents) = &arg.typ {
                contents.0.clone()
            } else {
                return Err(());
            };
            LLExpression {
                kind: LLExpressionKind::First(Box::new(arg)),
                typ,
            }
        }
        LLExpressionKind::Second(arg) => {
            let arg = remove_pair_parameters_from_expression(*arg)?;
            let typ = if let Sort::Product(contents) = &arg.typ {
                contents.1.clone()
            } else {
                return Err(());
            };
            LLExpression {
                kind: LLExpressionKind::Second(Box::new(arg)),
                typ,
            }
        }
        LLExpressionKind::Tuple(contents) => {
            let first = remove_pair_parameters_from_expression(contents.0)?;
            let second = remove_pair_parameters_from_expression(contents.1)?;
            let typ = Sort::Product(Box::new((first.typ.clone(), second.typ.clone())));
            LLExpression {
                kind: LLExpressionKind::Tuple(Box::new((first, second))),
                typ,
            }
        }
    })
}

fn generate_pairless_forall(body: LLProposition, vars: Vec<(Identifier, Sort)>) -> LLProposition {
    let mut forall = body;
    for var in vars.into_iter() {
        forall = LLProposition::Forall(var.0, var.1, Box::new(forall));
    }
    forall
}

fn add_fn_tree_to_vec(fn_tree: LLFunctionTree, target: &mut Vec<LLFunction>) {
    match fn_tree {
        LLFunctionTree::Function(fun) => {
            target.push(fun);
        }
        LLFunctionTree::Pair(contents) => {
            add_fn_tree_to_vec(contents.0, target);
            add_fn_tree_to_vec(contents.1, target);
        }
    }
}

enum Tree<T> {
    Leaf(T),
    Branch(Box<(Tree<T>, Tree<T>)>),
}

impl<T> Tree<T> {
    fn add_to_vec(self, target: &mut Vec<T>) {
        match self {
            Tree::Leaf(v) => target.push(v),
            Tree::Branch(contents) => {
                contents.0.add_to_vec(target);
                contents.1.add_to_vec(target);
            }
        }
    }

    fn to_vec(self) -> Vec<T> {
        let mut target = Vec::new();
        self.add_to_vec(&mut target);
        target
    }
}

enum LLFunctionTree {
    Function(LLFunction),
    Pair(Box<(LLFunctionTree, LLFunctionTree)>),
}

struct PairRemover {
    _next_fn_id: u32,
    _next_id: u32,
}

impl PairRemover {
    pub fn new(_next_id: u32, _next_fn_id: u32) -> PairRemover {
        PairRemover {
            _next_fn_id,
            _next_id,
        }
    }

    fn next_fn_id(&mut self) -> FnIdentifier {
        let id = self._next_fn_id;
        self._next_fn_id += 1;
        id
    }

    fn next_id(&mut self) -> Identifier {
        let id = self._next_id;
        self._next_id += 1;
        id
    }

    fn generate_pairless_returns(&mut self, fun: LLFunction) -> LLFunctionTree {
        let LLFunction {
            id,
            body,
            parameters,
        } = fun;
        let LLExpression {
            kind: body,
            typ: body_type,
        } = body;
        let body_type = remove_pair_returns_from_sort(body_type);
        if let Sort::Product(contents) = body_type {
            let first_id = self.next_fn_id();
            let second_id = self.next_fn_id();
            let body_type = Sort::Product(contents.clone());
            LLFunctionTree::Pair(Box::new((
                self.generate_pairless_returns(LLFunction {
                    id: first_id,
                    parameters: parameters.clone(),
                    body: LLExpression {
                        kind: LLExpressionKind::First(Box::new(LLExpression {
                            kind: body.clone(),
                            typ: body_type.clone(),
                        })),
                        typ: contents.0,
                    },
                }),
                self.generate_pairless_returns(LLFunction {
                    id: second_id,
                    parameters: parameters,
                    body: LLExpression {
                        kind: LLExpressionKind::Second(Box::new(LLExpression {
                            kind: body,
                            typ: body_type,
                        })),
                        typ: contents.1,
                    },
                }),
            )))
        } else {
            LLFunctionTree::Function(LLFunction {
                id,
                parameters,
                body: LLExpression {
                    kind: body,
                    typ: body_type,
                },
            })
        }
    }

    fn remove_pair_returns(
        &mut self,
        mut prop: LLProposition,
        mut fns: Vec<LLFunction>,
    ) -> (LLProposition, Vec<LLFunction>) {
        let new_fn_trees = fns.into_iter().map(|mut fun| {
            fun.parameters = fun
                .parameters
                .into_iter()
                .map(|(id, sort)| (id, remove_pair_returns_from_sort(sort)))
                .collect::<Vec<_>>();
            self.generate_pairless_returns(fun)
        });
        let mut new_fns = Vec::new();
        for fn_tree in new_fn_trees.into_iter() {
            add_fn_tree_to_vec(fn_tree, &mut new_fns);
        }
        (prop, new_fns)
    }

    fn uncurry(&mut self, mut fun: LLFunction) -> LLFunction {
        while let LLExpression {
            kind: mut body_kind,
            typ: Sort::Function(contents),
        } = fun.body
        {
            let param_id = self.next_id();
            fun.parameters.push((param_id, contents.0.clone()));
            body_kind = LLExpressionKind::Application(Box::new((
                LLExpression {
                    kind: body_kind,
                    typ: Sort::Function(contents.clone()),
                },
                LLExpression {
                    kind: LLExpressionKind::Variable(param_id),
                    typ: contents.0,
                },
            )));
            fun.body = LLExpression {
                kind: body_kind,
                typ: contents.1,
            };
        }
        fun
    }

    fn generate_pairless_parameters(
        &mut self,
        param: (Identifier, Sort),
    ) -> Tree<(Identifier, Sort)> {
        let (id, sort) = param;
        if let Sort::Product(contents) = sort {
            let first_id = self.next_id();
            let second_id = self.next_id();
            Tree::Branch(Box::new((
                self.generate_pairless_parameters((first_id, contents.0)),
                self.generate_pairless_parameters((first_id, contents.1)),
            )))
        } else {
            Tree::Leaf((id, sort))
        }
    }

    fn remove_pair_parameters_from_proposition(
        &mut self,
        prop: LLProposition,
    ) -> Result<LLProposition, ()> {
        Ok(match prop {
            LLProposition::Forall(id, typ, mut body) => {
                let var_tree =
                    self.generate_pairless_parameters((id, remove_pair_parameters_from_sort(typ)));
                body.substitute(&param_tree_to_expression(&var_tree), id);
                generate_pairless_forall(
                    self.remove_pair_parameters_from_proposition(*body)?,
                    var_tree.to_vec(),
                )
            }
            LLProposition::And(contents) => LLProposition::And(Box::new((
                self.remove_pair_parameters_from_proposition(contents.0)?,
                self.remove_pair_parameters_from_proposition(contents.1)?,
            ))),
            LLProposition::Implies(contents) => LLProposition::Implies(Box::new((
                self.remove_pair_parameters_from_proposition(contents.0)?,
                self.remove_pair_parameters_from_proposition(contents.1)?,
            ))),
            LLProposition::Call(pred, args) => LLProposition::Call(
                pred,
                args.into_iter()
                    .map(|arg| remove_pair_parameters_from_expression(arg))
                    .collect::<Result<Vec<_>, ()>>()?,
            ),
            LLProposition::CallLogic(pred, args) => LLProposition::CallLogic(
                pred,
                args.into_iter()
                    .map(|arg| remove_pair_parameters_from_expression(arg))
                    .collect::<Result<Vec<_>, ()>>()?,
            ),
            LLProposition::Equal(left, right) => LLProposition::Equal(
                remove_pair_parameters_from_expression(left)?,
                remove_pair_parameters_from_expression(right)?,
            ),
            LLProposition::False => LLProposition::False,
            LLProposition::True => LLProposition::True,
        })
    }

    fn remove_pair_parameters(
        &mut self,
        mut prop: LLProposition,
        mut fns: Vec<LLFunction>,
    ) -> Result<(LLProposition, Vec<LLFunction>), ()> {
        let new_fns = fns
            .into_iter()
            .map(|fun| {
                let LLFunction {
                    id,
                    parameters,
                    mut body,
                } = fun;
                let mut new_params = Vec::new();
                parameters
                    .into_iter()
                    .map(|(id, sort)| (id, remove_pair_parameters_from_sort(sort)))
                    .map(|param| (param.0, self.generate_pairless_parameters(param)))
                    .for_each(|(id, param_tree)| {
                        body.substitute(&param_tree_to_expression(&param_tree), id);
                        param_tree.add_to_vec(&mut new_params);
                    });
                Ok(LLFunction {
                    id,
                    parameters: new_params,
                    body: remove_pair_parameters_from_expression(body)?,
                })
            })
            .collect::<Result<Vec<_>, ()>>()?;
        Ok((self.remove_pair_parameters_from_proposition(prop)?, new_fns))
    }
}
