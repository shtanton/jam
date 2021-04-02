(declare-datatypes () (
	(F0 F0-0)
	(F0-env F0-env-dummy)
  (F0Ret F0Ret-F1-0)
	(F0Ret-env (F0Ret-env-F1-0 (f1-0-env-0 Term)) F0Ret-env-dummy)
	(F1 F1-0)
	(F1-env (F1-env-0 (f1-0-env-0 Term)) F1-env-dummy)
	(TermKind Nat Bool Ast F0 F1)
	(TermData
		(NatData (nat-project Int))
		(BoolData (bool-project Bool))
		AstData
		(F0Data (f0-project F0) (f0-env-project F0-env))
		(F1Data (f1-project F1) (f1-env-project F1-env))
	)
	(Term (mkterm (term-kind TermKind) (term-data TermData)))
))

(define-fun apply-f0 ((f F0) (env F0-env) (arg Term)) Term
	(ite (= f F0-0)
		(mkterm F1 (F1Data F1-0 (F1-env-0 arg)))
	(mkterm Ast AstData))
)
(define-fun apply-f1 ((f TermData) (arg Term)) Term
	(ite (= (f1-project f) F1-0)
		(mkterm Nat (NatData (+ (nat-project (term-data (f1-0-env-0 (f1-env-project f)))) (nat-project (term-data arg)))))
	(mkterm Ast AstData))
)

(define-fun nat ((t Term)) Bool
	(= (term-kind t) Nat)
)
(define-fun even ((t Term)) Bool
	(and (nat t) (= (mod (nat-project (term-data t)) 2) 0))
)

(declare-const m Term)
(assert (even m))
(declare-const n Term)
(assert (even n))

(assert (not
	(and 
		(even (apply-f1 (term-data (apply-f0 F0-0 F0-env-dummy m)) n))
	(and
		(even m)
		(even n)))
))

(check-sat)
(get-model)
