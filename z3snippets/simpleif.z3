(define-const a Int 1)
(define-const b Int 0)
(define-const c Bool false)
(define-fun f ((cond Bool) (then Int) (else Int)) Int
  (ite cond then else)
)
(define-const d Int (f c a b))

(assert (forall ((x Int))
  (=> (not (= x 0)) (not (= x d)))
))

(check-sat)

(declare-const x Int)
(define-fun f ((cond Bool) (then Int) (else Int)) Int
  (ite cond then else)
)
(declare-datatypes () ((F )))
(define-fun ap ((f )))

