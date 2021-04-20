(declare-sort bool_bool)
(declare-fun apply_bool_bool (bool_bool bool) bool)
(declare-sort bool_iter)
(declare-fun apply_bool_iter (bool_iter (_ BitVec 8)) bool_bool)


(define-fun succ ((x (_ BitVec 8))) (_ BitVec 8)
	(bvadd x (_ bv1 8))
)


(declare-fun u8rec_bool (bool bool_iter (_ BitVec 8)) bool)

(assert (forall ((x bool) (x_iter bool_iter)) (=
	(u8rec_bool x x_iter (_ bv0 8))
	x
)))

(assert (forall ((x bool) (x_iter bool_iter) (n (_ BitVec 8))) (=>
	(not (= n (_ bv255 8)))
	(=
		(u8rec_bool x x_iter (succ n))
		(apply_bool_bool (apply_bool_iter x_iter n) (u8rec_bool x x_iter n))
	)
)))

(declare-const even_iter bool_iter)

(define-fun even ((n (_ BitVec 8))) bool
	(u8rec_bool true even_iter n)
)

(check-sat)
(get-model)
