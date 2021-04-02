(declare-sort BoolToBool)
(declare-fun apply-BoolToBool (BoolToBool Bool) Bool)

(declare-fun invert (Bool) Bool)
(assert (forall ((x Bool))
	(= (not x) (invert x))
))
(declare-const invert-app BoolToBool)
(assert (forall ((x Bool))
	(= (apply-BoolToBool invert-app x) (invert x))
))

(define-fun f ((x BoolToBool)) Bool
	(apply-BoolToBool x true)
)

(assert (not (f invert-app)))

(check-sat)
(get-model)
