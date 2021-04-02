(declare-sort BoolToBool)
(declare-fun apply-BoolToBool (BoolToBool Bool) Bool)
(declare-sort BoolToBool-To-BoolToBool)
(declare-fun apply-BoolToBool-To-BoolToBool (BoolToBool-To-BoolToBool BoolToBool) BoolToBool)
(declare-sort btbTbtb-t-btb)
(declare-fun apply-btbTbtb-t-btb (btbTbtb-t-btb BoolToBool-To-BoolToBool) BoolToBool)

(declare-const inverter BoolToBool-To-BoolToBool)
(assert (forall ((g BoolToBool))
	(forall ((x Bool))
		(=
			(apply-BoolToBool g x)
			(not (apply-BoolToBool (apply-BoolToBool-To-BoolToBool inverter g) x))
		)
	)
))

(declare-const id BoolToBool)
(assert (forall ((x Bool))
	(= (apply-BoolToBool id x) x)
))

(declare-const caller btbTbtb-t-btb)
(assert (forall ((g BoolToBool-To-BoolToBool))
	(= (apply-btbTbtb-t-btb caller g) (apply-BoolToBool-To-BoolToBool g id))
))

(assert (not (forall ((x Bool))
	(= x (apply-BoolToBool (apply-btbTbtb-t-btb caller inverter) x))
)))

(check-sat)
(get-model)
