(declare-datatypes ((Lst 0)) (((cons (param0 Int) (param1 Lst))(nil))))
(declare-datatypes ((Queue 0)) (((queue  (param2 Lst) (param3 Lst)))))
(declare-fun append (Lst Lst ) Lst)
(assert (forall ((|_FH_2'| Lst)) (= (append nil |_FH_2'|) |_FH_2'|)))
(assert (forall ((x Int) (_FH_0 Lst) (_FH_1 Lst)) (= (append (cons x _FH_0) _FH_1) (cons x (append _FH_0 _FH_1)))))
(assert (not (forall ((|_FH_2'| Lst)) (= (append nil |_FH_2'|) |_FH_2'|))))
(check-sat)