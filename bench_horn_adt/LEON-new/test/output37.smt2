(declare-datatypes ((Lst 0)) (((cons (param148 Int) (param149 Lst))(nil))))
(declare-datatypes ((Queue 0)) (((queue  (param150 Lst) (param151 Lst)))))
(declare-fun append (Lst Lst ) Lst)
(declare-fun len (Lst ) Int)
(assert (forall ((|_FH_2'| Lst)) (= (append |_FH_2'| |_FH_2'|) nil)))
(assert (forall ((_FH_1 Lst) (x Int) (_FH_2 Lst)) (= (append _FH_1 (cons x _FH_2)) (cons x (append _FH_1 _FH_2)))))
(assert (not (forall ((_FH_1 Lst) (x Int) (_FH_2 Lst)) (= (append _FH_1 (cons x _FH_2)) (cons x (append _FH_1 _FH_2))))))
(check-sat)