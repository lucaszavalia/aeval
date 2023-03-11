(declare-datatypes ((Lst 0)) (((cons (param48 Int) (param49 Lst))(nil))))
(declare-datatypes ((Queue 0)) (((queue  (param50 Lst) (param51 Lst)))))
(declare-fun append (Lst Lst ) Lst)
(declare-fun len (Lst ) Int)
(assert (forall ((|_FH_2'| Lst)) (= (append nil |_FH_2'|) |_FH_2'|)))
(assert (forall ((x Int) (_FH_0 Lst) (_FH_1 Lst)) (= (append (cons x _FH_0) _FH_1) (cons x (append _FH_0 _FH_1)))))
(assert (= (len 0) nil))
(assert (forall ((_FH_4 Int) (x Int)) (=> true (= (len (+ _FH_4 1)) (cons x (len _FH_4))))))
(assert (not (= (len 0) nil)))
(check-sat)