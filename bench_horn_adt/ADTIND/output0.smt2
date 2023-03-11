(set-logic ALL)
(declare-datatypes ((Lst 0)) (((cons (param1 Int) (param2 Lst))(nil))))
(declare-fun length (Lst ) Int)
(assert (= (length nil) 0))
(assert (forall ((x Int) (_FH_0 Lst)) (=> true (= (length (cons x _FH_0)) (+ (length _FH_0) 1)))))

(assert (not (= (length nil) 0)))
(check-sat)
