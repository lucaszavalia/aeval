(set-logic ALL)
(declare-datatypes () ((DLst (Dcons (head Int) (tail DLst)) (Dnil))))
(declare-datatypes () ((Lst (cons (head DLst) (data Int) (tail Lst)) (nil))))

(assert (not (forall ((x Lst) (y Lst)) (= x y))))
(check-sat)
