(set-logic ALL)
(declare-datatypes ((DLst 0)) (((Dcons (head_ Int) (tail_ DLst)) (Dnil))))
(declare-datatypes ((Lst 0)) (((cons (head DLst) (data Int) (tail Lst)) (nil))))

(assert (not (forall ((x Lst) (y Lst)) (= x y))))
(check-sat)
