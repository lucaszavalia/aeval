(set-logic ALL)
(declare-datatypes ((Nat 0)) ((Nat (S (tail__ Nat)) (Z))))
(declare-datatypes ((DLst 0)) ((DLst (Dcons (head_ Int) (tail_ DLst)) (Dnil))))
(declare-datatypes ((Lst 0)) ((Lst (cons (head DLst) (data Nat) (tail Lst)) (nil))))

(assert (not (forall ((x Lst) (y Lst)) (= x y))))
(check-sat)
