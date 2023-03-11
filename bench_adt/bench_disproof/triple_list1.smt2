(set-logic ALL)
(declare-datatypes () ((Nat (S (tail Nat)) (Z))))
(declare-datatypes () ((Lst (cons (head Nat) (tail Lst)) (nil))))
(declare-datatypes () ((TLst (Tcons (head Lst) (tail TLst)) (Tnil))))

(assert (not (forall ((x TLst) (y TLst)) (= x y))))
(check-sat)
