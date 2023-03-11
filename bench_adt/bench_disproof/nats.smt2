(set-logic ALL)
(declare-datatypes () ((Nat (S (tail Nat)) (Z))))
(assert (not (forall ((x Nat) (y Nat)) (= x y))))
(check-sat)
