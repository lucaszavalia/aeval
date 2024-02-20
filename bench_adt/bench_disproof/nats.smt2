(set-logic ALL)
(declare-datatypes ((Nat 0)) (((S (tail Nat)) (Z))))
(assert (not (forall ((x Nat) (y Nat)) (= x y))))
(check-sat)
