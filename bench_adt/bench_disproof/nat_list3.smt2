(set-logic ALL)
(declare-datatypes ((Nat 0)) (((S (tail0 Nat)) (Z))))
(declare-datatypes ((Lst 0)) (((cons (head2 Int) (head1 Nat) (tail1 Lst)) (nil))))

(assert (not (forall ((x Lst) (y Lst)) (= x y))))
(check-sat)
