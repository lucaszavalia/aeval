(set-logic ALL)
(declare-datatypes () ((Nat (S (tail Nat)) (Z))))
(declare-datatypes () ((Lst (cons (head2 Int) (head1 Nat) (tail Lst)) (nil))))

(assert (not (forall ((x Lst) (y Lst)) (= x y))))
(check-sat)
