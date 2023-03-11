(set-logic ALL)
(declare-datatypes () ((Nat (S (tail Nat)) (Z))))
(declare-datatypes () ((Lst (cons (head Nat) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Nat) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun rev (Lst) Lst)
(assert (= (rev nil) nil))
(assert (forall ((x Nat) (y Lst)) (= (rev (cons x y)) (append (rev y) (cons x nil)))))

; extra lemmas
;(assert (forall ((x Lst) (y Lst)) (= (rev (append x y)) (append (rev y) (rev x)))))

(assert (not (forall ((x Lst)) (= (rev x) x))))
(check-sat)
