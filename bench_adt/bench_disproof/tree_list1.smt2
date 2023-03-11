(set-logic ALL)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Lst) (y Lst) (z Int)) (= (append (cons z y) x) (cons z (append y x)))))

(declare-fun rev (Lst) Lst)
(assert (= (rev nil) nil))
(assert (forall ((x Int) (y Lst)) (= (rev (cons x y)) (append (rev y) (cons x nil)))))

(declare-fun flatten (Tree) Lst)
(assert (= (flatten leaf) nil))
(assert (forall ((x Int) (y Tree) (z Tree)) (= (flatten (node x y z)) (append (cons x nil) (append (flatten y) (flatten z))))))

(assert (not (forall ((x Tree)) (= (rev (flatten x)) (flatten x)))))
(check-sat)
