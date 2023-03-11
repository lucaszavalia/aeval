(set-logic ALL)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Lst) (y Lst) (z Int)) (= (append (cons z y) x) (cons z (append y x)))))

(declare-fun flatten-app (Tree Lst) Lst)
(assert (forall ((x Lst)) (= (flatten-app leaf x) x)))
(assert (forall ((w Lst) (x Int) (y Tree) (z Tree)) (= (flatten-app (node x y z) w) (append (cons x nil) (append (flatten-app y w) (flatten-app z w))))))

(assert (not (forall ((x Tree) (y Lst) (z Tree)) (= (flatten-app x y) (flatten-app z y)))))
(check-sat)
