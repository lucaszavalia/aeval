(set-logic ALL)
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

(declare-fun tmirror (Tree) Tree)
(assert (= (tmirror leaf) leaf)
(assert (forall ((x Int)) (= (tmirror (node x leaf leaf)) (node x leaf leaf))))
(assert (forall ((x Int) (y Tree) (z Tree)) (= (tmirror (node x y z)) (node x (tmirror z) (tmirror y)))))

(assert (not (forall ((x Tree)) (= (tmirror x) x))))
(check-sat)
