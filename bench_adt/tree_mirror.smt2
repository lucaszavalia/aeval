(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

(declare-fun mirror (Tree) Tree)
(assert (= (mirror leaf) leaf))
(assert (forall ((x Int) (y Tree) (z Tree)) (= (mirror (node x y z)) (node x (mirror z) (mirror y)))))

(assert (not (forall ((x Tree)) (= (mirror (mirror x)) x))))
(check-sat)
