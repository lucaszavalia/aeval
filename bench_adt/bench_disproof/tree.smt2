(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))
(assert (not (forall ((x Tree) (y Tree)) (= x y))))
(check-sat)
