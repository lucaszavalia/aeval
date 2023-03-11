(declare-datatypes () ((Tree (node (data1 Int) (data2 Bool) (data3 Int) (left Tree) (right Tree)) (leaf))))
(assert (not (forall ((x Tree) (y Tree)) (= x y))))
(check-sat)
