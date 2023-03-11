(declare-datatypes () ((Tree (node (data Int) (a1 Tree) (a2 Tree) (a3 Tree)) (leaf))))
(assert (not (forall ((x Tree) (y Tree)) (= x y))))
(check-sat)
