(declare-datatypes () ((Color (red) (blue))))
(declare-datatypes () ((Tree (node (data Int) (color Color) (left Tree) (right Tree)) (leaf))))

(declare-fun swap_color (Color) Color)
(assert (= (swap_color red) blue))
(assert (= (swap_color blue) red))

(declare-fun is_color (Color Tree) Bool)
(assert (forall ((x Color)) (= (is_color x leaf) true)))
(assert (forall ((x Color) (a Int) (b Color) (c Tree) (d Tree)) (= (is_color x (node a b c d)) (= x b))))

(declare-fun switch_color (Tree) Tree)
(assert (= (switch_color leaf) leaf))
(assert (forall ((a Int) (b Color) (c Tree) (d Tree)) (= 
	(switch_color (node a b c d)) 
	(node a (swap_color b) (switch_color c) (switch_color d))
)))

(declare-fun is_rb (Tree) Bool)
(assert (= (is_rb leaf) true))
(assert (forall ((a Int) (b Color) (c Tree) (d Tree)) (= (is_rb (node a b c d)) (and (= (is_color (swap_color b) c) true) (= (is_color (swap_color b) d) true)))))

(assert (not (forall ((x Tree)) (= (is_rb x) (is_rb (switch_color x))))))
(check-sat)
