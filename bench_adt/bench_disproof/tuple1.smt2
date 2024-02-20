(declare-datatypes () ((Tuple (tup (idata Int) (flag Bool)))))
(declare-datatypes () (Lst (cons (data Tuple) (tail Lst)) (nil)))

;(declare-fun flag_flipper (Tuple) Tuple)
;(assert (= (flag_flipper empty) empty))
;(assert (forall ((x Int) (y Bool)) (= (flag_flipper (tup x y)) (tup x (not y)))))

;(declare-fun add_and (Tuple Tuple) Tuple)
;(assert (forall ((x Tuple)) (= (add_and x empty) x)))
;(assert (forall ((x0 Int) (x1 Int) (y0 Bool) (y1 Bool)) (=
;   (add_and (tup x0 y0) (tup x1 y1))
;   (tup (+ x0 x1) (and y0 y1))
;)))

(assert (not (forall ((x Lst) (y Lst)) (= x y))))
;(assert (not (forall ((x Tuple)) (= (flag_flipper x) x))))
;(assert (not (forall ((x Tuple) (y Tuple)) (= (and_add x y) y))))
(check-sat)
