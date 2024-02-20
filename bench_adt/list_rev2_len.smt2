(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))

;(declare-fun append (Lst Lst) Lst)
;(assert (forall ((x Lst)) (= (append nil x) x)))
;(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun rev2 (Lst Lst) Lst)
(assert (forall ((a Lst)) (= (rev2 nil a) a)))
(assert (forall ((x Int) (t Lst) (a Lst)) (= (rev2 (cons x t) a) (rev2 t (cons x a)))))

;extra lemmas
;(assert (forall ((x Lst) (a Lst)) (= (rev2 x a) (append (rev2 x nil) a))))
;(assert (forall ((x Lst) (y Lst)) (= (len (rev2 x y)) (+ (len x) (len y)))))

(assert (not (forall ((x Lst)) (= (len (rev2 x nil)) (len x)))))
(check-sat)
