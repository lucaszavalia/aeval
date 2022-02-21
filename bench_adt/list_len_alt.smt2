(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))

(declare-fun len2 (Lst Int) Int)
(assert (forall ((n Int)) (= (len2 nil n) n)))
(assert (forall ((x Int) (y Lst) (n Int)) (= (len2 (cons x y) n) (len2 y (+ 1 n)))))

(assert (not (forall ((x Lst)) (= (len x) (len2 x 0)))))

(check-sat)
