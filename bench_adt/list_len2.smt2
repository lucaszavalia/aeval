(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))

(declare-fun len2 (Lst Int) Int)
(assert (forall ((n Int)) (= (len2 nil n) n)))
(assert (forall ((x Int) (y Lst) (n Int)) (= (len2 (cons x y) n) (len2 y (+ 1 n)))))

(assert (exists ((x Lst)) (< (len2 x 0) 0)))
(check-sat)
