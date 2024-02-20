(declare-datatypes ((Lst 0)) (((nil) (cons (head1 Int) (tail Lst)))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x  y)) (+ 1 (len y)))))

(assert (exists ((x Lst)) (< (len x) 0)))
(check-sat)
