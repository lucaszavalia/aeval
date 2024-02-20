(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))

(declare-fun len2 (Lst Lst) Int)
(assert (= (len2 nil nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len2 nil (cons x y)) (+ 1 (len2 nil y)))))
(assert (forall ((x Int) (y Lst)) (= (len2 (cons x y) nil) (+ 1 (len2 y nil)))))
(assert (forall ((x Int) (y Lst) (a Int) (b Lst)) (= (len2 (cons x y) (cons a b)) (+ 2 (len2 y b)))))

(assert (not (forall ((x Lst)) (= (len2 x nil) (len2 nil x)))))
(check-sat)
