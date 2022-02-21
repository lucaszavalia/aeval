(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun append2 (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append2 nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append2 (cons x y) z) (append2 y (cons x z)))))

(declare-fun rev (Lst) Lst)
(assert (= (rev nil) nil))
(assert (forall ((x Int) (y Lst)) (= (rev (cons x y)) (append (rev y) (cons x nil)))))

(assert (not (forall ((x Lst) (y Lst)) (= (append (rev x) y) (append2 x y)))))

(check-sat)
