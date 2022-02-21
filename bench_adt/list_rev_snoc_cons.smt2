(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun snoc (Lst Int) Lst)
(assert (forall ((x Int)) (= (snoc nil x) (cons x nil))))
(assert (forall ((x Int) (y Lst) (z Int)) (= (snoc (cons x y) z) (cons x (snoc y z)))))

(declare-fun rev (Lst) Lst)
(assert (= (rev nil) nil))
(assert (forall ((x Int) (y Lst)) (= (rev (cons x y)) (snoc (rev y) x))))

(assert (not (forall ((x Lst) (y Int)) (= (rev (snoc x y)) (cons y (rev x))))))

(check-sat)
