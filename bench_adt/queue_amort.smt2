(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-datatypes () ((Queue (queue (front Lst) (back Lst)))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun rev2 (Lst Lst) Lst)
(assert (forall ((a Lst)) (= (rev2 nil a) a)))
(assert (forall ((x Int) (t Lst) (a Lst)) (= (rev2 (cons x t) a) (rev2 t (cons x a)))))

(declare-fun qrev (Lst) Lst)
(assert (forall ((x Lst)) (= (qrev x) (rev2 x nil))))

(declare-fun amortizeQueue (Lst Lst) Queue)
(assert (forall ((x Lst) (y Lst)) (= (amortizeQueue x y)
    (ite (<= (len y) (len x))
    (queue x y)
    (queue (append x (qrev y)) nil)))))

(declare-fun isAmortized (Queue) Bool)
(assert (forall ((x Lst) (y Lst)) (= (isAmortized (queue x y)) (<= (len y) (len x)))))

(assert (not (forall ((x Lst) (y Lst)) (isAmortized (amortizeQueue x y)))))
(check-sat)
