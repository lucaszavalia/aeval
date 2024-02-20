(set-logic ALL)
(declare-datatypes ((Lst 0)) (((cons (head Int) (tail Lst))(nil)))
(define-fun-rec 
    app ((x Lst) (y Lst)) Lst
    (
        ite (= x nil) 
            y 
            (cons (head x) (app (tail x) y))
    )
)

(assert (= (app (cons 1 nil) (cons 2 nil)) (cons 1 (cons 2 nil))))

(check-sat)
(get-model)
