(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))
(declare-datatypes ((Btr 0)) (((node (data Int) (left Tree) (right Tree)) (leaf))))



(declare-fun lstin (Int Lst) Bool)
(assert (forall ((x Int)) 
   (= 
      (lstin x nil) 
      false
   )
))
(assert (forall ((x Int) (y Lst) (z Int)) 
   (= 
      (lstin x (cons y z)) 
      (ite (= y x) true (lstin x z))
   )
))



(declare-fun lstinc (Lst) Bool)
(assert 
   (= 
      (lstinc nil) 
      true
   )
)
(assert (forall ((x Int)) 
      (= 
         (lstinc (cons x nil)) 
         true
      )
))
(assert (forall ((x Int) (y Int) (z Lst)) 
   (= 
      (lstinc (cons x (cons y z))) 
      (and (> x y) (lstinc z))
   )
))



(declare-fun btrin (Int Btr) Bool)
(assert (forall ((x Int)) 
   (= 
      (btrin x leaf) 
      (= 
         (btrin x leaf) 
         false
      )
   )
))
(assert (forall ((w Int) (x Int) (y Btr) (z Btr))
   (=
      (btrin w (node x y z))
      (ite 
         (= w x)
         true
         (and
            (btrin w y)
            (btrin w z)
         )
      )
   )
))



(declare-fun btrinc (Btr) Bool)
(assert (btrinc leaf) true)
(assert (forall ((a Int) (b Int) (c Btr) (d Btr))
   (=
      (btrinc (node a (node b c d) leaf))
      (> a b)
   )
))
(assert (forall ((a Int) (b Int) (c Btr) (d Btr))
   (=
      (btrinc (node a leaf (node b c d)))
      (> a b)
   )
))
(assert (forall ((a Int) (b Int) (c Int) (d Btr) (e Btr) (f Btr) (g Btr))
   (=
      (btrinc (node a (node b d e) (node c f g)))
      (and
         (> a b)
         (> a c)
         (btrinc d)
         (btrinc e)
         (btrinc f)
         (btrinc g)
      )
   )
))

;goal
;(declare-fun f (Lst) Btr)
(assert (not
   (exists ((x Btr)) ;(exists ((f (Lst)Btr)) ....)
      (forall ((y Lst))
         (and
            (=>
               (lstinc y)
               (btrinc x) ;replace x by f(y)
            )
            (forall ((z Int))
               (=>
                  (lstin z y)
                  (btrin z x)
               )
            )
         )
      )
   )
))
