(declare-datatypes ((Lst 0)) (((cons (param1 Int) (param2 Lst))(nil))))
(declare-fun length (Lst ) Int)
(assert (not (forall ((_FH_0 Lst)) (>= (length _FH_0) 0))))
