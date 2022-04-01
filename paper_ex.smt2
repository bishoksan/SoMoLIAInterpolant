


(set-logic QF_UFBV)

(declare-fun x() (_ BitVec 4))
(declare-fun y() (_ BitVec 4))
(declare-fun z() (_ BitVec 4))

(declare-fun get-interpolant (Bool Bool) Bool)

(assert (! (and (= y (bvadd x (_ bv9 4))) (bvule x y) (bvule y z)) :named formulaA))
(assert (!  (= z (bvadd y (_ bv9 4)))  :named formulaB))

(assert (get-interpolant formulaA formulaB))

(check-sat)