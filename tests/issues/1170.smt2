(set-logic QF_BV)
(declare-const A (_ BitVec 2))
(declare-const B (_ BitVec 1))
(declare-const C (_ BitVec 3))
(assert (= (bvmul (_ bv3 4) (concat A (concat #b0 B))) (concat C #b1)))
(check-sat)
