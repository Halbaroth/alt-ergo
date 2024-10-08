(set-logic ALL)
(declare-const x (_ BitVec 1024))
(declare-const y (_ BitVec 1024))
(declare-const z (_ BitVec 1024))
(declare-const w (_ BitVec 1024))
; Double zero stops carries
(assert (distinct ((_ extract 1027 1025) (bvadd (concat x (concat #b0100 y)) (concat y (concat #b1100 z)))) #b000))
(check-sat)
