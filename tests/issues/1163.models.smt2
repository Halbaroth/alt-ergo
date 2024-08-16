(set-option :produce-models true)
(set-option :verify-models false)
(set-logic ALL)
(declare-const x Int)
(define-fun myabs ((x Int)) Int (ite (< x 0) (- x) x))
(maximize (myabs x))
(assert (< x 0))
(assert (> x (- 10000)))
; (assert (or (>= (myabs x) 0) (<= (myabs x) 0)))
(check-sat)
(get-model)
(get-objectives)
