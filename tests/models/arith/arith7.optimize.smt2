(set-option :produce-models true)
(set-logic ALL)
(declare-const x Real)
(push 1)
(assert (< x 0.5))
(maximize x)
(check-sat)
(get-model)
(get-objectives)
(pop 1)
(push 1)
(assert (< x (- 0.0 0.5)))
(maximize x)
(check-sat)
(get-model)
(get-objectives)
(pop 1)
