(set-option :produce-models true)
(set-logic ALL)
(declare-const x Int)
(assert (<= 0 x 10))
(push 1)
(maximize x)
(check-sat)
(get-model)
(get-objectives)
(pop 1)
(minimize x)
(check-sat)
(get-model)
(get-objectives)
