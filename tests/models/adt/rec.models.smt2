(set-option :produce-models true)
(set-logic ALL)
(declare-datatype data (
  (cons1 (d1 data))
  (cons2)
))
(declare-const a data)
(assert ((_ is cons1) a))
(check-sat)
(get-model)
