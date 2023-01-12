(set-logic LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(get-qe-counted (exists-exactly 15 ((x Int)) (and (> x a) (< x b))))
