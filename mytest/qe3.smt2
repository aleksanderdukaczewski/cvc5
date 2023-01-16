(set-logic LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(get-qe (exists-exactly 15 ((x Int)) (and (> x a) (< x b))))
