; EXPECT: false
(set-logic LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun x () Int)
(get-qe (exists-exactly ((x Int)) 10 (and (> (* 2 x) a) (< x (* 2 a)))))
