; EXPECT: false
(set-logic LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(get-qe (exists-exactly (x Int) 1 (and (> x a) (= (* 4 x) a))))