; EXPECT : (let ((_let_1 (* 2 (+ (+ (+ 0 0) 0) 0)))) (let ((_let_2 (* 4 a))) (let ((_let_3 (* 2 10))) (let ((_let_4 (= (mod 1 2) (mod a 2)))) (or (and (and _let_4 (and (< 0 a) (< a _let_2))) (= _let_3 (+ (+ (+ 0 (+ (- 2) (* 2 (- a 0)))) (+ (- 2) (* 2 (- _let_2 a)))) _let_1))) (and (and _let_4 (and (< _let_2 a) (< a 0))) (= _let_3 (+ (+ (+ 0 (+ (- 2) (* 2 (- a _let_2)))) (+ (- 2) (* 2 (- 0 a)))) _let_1))))))))
(set-logic LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun x () Int)
(get-qe (exists-exactly ((x Int)) 10 (and (= (mod a 2) (mod x 2)) (and (> (* 2 x) a) (< x (* 2 a))))))