(set-logic ALL)
(set-info :status sat)
(declare-fun S () (Set Int))
(assert (>= (set.card S) 3))
(assert (not (set.member 1 S)))
(check-sat)