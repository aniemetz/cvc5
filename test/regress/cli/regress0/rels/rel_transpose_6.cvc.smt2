; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(declare-fun z () (Tuple Int Int))
(assert (= z (tuple 1 2)))
(declare-fun zt () (Tuple Int Int))
(assert (= zt (tuple 2 1)))
(assert (set.member z x))
(assert (set.member (tuple 3 4) x))
(assert (set.member (tuple 3 5) x))
(assert (set.member (tuple 3 3) x))
(assert (= x (rel.transpose y)))
(assert (not (set.member zt y)))
(assert (set.member z y))
(assert (not (set.member zt (rel.transpose y))))
(check-sat)
