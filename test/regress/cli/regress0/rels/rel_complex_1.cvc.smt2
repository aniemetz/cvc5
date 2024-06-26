; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)


(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(declare-fun r () (Relation Int Int))
(declare-fun w () (Relation Int))
(declare-fun z () (Relation Int))
(declare-fun r2 () (Relation Int Int))
(declare-fun a () (Tuple Int Int))
(assert (= a (tuple 3 1)))
(assert (set.member a x))
(declare-fun d () (Tuple Int Int))
(assert (= d (tuple 1 3)))
(assert (set.member d y))
(declare-fun e () (Tuple Int Int))
(assert (= e (tuple 4 3)))
(assert (= r (rel.join x y)))
(assert (set.member (tuple 1) w))
(assert (set.member (tuple 2) z))
(assert (= r2 (rel.product w z)))
(assert (not (set.member e r)))
(assert (set.subset r r2))
(assert (not (set.member (tuple 3 3) r2)))
(check-sat)
