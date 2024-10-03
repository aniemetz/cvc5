; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(set-option :incremental true)
(declare-fun t () (Set Int))
(declare-fun s () (Set Int))
(declare-const v Bool)
(assert (forall ((q Bool)) (distinct v (set.subset s t))))
(assert (= 1 (set.card t)))
(check-sat)
(assert v)
(check-sat)
