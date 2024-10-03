; COMMAND-LINE: -i
; SCRUBBER: grep -o "array store not assigned with correct type for array"
; EXPECT: array store not assigned with correct type for array
; EXIT: 1
(set-logic ALL)
(set-option :incremental true)
(declare-fun v () (Array Int (Array Int Real)))
(declare-fun va () (Array Int (Array Int Real)))
(push)
(assert (forall ((a (Array Int (Array Int Real)))) (and (= (select va 1) (select va 0)) (forall ((V Int)) (and (distinct va v) (= va (store va 0 (store (select a 0) 0 0))))))))
(check-sat)
