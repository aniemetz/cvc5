; COMMAND-LINE: -i
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(set-option :incremental true)
(push)
(assert (= "A" ""))
(check-sat)
(pop)
(assert (= "" "A"))
(check-sat)
