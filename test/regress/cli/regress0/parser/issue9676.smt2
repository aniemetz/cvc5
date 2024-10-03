; SCRUBBER: grep -o "Parse Error: issue9676.smt2:5.12: expected 3 arguments"
; EXPECT: Parse Error: issue9676.smt2:5.12: expected 3 arguments
; EXIT: 1
(set-logic ALL)
(assert (fp))
