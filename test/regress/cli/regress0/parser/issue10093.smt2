; REQUIRES: no-competition
; SCRUBBER: grep -o "Parse Error: issue10093.smt2:7.44: expecting a string-like term in argument of str.prefixof"
; EXPECT: Parse Error: issue10093.smt2:7.44: expecting a string-like term in argument of str.prefixof
; EXIT: 1
(set-logic ALL)
(declare-fun a () String)
(assert (str.prefixof (str.substr a 0 10) 2))
(check-sat)
