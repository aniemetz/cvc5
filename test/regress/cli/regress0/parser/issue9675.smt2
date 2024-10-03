; SCRUBBER: grep -o "Parse Error: issue9675.smt2:5.46: invalid argument"
; EXPECT: Parse Error: issue9675.smt2:5.46: invalid argument
; EXIT: 1
(set-logic ALL)
(assert (= (fp (_ bv0 1) (_ bv0 1) (_ bv0 11))))
