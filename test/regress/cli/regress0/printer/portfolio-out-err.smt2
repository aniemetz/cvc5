; REQUIRES: no-competition
; COMMAND-LINE:
; SCRUBBER: grep -o "Parse Error: portfolio-out-err.smt2:7.28: Can only enable use-portfolio via the command line"
; EXPECT: Parse Error: portfolio-out-err.smt2:7.28: Can only enable use-portfolio via the command line
; EXIT: 1
(set-logic UFLIA)
(set-option :use-portfolio true)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (P x)))
(assert (not (P 10)))
(check-sat)
