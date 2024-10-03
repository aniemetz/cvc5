; COMMAND-LINE: --no-fresh-declarations
; EXIT: 0
; EXPECT: sat
(set-logic ALL)
(declare-fun x () Int)
(declare-fun x () Int)
(check-sat)
