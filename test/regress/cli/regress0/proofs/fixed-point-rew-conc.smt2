(set-logic QF_SLIA)
(declare-const x String)
(assert (= (str.++ "c" x "a") (str.++ x "aa")))
(set-info :status unsat)
(check-sat)
