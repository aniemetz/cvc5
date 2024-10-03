; Fails on parsing back in after dumping post-asserts du to the logic string
; not containing Int (it's output as QF_BV).
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --solve-int-as-bv=9
; EXPECT: sat
(set-logic QF_NIA)
(declare-const a Int)
(declare-const b Int)
(assert (= (+ (* a 251) a) (+ b (* b 211))))
(assert (not (= a 0)))
(check-sat)
