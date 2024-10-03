; Fails on parsing back in after dumping post-asserts du to the logic string
; not containing Int (it's output as QF_BV).
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --solve-int-as-bv=5
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (< x 0))
(check-sat)
