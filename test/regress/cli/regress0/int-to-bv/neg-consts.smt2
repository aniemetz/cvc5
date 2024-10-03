; Fails on parsing back in after dumping post-asserts du to the logic string
; not containing Int (it's output as QF_BV).
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --solve-int-as-bv=4
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (> (- 1) x))
(assert (>= y x))
(assert (< 0 y))
(set-info :status sat)
(check-sat)
