; Fails on parsing back in after dumping post-asserts du to the logic string
; not containing Int (it's output as QF_BV).
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --solve-int-as-bv=32
(set-logic QF_NIA)
(set-info :status sat)
(declare-fun _substvar_7_ () Bool)
(declare-fun _substvar_3_ () Int)
(assert (or _substvar_7_ (= 0 _substvar_3_)))
(check-sat)
