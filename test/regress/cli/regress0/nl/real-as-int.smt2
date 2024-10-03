; Fails on parsing back in after dumping post-asserts du to the logic string
; not containing Int (it's output as QF_UFNRA).
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --solve-real-as-int 
; EXPECT: sat
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= (* a a) 4.0))
(assert (= (* b b) 0.0))
(assert (= (+ (* a a) (* b b)) 4.0))
(check-sat)
