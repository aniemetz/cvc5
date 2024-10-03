; Fails on parsing back in after dumping post-asserts due to printing
; FLOATINGPOINT_TO_REAL_TOTAL, which we don't export to the API. Hence we have
; to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; EXPECT: sat
(set-logic QF_FPLRA)
(set-info :status sat)
(declare-fun a () (_ FloatingPoint 11 53))
(assert (= (fp.to_real a) 0.0))
(check-sat)

