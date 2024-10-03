; Fails on parsing back in after dumping post-asserts due to printing
; FLOATINGPOINT_TO_REAL_TOTAL, which we don't export to the API. Hence we have
; to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; EXPECT: sat
(set-logic ALL)
(assert (= 0.0 (fp.to_real (_ NaN 8 24))))
(check-sat)
