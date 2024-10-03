; Fails on parsing back in after dumping post-asserts due to printing
; FLOATINGPOINT_MIN_TOTAL, which we don't export to the API. Hence we have
; to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; EXPECT: sat
(set-logic ALL)
(set-option :check-models true)
(declare-const a Float64)
(declare-const b Float64)
(declare-const c Float64)
(assert (= c (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))
(assert (= c (fp.min a (fp.min c b))))
(check-sat)
