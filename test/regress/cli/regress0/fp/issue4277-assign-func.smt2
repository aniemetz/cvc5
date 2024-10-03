; Fails on parsing back in after dumping post-asserts due to printing
; FLOATINGPOINT_TO_REAL_TOTAL, which we don't export to the API. Hence we have
; to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; EXPECT: sat
(set-logic HO_ALL)
(set-option :assign-function-values false)
(set-info :status sat)
(declare-fun b () (_ BitVec 1))
(declare-fun c () (_ BitVec 8))
(declare-fun d () (_ BitVec 23))
(assert (= 0.0 (fp.to_real (fp b c d))))
(check-sat)
