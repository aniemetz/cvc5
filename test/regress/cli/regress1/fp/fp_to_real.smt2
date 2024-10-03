; Fails on parsing back in after dumping post-asserts due to printing
; FLOATINGPOINT_TO_REAL_TOTAL, which we don't export to the API. Hence we have
; to disable the dump-post tester.
; DISABLE-TESTER: dump-post
(set-logic QF_FPLRA)
(declare-const c1 Bool)
(declare-const c2 Bool)
(declare-const x Float32)
(declare-const y Float32)
(assert (= x ((_ to_fp 8 24) RNE (ite c1 4.0 2.0))))
(assert (= y ((_ to_fp 8 24) RNE (ite c1 6.0 8.0))))
(assert (= 2.0 (fp.to_real (ite c2 x y))))
(set-info :status sat)
(check-sat)
