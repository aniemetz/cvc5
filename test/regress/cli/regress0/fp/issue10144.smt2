; Fails on parsing back in after dumping post-asserts due to printing
; FLOATINGPOINT_TO_UBV_TOTAL, which we don't export to the API. Hence we have
; to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; EXPECT: sat
(set-logic ALL)
(set-option :check-models true)
(declare-const y Float32)
(declare-const z Float32)
(define-const _y_8 (_ BitVec 8) ((_ fp.to_ubv 8) RNE y))
(define-const _z_8 (_ BitVec 8) ((_ fp.to_ubv 8) RNE z))
(assert (distinct _y_8 _z_8))
(check-sat)
