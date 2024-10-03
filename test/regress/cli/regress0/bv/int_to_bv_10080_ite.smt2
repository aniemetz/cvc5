; Dumps BITVECTOR_EAGER_ATOM post-asserts, which we don't support on the API
; level and can thus not parse back in.
; DISABLE-TESTER: dump-post
; EXPECT: sat
; COMMAND-LINE: --solve-int-as-bv=8
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (> y 0))
(assert (= z (ite (> x y) x (+ x y))))
(check-sat)
