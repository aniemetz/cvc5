; Dumps BITVECTOR_EAGER_ATOM post-asserts, which we don't support on the API
; level and can thus not parse back in.
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --bitblast=eager
(set-logic QF_BV)
(set-info :status unsat)
(declare-const x (_ BitVec 1))
(assert (= (_ bv2 4) ((_ zero_extend 3) x)))
(check-sat)
