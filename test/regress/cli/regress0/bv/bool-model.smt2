; Dumps BITVECTOR_EAGER_ATOM post-asserts, which we don't support on the API
; level and can thus not parse back in.
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --bitblast=eager
; COMMAND-LINE: --bitblast=eager --bv-solver=bitblast-internal
(set-info :status sat)
(set-logic QF_BV)
(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (xor y x))
(check-sat)
