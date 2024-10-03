; Dumps BITVECTOR_EAGER_ATOM post-asserts, which we don't support on the API
; level and can thus not parse back in.
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --bv-solver=bitblast --bitblast=eager
(set-logic QF_BV)
(set-info :status sat)
(declare-fun x () (_ BitVec 1))
(declare-fun y () (_ BitVec 1))
(assert (= y (ite (= x (_ bv1 1)) (_ bv1 1) (_ bv0 1))))
(assert (= y (_ bv1 1)))
(check-sat)
