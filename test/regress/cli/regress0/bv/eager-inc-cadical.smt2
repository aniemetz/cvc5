; Dumps BITVECTOR_EAGER_ATOM post-asserts, which we don't support on the API
; level and can thus not parse back in.
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --incremental --bv-sat-solver=cadical --bitblast=eager
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))

(assert (bvult a (bvadd b c)))
(set-info :status sat)
(check-sat)

(push 1)
(assert (bvult c b))
(set-info :status sat)
(check-sat)


(push 1)
(assert (bvugt c b))
(set-info :status unsat)
(check-sat)
(pop 2)

(set-info :status sat)
(check-sat)
(exit)
