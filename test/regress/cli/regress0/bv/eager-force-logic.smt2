; Dumps BITVECTOR_EAGER_ATOM post-asserts, which we don't support on the API
; level and can thus not parse back in.
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --bitblast=eager --force-logic="QF_BV"
; EXPECT: sat
(set-option :produce-models true)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))

(assert (bvult a (bvadd b c)))
(check-sat)
