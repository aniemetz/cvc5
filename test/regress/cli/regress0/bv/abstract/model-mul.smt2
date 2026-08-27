; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --check-models
; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --check-models --bv-solver=bitblast-internal
; EXPECT: sat
; EXPECT: (((bvmul a b) #b00001111))
; The model of an abstracted term must be consistent with the semantics of the
; abstracted operator, and querying its value must not report the value of the
; abstraction constant.
(set-logic QF_BV)
(set-option :produce-models true)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= (bvmul a b) #x0f))
(assert (bvugt a #x01))
(assert (bvugt b #x01))
(check-sat)
(get-value ((bvmul a b)))
