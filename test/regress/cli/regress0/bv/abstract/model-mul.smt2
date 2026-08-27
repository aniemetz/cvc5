; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --check-models
; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --check-models --bv-solver=bitblast-internal
; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --check-models --bv-abstraction-value-limiter=100
; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --check-models --bv-abstraction-value-limiter=100 --bv-solver=bitblast-internal
; EXPECT: sat
; EXPECT: (((bvmul a b) #b00001111))
; The model of an abstracted term must be consistent with the semantics of the
; abstracted operator, and get-value must report that value rather than the
; value of the (internal) abstraction constant. Note that the model does not
; go through TheoryBV::getValue: bit-blasted variables are assigned by
; collectModelValues, everything else is evaluated bottom-up.
;
; The last two configurations force the tier-4 bit-blasting fallback (the
; tier-3 budget is bit-width/N, i.e. 0 for N=100). Such a term is excluded
; from the model consistency check of the abstraction module, its model value
; is determined by the bit-blasted circuit alone.
(set-logic QF_BV)
(set-option :produce-models true)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= (bvmul a b) #x0f))
(assert (bvugt a #x01))
(assert (bvugt b #x01))
(check-sat)
(get-value ((bvmul a b)))
