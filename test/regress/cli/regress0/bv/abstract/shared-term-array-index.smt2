; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --incremental --check-models
; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --incremental --check-models --bv-solver=bitblast-internal
; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --incremental --check-models --bv-solver=bitblast-internal --decision=internal
; EXPECT: unsat
; EXPECT: sat
; An abstracted term that is also shared with another theory. The index of a
; select is not abstracted (abstract() does not descend into terms of other
; theories), but the same product occurs in pure bit-vector atoms, which are
; abstracted. Hence the equality engine and the array solver reason about
; (bvmul a b) while the bit-blaster constrains its abstraction constant.
;
; Theory combination asks TheoryBV::getEqualityStatus for the care pair
; ((bvmul a b), c), which falls back to the model value of the abstracted
; term. Reporting a value that is inconsistent with what the bit-blaster
; committed to would make the pair look disequal in the model, which
; suppresses the care pair (Theory::areCareDisequal,
; TheoryArrays::checkPair) and thus the split that the first query needs.
(set-logic QF_ABV)
(declare-const A (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (= (select A (bvmul a b)) #x01))
(assert (= (select A c) #x02))
(assert (= c #x0f))
(push 1)
; Forces (bvmul a b) = #x0f = c, i.e. both selects are on the same index,
; which contradicts #x01 != #x02. Requires the care pair to be split.
(assert (bvugt (bvmul a b) #x0e))
(assert (bvult (bvmul a b) #x10))
(check-sat)
(pop 1)
(push 1)
; Here the two indices must differ, and the model must be consistent with the
; semantics of the abstracted product.
(assert (bvult (bvmul a b) #x0f))
(assert (bvugt a #x01))
(assert (bvugt b #x01))
(check-sat)
(pop 1)
