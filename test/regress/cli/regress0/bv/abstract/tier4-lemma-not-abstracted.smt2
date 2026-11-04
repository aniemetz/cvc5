; REQUIRES: unrestricted-mode
; COMMAND-LINE: --bv-abstraction
; COMMAND-LINE: --bv-abstraction --bv-solver=bitblast-internal
; COMMAND-LINE: --bv-abstraction --bv-solver=bitblast-internal --sat-solver=minisat
; EXPECT: unsat
; DISABLE-TESTER: proof
; A square is never 2 (mod 2^64), so refinement has to fall back to
; bit-blasting the multiplier (tier 4). BVSolverBitblastInternal sends the
; tier-4 lemma `t = (bvmul x x)` to the inference manager and gets its atom
; back as a fact, which is abstracted to `t = t`. The multiplier must thus be
; bit-blasted when the lemma is added, not from the fact: otherwise it would
; never be bit-blasted and, once the inference manager drops the re-derived
; tier-4 lemma as a duplicate, the (inconsistent) model would be reported as
; sat.
(set-logic QF_BV)
(declare-const x (_ BitVec 64))
(assert (= (bvmul x x) (_ bv2 64)))
(check-sat)
