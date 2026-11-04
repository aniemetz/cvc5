; REQUIRES: unrestricted-mode
; COMMAND-LINE: --bv-abstraction --theoryof-mode=term
; COMMAND-LINE: --bv-abstraction --bv-solver=bitblast-internal --theoryof-mode=term
; EXPECT: unsat
; DISABLE-TESTER: proof
; As tier4-lemma-not-abstracted.smt2, but with --theoryof-mode=term, where
; the tier-4 atom `t = (bvmul x x)` is owned by THEORY_UF (`t` is a variable).
; BVSolverBitblastInternal thus never receives the atom as a fact, only the
; equalities between the terms in its class that are shared with THEORY_BV
; (here, `t = 2`). Hence the multiplier must be bit-blasted when the tier-4
; lemma is added, not when its atom is asserted.
(set-logic QF_UFBV)
(declare-const x (_ BitVec 64))
(assert (= (bvmul x x) (_ bv2 64)))
(check-sat)
