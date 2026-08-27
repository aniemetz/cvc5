; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --incremental
; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --incremental --bv-solver=bitblast-internal
; EXPECT: sat
; EXPECT: unsat
; Refinement across user contexts: the first query refines the abstraction of
; (bvmul a b) up to the bit-blasting fallback, the second query (in a new
; scope, after the refinement lemmas of the first one were retracted) requires
; the exact semantics of the same product again. The disjunction prevents the
; operands from being substituted away in preprocessing.
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(push 1)
(assert (= (bvmul a b) #x0f))
(assert (bvugt a #x01))
(assert (bvugt b #x01))
(check-sat)
(pop 1)
(push 1)
(assert (or (and (= a #x03) (= b #x05) (distinct (bvmul a b) #x0f))
            (and (= a #x02) (= b #x07) (distinct (bvmul a b) #x0e))))
(check-sat)
(pop 1)
