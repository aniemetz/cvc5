; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --produce-proofs --check-proofs
; EXPECT: unsat
; Abstraction is not supported with proofs and is disabled if proofs are
; enabled (which also forces --bv-solver=bitblast-internal). Odd * odd is odd,
; hence unsat.
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= ((_ extract 0 0) a) #b1))
(assert (= ((_ extract 0 0) b) #b1))
(assert (= ((_ extract 0 0) (bvmul a b)) #b0))
(check-sat)
