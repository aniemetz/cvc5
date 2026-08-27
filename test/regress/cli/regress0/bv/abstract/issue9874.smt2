; COMMAND-LINE: --bv-abstraction
; COMMAND-LINE: --bv-abstraction --bv-solver=bitblast-internal
; EXPECT: unsat
; DISABLE-TESTER: proof
(set-logic QF_BV)
(declare-const a (_ BitVec 64))
(assert (= a (bvurem (bvnot a) a)))
(check-sat)
