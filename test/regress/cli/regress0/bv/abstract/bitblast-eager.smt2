; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --bitblast=eager
; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --bitblast=eager --bv-solver=bitblast-internal
; EXPECT: unsat
; Abstraction with eager bit-blasting: the input is bit-blasted as a single
; BITVECTOR_EAGER_ATOM, the bit-vector atoms it contains are abstracted
; individually. Odd * odd is odd, hence unsat.
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= ((_ extract 0 0) a) #b1))
(assert (= ((_ extract 0 0) b) #b1))
(assert (= ((_ extract 0 0) (bvmul a b)) #b0))
(check-sat)
