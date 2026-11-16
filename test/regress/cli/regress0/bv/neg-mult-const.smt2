; EXPECT: (bvmul x #b10111101)
; EXPECT: #b00000000
; RewriteRule<NegMult> rewrites -(x * c) to x * -c for a constant c, which
; allows AddCombineLikeTerms to cancel x * c and -(x * c).
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(simplify (bvneg (bvmul x #x43)))
(simplify (bvadd (bvmul x #x43) (bvneg (bvmul x #x43))))
