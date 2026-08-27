; COMMAND-LINE: --bv-abstraction
; COMMAND-LINE: --bv-abstraction --bv-solver=bitblast-internal
; EXPECT: sat
; Ported from Bitwuzla test/regress/solver/abstract/murxla-346218efd24c9aba.min.smt2
(set-logic ALL)
(set-option :global-declarations true)
(set-info :status sat)
(declare-const _x0 (_ FloatingPoint 11 53))
(check-sat-assuming ((fp.isNaN _x0)))
