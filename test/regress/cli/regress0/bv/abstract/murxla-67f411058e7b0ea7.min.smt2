; COMMAND-LINE: --bv-abstraction --incremental
; COMMAND-LINE: --bv-abstraction --incremental --bv-solver=bitblast-internal
; EXPECT: sat
; EXPECT: sat
; Ported from Bitwuzla test/regress/solver/abstract/murxla-67f411058e7b0ea7.min.smt2
(set-logic ALL)
(declare-fun x (Bool) Bool)
(set-info :status sat)
(check-sat-assuming ((x false)))
(set-info :status sat)
(check-sat-assuming ((x false)))
