; COMMAND-LINE: --bv-abstraction
; COMMAND-LINE: --bv-abstraction --bv-solver=bitblast-internal
; EXPECT: sat
; Ported from Bitwuzla test/regress/solver/abstract/murxla-a2f5f3aa83d5a854.min.smt2
(set-logic ALL)
(set-info :status sat)
(declare-const __ Bool)
(declare-const x (Array Bool Float64))
(check-sat-assuming ((fp.isNaN (select (store x false (fp.min (select x false) (_ +zero 11 53))) __))))
