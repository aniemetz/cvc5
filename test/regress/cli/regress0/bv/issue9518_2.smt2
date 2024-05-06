(set-logic QF_ABV)
(set-info :status unsat)
(set-option :bv-solver bitblast-internal)
(set-option :check-models true)
(declare-const a (Array (_ BitVec 64) (_ BitVec 64)))
(declare-const b (_ BitVec 64))
(assert (= (store a #x0000000000000000 #x1111111111111111)
(store a #x0000000000000000 (bvadd #x1111111111111111
(bvor #x1111111111111111 b)))))
(check-sat)