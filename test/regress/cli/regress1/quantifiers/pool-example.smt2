; Fails on parsing back in after dumping post-asserts due to HO, hence we
; have to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --pool-inst
; EXPECT: unsat
(set-logic ALL)
(declare-pool L Int ())

(declare-fun P (Int) Bool)

(assert (not (=
(forall ((x Int)) (! 
  (P x)
  :skolem-add-to-pool ((- x 100) L) :pool (L) ))
(forall ((x Int)) (!
  (P (+ x 100))
  :skolem-add-to-pool ((+ x 100) L) :pool (L) )
))))

(check-sat)
