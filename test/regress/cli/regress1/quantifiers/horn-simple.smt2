; Fails on parsing back in after dumping post-asserts due to HO, hence we
; have to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --sygus-unif-pi=complete --sygus-inference=try
; EXPECT: sat
(set-logic UFLIA)
(set-info :status sat)
(declare-fun I (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (I x))))

(assert (forall ((x Int)) (=> (and (I x) (< x 6)) (I (+ x 1)))))

(assert (forall ((x Int)) (=> (I x) (<= x 10))))

(check-sat)
