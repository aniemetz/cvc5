; Fails on parsing back in after dumping post-asserts due to HO, hence we
; have to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; EXPECT: sat
; COMMAND-LINE: --sygus-inference=try -q
(set-logic LIA)
(assert (forall ((a Int)) (=> (> a 0) (exists ((b Int)) (> a (* b 2))))))
(check-sat)
