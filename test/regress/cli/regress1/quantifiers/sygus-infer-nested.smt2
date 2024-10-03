; Fails on parsing back in after dumping post-asserts due to HO, hence we
; have to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --sygus-inference=try -q
(set-logic LIA)
(set-info :status sat)
(assert (forall ((x Int) (y Int)) (or (<= x (+ y 1)) (exists ((z Int)) (and (> z y) (< z x))))))
(check-sat)
