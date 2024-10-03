; Fails on parsing back in after dumping post-asserts due to HO, hence we
; have to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; EXPECT: sat
; COMMAND-LINE: --sygus-inference=try -q
(set-logic ALL)
(assert
 (forall ((a Real))
  (exists ((b Real))
   (exists ((c Real))
    (and
     (< (+ a c) 0.0)
     (or (distinct a 0.0) (= b 5.0))
     (distinct (+ b c) 1.0)
     (< c 1.0))))))
(check-sat)
