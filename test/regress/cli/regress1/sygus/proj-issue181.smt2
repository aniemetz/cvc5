; Fails on parsing back in after dumping post-asserts due to HO, hence we have
; to disable the dump-post tester.
; DISABLE-TESTER: dump-post
(set-logic ALL)
(set-option :sygus-inference try)
(set-info :status sat)
(declare-fun a (Int) Int) 
(assert (exists ((b Int)) (distinct (a b) (- b  29)))) 
(assert (distinct (a 0) (- 4))) 
(assert (= (a (- 99)) (- 107))) 
(check-sat) 
