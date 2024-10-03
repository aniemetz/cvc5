; Fails on parsing back in after dumping post-asserts due to HO, hence we
; have to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --produce-abducts
; EXPECT: fail
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and (> x 5) (< x 2)))
(get-abduct A (> x y))
