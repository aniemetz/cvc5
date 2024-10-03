; Fails on parsing back in after dumping post-asserts due to HO, hence we have
; to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; EXPECT: fail
(set-logic ALL)
(set-option :produce-abducts true)
(set-option :cegis-sample use)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(get-abduct e (= a b) ((f Bool) (g Int)(h Int))
              ((f Bool ( (= g h))) (g Int (d)) (h Int (c))))
