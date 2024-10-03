; Fails on parsing back in after dumping post-asserts due to HO, hence we have
; to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; EXPECT: fail
(set-logic ALL)
(set-option :preprocess-only true)
(set-option :preregister-mode lazy)
(set-option :produce-abducts true)
(declare-fun x (Int) Bool)
(get-abduct A (x 0))
