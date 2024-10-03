; Fails on parsing back in after dumping post-asserts, hence we have
; to disable the dump-post tester.
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --parse-skolem-definitions --print-skolem-definitions
; EXPECT: sat
(set-option :parse-skolem-definitions true)
(set-logic QF_NIA)
(set-info :status sat)
(declare-fun b () Int)
(declare-fun a () Int)
(assert (not (= a b)))
(assert (not (<= a b)))
(assert (= b (div a 0)))
(assert (or (not (= a (@int_div_by_zero a))) (not (>= (+ a (* (- 1) (@int_div_by_zero a))) 1))))
(check-sat)
