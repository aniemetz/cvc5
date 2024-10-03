; SCRUBBER: grep -o "Cannot bind x to symbol of type Bool"
; EXPECT: Cannot bind x to symbol of type Bool
; EXIT: 1
(set-logic ALL)
(declare-const x Bool)
(declare-const x Bool)
(assert (= x x))
(check-sat)
