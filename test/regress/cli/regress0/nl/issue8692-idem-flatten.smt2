(set-logic ALL)
(set-info :status sat)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= 0.0 (* b (/ a (- 1)))))
(check-sat)
