; COMMAND-LINE: --finite-model-find --fmf-bound -i
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun P (Int) Bool)
(declare-fun ten () Int)

(assert (forall ((x Int)) (=> (<= 1 x ten) (P x))))

(push)
(assert (= ten 10))

(check-sat)
(pop)
