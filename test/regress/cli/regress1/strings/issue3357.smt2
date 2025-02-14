(set-logic ALL)

(set-info :status unsat)
(declare-fun a () String)
(declare-fun b () String)
(declare-const c String)
(declare-const d String)
(declare-const g String)
(declare-const e String)
(declare-const f String)
(assert (or  
            (and (= d (str.++ e g)) (str.in_re e (re.* (str.to_re "HG4"))) (> 0 (str.to_int g)) (= 1 (str.len e)) (= 2 (str.len (str.substr b 0 (str.len d)))))  
            (and 
                (str.in_re (str.replace (str.replace a c "") "T" "") (re.* (re.union (str.to_re "a") (str.to_re "")))) 
                (= 0 (str.to_int (str.replace (str.replace a c "") "T" "")))))
)
(assert (= b (str.++ d f)))
(check-sat)
