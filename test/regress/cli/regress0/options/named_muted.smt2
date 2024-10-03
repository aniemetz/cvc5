; DISABLE-TESTER: dump
; DISABLE-TESTER: dump-post
; COMMAND-LINE: --print-success
; EXPECT: success
; EXPECT: success

(set-logic UF)
(assert (! true :named t))
