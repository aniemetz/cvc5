; SCRUBBER: grep -o "Parse Error: parser-line-error.smt2:7"
; EXPECT: Parse Error: parser-line-error.smt2:7
; EXIT: 1
(set-info :source |abc
def
ghi|)
misplaced text
