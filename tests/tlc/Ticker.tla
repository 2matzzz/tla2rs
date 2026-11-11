---- MODULE Ticker ----
\* Instantiated by SpecInst
EXTENDS Naturals
CONSTANT N
VARIABLE c
Init == c = 0
Next == c' = (c + 1) % N
Spec == Init /\ [][Next]_c /\ WF_c(Next)
====
