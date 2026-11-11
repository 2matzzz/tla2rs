---- MODULE LiveForms ----
\* Temporal forms TLC accepts, under weak, strong, inline and quantified fairness, and none
EXTENDS Naturals
VARIABLE x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x < 2 /\ x' = x + 1 /\ UNCHANGED y
Reset == x = 2 /\ x' = 0 /\ UNCHANGED y
Flip == y' = 1 - y /\ UNCHANGED x
Next == Inc \/ Reset \/ Flip
SpecW == Init /\ [][Next]_vars /\ WF_vars(Inc) /\ WF_vars(Reset)
SpecS == Init /\ [][Next]_vars /\ SF_vars(Inc) /\ SF_vars(Reset)
SpecNone == Init /\ [][Next]_vars
SpecInl == Init /\ [][Next]_vars /\ WF_vars(x < 2 /\ x' = x + 1 /\ UNCHANGED y) /\ WF_vars(Reset)
SpecQ == Init /\ [][Next]_vars /\ \A k \in {0, 1} : WF_vars(x = k /\ x' = k + 1 /\ UNCHANGED y) /\ WF_vars(Reset)
P1 == []<>(x = 2)
P2 == <>[](y = 0)
P3 == []<>ENABLED Reset
P4 == []<><<Reset>>_vars
P5 == <>[][Flip]_vars
P6 == (x = 1) ~> (x = 2)
P7 == \E k \in {1, 2} : []<>(x = k)
P8 == \A k \in {1, 2} : []<>(x = k)
P9 == []<>(x = 2) \/ <>[](y = 1)
P10 == [](x = 1 => <>(x = 0))
P11 == <>(x = 2 /\ <>(x = 0))
P12 == []<>(ENABLED Flip /\ x = 0)
P13 == ~[]<>(y = 1)
P14 == <>[]ENABLED Inc
P15 == []<><<Flip>>_y
====
