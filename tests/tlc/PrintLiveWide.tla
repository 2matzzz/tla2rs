---- MODULE PrintLiveWide ----
\* As PrintLive, with more successors per state than TLC's set of them starts with room for, and
\* fairness over several actions
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Go(d) == x' = (x + d) % 11 /\ PrintT(<<"go", d, x, x'>>)
Next == \E d \in 1..10 : Go(d)
Spec == Init /\ [][Next]_x /\ \A d \in {1, 2} : WF_x(Go(d))
Back == PrintT(<<"back", x>>) /\ x = 0
Often == []<>Back
Leads == (x = 3) ~> Back
====
