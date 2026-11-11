---- MODULE RtSpec ----
\* RTnow and RTBound of RealTime as conjuncts of SPECIFICATION: TLC treats them like other
\* temporal conjuncts (it checks neither), and refuses them once there is a temporal property
EXTENDS Naturals, RealTime
VARIABLE x
vars == <<x, now>>
Init == x = 0 /\ now = 0
Tick == now' = now + 1 /\ UNCHANGED x
Inc == x' = (x + 1) % 3 /\ UNCHANGED now
Next == Tick \/ Inc
Con == now < 3
Inv == x < 2
Ev1 == <>(x = 1)
SpecNow == Init /\ [][Next]_vars /\ RTnow(x)
SpecFirst == RTnow(x) /\ Init /\ [][Next]_vars
SpecBound == Init /\ [][Next]_vars /\ RTBound(Inc, x, 0, 2)
====
