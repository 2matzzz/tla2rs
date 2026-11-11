---- MODULE RtClock ----
\* EXTENDS RealTime gives the variable now; TLC cannot check RTBound (it quantifies over Real and
\* uses \EE), and refuses it as a property
EXTENDS Naturals, RealTime
VARIABLE x
vars == <<x, now>>
Init == x = 0 /\ now = 0
Tick == now' = now + 1 /\ UNCHANGED x
Inc == x' = (x + 1) % 3 /\ UNCHANGED now
Next == Tick \/ Inc
Inv == x < 2
Con == now < 3
Spec == Init /\ [][Next]_vars
RT == RTBound(Inc, x, 0, 2)
====
