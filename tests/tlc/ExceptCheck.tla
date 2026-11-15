---- MODULE ExceptCheck ----
\* EXCEPT warnings raised only where TLC checks a successor or builds its liveness graph: in the
\* CONSTRAINT, the ACTION_CONSTRAINT, an action property, the VIEW, and through a recursive
\* operator in those and in a liveness property. TLC checks each successor as an action yields it
\* and stops at the first that violates the invariant, so a later successor's warning never comes
EXTENDS Naturals, TLC
VARIABLE x
vars == <<x>>
T == <<1, 2>>
RECURSIVE Probe(_, _)
Probe(n, v) == IF n = 0 THEN [T EXCEPT ![v] = 0] = T ELSE Probe(n - 1, v)
W(v) == v < 5 \/ [T EXCEPT ![v] = 0] = T
WRec(v) == v < 5 \/ Probe(1, v)
Init == x = 0
Next == \/ x < 9 /\ x' = x + 1
        \/ x < 9 /\ x' = x + 5
\* An action that warns too, on the first step, before the constraints of its successor
NextW == \/ x < 9 /\ x' = x + 5 /\ (x = 0 => [T EXCEPT ![9] = 0] = T)
         \/ x < 9 /\ x' = x + 1
Inv == x # 1
Con == W(x)
ConRec == WRec(x)
ACon == W(x')
AConRec == WRec(x')
Act == [][W(x')]_vars
ActRec == [][WRec(x')]_vars
View == <<x, W(x)>>
ViewRec == <<x, WRec(x)>>
\* A liveness property that warns only through the recursive operator, on every state
NextL == x' = (x + 1) % 3
SpecL == Init /\ [][NextL]_vars /\ WF_vars(NextL)
LiveRec == []<>(Probe(1, x + 3))
InvL == x < 2
====
