---- MODULE RecEnabled ----
\* ENABLED inside a recursive operator: in an invariant, a guard of Next, Init and a property
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc(i) == x < 3 /\ x' = x + i /\ UNCHANGED y
Bump == y < 2 /\ y' = y + 1 /\ UNCHANGED x
Next == Inc(1) \/ Inc(2) \/ Bump
RECURSIVE CountEnabled(_)
CountEnabled(n) == IF n = 0 THEN 0 ELSE (IF ENABLED Inc(n) THEN 1 ELSE 0) + CountEnabled(n - 1)
RECURSIVE AnyEnabled(_)
AnyEnabled(S) == IF S = {} THEN FALSE
                 ELSE LET i == CHOOSE i \in S : TRUE IN ENABLED Inc(i) \/ AnyEnabled(S \ {i})
Inv == CountEnabled(2) = (IF x < 3 THEN 2 ELSE 0)
InvBad == CountEnabled(2) > 0 \/ y < 2
RECURSIVE FirstEnabled(_)
FirstEnabled(S) == IF S = {} THEN FALSE
                   ELSE LET i == CHOOSE i \in S : TRUE IN IF ENABLED Inc(i) THEN TRUE ELSE FirstEnabled(S \ {i})
NextGuard == (FirstEnabled({1, 2}) /\ Bump) \/ Inc(1) \/ Inc(2)
NextGuardOr == (AnyEnabled({1, 2}) /\ Bump) \/ Inc(1) \/ Inc(2)
InitEnabled == x = 0 /\ y \in 0..1 /\ CountEnabled(2) = 2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Done == <>(CountEnabled(2) = 0)
====
