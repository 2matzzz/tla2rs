---- MODULE SpecShape ----
\* How TLC splits SPECIFICATION: through conjunctions and definitions without arguments (also
\* of an instance), not through LET, \E or operators with arguments; what it does without an
\* initial predicate or a next-state action
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 4
v == x
SLet == LET F == WF_v(Next) IN Init /\ [][Next]_v /\ F
SExInit == \E i \in {0} : (x = i /\ [][Next]_v)
SAllNext == Init /\ \A i \in {1} : [][Next]_v
SEn == Init /\ [][Next]_v /\ ENABLED Next
SAllInit == (\A i \in {0} : x = i) /\ [][Next]_v
SFalse == x = 1 /\ Init /\ [][Next]_v
Both(n) == x = n /\ [][Next]_v
SArgs == Both(0)
Fair(n) == WF_v(x = n /\ Next)
SFairArg == Init /\ [][Next]_v /\ Fair(1)
Body == Init /\ [][Next]_v
SDef == Body /\ WF_v(Next)
NotZero == x # 0
NonNeg == x >= 0
AlwNonNeg == [](x >= 0)
Ev1 == <>(x = 1)
AP == [][x' > x]_x
====
