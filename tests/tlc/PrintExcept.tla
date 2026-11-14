---- MODULE PrintExcept ----
\* An EXCEPT of a function whose body prints. Where the result is applied, TLC keeps the function
\* unevaluated: evaluating the EXCEPT evaluates the body at each argument it updates (unless an
\* earlier update names it; outside the domain it only warns), then the new value, and applying the
\* result evaluates the body at the argument unless an update names it. Used as a value, the
\* function is computed whole first
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
F(t) == [k \in {1, 2, 3} |-> PrintT(<<t, k, x>>)]
Apply == x < 1 /\ x' = x + 1 /\ LET g == [F("apply") EXCEPT ![2] = FALSE] IN PrintT("m0") /\ g[1] /\ PrintT("m1") /\ ~g[2] /\ PrintT("m2") /\ g[3] /\ g[1]
At == x < 1 /\ x' = x + 1 /\ LET g == [F("at") EXCEPT ![2] = ~@] IN PrintT("m0") /\ ~g[2] /\ PrintT("m1") /\ g[3]
Whole == x < 1 /\ x' = x + 1 /\ LET g == [F("whole") EXCEPT ![2] = FALSE] IN PrintT("m0") /\ g = g /\ PrintT("m1") /\ g[1] /\ PrintT("m2") /\ PrintT(g)
Two == x < 1 /\ x' = x + 1 /\ LET g == [F("two") EXCEPT ![2] = FALSE, ![3] = ~@] IN PrintT("m0") /\ g[1] /\ PrintT("m1") /\ g # g
Nest == x < 1 /\ x' = x + 1 /\ LET g == [[F("nest") EXCEPT ![2] = FALSE] EXCEPT ![1] = ~@] IN PrintT("m0") /\ g[3] /\ PrintT("m1") /\ ~g[1]
Out == x < 1 /\ x' = x + 1 /\ LET g == [F("out") EXCEPT ![7] = FALSE] IN PrintT("m0") /\ g[1]
ValueRhs == x < 1 /\ x' = x + 1 /\ PrintT("m0") /\ PrintT([F("value") EXCEPT ![2] = PrintT("rhs")])
AppRhs == x < 1 /\ x' = x + 1 /\ PrintT("m0") /\ [F("app") EXCEPT ![2] = PrintT("rhs")][3]
LetValue == x < 1 /\ x' = x + 1 /\ LET g == [F("let") EXCEPT ![2] = PrintT("rhs")] IN PrintT("m0") /\ PrintT(g) /\ PrintT("m1") /\ g[3]
Inline == x < 1 /\ x' = x + 1 /\ [F("inline") EXCEPT ![2] = FALSE][3] /\ PrintT("m0") /\ ~[F("inl2") EXCEPT ![2] = FALSE][2]
====
