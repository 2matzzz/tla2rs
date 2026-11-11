---- MODULE RecVars ----
\* Recursive operators that read variables in Init and primed variables in Next
EXTENDS Naturals, FiniteSets
CONSTANT N
VARIABLES lo, hi, sum
RECURSIVE SumTo(_)
SumTo(k) == IF k < lo THEN 0 ELSE k + SumTo(k - 1)
RECURSIVE SumNext(_)
SumNext(k) == IF k < lo' THEN 0 ELSE k + SumNext(k - 1)
RECURSIVE Grew(_)
Grew(k) == IF k = 0 THEN hi' >= hi ELSE Grew(k - 1) /\ UNCHANGED lo
Init == /\ lo \in 1..2
        /\ hi = N
        /\ sum = SumTo(hi)
Next == \/ /\ hi < N + 2
           /\ hi' = hi + 1
           /\ lo' = lo
           /\ Grew(2)
           /\ sum' = SumNext(hi')
        \/ /\ lo < hi
           /\ lo' = lo + 1
           /\ hi' = hi
           /\ sum' = SumNext(hi')
        \/ /\ UNCHANGED <<lo, hi>>
           /\ sum' = SumTo(hi)
Inv == sum = SumTo(hi)
\* Violated
Bound == sum < 10
====
