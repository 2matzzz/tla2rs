---- MODULE ToStringWide ----
\* ToString of values whose integers have no bound the type inference finds: it does not read
\* n < Max, so n may be any natural number and m any integer up to 0. TLC prints each value; the
\* invariants compare the text with that of the same value built as a constant
EXTENDS Integers, TLC
CONSTANT Max
VARIABLES n, m, s, t
Init == n = 0 /\ m = 0 /\ s = {} /\ t = ""
Next == /\ n < Max
        /\ n' = n + 1
        /\ m' = m - 2
        /\ s' = IF n < 6 THEN s \cup {3 * n} ELSE s
        /\ t' = ToString(m)
Elems(k) == {3 * i : i \in 0..(IF k < 6 THEN k ELSE 6) - 1}
ShowInt == [k \in 0..Max |-> <<ToString(k), ToString(-2 * k)>>]
ShowSet == [k \in 0..Max |-> ToString(Elems(k))]
ShowRec == [k \in 0..Max |-> <<ToString(<<k, -2 * k>>), ToString([a |-> Elems(k), b |-> k])>>]
IntInv == <<ToString(n), ToString(m)>> = ShowInt[n]
SetInv == ToString(s) = ShowSet[n]
RecInv == <<ToString(<<n, m>>), ToString([a |-> s, b |-> n])>> = ShowRec[n]
Last == t /= "-4"
====
