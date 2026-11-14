---- MODULE RecPlainMerge ----
\* @@ of two records of fixed fields, assigned to a variable that also holds a record
EXTENDS Naturals, TLC
VARIABLE r
Init == r = [a |-> 1]
Next == r.a < 3 /\ r' = ([a |-> r.a + 1] @@ [b |-> 3])
NextConst == r.a < 3 /\ r' = ([a |-> 2] @@ [b |-> 3])
NextSame == r.a < 3 /\ r' = ([a |-> r.a + 1] @@ [a |-> 0])
NextSet == r.a < 3 /\ r' \in {[a |-> r.a + 1], [a |-> r.a + 1] @@ [b |-> r.a]}
Inv == r.a \in 1..3
InvB == "b" \in DOMAIN r => r.b \in 1..3
====
