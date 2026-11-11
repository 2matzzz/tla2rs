---- MODULE SparseCap ----
\* A function over part of an unbounded type holds at most -setcap keys; `Cardinality(DOMAIN f) <= K`
\* in TypeOK raises that bound, as it does for a set
EXTENDS Integers, FiniteSets, TLC
VARIABLES x, f
TypeOK == /\ x \in Nat
          /\ Cardinality(DOMAIN f) <= 12
Init == x = 0 /\ f = << >>
Next == x < 10 /\ x' = x + 1 /\ f' = f @@ (x * x * 1000 :> x)
Inv == \A k \in DOMAIN f : f[k] * f[k] * 1000 = k
====
