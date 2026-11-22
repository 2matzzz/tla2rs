---- MODULE CapPerType ----
\* Each kind of set held as an array has a capacity of its own: `big` outgrows where its kind
\* starts twice (8, then 16), while `small` (records), `pairs` (pairs of integers) and the domain
\* of `f` (pairs of an integer and a boolean) stay at 8. A set of integers of another range would
\* share the capacity of `big`: the checker holds all integers alike
EXTENDS Naturals, FiniteSets, TLC
VARIABLES n, big, small, pairs, f
TypeOK == /\ n \in 0..40
          /\ big \subseteq Nat
          /\ small \subseteq [a : 0..999]
          /\ pairs \subseteq (0..999) \X (0..999)
Init == /\ n = 0
        /\ big = {}
        /\ small = {}
        /\ pairs = {}
        /\ f = [k \in {} |-> TRUE]
Next == /\ n < 40
        /\ n' = n + 1
        /\ big' = big \cup {n * n}
        /\ small' = IF n % 8 = 0 THEN small \cup {[a |-> n]} ELSE small
        /\ \/ /\ n < 3
              /\ pairs' = pairs \cup {<<n, 999 - n>>}
           \/ /\ n >= 3
              /\ UNCHANGED pairs
        /\ f' = IF n % 10 = 0 THEN f @@ (n * 100000 :> (n % 20 = 0)) ELSE f
Inv == /\ Cardinality(big) = n
       /\ Cardinality(small) = (n + 7) \div 8
       /\ Cardinality(pairs) = IF n < 3 THEN n ELSE 3
       /\ \A k \in DOMAIN f : f[k] = (k % 2000000 = 0)
====
