---- MODULE SparseThenVar ----
\* A set too large for a bitmask (sparse), declared before another variable.
\* Unpacking must keep reading after the set ends, not restart at bit 0.
EXTENDS Naturals
VARIABLES s, x, y
TypeOK == /\ s \subseteq [a: 0..15, b: 0..15]
          /\ x \in 0..5
          /\ y \in BOOLEAN
Init == s = {} /\ x = 0 /\ y = FALSE
Next == \/ /\ x < 5
           /\ x' = x + 1
           /\ y' = ~y
           /\ s' = IF x < 2 THEN s \cup {[a |-> x, b |-> 15 - x]} ELSE s
        \/ /\ x = 5
           /\ x' = 0
           /\ UNCHANGED <<s, y>>
Inv == x # 5 \/ y = TRUE
====
