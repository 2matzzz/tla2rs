---- MODULE InferRange ----
\* Variables without a TypeOK entry whose integer ranges are inferred as finite: a count of a set
\* of bounded type, a value taken modulo a constant, and one drawn from a constant range
EXTENDS Naturals, FiniteSets
CONSTANTS Procs, Items
VARIABLES held, cnt, turn, lvl
TypeOK == held \in [Procs -> SUBSET Items]
Init == /\ held = [p \in Procs |-> {}]
        /\ cnt = [p \in Procs |-> 0]
        /\ turn = 0
        /\ lvl = 1
Add(p, i) == /\ held' = [held EXCEPT ![p] = @ \cup {i}]
             /\ cnt' = [cnt EXCEPT ![p] = Cardinality(held'[p])]
             /\ turn' = (turn + 1) % 3
             /\ UNCHANGED lvl
Clear(p) == /\ held[p] # {}
            /\ held' = [held EXCEPT ![p] = {}]
            /\ cnt' = [cnt EXCEPT ![p] = 0]
            /\ lvl' \in 1..3
            /\ UNCHANGED turn
Next == \E p \in Procs : Clear(p) \/ \E i \in Items : Add(p, i)
Inv == /\ \A p \in Procs : cnt[p] = Cardinality(held[p])
       /\ turn \in 0..2 /\ lvl \in 1..3
\* Violated: the counterexample prints the inferred function
NotFull == \A p \in Procs : cnt[p] < 3 \/ lvl = 1
====
