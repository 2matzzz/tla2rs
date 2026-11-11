---- MODULE SetsOfSets ----
\* Sets of sets and sets of functions held in the state, iterated and printed in TLC's order
\* (smaller sets first), and SUBSET of a set in the state as a value
EXTENDS Naturals, FiniteSets, TLC
CONSTANTS Procs
VARIABLES groups, pick, fs, subs
TypeOK == /\ groups \in SUBSET SUBSET Procs
          /\ pick \subseteq Procs
          /\ fs \subseteq [Procs -> SUBSET Procs]
          /\ subs \subseteq SUBSET Procs
Init == groups = {} /\ pick = {} /\ fs = {} /\ subs = {{}}
Next == \/ \E g \in SUBSET Procs :
             /\ g \notin groups
             /\ Cardinality(groups) < 3
             /\ groups' = groups \cup {g}
             /\ UNCHANGED <<pick, fs, subs>>
        \/ /\ \E g \in groups : g # pick
           /\ pick' = CHOOSE g \in groups : g # pick
           /\ fs' = IF Cardinality(fs) < 2 THEN fs \cup {[p \in Procs |-> pick']} ELSE fs
           /\ subs' = SUBSET pick'
           /\ UNCHANGED groups
Inv == /\ \A g \in groups : g \subseteq Procs
       /\ \A f \in fs : \A p \in Procs : f[p] \in groups
       /\ subs = SUBSET pick
\* Violated
Few == Cardinality(groups) < 3 \/ Cardinality(pick) # 2
====
