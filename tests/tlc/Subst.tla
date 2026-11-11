---- MODULE Subst ----
\* A spec whose constants an MC module fills in through `<-` in the cfg
EXTENDS Naturals, FiniteSets
CONSTANTS Procs, Items, Owner, Conf, Limit
VARIABLES held, step
\* Replaced from the cfg
Cap == 1
TypeOK == held \in [Procs -> SUBSET Items] /\ step \in 0..Limit
Init == held = [p \in Procs |-> {}] /\ step = 0
Take(p, i) == /\ \A q \in Procs : i \notin held[q]
              /\ Owner[i] = p \/ Conf.shared
              /\ Cardinality(held[p]) < Cap
              /\ held' = [held EXCEPT ![p] = @ \cup {i}]
              /\ step' = IF step < Limit THEN step + 1 ELSE step
Drop(p) == held[p] # {} /\ held' = [held EXCEPT ![p] = {}] /\ UNCHANGED step
Next == \E p \in Procs : Drop(p) \/ \E i \in Items : Take(p, i)
Inv == \A p \in Procs : Cardinality(held[p]) <= Conf.max
====
