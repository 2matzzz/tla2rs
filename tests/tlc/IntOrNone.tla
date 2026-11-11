---- MODULE IntOrNone ----
\* Integers and model values in one type (`1..3 \cup {None}`, `Procs \cup {0}`): comparisons,
\* function arguments, membership in either direction, sets of them, and SYMMETRY.
EXTENDS Naturals, FiniteSets, TLC
CONSTANTS Procs, None
VARIABLES slot, used, seen, holder, free
TypeOK == /\ slot \in [Procs -> (1..3) \cup {None}]
          /\ used \subseteq 1..3
          /\ seen \subseteq (1..3) \cup {None}
          /\ holder \in [1..3 -> Procs \cup {0}]
          /\ free \subseteq Procs \cup {None}
Init == /\ slot = [p \in Procs |-> None]
        /\ used = {}
        /\ seen = {None}
        /\ holder = [k \in 1..3 |-> 0]
        /\ free = Procs \cup {None}
Take(p) == /\ slot[p] = None
           /\ \E k \in 1..3 : /\ k \notin used
                              /\ slot' = [slot EXCEPT ![p] = k]
                              /\ used' = used \cup {k}
                              /\ seen' = seen \cup {k}
                              /\ holder' = [holder EXCEPT ![k] = p]
                              /\ free' = free \ {p}
Give(p) == /\ slot[p] # None
           /\ used' = used \ {slot[p]}
           /\ holder' = [holder EXCEPT ![slot[p]] = 0]
           /\ slot' = [slot EXCEPT ![p] = None]
           /\ free' = free \cup {p}
           /\ UNCHANGED seen
Next == \E p \in Procs : Take(p) \/ Give(p)
Inv == /\ \A p \in Procs : slot[p] \in used \/ slot[p] = None
       /\ \A p, q \in Procs : p # q => slot[p] = None \/ slot[p] # slot[q]
       /\ \A p \in Procs : slot[p] \in {None, 1, 2, 3}
       /\ \A p \in Procs : slot[p] \in Nat \/ slot[p] = None
       /\ \A p \in Procs : slot[p] \notin Procs
       /\ \A p \in Procs : slot[p] \in free => slot[p] = None
       /\ \A p \in Procs : None \in {slot[p]} <=> slot[p] = None
       /\ \A p \in Procs : slot[p] \in seen
       /\ \A k \in 1..3 : holder[k] # 0 => slot[holder[k]] = k
       /\ \A k \in 1..3 : holder[k] \in Procs \/ holder[k] = 0
       /\ \A p \in Procs : p \in free <=> slot[p] = None
\* Violated: the counterexample prints integers and model values mixed
SomeoneHolds3 == \A p \in Procs : slot[p] # 3 \/ Cardinality(seen) < 4
Sym == Permutations(Procs)
====
