---- MODULE GuardedArith ----
\* Arithmetic and < on integer-or-model-value variables, guarded by a test for the model value
EXTENDS Integers
CONSTANTS Procs, None
VARIABLES slot, total
TypeOK == slot \in [Procs -> (0..3) \cup {None}] /\ total \in 0..6
Init == slot = [p \in Procs |-> None] /\ total = 0
Next == \E p \in Procs :
          \/ /\ slot[p] = None
             /\ slot' = [slot EXCEPT ![p] = 0]
             /\ UNCHANGED total
          \/ /\ slot[p] # None /\ slot[p] < 3
             /\ slot' = [slot EXCEPT ![p] = slot[p] + 1]
             /\ total' = IF total + 1 > 6 THEN 0 ELSE total + 1
          \/ /\ slot[p] # None => slot[p] + 1 > 2
             /\ slot' = [slot EXCEPT ![p] = None]
             /\ UNCHANGED total
Inv == \A p \in Procs : (IF slot[p] = None THEN 0 ELSE -slot[p]) <= 0
\* Violated
Low == \A p \in Procs : slot[p] = None \/ slot[p] < 3
====
