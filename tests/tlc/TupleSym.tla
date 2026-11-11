---- MODULE TupleSym ----
\* SYMMETRY permutes the model values inside tuples, also in a function domain of tuples.
EXTENDS Naturals, TLC
CONSTANTS Procs
VARIABLES owner, held, cnt
TypeOK == /\ owner \in Procs \X Procs
          /\ held \subseteq Procs \X {1, 2}
          /\ cnt \in [Procs \X Procs -> 0..1]
P0 == CHOOSE p \in Procs : TRUE
Init == /\ owner = <<P0, P0>>
        /\ held = {}
        /\ cnt = [t \in Procs \X Procs |-> 0]
Next == \E p, q \in Procs :
          \/ /\ owner' = <<q, owner[1]>>
             /\ held' = held \cup {<<p, IF p = q THEN 1 ELSE 2>>}
             /\ UNCHANGED cnt
          \/ /\ cnt[p, q] = 0
             /\ cnt' = [cnt EXCEPT ![<<p, q>>] = 1]
             /\ held' = held \ {<<p, 1>>}
             /\ UNCHANGED owner
Sym == Permutations(Procs)
====
