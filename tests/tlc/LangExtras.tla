---- MODULE LangExtras ----
\* Assert, ^, IsFiniteSet, <<x, y>> as bound variables, UNION of sets built from the state, and
\* \X and SUBSET of sets that depend on the state (in TLC's order)
EXTENDS Integers, FiniteSets, TLC
CONSTANTS Procs
VARIABLES S, f, pick
TypeOK == S \subseteq Procs /\ f \in [Procs -> 0..3] /\ pick \subseteq Procs
Init == S = {} /\ f = [p \in Procs |-> 0] /\ pick = {}
Next == \/ \E <<p, k>> \in Procs \X (1..2) :
             /\ f[p] + k <= 3
             /\ f' = [f EXCEPT ![p] = f[p] + k]
             /\ S' = S \cup {p}
             /\ UNCHANGED pick
        \/ \E T \in SUBSET S :
             /\ T # {}
             /\ pick' = T
             /\ S' = S \ T
             /\ UNCHANGED f
        \/ /\ S # {}
           /\ pick' = CHOOSE T \in SUBSET S : Cardinality(T) = Cardinality(S) - 1
           /\ UNCHANGED <<S, f>>
Inv == /\ Assert(\A p \in Procs : f[p] <= 3, "f out of range")
       /\ UNION {{p} : p \in S} = S
       /\ UNION {S, pick} \subseteq Procs
       /\ \A <<p, q>> \in S \X pick : p \in S /\ q \in pick
       /\ Cardinality(SUBSET S) = 2^Cardinality(S)
       /\ IsFiniteSet(S)
       /\ {<<p, f[p]>> : p \in S} = {t \in S \X (0..3) : t[2] = f[t[1]]}
       /\ \A <<p, k>> \in {<<q, f[q]>> : q \in Procs} : k = f[p]
\* Violated
Bound == \A p \in Procs : f[p] < 3 \/ Cardinality(pick) < 2
====
