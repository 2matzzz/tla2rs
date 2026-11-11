---- MODULE StateSets ----
\* Sets built from the state as values: UNION of a set of sets, [a : S] records, tuples in
\* [1..n -> S], and sets of sequences under Seq(S)
EXTENDS Integers, Sequences, FiniteSets
VARIABLES groups, n, msgs
TypeOK == /\ groups \subseteq SUBSET (1..3) /\ n \in 0..2
          /\ msgs \in Seq(0..1) /\ Len(msgs) <= 2
Init == groups = {} /\ n = 0 /\ msgs = <<>>
Next == \/ \E g \in SUBSET (1..3) : Cardinality(g) = 1 /\ groups' = groups \cup {g} /\ UNCHANGED <<n, msgs>>
        \/ n < 2 /\ n' = n + 1 /\ \E m \in 0..1 : msgs' = Append(msgs, m) /\ UNCHANGED groups
Inv == /\ Cardinality(UNION groups) = Cardinality(groups)
       /\ Cardinality([id : 1..n, flag : BOOLEAN]) = 2 * n
       /\ \A r \in [id : 1..n] : r.id \in 1..n
       /\ (<<0, 0>> \in [1..n -> 0..1]) = (n = 2)
       /\ (msgs \in [1..n -> 0..1])
       /\ {msgs, <<1>>} \subseteq Seq(0..1)
\* Violated
Small == Cardinality(UNION groups) + n < 4
====
