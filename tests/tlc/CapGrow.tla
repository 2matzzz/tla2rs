---- MODULE CapGrow ----
\* A sequence and a set held as an array that outgrow where their capacity starts, with nothing in
\* the spec bounding them: the checker is built again with more room and checks from the start
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLES x, q, s
ASSUME PrintT("checked once")
TypeOK == /\ x \in 0..12
          /\ q \in Seq(0..20)
          /\ s \subseteq (0..20) \X (0..20)
Init == x = 0 /\ q = <<>> /\ s = {}
Next == /\ x < 12
        /\ x' = x + 1
        /\ q' = Append(q, x)
        /\ s' = s \cup {<<x, 20 - x>>}
Inv == x = 0 \/ (Cardinality(s) = x /\ q[x] = x - 1)
\* Violated in the last state
Short == x < 12
====
