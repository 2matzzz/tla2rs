---- MODULE StdOverride ----
\* The cfg replaces Nat and Seq, operators of standard modules, with finite definitions, as one does to
\* model-check a spec that quantifies over them
EXTENDS Naturals, Sequences
CONSTANT Vals
VARIABLE x, q
SmallNat == 0..3
ShortSeq(S) == UNION {[1..n -> S] : n \in 0..2}
Init == x \in Nat /\ q = <<>>
Next == \/ \E y \in Nat : y > x /\ x' = y /\ UNCHANGED q
        \/ \E s \in Seq(Vals) : Len(s) > Len(q) /\ q' = s /\ UNCHANGED x
Spec == Init /\ [][Next]_<<x, q>>
Inv == \A s \in Seq(Vals) : Len(s) <= 2
====
