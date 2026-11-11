---- MODULE SortOps ----
\* SortSeq with a built-in operator and with a LAMBDA, and built-in infix operators passed to an
\* operator parameter
EXTENDS Integers, Sequences, TLC
VARIABLES q
Fold(Op(_, _), a, b) == Op(a, b)
TypeOK == q \in Seq(0..3)
Init == q = <<>>
Next == \E v \in 0..3 :
          /\ Len(q) < 3
          /\ q' = SortSeq(Append(q, v), <)
Inv == /\ SortSeq(q, LAMBDA a, b : a > b) = [i \in 1..Len(q) |-> q[Len(q) + 1 - i]]
       /\ Fold(+, Len(q), 1) = Len(q) + 1 /\ Fold(\cup, {1}, {2}) = {1, 2}
       /\ \A i \in 1..Len(q) - 1 : q[i] <= q[i + 1]
\* Violated
NoTriple == ~(Len(q) = 3 /\ q[1] = q[3])
====
