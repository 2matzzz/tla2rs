---- MODULE RecNestOp ----
\* A recursive operator whose operator argument calls the same operator again
EXTENDS Naturals, Sequences
RECURSIVE Fold(_, _, _)
Fold(Op(_, _), base, s) == IF s = <<>> THEN base ELSE Op(Head(s), Fold(Op, base, Tail(s)))
Sum(s) == Fold(LAMBDA a, b : a + b, 0, s)
Total(ss) == Fold(LAMBDA t, acc : acc + Sum(t), 0, ss)
VARIABLE q
Init == q = <<>>
Next == Len(q) < 3 /\ q' = Append(q, <<Len(q), 1>>)
Small == Total(q) < 5
====
