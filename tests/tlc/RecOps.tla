---- MODULE RecOps ----
\* Recursive operators that take operators as parameters
EXTENDS Naturals, Sequences
VARIABLES items, total
RECURSIVE FoldSeq(_, _, _)
FoldSeq(Op(_, _), acc, s) == IF s = <<>> THEN acc ELSE FoldSeq(Op, Op(acc, Head(s)), Tail(s))
RECURSIVE Apply(_, _, _)
Apply(F(_), n, x) == IF n = 0 THEN x ELSE Apply(F, n - 1, F(x))
Add(a, b) == a + b
Double(x) == 2 * x
ASSUME FoldSeq(Add, 0, <<1, 2, 3>>) = 6 /\ Apply(LAMBDA y : y * 3, 3, 1) = 27
Init == items = <<>> /\ total = 0
Next == \/ Len(items) = 4 /\ UNCHANGED <<items, total>>
        \/ /\ Len(items) < 4
           /\ \E k \in 1..3 :
                /\ items' = Append(items, k)
                /\ total' = FoldSeq(Add, 0, items') + FoldSeq(LAMBDA a, b : IF a > b THEN a ELSE b, 0, items)
Inv == /\ total <= 15
       /\ Apply(Double, Len(items), 1) = 2 ^ Len(items)
       /\ \A m \in 1..2 : Apply(LAMBDA y : y + m, Len(items), 0) = m * Len(items)
\* Violated
Small == FoldSeq(Add, 0, items) < 8
====
