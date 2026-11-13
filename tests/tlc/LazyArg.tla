---- MODULE LazyArg ----
\* Arguments of an operator where TLC evaluates an expression: each is evaluated where the body first
\* uses it and kept for the rest of the body, in the order the body uses them; one the body does not
\* use is never evaluated, nor fails
EXTENDS Naturals, TLC
VARIABLE x
Sum(a) == a + a
Second(a, b) == b /\ a /\ b
Pick(c, a, b) == IF c THEN a ELSE b
AllOf(S, a) == \A e \in S : a /\ e > 0
Init == x = 0
Next == /\ x < 2
        /\ Sum(IF PrintT(<<"sum", x>>) THEN 1 ELSE 2) > 0
        /\ Second(PrintT(<<"first", x>>), PrintT(<<"second", x>>))
        /\ Pick(TRUE, PrintT(<<"picked", x>>), 1 \div 0 = 0)
        /\ AllOf({1, 2, 3}, PrintT(<<"all", x>>))
        /\ x' = x + 1
Inv == /\ Sum(IF PrintT(<<"inv", x>>) THEN x ELSE 0) >= 0
       /\ Pick(x < 5, TRUE, 1 \div 0 = 0)
====
