---- MODULE LazyLet ----
\* LET definitions where TLC evaluates an expression: each is evaluated where it is first used and
\* kept for the rest of the LET, and one never used is never evaluated, nor fails
EXTENDS Naturals, Sequences, TLC
VARIABLE x
RECURSIVE Depth(_)
\* A LET inside a recursive operator: once per call
Depth(n) == IF n = 0 THEN 0 ELSE LET p == PrintT(<<"depth", n>>) IN IF p /\ p THEN 1 + Depth(n - 1) ELSE 0
Init == x = 0
Next == /\ x < 3
        /\ x' = x + 1
        \* Every variable is assigned: the rest is evaluated as an expression
        /\ LET d == PrintT(<<"once", x>>) IN d /\ d
        /\ LET unused == 1 \div 0 IN TRUE
        /\ LET a == PrintT(<<"a", x>>)
               b == a /\ PrintT(<<"b", x>>)
           IN b /\ a /\ b
        /\ LET w == (IF x = 0 THEN "a" ELSE "b") \o "c" IN Len(w) = Len(w)
Inv == /\ LET d == PrintT(<<"inv", x>>)
              s == {d, ~d}
          IN d /\ s = {TRUE, FALSE}
       \* Used only when x < 2, so it never divides by zero
       /\ LET q == 4 \div (2 - x) IN x < 2 => q > 0
       /\ Depth(x) = x
\* The value of the right side of an assignment is an expression too
Step == /\ x < 3
        /\ x' = LET p == PrintT(<<"rhs", x>>) IN IF p /\ p THEN x + 1 ELSE x
\* A definition that fails is evaluated where it is first used: what is printed before comes first
Fail == /\ x < 3
        /\ x' = x + 1
        /\ LET p == PrintT(<<"before", x>>)
               q == 6 \div (2 - x)
           IN p /\ q > 0 /\ p
====
