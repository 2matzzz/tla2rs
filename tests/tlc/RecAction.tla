---- MODULE RecAction ----
\* Recursive operators called with constant arguments in actions and in Init (TLC evaluates the
\* body, which can assign variables and branch)
EXTENDS Naturals, Sequences
VARIABLES x, y
Init == x = 0 /\ y = 0
RECURSIVE Pick(_)
Pick(n) == IF n = 0 THEN x' = 0 ELSE \/ x' = n /\ x # n
                                     \/ Pick(n - 1)
RECURSIVE Last(_)
Last(n) == IF n = 0 THEN UNCHANGED y ELSE Last(n - 1) /\ y' = (y + n) % 5
RECURSIVE Walk(_)
Walk(s) == IF s = <<>> THEN TRUE ELSE x' \in {Head(s), x} /\ Walk(Tail(s))
Next == \/ Pick(3) /\ UNCHANGED y
        \/ Last(2) /\ UNCHANGED x
        \/ Walk(<<1, 2>>) /\ UNCHANGED y
RECURSIVE SetX(_)
SetX(n) == IF n = 0 THEN x = 0 ELSE SetX(n - 1)
InitRec == SetX(2) /\ y = 0
Inv == x + y < 7
Low == x < 3
====
