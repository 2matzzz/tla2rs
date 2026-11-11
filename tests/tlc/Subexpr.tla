---- MODULE Subexpr ----
\* Subexpressions of definitions named by position (Op!1, Op!<<, Op!>>, Op!:, Op!(e)) and by
\* label (Op!lab, Op(a)!lab(b)), as SANY names them. Infix /\ and \/ are binary and associate to
\* the left, so A3!1 is the first two of three conjuncts
EXTENDS Naturals
VARIABLE x, y
A3 == x < 9 /\ y < 9 /\ x + y > 1
B(p) == p + x > 3 /\ x # p
Bul == /\ x >= 0
       /\ y >= 0
       /\ lim :: x + y < 6
C == \E k \in 1..3 : k + x = 4
Ch == CHOOSE k \in 0..5 : k > x
Q2 == \A i \in 0..1, j \in 2..3 : i + x < j + y
F == LET d == x * 2 IN d + 1
I == IF x > y THEN x - y ELSE y - x
T == <<x, x + 7, {y}>>
R == [a |-> x, b |-> y + 1]
Cs == CASE x = 0 -> 10 [] x = 1 -> 20 [] OTHER -> 30
G(p) == \E q \in 1..2 : lab2(q) :: p + q > x
Step == /\ go :: x < 3
        /\ x' = x + 1
        /\ y' = y
Init == x = 0 /\ y = 0
Next == \/ Step!go /\ Step!2 /\ Step!3
        \/ /\ y < 2 /\ y' = y + 1
           /\ UNCHANGED x
Infix == A3!1 = (x < 9 /\ y < 9) /\ A3!2 = (x + y > 1) /\ A3!1!2 = (y < 9)
Ops == B(1)!1 = (1 + x > 3) /\ B(2)!2!<< = x /\ B(2)!2!>> = 2 /\ Bul!3 = (x + y < 6) /\ Bul!lim
Binders == C!1 = 1..3 /\ C!(2) = (x = 2) /\ C!(2)!<< = 2 + x /\ Ch!(4) = (4 > x) /\ Ch!1 = 0..5
           /\ Q2!(1, 3) = (1 + x < 3 + y) /\ Q2!2 = 2..3
Others == F!: = 2 * x + 1 /\ F!1 = F /\ I!1 = (x > y) /\ I!3 = y - x /\ T!3 = {y} /\ R!2 = y + 1
          /\ Cs!1!2 = 10 /\ Cs!2!1 = (x = 1) /\ Cs!3!2 = 30 /\ T!2!1 = x
Labels == G(1)!lab2(2) = (3 > x) /\ Bul!lim = (x + y < 6)
Viol == Step!go
====
