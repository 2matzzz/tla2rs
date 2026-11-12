---- MODULE ModelArithInt ----
\* A model value in arithmetic: TLC names the Java method of the operator in the module it loaded
\* (Integers) and the cast that failed
EXTENDS Integers
CONSTANT None
VARIABLE x
TypeOK == x \in (0..1) \cup {None}
Init == x = 0
NextNeg ==
        /\ x' = IF x = 1 THEN None ELSE 1
        /\ x = 0 \/ -x < 0
NextPlus ==
        /\ x' = IF x = 1 THEN None ELSE 1
        /\ x = 0 \/ x + 1 > 0
NextLess ==
        /\ x' = IF x = 1 THEN None ELSE 1
        /\ x = 0 \/ x < 2
NextAtLeast ==
        /\ x' = IF x = 1 THEN None ELSE 1
        /\ x = 0 \/ 2 >= x
====
