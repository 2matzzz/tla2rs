---- MODULE ModelArith ----
\* A model value in arithmetic: TLC names the Java method of the operator in the module it loaded
\* (Naturals) and the cast that failed
EXTENDS Naturals
CONSTANT None
VARIABLE x
TypeOK == x \in (0..1) \cup {None}
Init == x = 0
NextPlus ==
        /\ x' = IF x = 1 THEN None ELSE 1
        /\ x = 0 \/ 1 + x > 0
NextMinus ==
        /\ x' = IF x = 1 THEN None ELSE 1
        /\ x = 0 \/ x - 1 >= 0
NextTimes ==
        /\ x' = IF x = 1 THEN None ELSE 1
        /\ x = 0 \/ x * 2 > 0
NextDivide ==
        /\ x' = IF x = 1 THEN None ELSE 1
        /\ x = 0 \/ x \div 2 >= 0
NextMod ==
        /\ x' = IF x = 1 THEN None ELSE 1
        /\ x = 0 \/ x % 2 > 0
NextExpt ==
        /\ x' = IF x = 1 THEN None ELSE 1
        /\ x = 0 \/ x ^ 2 > 0
NextDotDot ==
        /\ x' = IF x = 1 THEN None ELSE 1
        /\ x = 0 \/ 1 \in x..2
====
