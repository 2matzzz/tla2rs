---- MODULE LiveConstErr ----
\* TLC evaluates each part of constant level of a temporal property when it starts, going through
\* /\, \/, ~, =>, IF and LET: also a branch of an IF that is never taken, whose error stops it
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Untaken == []<>(IF {} = {} THEN x = 0 ELSE CHOOSE c \in {} : TRUE)
Let == <>(LET s == {c \in BOOLEAN : FALSE} IN IF s = {} THEN x = 1 ELSE CHOOSE c \in s : TRUE)
Leads == x = 0 ~> (IF x = 1 THEN TRUE ELSE CHOOSE c \in {} : TRUE)
Taken == []<>(IF x = 0 THEN TRUE ELSE x = 1)
\* but not inside <<A>>_v, an action of the formula
Angle == []<><<Next /\ (IF {} = {} THEN TRUE ELSE CHOOSE c \in {} : TRUE)>>_x
\* A call of a definition of constant level is evaluated whole: the branch its IF does not take is not
Pick(s) == IF s = {} THEN TRUE ELSE CHOOSE c \in s : TRUE
Call == [](Pick({}) => <>(x = 1))
====
