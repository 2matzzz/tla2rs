---- MODULE InstLet ----
\* An instance's action whose LET definition calls another definition of the instantiated module
EXTENDS Naturals
VARIABLE count
I == INSTANCE InstLetInner WITH tally <- count
Init == count = 0
Next == I!Bump
Low == count < 3
====
