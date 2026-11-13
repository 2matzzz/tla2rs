---- MODULE BoxName ----
EXTENDS Naturals
VARIABLES x
Init == x = 0
Next == x' = (x + 1) % 3
Inv == x < 2
Fls == FALSE
\* TLC names the invariant []P is checked as after P when P applies an operator without arguments
Prop == []Inv
PropDef == []Fls
PropFalse == [](FALSE)
PropPart == []FALSE /\ []TRUE
PropExpr == [](x < 2 /\ TRUE)
====
