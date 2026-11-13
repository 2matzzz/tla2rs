---- MODULE BoxName ----
EXTENDS Naturals
VARIABLES x, b
Init == x = 0 /\ b = TRUE
Next == x' = (x + 1) % 3 /\ b' = (x # 1)
Inv == x < 2
Fls == FALSE
\* TLC names the invariant []P is checked as after P when P applies an operator without arguments
Prop == []Inv
PropDef == []Fls
PropFalse == [](FALSE)
PropPart == []FALSE /\ []TRUE
PropExpr == [](x < 2 /\ TRUE)
PropVar == []b
====
