---- MODULE SanyScopeNested ----
\* A nested module sees the names defined before it, and may name a parameter like one defined after it
EXTENDS Naturals
VARIABLE x
Step == 1
---- MODULE Inner ----
Add(After) == After + Step
====
I == INSTANCE Inner
After == 2
Init == x = 0
Next == x' = I!Add(x + After) % 4
====
