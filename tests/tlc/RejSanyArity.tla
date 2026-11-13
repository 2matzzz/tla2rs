---- MODULE RejSanyArity ----
\* An operator that takes arguments, named without them, is refused, but not as an argument; so is a call with
\* other arguments, whose arguments SANY then does not look at
EXTENDS Naturals, Sequences
VARIABLE x
RECURSIVE Down(_)
Early == Down
Down(n) == IF n = 0 THEN 0 ELSE Down(n - 1)
Size == Len
Apply(F(_), v) == F(v)
Fine == Apply(Len, <<1>>)
Once(v) == v
Twice == Once(q, 2)
Inner == LET G(a) == a IN G(1, 2)
Init == x = 0
Next == x' = (x + 1) % 3
====
