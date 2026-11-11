---- MODULE FunTuple ----
\* Tuples of bound variables in function constructors with several bound variables and in
\* function definitions
EXTENDS Naturals
VARIABLE x
g == [<<a, b>> \in {<<1, 2>>, <<3, 4>>}, c \in {10, 20} |-> a + b * c]
h[<<i, j>> \in (1..2) \X (1..2)] == i * 10 + j
k[<<i, j>> \in (0..2) \X (0..2), n \in 0..1] == IF n = 0 THEN i ELSE j
Init == x = 0
Next == x' = (x + 1) % 3
Inv == /\ g[<<1, 2>>, 10] = 21 /\ g[<<<<3, 4>>, 20>>] = 83
       /\ DOMAIN g = {<<1, 2>>, <<3, 4>>} \X {10, 20}
       /\ h[<<2, 1>>] = 21
       /\ k[<<x, 2 - x>>, 1] = 2 - x
Pick == k[<<x, 1>>, 0] < 2
====
