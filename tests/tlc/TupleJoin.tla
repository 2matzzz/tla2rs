---- MODULE TupleJoin ----
\* Functions over 1..n built with :> and @@: `1 :> a` is the tuple <<a>>, and @@ joins it as the
\* function it is. Such a function, over part of 1..n as far as the types tell, may be assigned to
\* a variable of functions over 1..n
EXTENDS Naturals, TLC
VARIABLE x
TypeOK == x \in [1..2 -> BOOLEAN]
Init == x = <<TRUE, TRUE>>
Let == x' = (LET t == (1 :> FALSE) @@ (2 :> x[1]) IN IF t \in [1..2 -> BOOLEAN] THEN t ELSE x)
Except == x' = [(1 :> FALSE) @@ (2 :> x[1]) EXCEPT ![2] = TRUE]
In == x' \in {x, (1 :> FALSE) @@ (2 :> x[1])}
Join == x' = (1 :> FALSE) @@ (2 :> x[1])
====
