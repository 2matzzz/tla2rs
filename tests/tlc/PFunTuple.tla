---- MODULE PFunTuple ----
EXTENDS Naturals, TLC
VARIABLES x
TypeOK == x \in [1..2 -> BOOLEAN]
\* A function built with @@ and a tuple in one IF or set: the tuple is a function over 1..n
Init == x = <<FALSE, FALSE>>
Next == \/ x' \in ({(1 :> TRUE) @@ (2 :> x[1])} \cap [1..2 -> BOOLEAN])
        \/ x' = IF x[1] THEN (1 :> FALSE) @@ (2 :> TRUE) ELSE <<x[2], TRUE>>
        \/ x' \in {<<TRUE, TRUE>>, (1 :> FALSE) @@ (2 :> FALSE)}
====
