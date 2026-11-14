---- MODULE RecFunEq ----
\* A record is the function over its field names: a set the compiler evaluates holds [a |-> 0, b |-> 1]
\* once, also when the same function is built with :>, @@, a function constructor or EXCEPT
EXTENDS Naturals, FiniteSets, TLC
VARIABLES x, y
G == ("b" :> 1) @@ ("a" :> 0)
S == {[a |-> 0, b |-> 1], G, [G EXCEPT !["b"] = 1], [k \in {"a", "b"} |-> IF k = "a" THEN 0 ELSE 1]}
T == {"a" :> 0, [("a" :> 1) EXCEPT !["a"] = 0], [a |-> 0]}
Init == x \in 1..Cardinality(S) /\ y = 0
Next == /\ y < 2
        /\ y' = y + 1
        /\ x' \in 1..(Cardinality(T) + Cardinality({{[a |-> 0]}, {"a" :> 0}}))
\* The set's element as a value of the state
InitIn == x \in S /\ y \in T
NextIn == UNCHANGED <<x, y>>
====
