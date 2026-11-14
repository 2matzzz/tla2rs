---- MODULE EmptyFunToString ----
\* ToString of an empty function that a variable over part of a domain holds: one left by a
\* function constructor over DOMAIN p \ {4}, and one from [i \in {} |-> {}] before a step assigns
\* a function over another domain. TLC makes << >> for both
EXTENDS Naturals, TLC
VARIABLE p
Init == p = 4 :> 1
Next == p' = [i \in DOMAIN p \ {4} |-> p[i]]
InitJoin == p = [i \in {} |-> {}]
NextJoin == p' = 4 :> 1..3
Inv == ToString(p) = IF DOMAIN p = {} THEN "<< >>" ELSE "(4 :> 1)"
InvJoin == ToString(p) = IF DOMAIN p = {} THEN "<< >>" ELSE "(4 :> 1..3)"
InvViol == ToString(p) # "<< >>"
====
