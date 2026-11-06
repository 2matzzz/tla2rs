---- MODULE InferRecIf ----
\* r has no type declaration, so its record type is inferred from Init and Next.
\* The two IF branches build records whose field ranges differ; the inferred
\* type must cover both instead of shrinking to the first one's.
EXTENDS Naturals
VARIABLES r
Init == r = [e |-> 0, k |-> "a"]
Next == r' = IF r.e < 3 THEN [e |-> r.e + 1, k |-> "b"] ELSE [e |-> 0, k |-> "a"]
Inv == r.e <= 3
====
