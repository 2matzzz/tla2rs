---- MODULE StrFieldName ----
\* A function over strings prints as a record only when every string of its domain is an
\* identifier (with a letter, and not WF_ or SF_ followed by more), when TLC starts and while it
\* explores: a function over part of the strings decides by those it holds
EXTENDS Integers, TLC
VARIABLES k, f, g
TypeOK == k \in 0..2
ASSUME PrintT(<<("a-b" :> 1), ("1" :> 1), ("_x" :> 1), ("IF" :> 1), ("" :> 1), ("x1" :> 1), ("1a" :> 1),
                ("_" :> 1), ("WF_" :> 1), ("SF_a" :> 1), ("a b" :> 1), [s \in {"c", "d:e"} |-> 0]>>)
ASSUME PrintT(("abc" :> 1) @@ ("a-b" :> 2))
Keys == <<"ok", "a-b", "fine">>
Init == k = 0 /\ f = ("ok" :> 0) /\ g = [s \in {"c", "d:e"} |-> 0]
Next == k < 2 /\ k' = k + 1 /\ f' = f @@ (Keys[k' + 1] :> k') /\ g' = [g EXCEPT !["c"] = k']
Shown == PrintT(<<f, g>>)
Small == k < 2
====
