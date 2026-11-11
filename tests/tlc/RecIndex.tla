---- MODULE RecIndex ----
\* A record is a function from its field names: r["a"] and !["a"]
EXTENDS Naturals
VARIABLE r
Init == r = [a |-> 0, b |-> 1]
Next == r' = [r EXCEPT !["a"] = (@ + r["b"]) % 3]
Inv == r["a"] = r.a /\ [r EXCEPT !["b"] = 5].b = 5
Low == r["a"] < 2
====
