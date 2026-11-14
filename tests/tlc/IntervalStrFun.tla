---- MODULE IntervalStrFun ----
\* An interval keeps its form as a value of a function over strings, which prints as a record (or
\* with :> and @@ when a string is no field name), and of a function built by :> and @@, through
\* EXCEPT and application. The invariant compares ToString with the text TLC makes
EXTENDS Naturals, Sequences, TLC
VARIABLES f, g, h, p, u, x, n
Init == /\ f = [s \in {"a", "b"} |-> 1..2]
        /\ g = ("a" :> 2..3) @@ ("b" :> {4})
        /\ h = (1 :> 1..2) @@ (3 :> {5})
        /\ p = 0 :> {}
        /\ u = [s \in {"a b", "c"} |-> 1..2]
        /\ x = {}
        /\ n = 0
Next == /\ n < 3 /\ n' = n + 1
        /\ f' = [f EXCEPT !["a"] = IF n = 0 THEN {1, 2} ELSE 3..4]
        /\ g' = IF n = 0 THEN g @@ ("c" :> 5..6) ELSE [g EXCEPT !["b"] = 1..1]
        /\ h' = IF n = 0 THEN (2 :> 6..7) @@ h ELSE h
        /\ p' = IF n = 1 THEN 4 :> 1..3 ELSE p
        /\ u' = [u EXCEPT !["c"] = {n}]
        /\ x' = h[1]
        /\ PrintT(<<n, f, g, h, p, u, f["b"]>>)
Inv == /\ ToString(x) \in {"{}", "1..2"}
       /\ ToString(f["b"]) = "1..2"
       /\ ToString(f) \in {"[a |-> 1..2, b |-> 1..2]", "[a |-> {1, 2}, b |-> 1..2]", "[a |-> 3..4, b |-> 1..2]"}
Short == n < 2
====
