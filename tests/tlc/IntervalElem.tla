---- MODULE IntervalElem ----
\* An interval keeps its form when a state takes it from a constant set (\in, CHOOSE), from a set
\* written with it, as a constant function's value, or from an IF whose condition makes a string.
\* The invariant compares ToString with the text TLC makes, so a checker that printed {3, 4} for
\* 3..4 would report a violation TLC does not
EXTENDS Naturals, Sequences, TLC
VARIABLES x, y, z, p, w, n
F == [i \in 1..2 |-> 1..i]
G == [a |-> 2..3, b |-> {4}]
Init == /\ x \in {1..2, {5}}
        /\ y = CHOOSE s \in {3..4, {6}} : 3 \in s
        /\ z = F[2]
        /\ p = <<G.a, 0>>
        /\ w = {5}
        /\ n = 0
Next == \/ /\ n < 2 /\ n' = n + 1
           /\ x' = IF n = 0 THEN x ELSE {7}
           /\ y' \in {y, 8..9, {1}}
           /\ z' = F[1]
           /\ p' = <<G.b, n>>
           /\ w' = IF ToString(n % 2) = "0" THEN 5..6 ELSE {5}
           /\ PrintT(<<n, x, y, z, p, ToString(x), ToString(z), F, <<G.a>>, ToString(<<F[2]>>)>>)
        \/ n = 2 /\ UNCHANGED <<x, y, z, p, w, n>>
Inv == /\ ToString(z) \in {"1..2", "1..1"}
       /\ ToString(y) \in {"3..4", "8..9", "{1}"}
       /\ ToString(x) \in {"1..2", "{5}", "{7}"}
       /\ ToString(p[1]) \in {"2..3", "{4}"}
       /\ ToString(w) \in {"{5}", "5..6"}
====
