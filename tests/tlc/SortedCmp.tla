---- MODULE SortedCmp ----
\* A value compared with a sorted set it cannot be compared with: TLC searches the set and fails on
\* the first comparison, with the element in the middle; a set written out is compared with in order
EXTENDS Naturals
VARIABLES s, t, r, n
Trio == {<<"a">>, <<"b">>, <<"c">>}
Quad == {<<"a">>, <<"b">>, <<"c">>, <<"d">>}
TypeOK == s \in {"x", "y"} /\ t \in {1, 2} \X {3} /\ r \subseteq 1..4 /\ n \in 0..2
Init == s = "x" /\ t = <<1, 3>> /\ r = {1, 2, 3, 4} /\ n = 0
Next == n < 2 /\ n' = n + 1 /\ UNCHANGED <<s, t, r>>
InTrio == n = 1 => s \in Trio
InQuad == n = 1 => s \in Quad
InState == n = 1 => t \notin r
====
