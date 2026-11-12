---- MODULE ActName ----
\* How TLC names the actions of a trace: it splits the next-state relation through \/, \E over a
\* constant set, LET, labels and calls with constant arguments, and names each part by the innermost
\* definition called and the position of the part
EXTENDS Naturals
VARIABLE x
Init == x = 0
Inc(k) == x' = x + k
Up == \E k \in {1} : Inc(k)
Dyn == \E k \in {x, x + 1} : x' = k + 1
ByVar == Inc(x - x + 1)
Lets == LET d == 1 IN x' = x + d
Lab == lab :: x' = x + 1
One == \/ x' = x + 1
Paren == (x > 0 /\ x' = x + 1) \/ ((x' = x + 1))
Both == /\ x < 5
        /\ \/ x' = x + 1
           \/ x' = x + 2
RECURSIVE Rec(_)
Rec(n) == IF n = 0 THEN x' = x + 1 ELSE Rec(n - 1)
Recs == Rec(2) \/ (x > 9 /\ Rec(x))
RecVar == Rec(x - x)
Sub(n) == \/ Inc(n)
          \/ \E k \in 1..n : x' = x + k + 2
Mixed == Sub(1) \/ Lets
SpecInl == Init /\ [][x' = x + 1]_x
SpecBox == Init /\ [][Up]_x
Inv == x < 2
====
