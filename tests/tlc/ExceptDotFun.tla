---- MODULE ExceptDotFun ----
\* In an EXCEPT path, .a is ["a"]: it also updates a function over strings (built with a function
\* constructor or with :> and @@), alone and nested with other steps, with @ for the old value
EXTENDS Naturals, TLC
VARIABLES f, h, m, s, n
F0 == ("a" :> 0) @@ ("b" :> 0)
H0 == [k \in {"a", "b"} |-> [j \in {"b", "c"} |-> 0]]
M0 == [i \in 1..2 |-> [k \in {"a", "b"} |-> 0]]
S0 == [k \in {"a", "b"} |-> <<0, 1..2>>]
Init == f = F0 /\ h = H0 /\ m = M0 /\ s = S0 /\ n = 0
Next == /\ n < 3
        /\ n' = n + 1
        /\ f' = [f EXCEPT !.a = @ + 1, !.b = n]
        /\ h' = [h EXCEPT !.a.b = @ + 1, !.b.c = n]
        /\ m' = [m EXCEPT ![1].a = @ + 1, ![2].b = f.a]
        /\ s' = [s EXCEPT !.a[1] = @ + 1, !.b[2] = 1..n]
\* A key outside the domain changes nothing, and TLC warns
NextMiss == /\ n < 2
            /\ n' = n + 1
            /\ f' = [f EXCEPT !.c = 1, !.a = n]
            /\ h' = [h EXCEPT !.a.d = 1]
            /\ UNCHANGED <<m, s>>
\* The same updates of constant values
InitConst == /\ f = [F0 EXCEPT !.a = @ + 5, !.c = 1]
             /\ h = [H0 EXCEPT !.a.b = @ + 5, !.e.b = 1]
             /\ m = [M0 EXCEPT ![1].a = @ + 5]
             /\ s = [S0 EXCEPT !.a[1] = @ + 5, !.b[2] = 1..3]
             /\ n = 0
Inv == h.a.b < 2
====
