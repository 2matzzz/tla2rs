---- MODULE BigSteps ----
\* Constant sets of more than a thousand elements, which the checker enumerates from their parts
\* instead of writing them out: in an action (\E and CHOOSE), and in quantifiers and set
\* constructors in an invariant
EXTENDS Naturals, FiniteSets
VARIABLES p, k

Pairs == (1..300) \X {1, 5, 9, 20}
Lamps == [1..11 -> BOOLEAN]
Recs == [a : 1..100, b : BOOLEAN, c : {1, 4, 9}, d : {"x", "y"}]
Square == (1..40) \X (1..40)

Init == p = <<1, 1>> /\ k = 0
\* To any pair one column on, in another row
Step == /\ p[1] < 30
        /\ \E q \in Pairs : q[1] = p[1] + 1 /\ q[2] # p[2] /\ p' = q /\ k' = (k + q[2]) % 3
\* To the first pair past a bound, as CHOOSE picks it
Jump == /\ p[1] = 30
        /\ p' = CHOOSE q \in Pairs : q[1] > 290 - k /\ q[2] # 1
        /\ UNCHANGED k
Next == Step \/ Jump

Inv == /\ \A g \in Lamps : Cardinality({i \in 1..11 : g[i]}) <= 11
       /\ \E r \in Recs : r.a = (p[1] % 100) + 1 /\ r.c = 9 /\ r.d = "y"
       /\ Cardinality({q \in Pairs : q[1] <= p[1]}) = 4 * p[1]
       /\ {q[2] : q \in Pairs} = {1, 5, 9, 20}
       /\ \E q \in Square : q[1] * q[2] = (p[1] % 40) + 1
       /\ p \in Pairs
\* Fails after steps that depend on the order of the pairs
NotThere == ~(p[1] = 12 /\ k = 2)
====
