---- MODULE HigherOrder ----
\* Operators that take operator arguments, passed by name (also LET definitions and parameters
\* passed on) or as LAMBDA
EXTENDS Naturals, FiniteSets
VARIABLES x, seen
Apply(F(_), v) == F(v)
Twice(F(_), v) == F(F(v))
PassOn(F(_), v) == Apply(F, v)
MapSet(F(_), S) == {F(e) : e \in S}
Fold2(Op(_, _), a, b, c) == Op(Op(a, b), c)
Inc(v) == (v + 1) % 5
Add(a, b) == (a + b) % 5
TypeOK == x \in 0..4 /\ seen \subseteq 0..4
Init == x = 0 /\ seen = {}
Next == \/ x' = Apply(Inc, x) /\ seen' = seen \cup {x}
        \/ x' = Twice(LAMBDA v : (v * 2) % 5, x) /\ seen' = MapSet(LAMBDA e : (e + x) % 5, seen)
        \/ LET K == 3
               G(v) == (v + K) % 5
           IN x' = PassOn(G, x) /\ seen' = seen
        \/ x' = Fold2(Add, x, 1, 2) /\ UNCHANGED seen
        \/ x' = Fold2(LAMBDA a, b : (a * b) % 5, x, 2, 3) /\ UNCHANGED seen
Inv == \A e \in seen : Apply(LAMBDA v : v < 5, e)
\* Violated
Small == Cardinality(seen) < 4
====
