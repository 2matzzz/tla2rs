---- MODULE LiveTab ----
\* Properties TLC checks with its tableau (temporal formulas other than <>[]A and []<>A). The
\* checker follows TLC's tableau and its search over the product with the state graph, so it prints
\* the counterexample TLC prints
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == \/ x < 3 /\ x' = x + 1
        \/ x = 3 /\ x' = 1
        \/ x = 2 /\ x' = 0
Spec == Init /\ [][Next]_x /\ WF_x(Next)
SpecNone == Init /\ [][Next]_x
\* Two promises in one tableau
Both == ~(<>(x = 2) /\ <>(x = 3))
\* <>[] under [] and =>
NestedEv == [](x = 0 => <>[](x # 0))
\* An order of solution without a tableau, which finds nothing, then one with a tableau
Mixed == []<>(x # 5) /\ (x = 1 ~> x = 0)
Never0 == [](x = 1 => [](x # 0))
\* Without fairness: a counterexample that ends stuttering
Ev3 == <>(x = 3)
====
