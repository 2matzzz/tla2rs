---- MODULE LiveAssumed ----
\* Temporal conjuncts of the spec that are not fairness, too many for one automaton of them and
\* the negated property: each disjunct of their normal form is checked on its own, its []<> and
\* <>[] parts as conditions on the components of the state graph
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 14 \/ x' = 0
Spec == Init /\ [][Next]_x /\ (\A i \in 0..12 : []<>(x = i)) /\ []<><<x' = 0>>_x
Back == []<>(x = 0)
Top == []<>(x = 13)
Leads == [](x = 5 => <>(x = 13))
====
