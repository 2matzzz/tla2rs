---- MODULE LiveConst ----
\* A temporal property with a predicate of constant level under [] or <>. TLC evaluates such a
\* predicate to TRUE or FALSE, and its tableau ignores the constant (it checks state predicates
\* only), so `<>TRUE` is violated by every behavior. <>[] and []<> of a constant are checked
\* without the tableau, and hold as they should
EXTENDS Naturals
CONSTANT N
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
EvTrue == <>TRUE
EvEq == <>(N = 2)
Leads == x = 1 ~> (N > 1)
NotBox == ~[]FALSE
AE == []<>TRUE
EA == <>[](N = 2)
EvState == <>(x = x)
====
