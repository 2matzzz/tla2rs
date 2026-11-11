---- MODULE Labels ----
\* Labels `l :: e` and `l(a) :: e`: transparent, except that TLC cannot check a labeled temporal
\* formula and does not split a labeled SPECIFICATION
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == \/ up :: (x < 2 /\ x' = x + 1)
        \/ down :: (x = 2 /\ x' = 0)
Spec == Init /\ [][Next]_x /\ WF_x(Next)
SLab == lb :: (Init /\ [][Next]_x)
SFairLab == Init /\ [][Next]_x /\ fl :: WF_x(Next)
Inv == inv :: x \in 0..2
InvQ == \A i \in {1, 2} : each(i) :: i + x > 0
Low == low :: x < 2
PLab == lp :: <>(x = 2)
PInner == <>(lq :: x = 2)
PInner2 == <>[](x = 1) \/ []<>(lr :: x = 0)
PLeads == [](x = 0 => ls :: <>(x = 1))
====
