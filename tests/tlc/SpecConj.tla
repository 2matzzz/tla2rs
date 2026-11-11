---- MODULE SpecConj ----
\* Temporal conjuncts of SPECIFICATION other than [][Next]_v and WF / SF. TLC checks none of them;
\* it checks temporal properties under all of them (a property that is a state predicate under []
\* is still checked as an invariant, on every state)
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 4
B == x < 3 /\ x' = x + 1
v == x
SBox == Init /\ [][Next]_v /\ [](x < 3)
SEv == Init /\ [][Next]_v /\ <>(x = 3)
SBoxEv == Init /\ [][Next]_v /\ []<>(x = 3)
SEvBox == Init /\ [][Next]_v /\ <>[](x = 0)
SLeads == Init /\ [][Next]_v /\ ((x = 1) ~> (x = 2))
STwo == Init /\ [][Next]_v /\ [][x' # 2]_x
SOrF == Init /\ [][Next]_v /\ (WF_v(Next) \/ SF_v(B))
SNotF == Init /\ [][Next]_v /\ ~[]<>(x = 1)
SImpF == Init /\ [][Next]_v /\ (WF_v(B) => WF_v(Next))
SBoxEn == Init /\ [][Next]_v /\ []ENABLED B
SBoxImp == Init /\ [][Next]_v /\ [](x = 1 => <>(x = 2))
SQBox == Init /\ [][Next]_v /\ \A i \in {1, 2} : []<>(x = i)
SBoxWF == Init /\ [][Next]_v /\ [](x < 3) /\ WF_v(Next)
SExF == Init /\ [][Next]_v /\ \E i \in {1, 2} : WF_v(x = i /\ Next)
SIfF == Init /\ [][Next]_v /\ IF TRUE THEN WF_v(Next) ELSE TRUE
SEvAct == Init /\ [][Next]_v /\ <><<Next>>_v
SBoxAng == Init /\ [][Next]_v /\ []<><<Next>>_v
SMix == Init /\ [][Next]_v /\ (x = 0 \/ <>(x = 1))
PLt3 == x < 3
PEvAlwLt3 == <>[](x < 3)
PAlwLt3 == [](x < 3)
PEv3 == <>(x = 3)
PEv1 == <>(x = 1)
PEvAlwNot1 == <>[](x # 1)
PLeads == (x = 1) ~> (x = 2)
PBoxEv2 == []<>(x = 2)
====
