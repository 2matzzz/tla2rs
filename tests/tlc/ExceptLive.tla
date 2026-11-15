---- MODULE ExceptLive ----
\* EXCEPT warnings raised only while TLC evaluates the liveness checks: in the state and action
\* predicates of a property, and in a fair action and its subscript. TLC prints them as it builds
\* its liveness graph, among the lines of the actions, and decides <<A>>_v on a step that leaves v
\* unchanged without A. The first warning of a run comes at most twice (once with the note about
\* -nowarning), any other text once
EXTENDS Naturals, TLC
VARIABLE x
vars == <<x>>
T == <<1, 2>>
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
SpecFair == Init /\ [][Next]_vars /\ WF_vars(Next /\ [T EXCEPT ![x + 3] = 0] = T)
SpecSub == Init /\ [][Next]_vars /\ WF_<<x, [T EXCEPT ![x + 3] = 0]>>(Next)
AE == []<>([T EXCEPT ![x + 3] = 0] = T)
Ev == <>([T EXCEPT ![x + 3] = 0] = T /\ x = 2)
Act == []<><<[T EXCEPT ![x' + 3] = 0] = T>>_vars
Fail == <>([T EXCEPT ![x + 3] = 0] # T)
Cyc == []<>(x = 2)
\* Two warnings, each raised on every state
Two == []<>([T EXCEPT ![x + 3] = 0] = T /\ [T EXCEPT ![x + 4] = 0] = T)
\* With an action that warns too, one that prints, and an invariant TLC finds violated
NextW == x' = (x + 1) % 3 /\ (x = 1 => [T EXCEPT ![9] = 0] = T)
SpecW == Init /\ [][NextW]_vars /\ WF_vars(NextW)
NextP == x' = (x + 1) % 3 /\ PrintT(x)
SpecP == Init /\ [][NextP]_vars /\ WF_vars(NextP)
Inv == x < 2
====
