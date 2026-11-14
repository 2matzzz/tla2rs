---- MODULE PrintLive ----
\* What TLC evaluates while it builds its liveness graph, after each state's successors: the step
\* predicates on the step to each successor in its set of them (WF_x(A) is ~ENABLED <<A>>_x \/
\* <<A>>_x on each step; a step that leaves x unchanged does not evaluate A), the state predicates,
\* then each particle of the tableau on each successor; a node new to a state already expanded
\* makes it evaluate that state again and generate its successors again. Each new initial state is
\* checked against the formula's particles before its invariants. A definition called in a
\* property prints its parts of constant level when TLC starts, and again with the rest
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
InitTwo == x \in {0, 1} /\ PrintT(<<"init", x>>)
A == \E d \in {1, 2} : x + d <= 3 /\ x' = x + d /\ PrintT(<<"A", x, x'>>)
B == x = 3 /\ PrintT(<<"B", x>>) /\ x' = 0
Next == A \/ B
SpecA == Init /\ [][Next]_x /\ WF_x(A)
SpecB == Init /\ [][Next]_x /\ WF_x(B)
SpecS == Init /\ [][Next]_x /\ SF_x(B)
SpecN == Init /\ [][Next]_x
SpecT == InitTwo /\ [][Next]_x /\ WF_x(A)
SpecAll == Init /\ [][Next]_x /\ WF_x(Next)
P == PrintT(<<"P", x>>) /\ x = 0
Q == PrintT(<<"Q", x>>) /\ x = 3
R == PrintT(<<"R", x>>) /\ x = 1
Often == []<>P
Ev == <>Q
Leads == R ~> (x = 7)
Inv == PrintT(<<"inv", x>>)
Stay == x < 2 /\ PrintT(<<"stay", x>>) /\ x' = x
SpecLoop == Init /\ [][Next \/ Stay]_x /\ WF_x(Stay \/ A)
Step == []<><<A>>_x
Inline == <>(PrintT("inline") /\ x = 3)
Cst == PrintT("def") /\ x = 3
EvCst == <>Cst
====
