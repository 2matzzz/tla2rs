---- MODULE ForallState ----
\* \A over a set from the state that assigns variables. TLC evaluates it as the conjunction of its
\* body over the elements in order: the first element assigns, the others compare (over the empty
\* set it is TRUE and assigns nothing)
EXTENDS Naturals, FiniteSets
VARIABLE s, x, y
Init == s = {} /\ x = 0 /\ y = 0
Grow == /\ s' \in {s \cup {k} : k \in 1..3}
        /\ UNCHANGED <<x, y>>
\* Every element agrees on x' (a function of the whole set)
Same == /\ s # {}
        /\ \A k \in s : x' = Cardinality(s)
        /\ y' = (y + 1) % 2
        /\ UNCHANGED s
\* Only a set of one element (or the empty set, with x' assigned after) gives successors
Each == /\ \A k \in s : x' = k
        /\ x' = IF s = {} THEN 0 ELSE x'
        /\ UNCHANGED <<s, y>>
\* \in in the body: the first element enumerates, the others test membership
Range == /\ \A k \in s, j \in s : x' \in k..3 /\ y' \in {j % 2, 1}
        /\ s # {}
        /\ UNCHANGED s
\* The element 2 assigns, wherever it comes in the set; without it, x' is assigned after
Cond == /\ \A k \in s : k = 2 => x' = 7
        /\ 2 \notin s => x' = 1
        /\ UNCHANGED <<s, y>>
Next == Grow \/ Same \/ Each \/ Range \/ Cond
Small == x < 3
NotSeven == x # 7
====
