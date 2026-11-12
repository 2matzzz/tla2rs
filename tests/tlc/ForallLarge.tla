---- MODULE ForallLarge ----
\* \A over a set from the state whose elements can take more than 16 values, with a body that
\* assigns a variable for some elements only, wherever they come in the set. TLC evaluates it as
\* the conjunction of the body over the elements in order
EXTENDS Naturals, FiniteSets
VARIABLE s, x, y
Init == s = {} /\ x = 0 /\ y = 0
Grow == /\ Cardinality(s) < 3
        /\ s' \in {s \cup {k} : k \in {3, 11, 20}}
        /\ UNCHANGED <<x, y>>
\* The element 20 assigns, wherever it comes; without it, x' is assigned after
Cond == /\ \A k \in s : k = 20 => x' = 7
        /\ 20 \notin s => x' = 1
        /\ UNCHANGED <<s, y>>
\* Each element above 10 assigns y' or compares with it, and the first one also branches on x'
Above == /\ s # {}
         /\ \A k \in s : k > 10 => (y' = k % 4 /\ x' \in {k % 3, 2})
         /\ (\A k \in s : k <= 10) => (x' = 0 /\ y' = 0)
         /\ UNCHANGED s
Next == Grow \/ Cond \/ Above
NotSeven == x # 7
====
