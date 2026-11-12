---- MODULE RecInit ----
\* A recursive operator that assigns variables, called in the initial predicate with an argument
\* from a variable assigned before. TLC evaluates the call as its body with the argument bound
EXTENDS Naturals
VARIABLE n, x, y
RECURSIVE Fill(_), Pair(_)
\* One initial state per k down to 0
Fill(k) == IF k = 0 THEN x = 0 ELSE x = k \/ Fill(k - 1)
\* Assigns y at the first level, then only compares it
Pair(k) == IF k = 0 THEN TRUE ELSE y = n * 2 /\ Pair(k - 1)
Init == n \in 1..3 /\ Fill(n) /\ Pair(n)
Next == x < 5 /\ x' = x + 1 /\ UNCHANGED <<n, y>>
Small == x + y < 10
====
