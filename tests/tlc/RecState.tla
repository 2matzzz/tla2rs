---- MODULE RecState ----
\* Recursive operators that assign variables, called with arguments from the state. TLC evaluates
\* the call as the body with the arguments bound, so it can assign at any depth and branch
EXTENDS Naturals, FiniteSets
VARIABLE s, n, x, y
RECURSIVE Count(_), Pick(_), Sum(_, _), Both(_)
\* Assigns only once the recursion reaches 0
Count(k) == IF k = 0 THEN x' = n ELSE Count(k - 1)
\* One branch per element: like x' \in S
Pick(S) == IF S = {} THEN FALSE
           ELSE LET e == CHOOSE e \in S : TRUE IN x' = e \/ Pick(S \ {e})
\* Assigns at the end, from what the recursion collected
Sum(S, acc) == IF S = {} THEN x' = acc % 5
               ELSE LET e == CHOOSE e \in S : TRUE IN Sum(S \ {e}, acc + e)
\* Assigns y at the first level, then only compares it
Both(k) == IF k = 0 THEN x' = 1 ELSE y' = k /\ Both(k - 1)
Init == s = {} /\ n = 0 /\ x = 0 /\ y = 0
Grow == /\ s' \in {s \cup {k} : k \in 1..3}
        /\ n' = (n + 1) % 3
        /\ UNCHANGED <<x, y>>
Next == \/ Grow
        \/ Count(n) /\ UNCHANGED <<s, n, y>>
        \/ Pick(s) /\ UNCHANGED <<s, n, y>>
        \/ Sum(s, n) /\ UNCHANGED <<s, n, y>>
        \/ Both(n) /\ UNCHANGED <<s, n>> /\ (n = 0 => y' = y)
Small == x < 4
====
