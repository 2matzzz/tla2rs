---- MODULE OptViewVars ----
\* TLC's -view prints a VIEW that is a tuple with one element per variable it reads as a state of
\* those variables, in their order, whatever the elements are
EXTENDS Naturals
VARIABLES n, steps, flag
TypeOK == n \in 0..4 /\ steps \in 0..8 /\ flag \in BOOLEAN
Init == n = 0 /\ steps = 0 /\ flag = FALSE
Next == /\ steps < 8
        /\ \/ n' = (n + 1) % 5
           \/ n' = n
        /\ steps' = steps + 1
        /\ flag' = ~flag
Bound == n < 3
Pos == n > 0
Swapped == <<steps, n>>
Sum == <<n + steps + 10, 5>>
One == <<steps + 10>>
Fewer == <<steps + 10, 7>>
====
