---- MODULE Recur ----
\* RECURSIVE operators and recursive function definitions, over constants and over the state
EXTENDS Naturals, FiniteSets
CONSTANTS Items
VARIABLES held, total, n
RECURSIVE SumSet(_), IsEven(_), IsOdd(_)
SumSet(S) == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN x + SumSet(S \ {x})
IsEven(k) == IF k = 0 THEN TRUE ELSE IsOdd(k - 1)
IsOdd(k) == IF k = 0 THEN FALSE ELSE IsEven(k - 1)
Fact[k \in 0..5] == IF k = 0 THEN 1 ELSE k * Fact[k - 1]
Fib[k \in Nat] == IF k < 2 THEN k ELSE Fib[k - 1] + Fib[k - 2]
Ack[a \in 0..2, b \in 0..3] == IF a = 0 THEN b + 1
                               ELSE IF b = 0 THEN Ack[a - 1, 1] ELSE IF Ack[a, b - 1] > 3 THEN 0 ELSE Ack[a - 1, Ack[a, b - 1]]
TypeOK == held \subseteq Items /\ total \in 0..20 /\ n \in 0..5
Init == held = {} /\ total = 0 /\ n = 0
Next == \/ \E i \in Items :
             /\ i \notin held
             /\ held' = held \cup {i}
             /\ total' = SumSet(held')
             /\ n' = (n + 1) % 6
        \/ /\ held # {}
           /\ held' = {}
           /\ total' = IF IsEven(n) THEN Fact[n] % 7 ELSE Fib[n] % 7
           /\ UNCHANGED n
Inv == /\ total <= SumSet(Items)
       /\ Fact[3] = 6 /\ Fib[10] = 55 /\ IsOdd(7)
       /\ LET RECURSIVE Len(_) Len(S) == IF S = {} THEN 0 ELSE 1 + Len(S \ {CHOOSE y \in S : TRUE})
          IN Len(held) = Cardinality(held)
       /\ Ack[1, 2] = 4
       /\ LET Pow[k \in 0..5] == IF k = 0 THEN 1 ELSE 2 * Pow[k - 1] IN Pow[n] >= n + 1
       \* The recursive operator refers to i, bound outside it
       /\ \A i \in Items :
            LET RECURSIVE Has(_)
                Has(S) == IF S = {} THEN 0
                          ELSE LET y == CHOOSE z \in S : TRUE IN (IF y = i THEN 1 ELSE 0) + Has(S \ {y})
            IN Has(held) = IF i \in held THEN 1 ELSE 0
\* Violated
Small == total < 6
====
