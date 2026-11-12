---- MODULE TypeFallback ----
\* TypeOK gives a variable a set that is no type (functions into Int): its type is inferred from Init
\* and Next instead, and TypeOK is checked as an ordinary invariant
EXTENDS Integers
CONSTANT Limit
VARIABLE balance, last
Accounts == {"a", "b"}
TypeOK == /\ balance \in [Accounts -> Int]
          /\ last \in Accounts \cup {"none"}
Init == balance = [a \in Accounts |-> 0] /\ last = "none"
Next == \E a \in Accounts : balance[a] < Limit /\ balance' = [balance EXCEPT ![a] = @ + 1] /\ last' = a
Small == \A a \in Accounts : balance[a] <= 1
====
