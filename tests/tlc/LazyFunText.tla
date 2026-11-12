---- MODULE LazyFunText ----
\* How TLC prints a function over a set it cannot enumerate (ToString, Print, PrintT): the bound
\* variables with their domains as TLC prints them (only the first name of `a, c \in Nat`), and
\* the position of the body, or a number as written. EXCEPT changes nothing in the text
EXTENDS Integers, Sequences, TLC
VARIABLE x
Double == [n \in Nat |-> 2 * n]
Fact[n \in Nat] == n + 1
Sum[n \in Nat] == IF n = 0 THEN 0 ELSE n + Sum[n - 1]
ASSUME PrintT(ToString(Double))
ASSUME PrintT(ToString([n \in Int |->
                          n * n]))
ASSUME PrintT(ToString([q \in Seq({1, 2}) |-> Len(q)]))
ASSUME PrintT(ToString([a \in Nat, c \in Nat |-> a + c]))
ASSUME PrintT(ToString([a, c \in Nat, b \in Int |-> 007]))
ASSUME PrintT(ToString([<<a, c>> \in Nat \X {1, 2} |-> (a)]))
ASSUME PrintT(ToString([t \in STRING |-> t \o "x"]))
ASSUME PrintT(ToString([Double EXCEPT ![2] = 7]))
ASSUME PrintT(ToString(Fact))
ASSUME PrintT(ToString(Sum))
ASSUME PrintT(ToString(Double) \o "!")
ASSUME PrintT(Double)
ASSUME Print([n \in Nat |-> -1], TRUE)
Init == x = 0
Next == /\ x < 2
        /\ x' = x + 1
        /\ PrintT(ToString([n \in Nat |-> n + x]))
Inv == Len(ToString([n \in Nat |-> x])) > 10
====
