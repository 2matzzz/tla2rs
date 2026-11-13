---- MODULE OptDumpColor ----
\* TLC's -dump dot,colorize: each edge has the color of its action (by name, numbered from 2 in
\* the order first written), and a legend lists the actions in the order of a Java HashMap
EXTENDS Naturals
CONSTANT Limit
VARIABLE x
A(i) == x' = (x + i) % 40
Alpha == x' = (x * 3 + 5) % 40 /\ x # 39
Beta == x' = (x * 3 + 4) % 40 /\ x # 39
Gamma == x' = (x * 3 + 5) % 40 /\ x # 39
Delta == x' = (x * 3 + 5) % 40 /\ x # 39
Eps == x' = (x * 3 + 3) % 40 /\ x # 39
Zeta == x' = (x * 3 + 4) % 40 /\ x # 39
Eta == x' = (x * 3 + 3) % 40 /\ x # 39
Theta == x' = (x * 3 + 5) % 40 /\ x # 39
Iota == x' = (x * 3 + 4) % 40 /\ x # 39
Kappa == x' = (x * 3 + 5) % 40 /\ x # 39
Lambda1 == x' = (x * 3 + 7) % 40 /\ x # 39
Mu == x' = (x * 3 + 2) % 40 /\ x # 39
Nu == x' = (x * 3 + 2) % 40 /\ x # 39
Xi == x' = (x * 3 + 2) % 40 /\ x # 39
Omicron == x' = (x * 3 + 7) % 40 /\ x # 39
Next == \/ A(1) \/ A(2) \/ \E i \in 3..4 : A(i) \/ (x = 0 /\ x' = 39)
        \/ Alpha
        \/ Beta
        \/ Gamma
        \/ Delta
        \/ Eps
        \/ Zeta
        \/ Eta
        \/ Theta
        \/ Iota
        \/ Kappa
        \/ Lambda1
        \/ Mu
        \/ Nu
        \/ Xi
        \/ Omicron
Init == x = 0
Small == x < Limit
====
