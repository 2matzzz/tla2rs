---- MODULE ConstInv ----
\* An invariant or property of constant level is evaluated before exploring; TLC stops if it is
\* not TRUE (and evaluates it on every state if it fails to evaluate)
EXTENDS Naturals
CONSTANT N
VARIABLE x
Init == x = 0
Next == x' = 1 - x
InvF == N > 5
InvT == N > 1
InvNum == N
InvErr == 1 \div (N - 3) = 0
PF == N > 5
PBox == [](N > 5)
====
