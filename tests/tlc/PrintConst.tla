---- MODULE PrintConst ----
\* Print and PrintT: TLC evaluates the definitions of constant level without arguments when it
\* starts (and uses those values later), then the ASSUMEs; elsewhere they print each time they
\* are evaluated. crosscheck.sh compares the lines printed, in order
EXTENDS Naturals, TLC
CONSTANT N
VARIABLE x
ASSUME PrintT("assume1")
A == PrintT("A")
B == A /\ PrintT("B")
ASSUME PrintT(<<"assume2", N>>)
E == PrintT("E")
D == E /\ PrintT("D")
F(n) == PrintT(n)
G == F(7)
H == Print("H", 3) + 1
Init == x = 0 /\ PrintT("init")
Next == x' = (x + 1) % 3
Inv == B
InvState == x >= 0 /\ PrintT(<<"state", x>>)
InvLet == LET L == PrintT("L") IN L /\ x >= 0
InvCached == D /\ x >= 0
====
