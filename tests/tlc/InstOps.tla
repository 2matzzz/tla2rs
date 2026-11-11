---- MODULE InstOps ----
\* INSTANCE forms TLC accepts: named instances of standard modules (S!Len, N!+), an operator symbol
\* substituted for an infix constant (** <- Mul, ** <- +), an instance with an operator parameter, and
\* an instance inside LET
EXTENDS Naturals
VARIABLE n
S == INSTANCE Sequences
N == INSTANCE Naturals
Mul(a, b) == a * b
O == INSTANCE Powered WITH ** <- Mul, F <- LAMBDA z : z, v <- n
P(G(_)) == INSTANCE Powered WITH ** <- +, F <- G, v <- n
Init == O!Init
Next == O!Next
Inv == /\ S!Len(<<1, 2>>) = 2
       /\ N!+(1, 2) = 3
       /\ 2 \in N!Nat
       /\ (LET Q == INSTANCE Powered WITH ** <- Mul, F <- LAMBDA z : z, v <- n IN ~Q!Big \/ n = 4)
       /\ ~P(LAMBDA z : 0)!Big \/ n > 3
====
