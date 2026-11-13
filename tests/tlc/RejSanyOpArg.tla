---- MODULE RejSanyOpArg ----
\* What an operator is passed must fit the parameter: an operator's name or a LAMBDA where the
\* parameter takes no arguments is refused, and so is anything but an operator of as many
\* parameters where it takes some
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANT K
VARIABLE x
A(p) == p
C(F(_, _)) == F(1, 2)
B(F(_)) == F(1)
E(F(_), q) == F(q)
a ++ b == a
D1 == A(Len)
D2 == C(Len)
D3 == Cardinality(Len)
D4 == SelectSeq(<<1>>, Len)
D5 == A(LAMBDA y : y)
D6 == B(5)
D7(G(_)) == A(G)
D8 == 1 ++ Len
D9 == B(A)
D10 == B(D1)
D11 == B(x)
D12 == B(K)
D13 == C(LAMBDA y : y)
D14 == B(Unknown + 1)
D15 == Print(Len, TRUE)
D16 == B(LAMBDA y : Len)
D17 == E(5, Unknown2)
D18 == LET L(F(_)) == F(1) IN L(5)
D19(G(_)) == B(G)
D20 == E(Len, Head)
D21 == SelectSeq(<<1>>, 3)
Init == x = 0
Next == x' = 0
====
