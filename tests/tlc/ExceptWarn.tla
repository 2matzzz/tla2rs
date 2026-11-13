---- MODULE ExceptWarn ----
\* EXCEPT on an argument or field the value does not have changes nothing there, and TLC warns,
\* naming where the value is written, only when it has not printed the same text before (its
\* first warning carries a note, so the same warning comes once more without it)
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Short == [<<1, 2>> EXCEPT ![x + 3] = 0]
Inner == [[i \in 1..2 |-> <<x>>] EXCEPT ![1][x + 2] = 0]
Outer == [[i \in 1..2 |-> <<x>>] EXCEPT ![x + 5][1] = 0]
Two == [[i \in 1..2 |-> x] EXCEPT ![x + 7] = 0, ![x + 8] = 0]
Inv == Short # <<>> /\ Inner # <<>> /\ Outer # <<>>
InvTwo == x = 0 => Two # <<>>
\* Of constant level: evaluated when TLC starts, and again as an invariant
Fixed == [[i \in 1..2 |-> i] EXCEPT ![3] = 0]
InvFixed == Fixed = <<1, 2>>
====
