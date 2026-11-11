---- MODULE SubSeqErr ----
\* An index outside the sequence in SubSeq stops TLC like its other built-in operators
EXTENDS Integers, Sequences
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ (x < 2 \/ SubSeq(<<1, 2>>, 1, x) # <<>>)
====
