---- MODULE SeqWindow ----
\* A sliding window whose length settles without any length test in the spec
EXTENDS Integers, Sequences
VARIABLE win
Init == win = <<0, 0, 0>>
Next == \E x \in 0..1 : win' = Append(Tail(win), x)
Inv == Head(win) \in 0..1
\* Violated
NotAllOnes == win # <<1, 1, 1>>
====
