---- MODULE SeqSettle ----
\* Sequence lengths that settle without a bound in TypeOK: a sliding window, a history capped by
\* a length test, and a longer sequence built only in an invariant
EXTENDS Integers, Sequences
VARIABLES win, hist
Init == win = <<0, 0>> /\ hist = <<>>
Next == \E x \in 0..2 :
          /\ win' = Append(Tail(win), x)
          /\ hist' = IF Len(hist) < 3 THEN Append(hist, x) ELSE Append(Tail(hist), x)
Inv == /\ Len(win) = 2
       /\ Len(hist) <= 3
       /\ Len(Append(hist, 9) \o win) <= 6
\* Violated
NoRun == hist # <<2, 2, 2>>
====
