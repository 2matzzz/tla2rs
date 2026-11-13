---- MODULE IntervalCase ----
\* An interval keeps its form through CASE, through an IF whose condition prints (TLC evaluates the
\* condition once), in an EXCEPT that reads @, in a function over 0..2 and a sequence in a record,
\* and in a name bound by \E over a set written with values from the state. The invariant compares
\* ToString with the text TLC makes
EXTENDS Naturals, Sequences, TLC
VARIABLES a, b, r, h, k, n
Init == /\ a = {}
        /\ b = <<>>
        /\ r = [x |-> <<1..2>>, y |-> 0]
        /\ h = [i \in 0..2 |-> IF i = 0 THEN {} ELSE 1..i]
        /\ k = <<{}, {}>>
        /\ n = 0
Next == /\ n < 3 /\ n' = (n + 1) % 4
        /\ a' = IF PrintT(<<"c", n>>) /\ n % 2 = 0 THEN 1..3 ELSE {1, 2, 3}
        /\ b' = CASE n = 0 -> <<2..3>> [] n = 1 -> Append(b, {4}) [] OTHER -> <<>>
        /\ r' = [r EXCEPT !.x = Append(@, 3..4), !.y = n]
        /\ h' = [h EXCEPT ![n % 3] = {n}]
        /\ \E e \in {h[1], h[2]} : k' = <<e, h[2]>>
        /\ PrintT(<<ToString(a), b, r, h, k>>)
Inv == /\ ToString(r.x[1]) = "1..2"
       /\ Len(r.x) > 1 => ToString(r.x[2]) = "3..4"
       /\ ToString(k[2]) \in {"1..2", "{2}", "{}"}
====
