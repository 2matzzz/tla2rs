---- MODULE IntervalConst ----
\* TLC prints a value in the form it holds it, also when the compiler evaluates it: an interval stays
\* one inside a tuple, record, function or set, and when taken out again (application, CHOOSE, a
\* bound variable, SelectSeq, Head); a set keeps the first of equal elements as written; DOMAIN of a
\* function built by [x \in S |-> e] enumerates. ToString makes the same text, so the ASSUMEs on it
\* hold in TLC
EXTENDS Naturals, Sequences, TLC
VARIABLE x
F == [i \in 1..2 |-> 1..i]
S == {1..2, 3..4}
T == <<1..2, {3}, 5..6>>
ASSUME PrintT(<<<<1..2>>, [a |-> 1..2], S, {1..2, {1, 2}}, {{1, 2}, 1..2}, F, F[2], CHOOSE s \in S : TRUE>>)
ASSUME PrintT(<<IF TRUE THEN 1..2 ELSE {1}, {s \in S : 1 \in s}, {1..k : k \in 1..2}, Append(<<>>, 1..2),
                DOMAIN [i \in 1..2 |-> 0], DOMAIN T, [s \in S |-> s], [F EXCEPT ![1] = {5}]>>)
ASSUME PrintT(<<{1..2} \cup {{1, 2}}, S \ {{3, 4}}, Tail(T), SubSeq(T, 2, 3), T \o <<7..7>>, Head(T),
                [T EXCEPT ![2] = 8..9], [T EXCEPT ![1] = @ \cup {3}], (1 :> 1..2) @@ (2 :> 3..4),
                SelectSeq(T, LAMBDA s : 5 \in s), 1..0, <<2..1>>, (1..2) \cap (1..2)>>)
ASSUME /\ ToString(<<1..2>>) = "<<1..2>>" /\ ToString(S) = "{1..2, 3..4}" /\ ToString(F) = "<<1..1, 1..2>>"
       /\ ToString(F[2]) = "1..2" /\ ToString([a |-> 1..2]) = "[a |-> 1..2]"
Init == x = 0
Next == UNCHANGED x
====
