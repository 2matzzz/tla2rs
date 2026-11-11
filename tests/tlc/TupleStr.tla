---- MODULE TupleStr ----
\* A tuple compared with a string from the state. TLC asks the value on the left: a tuple compares
\* itself with the characters of a string, and a string asked about a tuple stops with an error. A
\* set written out where it is used asks each of its elements; a set from a definition is sorted
\* first, and comparing a string with a tuple then fails
EXTENDS Naturals, Sequences
VARIABLE s, q, n
Pairs == {<<"a", "b">>, <<"c", "d">>}
Init == s = "ab" /\ q = <<"a">> /\ n = 0
Next == /\ n' = (n + 1) % 3
        /\ s' = IF n = 1 THEN "cd" ELSE s
        /\ q' = IF Len(q) < 2 THEN Append(q, "b") ELSE q
TupLeft == <<"a", "b">> = s \/ <<"c", "d">> = s
TupLeftViol == <<"a", "b">> = s
SeqLeft == n = 0 \/ q = s \/ s = "cd"
StrLeft == n = 2 => s = <<"c", "d">>
InWritten == (s \in {<<"x">>, <<"c", "d">>, <<"a", "b">>} /\ s \notin {q, <<"y">>}) \/ n # 1
InWrittenErr == n = 1 => q \in {<<"a">>, s}
InDef == n = 2 => s \in Pairs
Concat == Len(<<"x">> \o s) = 3 /\ (n = 1 => Len(Append(s, "x")) = 3)
ConcatErr == n = 2 => Len(s \o <<"x">>) = 3
IntElems == n = 1 => <<1, 2>> # s
====
