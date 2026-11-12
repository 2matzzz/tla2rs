---- MODULE TupleStrCup ----
\* A string tested for membership in a set of tuples that TLC builds where it is used without
\* sorting it: the union of a set with another (TLC copies the elements of the first and adds
\* those of the second), or a set {f(y) : y \in S}. TLC then asks each tuple whether it equals the
\* string, comparing it with the characters. When the first set of a union is empty the union is
\* the second set, sorted, and comparing the string with a tuple fails, as for TS itself
EXTENDS Naturals, Sequences
VARIABLE s, n
TS == {<<"a", "b">>, <<"c", "d">>}
Strs == {"ab", "cd"}
Init == s = "ab" /\ n = 0
Next == n < 2 /\ n' = n + 1 /\ s' = IF n = 0 THEN "cd" ELSE "xy"
Cup == (s \in TS \cup {}) = (n < 2)
CupMore == /\ (s \in TS \cup {<<"x", "z">>}) = (n < 2)
           /\ (s \notin {<<"z">>} \cup TS) = (n = 2)
Map == (s \in {t : t \in TS}) = (n < 2)
EmptyFirst == s \in {} \cup TS
TupInStrs == n = 1 => <<"a", "b">> \in Strs \cup {}
====
