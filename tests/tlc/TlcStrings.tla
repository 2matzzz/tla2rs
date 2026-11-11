---- MODULE TlcStrings ----
\* Strings as sequences of characters (\o, Len, Head, Tail, Append, SubSeq), ToString, TLCEval,
\* Any, RandomElement of a single element, and Permutations of integers
EXTENDS Integers, Sequences, TLC
VARIABLES name, n
Names == {"ab" \o "c", Tail("xabc"), SubSeq("zabcz", 2, 4), ToString(7), Append("ab", "d")}
TypeOK == name \in Names \cup {"start"} /\ n \in 0..3
Init == name = "start" /\ n = 0
Next == \E s \in Names :
          /\ s # name
          /\ Len(s) = 3 \/ s = ToString(7)
          /\ name' = s
          /\ n' = TLCEval((n + 1) % 4)
Inv == /\ name \in Any
       /\ Head(ToString(<<1>>)) = "<"
       /\ RandomElement({n}) = n
       /\ Permutations({1, 2}) = {<<1, 2>>, <<2, 1>>}
       /\ "a" \in Seq({"a", "b"})
\* Violated
NotSeven == name # "7" \/ n < 3
====
