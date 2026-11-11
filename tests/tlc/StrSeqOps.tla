---- MODULE StrSeqOps ----
\* Strings as sequences of characters: SelectSeq and SortSeq of a string give tuples, a tuple
\* followed by a string gives a tuple; a tuple compared with a string compares characters, while a
\* string compared with a tuple is an error (TLC asks the left value)
EXTENDS Integers, Sequences, TLC
VARIABLES s, k
ASSUME /\ <<"a", "b">> = "ab" /\ ~(<<"a", "b">> # "ab") /\ <<>> = "" /\ {<<"a", "b">>} = {"ab"}
       /\ <<"a", "b">> # "ac" /\ "ab" \in {<<"a", "b">>} /\ <<1>> # "ab"
       /\ [a |-> 1] = ("a" :> 1) /\ ("a" :> 1) = [a |-> 1] /\ [a |-> 1] \in {("a" :> 1)}
Init == s \in {"ab", "xyz", ""} /\ k = 0
Next == \/ k < 2 /\ k' = k + 1 /\ UNCHANGED s
        \/ UNCHANGED <<s, k>>
Inv == /\ SelectSeq(s, LAMBDA c : c # "a") \in {<<"b">>, <<"x", "y", "z">>, <<>>}
       /\ SortSeq(s, LAMBDA x, y : TRUE) \in {<<"b", "a">>, <<"z", "y", "x">>, <<>>}
       /\ (<<"q">> \o s) \in {<<"q", "a", "b">>, <<"q", "x", "y", "z">>, <<"q">>}
       /\ Len(SelectSeq(s, LAMBDA c : c \in {"x", "a"})) = IF s = "" THEN 0 ELSE 1
\* Fails once k is 1: a string asked whether it equals a tuple
StrLeft == k = 0 \/ <<"a">> \in {"ab"}
\* Violated
NotRev == SortSeq(s, LAMBDA x, y : TRUE) # <<"z", "y", "x">>
====
