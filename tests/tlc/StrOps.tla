---- MODULE StrOps ----
\* Head, Tail, Len, Append, and \o on strings held in the state
EXTENDS Integers, Sequences
VARIABLES w
Words == {"abc", "b", "bb", "bbb", "bc", "bcb", "bx", "bxb", "c", "cb", "cbc", "cc", "ccc", "cx", "cxc", "x", "xb", "xbx", "xc", "xcx", "xx", "xxx"}
TypeOK == w \in Words
Init == w = "abc"
Next == \/ Len(w) > 1 /\ w' = Tail(w)
        \/ Len(w) < 3 /\ w' = w \o Head(w)
        \/ Len(w) = 1 /\ w' = Append("x", w)
Inv == Len(w) <= 3
\* Violated
NotXc == w # "xcx"
====
