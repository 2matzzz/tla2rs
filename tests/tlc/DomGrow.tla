---- MODULE DomGrow ----
\* Variables holding functions over 0..n-1 for different n, and the empty tuple: functions over part
\* of a type, compared with <<>>, applied, updated, and collected in a set
EXTENDS Integers, FiniteSets
CONSTANT Max
Words(S, n) == IF n = 0 THEN {<<>>} ELSE [0..(n - 1) -> S]
AllWords == UNION {Words({0, 1}, n) : n \in 0..Max}
Size(s) == IF s = <<>> THEN 0 ELSE Cardinality(DOMAIN s)
VARIABLE w, marks, pos, pre
Init == /\ w \in AllWords
        /\ marks = [i \in 0..Size(w) |-> -1]
        /\ pos = 0
        /\ pre = {<<>>}
Next == \/ /\ pos < Size(w)
           /\ marks' = [marks EXCEPT ![pos] = w[pos]]
           /\ pre' = pre \cup {[i \in 0..pos |-> w[i]]}
           /\ pos' = pos + 1
           /\ UNCHANGED w
        \/ pos = Size(w) /\ UNCHANGED <<w, marks, pos, pre>>
TypeOK == /\ w \in AllWords
          /\ marks \in [0..Size(w) -> {-1, 0, 1}]
          /\ pos \in 0..Max
          /\ \A v \in pre : v \in AllWords
NoTwoOnes == Cardinality({v \in pre : v /= <<>> /\ v[Size(v) - 1] = 1}) < 2
====
