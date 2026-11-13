---- MODULE StrMadeCond ----
\* A string made only in a constant condition counts when TLC evaluates the condition: "cb" is
\* made in the condition of the first step, before "ca", so the set prints as {"cb", "ca"}. Also
\* the condition of an IF in an expression, a conjunct of an action, the set of a \A that assigns
\* variables and the argument of a recursive operator that does, which TLC evaluates only where
\* the body reads its parameter (not at all in Put)
EXTENDS Naturals, FiniteSets, Sequences
VARIABLES x, s
Init == x = "c" /\ s = {}
Inv == Cardinality(s) < 2
NextIf == IF s = {}
          THEN IF "c" \o "b" = "q" THEN FALSE ELSE x' = x /\ s' = {x \o "a"}
          ELSE x' = x /\ s' = s \cup {x \o "b"}
NextExpr == /\ x' = x
            /\ s' = IF s = {} THEN (IF "c" \o "b" = "q" THEN {} ELSE {x \o "a"}) ELSE s \cup {x \o "b"}
NextConj == IF s = {}
            THEN "c" \o "b" # "q" /\ x' = x /\ s' = {x \o "a"}
            ELSE x' = x /\ s' = s \cup {x \o "b"}
NextAll == IF s = {}
           THEN \A i \in {Len("c" \o "b")} : x' = x /\ s' = {x \o "a"}
           ELSE x' = x /\ s' = s \cup {x \o "b"}
RECURSIVE Put(_)
Put(w) == x' = x /\ s' = {x \o "a"}
NextRec == IF s = {}
           THEN Put("c" \o "b")
           ELSE x' = x /\ s' = s \cup {x \o "b"}
RECURSIVE PutUsed(_)
PutUsed(w) == x' = x /\ s' = IF Len(w) = 2 THEN {x \o "a"} ELSE {}
NextRecUsed == IF s = {}
               THEN PutUsed("c" \o "b")
               ELSE x' = x /\ s' = s \cup {x \o "b"}
====
