---- MODULE BoxedMember ----
\* Variables that hold a model value or a value of another kind (a tuple, a sequence, a function,
\* a set, a Boolean), tested for membership in sets whose membership TLC decides by the value's
\* structure: a product, Seq(S), [D -> R], SUBSET S, BOOLEAN (issue #131). Each test is compared
\* with membership in the same set written out, so both outcomes are evaluated, and with the model
\* value too
EXTENDS Naturals, Sequences
CONSTANT None
VARIABLE t, q, f, s, b, k
Ids == {"A", "B"} \X (0 .. 1)
TypeOK == /\ t = None \/ t \in Ids \/ t = <<"C", 0>>
          /\ q = None \/ q \in Seq({1, 2, 3})
          /\ f = None \/ f \in [{1, 2} -> {0, 1, 2}]
          /\ s = None \/ s \in SUBSET {1, 2, 3}
          /\ b = None \/ b \in BOOLEAN
Init == /\ t = <<"A", 0>>
        /\ q = <<1>>
        /\ f = <<0, 1>>
        /\ s = {1}
        /\ b = TRUE
        /\ k = 0
Next == /\ k < 3
        /\ k' = k + 1
        /\ t' = CASE k = 0 -> None [] k = 1 -> <<"B", 1>> [] OTHER -> <<"C", 0>>
        /\ q' = CASE k = 0 -> None [] k = 1 -> <<2, 1, 2>> [] OTHER -> <<3>>
        /\ f' = CASE k = 0 -> None [] k = 1 -> <<1, 1>> [] OTHER -> <<2, 0>>
        /\ s' = CASE k = 0 -> None [] k = 1 -> {1, 2} [] OTHER -> {3}
        /\ b' = CASE k = 0 -> None [] k = 1 -> FALSE [] OTHER -> TRUE
InProduct == (t \in Ids) = (t \in {<<"A", 0>>, <<"A", 1>>, <<"B", 0>>, <<"B", 1>>})
InSeq == (q \in Seq({1, 2})) = (q # None /\ \A i \in DOMAIN q : q[i] \in {1, 2})
InFunSet == (f \in [{1, 2} -> {0, 1}]) = (f \in {<<0, 0>>, <<0, 1>>, <<1, 0>>, <<1, 1>>})
InBool == (b \in BOOLEAN) = (b \in {TRUE, FALSE})
InSubset == s # None => (s \in SUBSET {1, 2}) = (s \in {{}, {1}, {2}, {1, 2}})
\* Violated on the third state, where t is <<"C", 0>>
OnlyIds == t = None \/ t \in Ids
\* TLC stops with an error on the model value in SUBSET S
SubsetAll == s \in SUBSET {1, 2, 3}
====
