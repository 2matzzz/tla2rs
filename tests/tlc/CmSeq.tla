---- MODULE CmSeq ----
\* SequencesExt of the CommunityModules, on a sequence from the state and on constants
EXTENDS Naturals, Sequences, SequencesExt, TLC
VARIABLES q, r
Facts(s) == <<ToSet(s), Contains(s, 2), Reverse(s), Remove(s, 1), ReplaceAll(s, 1, 3),
              IsPrefix(<<1>>, s), IsStrictPrefix(s, <<1, 2, 1>>), IsSuffix(<<2>>, s), IsStrictSuffix(<<>>, s),
              Front(s), IF s = <<>> THEN 0 ELSE Last(s), Prefixes(s), Suffixes(s),
              SelectInSeq(s, LAMBDA x : x = 2), SelectLastInSeq(s, LAMBDA x : x = 1), InsertAt(s, 1, 3),
              RemoveFirst(s, 2), Cons(3, s), Snoc(3, s), FoldLeft(LAMBDA a, b : 10 * a + b, 0, s),
              FoldRight(LAMBDA a, b : 10 * b + a, s, 0), FoldSeq(LAMBDA a, b : 10 * b + a, 0, s),
              ToBag(s), SeqMod(Len(s) + 1, 2), Zip(s, <<5, 6>>), IsSorted(s, LAMBDA a, b : a < b)>>
Init == q = <<>> /\ r = Facts(<<>>)
Next == \/ Len(q) < 3 /\ \E x \in {1, 2} : q' = Append(q, x) /\ r' = Facts(q')
        \/ q # <<>> /\ q' = Tail(q) /\ r' = Facts(q')
Consts == <<LongestCommonPrefix({<<1, 2, 3>>, <<1, 2>>, <<1, 2, 4>>}), CommonPrefixes({<<1, 2>>, <<1, 3>>}),
            SetToSeq({3, 1, 2}), SetToSeqs({1, 2}), SetToSortSeq({3, 1, 2}, LAMBDA a, b : a > b),
            SetToAllKPermutations({1, 2}) \ {<<>>}, TupleOf({1, 2}, 2), SeqOf({1}, 2) \ {<<>>}, BoundedSeq({1}, 2) \ {<<>>},
            <<>> \in SeqOf({1}, 2) \cap BoundedSeq({1}, 0) \cap SetToAllKPermutations({1}),
            SelectInSubSeq(<<1, 2, 1, 2>>, 2, 4, LAMBDA x : x = 1), SelectLastInSubSeq(<<1, 2, 1, 2>>, 1, 3, LAMBDA x : x = 2),
            ReplaceAt(<<1, 2>>, 2, 5), RemoveAt(<<1, 2, 3>>, 2), RemoveFirstMatch(<<1, 2, 3>>, LAMBDA x : x > 1),
            FoldLeftDomain(LAMBDA a, b : 10 * a + b, 0, <<7, 8, 9>>), FoldRightDomain(LAMBDA a, b : 10 * b + a, <<7, 8, 9>>, 0),
            FlattenSeq(<<<<1>>, <<>>, <<2, 3>>>>), FlattenSeq(<<>>), SubSeqs(<<1, 2>>),
            ReplaceSubSeqAt(2, <<9>>, <<2, 3>>, <<1, 2, 3, 4>>)>>
ASSUME PrintT(Consts)
====
