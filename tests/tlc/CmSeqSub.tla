---- MODULE CmSeqSub ----
\* The subsequence operators of SequencesExt (CommunityModules), on a sequence from the state and on
\* constants: AllSubSeqs lists each subsequence backwards, as TLC evaluates the module's definition
\* (ReplaceAllSubSeqs makes TLC enumerate sequences of sequences, so q stays short)
EXTENDS Naturals, Sequences, SequencesExt, TLC
VARIABLES q, r
Facts(s) == <<Interleave(s, Reverse(s)), AllSubSeqs(s),
              IF <<1>> \in SubSeqs(s) THEN IndexFirstSubSeq(<<1>>, s) ELSE 0, IndexFirstSubSeq(<<>>, s),
              ReplaceFirstSubSeq(<<3>>, <<1, 2>>, s), ReplaceFirstSubSeq(<<>>, <<2>>, s),
              ReplaceAllSubSeqs(<<3>>, <<1>>, s), ReplaceAllSubSeqs(<<>>, <<2, 1>>, s),
              ReplaceAllSubSeqs(<<4>>, <<>>, s), ReplaceAllSubSeqs(<<5, 5>>, <<1, 1>>, s)>>
Init == q = <<>> /\ r = Facts(<<>>)
Next == \/ Len(q) < 3 /\ \E x \in {1, 2} : q' = Append(q, x) /\ r' = Facts(q')
        \/ q # <<>> /\ q' = Tail(q) /\ r' = Facts(q')
Consts == <<Interleave(<<1, 2>>, <<3, 4>>), AllSubSeqs(<<1, 2, 3>>), IndexFirstSubSeq(<<2, 2>>, <<1, 2, 2, 2>>),
            ReplaceFirstSubSeq(<<9>>, <<1, 1>>, <<2, 1, 1, 1>>), ReplaceAllSubSeqs(<<2, 2>>, <<1, 1>>, <<1, 1, 1>>),
            ReplaceAllSubSeqs(<<7>>, <<1, 2>>, <<1, 2>>), ReplaceAllSubSeqs(<<1>>, <<1>>, <<3, 1>>)>>
ASSUME PrintT(Consts)
====
