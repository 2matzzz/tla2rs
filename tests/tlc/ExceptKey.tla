---- MODULE ExceptKey ----
\* An EXCEPT key of another kind than the value takes (issue #123): a tuple stops TLC on a key
\* that is no integer, a record on one that is no string, and a function compares the first
\* element of its domain with the key (an error on an integer against a string, only unequal
\* against a model value, which warns). Each Init<Case> / Next<Case> pair is one configuration
EXTENDS Naturals, Sequences, TLC
CONSTANT m
VARIABLE x
InitTup == x = <<1, 2>>
NextTup == x' = [x EXCEPT !["a"] = 9]
InitTupModel == x = <<1, 2>>
NextTupModel == x' = [x EXCEPT ![m] = 9]
InitTupOut == x = <<1, 2>>
NextTupOut == x' = [x EXCEPT ![5] = 9]
InitTupDot == x = <<1, 2>>
NextTupDot == x' = [x EXCEPT !.a = 9]
InitEmpty == x = <<>>
NextEmpty == x' = [x EXCEPT !["a"] = 9]
InitEmptyTail == x = <<1>>
NextEmptyTail == x' = [Tail(x) EXCEPT ![m] = 9]
InitSeq == x = Append(<<1>>, 2)
NextSeq == x' = [x EXCEPT !["a"] = 9]
InitSeqFun == x = [i \in 1..2 |-> 0]
NextSeqFun == x' = [x EXCEPT !["a"] = 9]
InitSeqFunModel == x = [i \in 1..2 |-> 0]
NextSeqFunModel == x' = [x EXCEPT ![m] = 9]
InitSeqFunDot == x = [i \in 1..2 |-> 0]
NextSeqFunDot == x' = [x EXCEPT !.a = 9]
InitFun == x = [i \in {3, 1} |-> 0]
NextFun == x' = [x EXCEPT !["a"] = 9]
InitFunModel == x = [i \in {1, 3, 5, 7} |-> 0]
NextFunModel == x' = [x EXCEPT ![m] = 9]
InitFunPart == x = (3 :> 0 @@ 1 :> 0)
NextFunPart == x' = [x EXCEPT !["a"] = 9]
InitFunOut == x = [i \in {1, 3} |-> 0]
NextFunOut == x' = [x EXCEPT ![2] = 9]
InitStrFun == x = ("b" :> 1 @@ "c" :> 2)
NextStrFun == x' = [x EXCEPT ![5] = 9]
InitStrFunModel == x = ("b" :> 1 @@ "c" :> 2)
NextStrFunModel == x' = [x EXCEPT ![m] = 9]
InitStrFunMiss == x = ("b" :> 1 @@ "c" :> 2)
NextStrFunMiss == x' = [x EXCEPT !["a"] = 9]
InitRec == x = [b |-> 1, c |-> 2]
NextRec == x' = [x EXCEPT ![5] = 9]
InitRecModel == x = [b |-> 1, c |-> 2]
NextRecModel == x' = [x EXCEPT ![m] = 9]
InitRecMiss == x = [b |-> 1]
NextRecMiss == x' = [x EXCEPT !["a"] = 9]
InitInitLit == x = [<<>> EXCEPT !["a"] = 1]
NextInitLit == UNCHANGED x
InitInitDot == x = [<<>> EXCEPT !.a = 1]
NextInitDot == UNCHANGED x
InitBaseFun == x = <<0, 0>>
NextBaseFun == x' = [[i \in 1..2 |-> 0] EXCEPT !["a"] = 9]
InitBaseTup == x = [i \in 1..2 |-> 0]
NextBaseTup == x' = [<<0, 0>> EXCEPT !["a"] = 9]
====
