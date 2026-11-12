---- MODULE CmPad ----
\* IOUtils (CommunityModules): zeroPadN with constant arguments, and IOSerialize, which TLC 2.19
\* evaluates to TRUE
EXTENDS Integers, IOUtils, TLC
VARIABLES k, label
Labels == [i \in 0..12 |-> zeroPadN(i, 2)]
Init == k = 0 /\ label = Labels[k]
Next == k < 10 /\ k' = k + 5 /\ label' = Labels[k']
Shown == PrintT(label)
Consts == <<zeroPadN(5, 3), zeroPadN(1234, 2), zeroPadN(0 - 5, 4), zeroPadN(7, 0), zeroPadN(<<1>>, 6),
            zeroPadN("ab", 3), IOSerialize(<<1>>, "out.bin", TRUE)>>
ASSUME PrintT(Consts)
====
