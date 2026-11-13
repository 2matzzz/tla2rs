---- MODULE OptUserFile ----
\* TLC's -userFile FILE: the lines the spec prints (Print and PrintT) go to FILE instead of the
\* standard output, which keeps TLC's own messages and warnings
EXTENDS Naturals, TLC
CONSTANT Mode
VARIABLES x, y
ASSUME Mode # "quiet" => PrintT("assume")
ASSUME Mode # "quiet" => Print(<<1, "two">>, TRUE)
ASSUME Mode = "wide" => PrintT([i \in 1..12 |-> <<i, "a longer string", {i}>>])
ASSUME Mode # "false"
Init == x = 0 /\ y = 0 /\ (Mode # "quiet" => PrintT(<<"init", x>>))
Inc == x < 2 /\ x' = x + 1 /\ y' = y /\ (Mode # "quiet" => PrintT(<<"inc", x>>))
Dec == x > 0 /\ x' = x - 1 /\ UNCHANGED y /\ (Mode # "quiet" => Print("dec", TRUE))
Flip == y' = 1 - y /\ UNCHANGED x
Next == Inc \/ Dec \/ Flip
Inv == Mode = "inv" => x + y < 3
====
