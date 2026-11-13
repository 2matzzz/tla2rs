---- MODULE ArgShareNext ----
\* ArgShare in the next-state relation, with an argument that depends on the state: code generation
\* binds it to a name, and the call site of each Twice notes what the argument reads
EXTENDS Naturals
VARIABLE x
Twice(n) == n + n
Init == x = 1
Next == x' = (Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(x)))))))))))))))))))))))) + 1) % 7
====
