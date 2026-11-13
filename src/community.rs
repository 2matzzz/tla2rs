//! Modules of the CommunityModules (https://github.com/tlaplus/CommunityModules, MIT licence),
//! which tla2rs provides itself when a spec names one in EXTENDS or INSTANCE and no module of that
//! name is next to it (`compile::find_module`).
//!
//! The definitions below are written for tla2rs from the documented meaning of each operator, and
//! checked against TLC 2.19 (`tests/tlc/Cm*`). TLC 2.19 cannot load the Java overrides in the
//! CommunityModules jar (the releases from 2023-12 on need a class TLC 2.19 does not have), so it
//! evaluates the modules' TLA+ definitions, and so do these: an operator defined with CHOOSE picks
//! what the module's definition picks, and a fold applies its operator in the order the module's
//! definition does.
//!
//! Each module exports the same names in the same order as the release's (what it extends, then
//! its definitions and RECURSIVE declarations), since SANY's context, and with it the order TLC
//! prints variables in, depends on them (see `sany::var_order`). The operators listed in
//! `UNSUPPORTED` are refused when used: TLC 2.19 cannot evaluate them without their Java overrides
//! (they enumerate `Seq(S)`, or read files, run commands or read the environment). Those in
//! `CONST_ONLY` are refused on values from the state. The modules not here (files, reals,
//! animation) are listed with the reason in CLAUDE.md, "CommunityModules".

/// The source of each module, by name
pub fn source(name: &str) -> Option<&'static str> {
    Some(match name {
        "Folds" => FOLDS,
        "Functions" => FUNCTIONS,
        "FiniteSetsExt" => FINITE_SETS_EXT,
        "SequencesExt" => SEQUENCES_EXT,
        "UndirectedGraphs" => UNDIRECTED_GRAPHS,
        "Bitwise" => BITWISE,
        "Relation" => RELATION,
        "BagsExt" => BAGS_EXT,
        "Graphs" => GRAPHS,
        "Combinatorics" => COMBINATORICS,
        "Statistics" => STATISTICS,
        "GraphViz" => GRAPH_VIZ,
        "DyadicRationals" => DYADIC_RATIONALS,
        "VectorClocks" => VECTOR_CLOCKS,
        "Quorum" => QUORUM,
        "Json" => JSON,
        "IOUtils" => IO_UTILS,
        "HTML" => HTML,
        _ => return None,
    })
}

/// The operators of each module that are refused when used, with the reason
pub const UNSUPPORTED: &[(&str, &str, &str)] = &[
    ("UndirectedGraphs", "Path", "TLC 2.19 cannot enumerate it without its Java override (a subset of Seq(S))"),
    ("UndirectedGraphs", "SimplePath", "TLC 2.19 cannot enumerate it without its Java override (a subset of Seq(S))"),
    ("UndirectedGraphs", "AreConnectedIn", "TLC 2.19 cannot evaluate it without its Java override (\\E over Seq(S))"),
    ("UndirectedGraphs", "ConnectedComponents", "TLC 2.19 cannot evaluate it without its Java override (\\E over Seq(S))"),
    ("UndirectedGraphs", "IsStronglyConnected", "TLC 2.19 cannot evaluate it without its Java override (\\E over Seq(S))"),
    ("Graphs", "Path", "TLC 2.19 cannot enumerate it without its Java override (a subset of Seq(S))"),
    ("Graphs", "SimplePath", "TLC 2.19 cannot enumerate it without its Java override (a subset of Seq(S))"),
    ("Graphs", "AreConnectedIn", "TLC 2.19 cannot evaluate it without its Java override (\\E over Seq(S))"),
    ("Graphs", "IsStronglyConnected", "TLC 2.19 cannot evaluate it without its Java override (\\E over Seq(S))"),
    ("Graphs", "IsTreeWithRoot", "TLC 2.19 cannot evaluate it without its Java override (AreConnectedIn, \\E over Seq(S))"),
    ("Json", "JsonDeserialize", "it reads a file; TLC 2.19 stops on its definition (an unbounded CHOOSE)"),
    ("Json", "ndJsonDeserialize", "it reads a file; TLC 2.19 stops on its definition (an unbounded CHOOSE)"),
    ("IOUtils", "IODeserialize", "it reads a file; TLC 2.19 stops on its definition (an unbounded CHOOSE)"),
    ("IOUtils", "Serialize", "it writes a file; TLC 2.19 stops on its definition (a CHOOSE over records with an Int field)"),
    ("IOUtils", "Deserialize", "it reads a file; TLC 2.19 stops on its definition (an unbounded CHOOSE)"),
    ("IOUtils", "IOExec", "it runs a command; TLC 2.19 stops on its definition (a CHOOSE over records with an Int field)"),
    ("IOUtils", "IOEnvExec", "it runs a command; TLC 2.19 stops on its definition (a CHOOSE over records with an Int field)"),
    ("IOUtils", "IOExecTemplate", "it runs a command; TLC 2.19 stops on its definition (a CHOOSE over records with an Int field)"),
    ("IOUtils", "IOEnvExecTemplate", "it runs a command; TLC 2.19 stops on its definition (a CHOOSE over records with an Int field)"),
    ("IOUtils", "IOEnv", "it reads the environment; TLC 2.19 stops on its definition (a CHOOSE over [STRING -> STRING])"),
    ("IOUtils", "atoi", "TLC 2.19 stops on its definition (a CHOOSE over Int)"),
];

/// The operators of each module that tla2rs evaluates only when compiling, with the reason: their
/// value on values from the state is refused (the checker numbers its strings when it is built,
/// and these build strings by recursion over values it would print at run time)
pub const CONST_ONLY: &[(&str, &str, &str)] = &[
    ("Json", "ToJson", STRINGS_BY_RECURSION),
    ("Json", "ToJsonArray", STRINGS_BY_RECURSION),
    ("Json", "ToJsonObject", STRINGS_BY_RECURSION),
    ("IOUtils", "zeroPadN", STRINGS_BY_RECURSION),
];

/// Where TLC 2.19 says a CASE without OTHER of a module is written, when none of its conditions
/// is true: SANY's span of the CASE in the release's module file, from CASE to the last character
/// of its last arm (comments between arms included), as TLC prints a position (measured)
pub const CASE_AT: &[(&str, &str, &str)] = &[("SequencesExt", "Interleave", "line 445, col 3 to line 455, col 45 of module SequencesExt")];

const STRINGS_BY_RECURSION: &str = "it builds a string by recursion, which the checker cannot do at run time";

/// Folding a set: `op(f(x1), op(f(x2), ... op(f(xn), base)))` where x1 is `choose(S)`, x2 is
/// `choose(S \ {x1})`, and so on
const FOLDS: &str = r#"
---- MODULE Folds ----
RECURSIVE MapThenFoldSet(_, _, _, _, _)
MapThenFoldSet(op(_, _), base, f(_), choose(_), S) ==
  IF S = {} THEN base
  ELSE LET x == choose(S) IN op(f(x), MapThenFoldSet(op, base, f, choose, S \ {x}))
====
"#;

const FUNCTIONS: &str = r#"
---- MODULE Functions ----
EXTENDS Integers, Folds
Restrict(f, S) == [a \in S |-> f[a]]
RestrictDomain(f, Test(_)) == Restrict(f, {a \in DOMAIN f : Test(a)})
RestrictValues(f, Test(_)) == Restrict(f, {a \in DOMAIN f : Test(f[a])})
IsRestriction(narrow, wide) ==
  /\ DOMAIN narrow \subseteq DOMAIN wide
  /\ \A a \in DOMAIN narrow \cap DOMAIN wide : narrow[a] = wide[a]
Range(f) == {f[a] : a \in DOMAIN f}
Pointwise(f, g, T(_, _)) == [a \in DOMAIN f |-> T(f[a], g[a])]
Inverse(f, S, T) == [b \in T |-> CHOOSE a \in S : b \in Range(f) => f[a] = b]
AntiFunction(f) == Inverse(f, DOMAIN f, Range(f))
IsInjective(f) == \A a, b \in DOMAIN f : f[a] = f[b] => a = b
Injection(S, T) == {g \in [S -> T] : IsInjective(g)}
Surjection(S, T) == {g \in [S -> T] : \A b \in T : \E a \in S : g[a] = b}
Bijection(S, T) == Injection(S, T) \cap Surjection(S, T)
ExistsInjection(S, T) == Injection(S, T) # {}
ExistsSurjection(S, T) == Surjection(S, T) # {}
ExistsBijection(S, T) == Bijection(S, T) # {}
FoldFunctionOnSet(op(_, _), base, fun, indices) ==
  MapThenFoldSet(op, base, LAMBDA a : fun[a], LAMBDA T : CHOOSE a \in T : TRUE, indices)
FoldFunction(op(_, _), base, fun) == FoldFunctionOnSet(op, base, fun, DOMAIN fun)
SumFunctionOnSet(fun, indices) == FoldFunctionOnSet(LAMBDA a, b : a + b, 0, fun, indices)
SumFunction(fun) == SumFunctionOnSet(fun, DOMAIN fun)
====
"#;

const FINITE_SETS_EXT: &str = r#"
---- MODULE FiniteSetsExt ----
EXTENDS Integers, FiniteSets, Folds, Functions
FoldSet(op(_, _), base, set) == MapThenFoldSet(op, base, LAMBDA a : a, LAMBDA T : CHOOSE a \in T : TRUE, set)
SumSet(set) == FoldSet(LAMBDA a, b : a + b, 0, set)
ProductSet(set) == FoldSet(LAMBDA a, b : a * b, 1, set)
ReduceSet(op(_, _), set, acc) == FoldSet(op, acc, set)
MapThenSumSet(op(_), set) == MapThenFoldSet(LAMBDA a, b : a + b, 0, op, LAMBDA T : CHOOSE a \in T : TRUE, set)
FlattenSet(S) == UNION S
SymDiff(A, B) == (A \ B) \cup (B \ A)
Quantify(S, P(_)) == Cardinality({a \in S : P(a)})
kSubset(k, S) == {T \in SUBSET S : Cardinality(T) = k}
Max(S) == CHOOSE a \in S : \A b \in S : a >= b
Min(S) == CHOOSE a \in S : \A b \in S : a =< b
Choices(Sets) == {Range(g) : g \in {g \in [Sets -> UNION Sets] : \A T \in Sets : g[T] \in T}}
ChooseUnique(S, P(_)) == CHOOSE a \in S : P(a) /\ \A b \in S : P(b) => b = a
====
"#;

const SEQUENCES_EXT: &str = r#"
---- MODULE SequencesExt ----
EXTENDS Sequences, Naturals, FiniteSets, FiniteSetsExt, Folds, Functions, Bags, TLC
ToSet(s) == {s[i] : i \in DOMAIN s}
ToBag(s) == [a \in Range(s) |-> Cardinality({i \in DOMAIN s : s[i] = a})]
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)
SetToSeqs(S) == {f \in [1..Cardinality(S) -> S] : IsInjective(f)}
SetToSortSeq(S, op(_, _)) == SortSeq(SetToSeq(S), op)
SetToAllKPermutations(S) == UNION {SetToSeqs(T) : T \in SUBSET S}
TupleOf(set, n) == [1..n -> set]
SeqOf(set, n) == UNION {[1..k -> set] : k \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)
Contains(s, e) == \E i \in 1..Len(s) : s[i] = e
IsSorted(s, op(_, _)) == \A i, j \in 1..Len(s) : i < j => op(s[i], s[j])
Reverse(s) == [i \in 1..Len(s) |-> s[(Len(s) - i) + 1]]
Remove(s, e) == SelectSeq(s, LAMBDA a : a # e)
ReplaceAll(s, old, new) == [i \in 1..Len(s) |-> IF s[i] = old THEN new ELSE s[i]]
SelectInSeq(seq, Test(_)) ==
  LET I == {i \in 1..Len(seq) : Test(seq[i])} IN IF I # {} THEN Min(I) ELSE 0
SelectInSubSeq(seq, from, to, Test(_)) ==
  LET I == {i \in from..to : Test(seq[i])} IN IF I # {} THEN Min(I) ELSE 0
SelectLastInSeq(seq, Test(_)) ==
  LET I == {i \in 1..Len(seq) : Test(seq[i])} IN IF I # {} THEN Max(I) ELSE 0
SelectLastInSubSeq(seq, from, to, Test(_)) ==
  LET I == {i \in from..to : Test(seq[i])} IN IF I # {} THEN Max(I) ELSE 0
InsertAt(s, i, e) == SubSeq(s, 1, i - 1) \o <<e>> \o SubSeq(s, i, Len(s))
ReplaceAt(s, i, e) == [s EXCEPT ![i] = e]
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))
RemoveFirst(s, e) ==
  IF \E i \in 1..Len(s) : s[i] = e THEN RemoveAt(s, SelectInSeq(s, LAMBDA a : a = e)) ELSE s
RemoveFirstMatch(s, Test(_)) ==
  IF \E i \in 1..Len(s) : Test(s[i]) THEN RemoveAt(s, SelectInSeq(s, Test)) ELSE s
Cons(elt, seq) == <<elt>> \o seq
Snoc(elt, seq) == Append(seq, elt)
Front(s) == SubSeq(s, 1, Len(s) - 1)
Last(s) == s[Len(s)]
IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))
IsStrictPrefix(s, t) == IsPrefix(s, t) /\ s # t
IsSuffix(s, t) == IsPrefix(Reverse(s), Reverse(t))
IsStrictSuffix(s, t) == IsSuffix(s, t) /\ s # t
Prefixes(s) == {SubSeq(s, 1, k) : k \in 0..Len(s)}
CommonPrefixes(S) == {p \in UNION {Prefixes(s) : s \in S} : \A t \in S : IsPrefix(p, t)}
LongestCommonPrefix(S) ==
  CHOOSE p \in CommonPrefixes(S) : \A q \in CommonPrefixes(S) : Len(q) <= Len(p)
Suffixes(s) == {SubSeq(s, k, Len(s)) : k \in 1..Len(s)} \cup {<<>>}
SeqMod(a, b) == IF a % b = 0 THEN b ELSE a % b
FoldSeq(op(_, _), base, seq) == FoldFunction(op, base, seq)
FoldLeft(op(_, _), base, seq) ==
  MapThenFoldSet(LAMBDA a, b : op(b, a), base, LAMBDA i : seq[i], LAMBDA T : Max(T), DOMAIN seq)
FoldRight(op(_, _), seq, base) ==
  MapThenFoldSet(op, base, LAMBDA i : seq[i], LAMBDA T : Min(T), DOMAIN seq)
FoldLeftDomain(op(_, _), base, seq) == FoldLeft(op, base, [i \in DOMAIN seq |-> i])
FoldRightDomain(op(_, _), seq, base) == FoldRight(op, [i \in DOMAIN seq |-> i], base)
FlattenSeq(seqs) == IF Len(seqs) = 0 THEN seqs ELSE FoldLeft(LAMBDA a, b : a \o b, <<>>, seqs)
Zip(s, t) ==
  LET n == IF Len(s) <= Len(t) THEN Len(s) ELSE Len(t) IN [i \in 1..n |-> <<s[i], t[i]>>]
Interleave(s, t) ==
  CASE Len(s) = Len(t) -> [k \in 1..2 * Len(s) |-> IF k % 2 = 1 THEN <<s[(k + 1) \div 2]>> ELSE <<t[k \div 2]>>]
SubSeqs(s) == {SubSeq(s, i + 1, j) : i, j \in 0..Len(s)}
AllSubSeqs(s) ==
  {[k \in 1..Cardinality(D) |-> s[CHOOSE i \in D : Cardinality({j \in D : j > i}) = k - 1]] : D \in SUBSET DOMAIN s}
LOCAL Starts(s, t) == {k \in 1..Len(t) - Len(s) + 1 : SubSeq(t, k, k + Len(s) - 1) = s}
IndexFirstSubSeq(s, t) == CHOOSE k \in Starts(s, t) : \A j \in Starts(s, t) : k <= j
ReplaceSubSeqAt(i, r, s, t) == SubSeq(t, 1, i - 1) \o r \o SubSeq(t, i + Len(s), Len(t))
ReplaceFirstSubSeq(r, s, t) ==
  IF Starts(s, t) # {} THEN ReplaceSubSeqAt(IndexFirstSubSeq(s, t), r, s, t) ELSE t
ReplaceAllSubSeqs(r, s, t) ==
  CASE s = t -> r
    [] r = s -> t
    [] Len(s) = 0 ->
         LET upto[k \in 0..Len(t)] == IF k = 0 THEN <<>> ELSE upto[k - 1] \o r \o <<t[k]>>
         IN upto[Len(t)]
    [] Starts(s, t) # {} ->
         LET from[k \in 1..Len(t) + 1] ==
               IF k > Len(t) - Len(s) + 1 THEN SubSeq(t, k, Len(t))
               ELSE IF SubSeq(t, k, k + Len(s) - 1) = s THEN r \o from[k + Len(s)]
               ELSE <<t[k]>> \o from[k + 1]
         IN from[1]
    [] OTHER -> t
====
"#;

const UNDIRECTED_GRAPHS: &str = r#"
---- MODULE UndirectedGraphs ----
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
IsUndirectedGraph(G) ==
  /\ G = [node |-> G.node, edge |-> G.edge]
  /\ \A e \in G.edge : \E a, b \in G.node : e = {a, b}
IsLoopFreeUndirectedGraph(G) ==
  /\ G = [node |-> G.node, edge |-> G.edge]
  /\ \A e \in G.edge : \E a, b \in G.node : a # b /\ e = {a, b}
UndirectedSubgraph(G) == {H \in [node : SUBSET G.node, edge : SUBSET G.edge] : IsUndirectedGraph(H)}
Path(G) == FALSE
SimplePath(G) == FALSE
AreConnectedIn(m, n, G) == FALSE
ConnectedComponents(G) == FALSE
IsStronglyConnected(G) == FALSE
UndirectedGraphs(S) == [node : {S}, edge : SUBSET {{a, b} : <<a, b>> \in S \X S}]
====
"#;

/// Bitwise operations on natural numbers, bit by bit from the lowest: `bit` is the value of the
/// bit looked at and `rest` what is left of the larger argument
const BITWISE: &str = r#"
---- MODULE Bitwise ----
LOCAL INSTANCE Integers
RECURSIVE And(_, _, _, _)
LOCAL And(x, y, bit, rest) ==
  IF rest = 0 THEN 0
  ELSE bit * ((x \div bit) % 2) * ((y \div bit) % 2) + And(x, y, 2 * bit, rest \div 2)
x & y == IF x >= y THEN And(x, y, 1, x) ELSE And(y, x, 1, y)
RECURSIVE Or(_, _, _, _)
LOCAL Or(x, y, bit, rest) ==
  IF rest = 0 THEN 0
  ELSE LET a == (x \div bit) % 2
           b == (y \div bit) % 2
       IN bit * ((a + b + a * b) % 2) + Or(x, y, 2 * bit, rest \div 2)
x | y == IF x >= y THEN Or(x, y, 1, x) ELSE Or(y, x, 1, y)
RECURSIVE Xor(_, _, _, _)
LOCAL Xor(x, y, bit, rest) ==
  IF rest = 0 THEN 0
  ELSE bit * (((x \div bit) + (y \div bit)) % 2) + Xor(x, y, 2 * bit, rest \div 2)
x ^^ y == IF x >= y THEN Xor(x, y, 1, x) ELSE Xor(y, x, 1, y)
RECURSIVE NotR(_, _, _)
LOCAL NotR(x, bit, rest) ==
  IF rest = 0 THEN 0 ELSE bit * ((((x \div bit) % 2) + 1) % 2) + NotR(x, 2 * bit, rest \div 2)
Not(a) == NotR(a, 1, a)
RECURSIVE shiftR(_, _)
shiftR(n, pos) == IF pos = 0 THEN n ELSE shiftR(n \div 2, pos - 1)
====
"#;

/// Properties of a relation given as a function from pairs to booleans (`R[a, b]`), or as an
/// operator (`...Under`). A value used more than once is bound by `\E x \in {e}` or `{... : x \in {e}}`, so
/// that it is computed once: LET definitions are expanded at each use
const RELATION: &str = r#"
---- MODULE Relation ----
EXTENDS Naturals, FiniteSets
IsReflexive(R, S) == \A a \in S : R[a, a]
IsReflexiveUnder(op(_, _), S) == \A a \in S : op(a, a)
IsIrreflexive(R, S) == \A a \in S : ~R[a, a]
IsIrreflexiveUnder(op(_, _), S) == \A a \in S : ~op(a, a)
IsSymmetric(R, S) == \A a, b \in S : R[a, b] = R[b, a]
IsSymmetricUnder(op(_, _), S) == \A a, b \in S : op(a, b) = op(b, a)
IsAntiSymmetric(R, S) == \A a, b \in S : a # b => ~(R[a, b] /\ R[b, a])
IsAntiSymmetricUnder(op(_, _), S) == \A a, b \in S : a # b => ~(op(a, b) /\ op(b, a))
IsAsymmetric(R, S) == \A a, b \in S : ~R[a, b] \/ ~R[b, a]
IsAsymmetricUnder(op(_, _), S) == \A a, b \in S : ~op(a, b) \/ ~op(b, a)
IsTransitive(R, S) == \A a, b, c \in S : (R[a, b] /\ R[b, c]) => R[a, c]
IsTransitiveUnder(op(_, _), S) == \A a, b, c \in S : (op(a, b) /\ op(b, c)) => op(a, c)
IsStrictlyPartiallyOrdered(R, S) == IsIrreflexive(R, S) /\ IsAntiSymmetric(R, S) /\ IsTransitive(R, S)
IsStrictlyPartiallyOrderedUnder(op(_, _), S) ==
  IsIrreflexiveUnder(op, S) /\ IsAntiSymmetricUnder(op, S) /\ IsTransitiveUnder(op, S)
IsPartiallyOrdered(R, S) == IsReflexive(R, S) /\ IsAntiSymmetric(R, S) /\ IsTransitive(R, S)
IsPartiallyOrderedUnder(op(_, _), S) ==
  IsReflexiveUnder(op, S) /\ IsAntiSymmetricUnder(op, S) /\ IsTransitiveUnder(op, S)
IsStrictlyTotallyOrdered(R, S) ==
  IsStrictlyPartiallyOrdered(R, S) /\ \A a, b \in S : a = b \/ R[a, b] \/ R[b, a]
IsStrictlyTotallyOrderedUnder(op(_, _), S) ==
  IsStrictlyPartiallyOrderedUnder(op, S) /\ \A a, b \in S : a = b \/ op(a, b) \/ op(b, a)
IsTotallyOrdered(R, S) == IsPartiallyOrdered(R, S) /\ \A a, b \in S : R[a, b] \/ R[b, a]
IsTotallyOrderedUnder(op(_, _), S) == IsPartiallyOrderedUnder(op, S) /\ \A a, b \in S : op(a, b) \/ op(b, a)
TransitiveClosure(R, S) ==
  LET pairs[k \in 0..Cardinality(S)] ==
        IF k = 0 THEN {p \in S \X S : R[p[1], p[2]]}
        ELSE UNION {P \cup {p \in S \X S : \E c \in S : <<p[1], c>> \in P /\ <<c, p[2]>> \in P} : P \in {pairs[k - 1]}}
  IN CHOOSE f \in {[p \in S \X S |-> p \in P] : P \in {pairs[Cardinality(S)]}} : TRUE
ReflexiveTransitiveClosure(R, S) ==
  CHOOSE f \in {[p \in S \X S |-> p[1] = p[2] \/ T[p]] : T \in {TransitiveClosure(R, S)}} : TRUE
IsConnected(R, S) == \E T \in {ReflexiveTransitiveClosure(R, S)} : \A a, b \in S : T[a, b]
====
"#;

/// Bags: a fold applies `op` to `base` and f(x) once per copy of x for each element, the elements
/// taken as `MapThenFoldSet` takes them
const BAGS_EXT: &str = r#"
---- MODULE BagsExt ----
LOCAL INSTANCE Bags
LOCAL INSTANCE Integers
LOCAL INSTANCE Folds
BagAdd(B, x) == B (+) SetToBag({x})
BagRemove(B, x) == B (-) SetToBag({x})
BagRemoveAll(B, x) ==
  IF x \in DOMAIN B THEN LET less[n \in 0..B[x]] == IF n = 0 THEN B ELSE less[n - 1] (-) SetToBag({x}) IN less[B[x]]
  ELSE B
MapThenFoldBag(op(_, _), base, f(_), choose(_), B) ==
  LET Copies(x) == LET acc[n \in 1..B[x]] == op(IF n > 1 THEN acc[n - 1] ELSE base, f(x)) IN acc[B[x]]
  IN MapThenFoldSet(op, base, Copies, LAMBDA T : CHOOSE a \in T : TRUE, DOMAIN B)
FoldBag(op(_, _), base, B) == MapThenFoldBag(op, base, LAMBDA a : a, LAMBDA T : CHOOSE a \in T : TRUE, B)
SumBag(B) == FoldBag(LAMBDA a, b : a + b, 0, B)
ProductBag(B) == FoldBag(LAMBDA a, b : a * b, 1, B)
====
"#;

/// Directed graphs as records `[node |-> N, edge |-> E]` with E a set of pairs (values used more
/// than once are bound as in Relation)
const GRAPHS: &str = r#"
---- MODULE Graphs ----
EXTENDS Naturals, Sequences, FiniteSets, SequencesExt, Relation
IsDirectedGraph(G) == G = [node |-> G.node, edge |-> G.edge] /\ G.edge \subseteq G.node \X G.node
DirectedSubgraph(G) == {H \in [node : SUBSET G.node, edge : SUBSET G.edge] : H.edge \subseteq H.node \X H.node}
Transpose(G) == [node |-> G.node, edge |-> {<<e[2], e[1]>> : e \in G.edge}]
IsUndirectedGraph(G) == IsDirectedGraph(G) /\ \A e \in G.edge : <<e[2], e[1]>> \in G.edge
UndirectedSubgraph(G) == {H \in DirectedSubgraph(G) : IsUndirectedGraph(H)}
Path(G) == FALSE
SimplePath(G) == FALSE
AreConnectedIn(m, n, G) == FALSE
IsStronglyConnected(G) == FALSE
ConnectionsIn(G) == ReflexiveTransitiveClosure([p \in G.node \X G.node |-> p \in G.edge], G.node)
IsTreeWithRoot(G, r) == FALSE
GraphUnion(G, H) == [node |-> G.node \cup H.node, edge |-> G.edge \cup H.edge]
IsBipartiteWithPartitions(G, U, V) ==
  /\ U \cap V = {}
  /\ G.node \subseteq U \cup V
  /\ \A e \in G.edge : {e[1], e[2]} \cap U # {} /\ {e[1], e[2]} \cap V # {}
HasCycle(G) == \E C \in {ConnectionsIn(G)} : \E e \in G.edge : e[1] \in G.node /\ e[2] \in G.node /\ C[e[2], e[1]]
IsDag(G) == IsDirectedGraph(G) /\ ~HasCycle(G)
Successors(G, n) == {m \in G.node : <<n, m>> \in G.edge}
AllSuccessors(G, S) == UNION {Successors(G, n) : n \in S}
Predecessors(G, n) == {m \in G.node : <<m, n>> \in G.edge}
AllPredecessors(G, S) == UNION {Predecessors(G, n) : n \in S}
Ancestors(G, n) == UNION {{m \in G.node : \E k \in Successors(G, m) : C[k, n]} : C \in {ConnectionsIn(G)}}
Descendants(G, n) == UNION {{m \in G.node : \E k \in Successors(G, n) : C[k, m]} : C \in {ConnectionsIn(G)}}
InDegree(G, n) == Cardinality(Predecessors(G, n))
OutDegree(G, n) == Cardinality(Successors(G, n))
Roots(G) == {n \in G.node : \A m \in G.node : <<m, n>> \notin G.edge}
Leaves(G) == {n \in G.node : \A m \in G.node : <<n, m>> \notin G.edge}
EmptyGraph == [node |-> {}, edge |-> {}]
Graphs(S) == [node : {S}, edge : SUBSET (S \X S)]
====
"#;

/// `factorial` is a function over Nat, applied where it is used
const COMBINATORICS: &str = r#"
---- MODULE Combinatorics ----
EXTENDS Naturals
factorial[n \in Nat] == IF n > 0 THEN n * factorial[n - 1] ELSE 1
choose(n, k) == factorial[n] \div (factorial[n - k] * factorial[k])
====
"#;

/// The module's definition is TRUE (the test is its Java override, which TLC 2.19 does not load)
const STATISTICS: &str = r#"
---- MODULE Statistics ----
EXTENDS Naturals
ChiSquare(expected, actual, alpha) == TRUE
====
"#;

/// The module's definition is TRUE (the drawing is its Java override, which TLC 2.19 does not load)
const GRAPH_VIZ: &str = r#"
---- MODULE GraphViz ----
DotDiGraph(G, VL(_), EL(_)) == TRUE
====
"#;

/// Rationals `[num |-> n, den |-> d]` whose denominator is a power of two. Reducing takes the
/// greatest common divisor among 1..num, so a numerator of 0 or less is an evaluation error, as in
/// the module's definition
const DYADIC_RATIONALS: &str = r#"
---- MODULE DyadicRationals ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE TLC
LOCAL Gcd(a, b) ==
  LET Common == {d \in (1..a) \cap (1..b) : a % d = 0 /\ b % d = 0} IN CHOOSE d \in Common : \A e \in Common : e <= d
LOCAL Lowest(p) ==
  LET g == Gcd(p.num, p.den) IN IF g = 1 THEN p ELSE [num |-> p.num \div g, den |-> p.den \div g]
IsDyadicRational(r) == \E k \in 0..r.den : 2^k = r.den
Zero == [num |-> 0, den |-> 1]
One == [num |-> 1, den |-> 1]
Add(p, q) ==
  IF p = Zero THEN q
  ELSE LET d == IF p.den < q.den THEN q.den ELSE p.den
       IN Lowest([num |-> q.num * (d \div q.den) + p.num * (d \div p.den), den |-> d])
Half(p) == Lowest([num |-> p.num, den |-> 2 * p.den])
PrettyPrint(p) == CASE p = Zero -> "0" [] p = One -> "1" [] OTHER -> ToString(p.num) \o "/" \o ToString(p.den)
====
"#;

/// Vector clocks: functions from nodes to counters, a missing node counting 0
const VECTOR_CLOCKS: &str = r#"
---- MODULE VectorClocks ----
EXTENDS Naturals, Sequences, Functions
LOCAL Before(a, b, D) == (\A d \in D : a[d] <= b[d]) /\ \E d \in D : a[d] < b[d]
LOCAL Apart(a, b, D) == \E d, e \in D : d # e /\ a[d] < b[d] /\ a[e] > b[e]
IsCausalOrder(log, clock(_)) ==
  \A i \in 1..Len(log) : \A j \in 1..i - 1 :
    LET D == DOMAIN clock(log[i]) \cup DOMAIN clock(log[j])
        Full(c) == [d \in D |-> IF d \in DOMAIN c THEN c[d] ELSE 0]
    IN Before(Full(clock(log[j])), Full(clock(log[i])), D) \/ Apart(Full(clock(log[j])), Full(clock(log[i])), D)
CausalOrder(log, clock(_), node(_), domain(_)) ==
  CHOOSE f \in {g \in [1..Len(log) -> Range(log)] : Range(g) = Range(log)} : IsCausalOrder(f, clock)
====
"#;

/// Sets of subsets of S any two of which meet, closed under supersets within S
const QUORUM: &str = r#"
---- MODULE Quorum ----
QuorumSystem(S) ==
  {Q \in SUBSET SUBSET S :
     /\ Q # {}
     /\ \A A, B \in Q : A \cap B # {}
     /\ \A A, B \in SUBSET S : (A \in Q /\ A \subseteq B) => B \in Q}
====
"#;

/// JSON text of a function, built with ToString: each element of the domain is taken as CHOOSE
/// takes it (the smallest first), each value printed as TLC prints it (a nested record or tuple is
/// not turned into JSON), and a key is the string of the string ToString gives. ToJson of a record
/// lists its values as an array, as the module's definition does. The strings are concatenated in
/// the order the module's definition concatenates them, which is the order TLC makes them in.
/// Writing to and reading from files is not done: the serializing operators are TRUE in the
/// module's definition
const JSON: &str = r#"
---- MODULE Json ----
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE TLC
LOCAL IsSequence(F, D) == TRUE
LOCAL ToJsonKeyValue(F, d) == ToString(ToString(d)) \o ":" \o ToString(F[d])
RECURSIVE ToJsonObjectString(_, _)
LOCAL ToJsonObjectString(F, D) ==
  LET d == CHOOSE e \in D : TRUE
      tail == IF D \ {d} = {} THEN "}" ELSE ToJsonObjectString(F, D \ {d})
  IN (IF D = DOMAIN F THEN "{" ELSE ", ") \o ToJsonKeyValue(F, d) \o tail
RECURSIVE ToJsonArrayString(_, _)
LOCAL ToJsonArrayString(F, D) ==
  LET d == CHOOSE e \in D : TRUE
      tail == IF D \ {d} = {} THEN "]" ELSE ToJsonArrayString(F, D \ {d})
  IN (IF D = DOMAIN F THEN "[" ELSE ", ") \o ToString(F[d]) \o tail
RECURSIVE ToJsonString(_, _)
LOCAL ToJsonString(F, D) == ToJsonArrayString(F, D)
ToJson(value) == IF DOMAIN value = {} THEN "{}" ELSE ToJsonString(value, DOMAIN value)
ToJsonArray(value) == IF DOMAIN value = {} THEN "[]" ELSE ToJsonArrayString(value, DOMAIN value)
ToJsonObject(value) == IF DOMAIN value = {} THEN "{}" ELSE ToJsonObjectString(value, DOMAIN value)
JsonSerialize(absoluteFilename, value) == TRUE
JsonDeserialize(absoluteFilename) == FALSE
ndJsonSerialize(absoluteFilename, value) == TRUE
ndJsonDeserialize(absoluteFilename) == FALSE
====
"#;

/// Files, commands and the environment are not read or written: what TLC 2.19 evaluates of the
/// module's definitions is IOSerialize (TRUE) and zeroPadN, n printed with ToString after as
/// many "0" as it is shorter than width
const IO_UTILS: &str = r#"
---- MODULE IOUtils ----
LOCAL INSTANCE TLC
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt
IOSerialize(val, absoluteFilename, compress) == TRUE
IODeserialize(absoluteFilename, compressed) == FALSE
Serialize(value, dest, options) == FALSE
Deserialize(src, options) == FALSE
IOExec(command) == FALSE
IOEnvExec(env, command) == FALSE
IOExecTemplate(commandTemplate, parameters) == FALSE
IOEnvExecTemplate(env, commandTemplate, parameters) == FALSE
IOEnv == FALSE
atoi(str) == FALSE
zeroPadN(n, width) ==
  LET s == ToString(n)
      pad == [i \in 1..width - Len(s) |-> "0"]
  IN FoldLeft(LAMBDA a, b : a \o b, "", pad) \o s
====
"#;

/// HTML text built from templates: each `%key%` of a template is replaced in turn by its value, the
/// first occurrence only and in the text as replaced so far (`ReplaceFirstSubSeq` in a fold from the
/// left), and parts are joined with a separator that is left out after an empty text built so far,
/// as the module's definitions do; the strings are made in the order those definitions make them
const HTML: &str = r##"
---- MODULE HTML ----
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt
HTMLFill(template, pairs) == FoldLeft(LAMBDA text, p : ReplaceFirstSubSeq(p[2], p[1], text), template, pairs)
LOCAL Joined(parts, sep) == FoldLeft(LAMBDA text, part : IF text = "" THEN part ELSE text \o sep \o part, "", parts)
HTMLDocument(head, body, scripts) ==
  Joined(<<"<!DOCTYPE html>", "<html>", head, body, Joined(scripts, "\n"), "</html>">>, "\n")
HTMLClass(name, attrs) == Joined(<<ReplaceFirstSubSeq(name, "%classname%", "%classname% {"), Joined(attrs, "\n"), "}">>, "\n")
HTMLAttribute(key, val) == HTMLFill("%name%: %value%;", <<<<"%name%", key>>, <<"%value%", val>>>>)
HTMLDefaultStyle ==
  Joined(<<HTMLClass(".default_grid", <<HTMLAttribute("display", "grid")>>),
           HTMLClass(".default_box", <<HTMLAttribute("border", "1px solid black")>>),
           HTMLClass(".default_circle", <<HTMLAttribute("border-radius", "50%")>>)>>, "\n")
HTMLStyleSheet(classes) == Joined(<<"<style type=\"text/css\">", HTMLDefaultStyle, Joined(classes, "\n"), "</style>">>, "\n")
HTMLScriptFile(src) == HTMLFill("<script src=\"%name%\"></script>", <<<<"%name%", src>>>>)
HTMLScript(lines) == Joined(<<"<script>", Joined(lines, "\n"), "</script>">>, "\n")
HTMLLink(href, rel) == HTMLFill("<link href=\"%name%\" rel=\"%type%\"/>", <<<<"%name%", href>>, <<"%type%", rel>>>>)
HTMLHeader(title, links, classes) ==
  Joined(<<"<head>", "<meta charset=\"UTF-8\">", ReplaceFirstSubSeq(title, "%title%", "<title>%title%</title>"),
           Joined(links, "\n"), HTMLStyleSheet(classes), "</head>">>, "\n")
HTMLBody(inner) == Joined(<<"<body>", inner, "</body>">>, "\n")
HTMLFrame(id, inner) == Joined(<<ReplaceFirstSubSeq(id, "%id%", "<div id=\"%id%\">"), Joined(inner, "\n"), "</div>">>, "\n")
HTMLGridContainer(id, classes, inner) ==
  Joined(<<HTMLFill("<div id=\"%id%\" class=\"default_grid %class_list%\">", <<<<"%id%", id>>, <<"%class_list%", Joined(classes, " ")>>>>),
           Joined(inner, "\n"), "</div>">>, "\n")
HTMLBox(id, classes, size, inner) ==
  Joined(<<HTMLFill("<div id=\"%id%\" class=\"default_box %class_list%\" style=\"%size%\">",
                    <<<<"%id%", id>>, <<"%class_list%", Joined(classes, " ")>>, <<"%size%", size>>>>),
           Joined(inner, "\n"), "</div>">>, "\n")
HTMLCircle(id, classes, size, inner) == HTMLBox(id, <<"default_circle">> \o classes, size, inner)
HTMLText(id, text) == Joined(<<ReplaceFirstSubSeq(id, "%id%", "<span id=\"%id%\">"), text, "</span>">>, "\n")
HTMLSVG(id, box, size, svg) ==
  Joined(<<HTMLFill("<svg id=\"%id%\" viewBox=\"%viewBox%\" style=\"%size%\">", <<<<"%id%", id>>, <<"%viewBox%", box>>, <<"%size%", size>>>>),
           svg, "</svg>">>, "\n")
HTMLSize(w, h) == Joined(<<HTMLAttribute("width", w), HTMLAttribute("height", h)>>, " ")
HTMLNewLine == "<br>"
HTMLFlexCenterAttributes ==
  Joined(<<HTMLAttribute("display", "flex"), HTMLAttribute("align-items", "center"), HTMLAttribute("justify-content", "center")>>, "\n")
HTMLJSLineElems(from, to) ==
  HTMLFill("document.getElementById(\"%id1%\"), document.getElementById(\"%id2%\")", <<<<"%id1%", from>>, <<"%id2%", to>>>>)
HTMLJSLine(from, to, color, size) ==
  HTMLFill("new LeaderLine(%elems%, {color: '%color%', size: %size%})",
           <<<<"%elems%", HTMLJSLineElems(from, to)>>, <<"%color%", color>>, <<"%size%", size>>>>)
HTMLJSLineDash(from, to, color, size) ==
  HTMLFill("new LeaderLine(%elems%,  {color: '%color%', size: %size%, dash: true})",
           <<<<"%elems%", HTMLJSLineElems(from, to)>>, <<"%color%", color>>, <<"%size%", size>>>>)
HTMLJSKeyListener(events) ==
  Joined(<<"window.onkeyup = function(event) {", "let key = event.key.toUpperCase();", Joined(events, "\n"), "}">>, "\n")
HTMLJSNavigationKey(key, file) ==
  Joined(<<ReplaceFirstSubSeq(key, "%key%", "if(key == '%key%'){"),
           ReplaceFirstSubSeq(file, "%file%", "window.location.replace(\"%file%\");"), "}">>, "\n")
====
"##;
