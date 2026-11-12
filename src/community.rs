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
//! (they enumerate `Seq(S)`), or they are not written yet.

/// The source of each module, by name
pub fn source(name: &str) -> Option<&'static str> {
    Some(match name {
        "Folds" => FOLDS,
        "Functions" => FUNCTIONS,
        "FiniteSetsExt" => FINITE_SETS_EXT,
        "SequencesExt" => SEQUENCES_EXT,
        "UndirectedGraphs" => UNDIRECTED_GRAPHS,
        "Bitwise" => BITWISE,
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
];

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
