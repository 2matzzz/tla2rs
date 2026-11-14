# tla2rs

[日本語](README.ja.md)

tla2rs compiles a TLA+ specification into **a Rust model checker built for that one spec**.

TLC interprets the spec on every step and represents values as heap objects. tla2rs instead reads a finite type for each
variable from `TypeOK`, then emits Rust with a bit-packed state struct and `Next` unrolled into nested `for` / `if`, and
builds it with `cargo build --release`. You pay a few seconds of build time whenever the spec changes; in return, the
search itself is an order of magnitude faster than TLC.

```
$ tla2rs examples/Peterson.tla -config examples/Peterson-Live.cfg
tla2rs: generated .tla2rs/Peterson-Live/src/main.rs in 4 ms
tla2rs: built in 1.3 s
63 states generated, 34 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 10.
Temporal properties hold (3 properties, 2 fairness conditions, 62 edges).
Model checking completed. No error has been found.
```

## Usage

```sh
cargo build --release
./target/release/tla2rs Spec.tla                  # reads Spec.cfg
./target/release/tla2rs Spec.tla -config Other.cfg -deadlock -workers 8
./target/release/tla2rs Spec.tla -memlimit 64 -notrace        # use less memory
./target/release/tla2rs Spec.tla --emit-only      # only write the Rust (.tla2rs/<cfg name>/src/main.rs)
```

- `-deadlock` / `CHECK_DEADLOCK FALSE` mean the same as in TLC: deadlock is not an error
- `-workers N` sets the number of search threads (default: number of CPUs)
- `-memlimit MB` caps how much of the BFS queue stays in memory (default 256 MB), and with temporal properties how
  much of the state graph does; the rest spills to temp files in `-tmpdir DIR`. By default that is the system's temp
  dir, unless it is a tmpfs (as `/tmp` is on many Linux systems), whose files take memory like the data they hold;
  then it is the directory of the generated checker's executable
- `-notrace` stops recording what is needed to rebuild a counterexample (16 bytes per state drops to 8)
- `-setcap N` and `-seqcap N` set where the capacity of sets held as arrays (and of the domains of functions and
  bags over large types) and the maximum length of sequences start. They are never needed: a value that outgrows
  its capacity makes tla2rs build the checker again with twice the room and check from the start (see Limitations)
- `-fp128` uses 128-bit fingerprints instead of 64-bit ones
- `-metal` runs the "already seen?" lookups on the GPU (Apple Metal); `-batched` runs the same three-phase pipeline on
  the CPU
- `-dumpgraph FILE` writes the states and transitions explored to FILE in the form of TLC's `-dump dot FILE` (a node
  per state, labelled with the state as TLC prints it, and an edge per successor). `tla2rs --graph FILE` reduces
  either file to hashes of its states and its edges that do not depend on node ids or order, and `--graph-text FILE`
  prints that canonical form
- `-lassocheck DIR` makes a checker that finds a liveness counterexample write `DIR/Tla2rsLasso.tla` and
  `Tla2rsLasso.cfg`: a spec whose only behavior is that lasso, which TLC reports as violating the properties only if
  the lasso is a fair behavior of the spec that violates them (see CLAUDE.md, "Counterexamples")
- `tla2rs --trace FILE` reduces the counterexample in an output of TLC or of a checker to its length and a hash of its
  states and actions; `--trace-text FILE` prints the canonical form
- `tla2rs --messages FILE` reduces the messages and printed lines in such an output (everything but the progress,
  statistics and counterexample) to a hash, and its error lines to another; `--messages-text FILE` prints the
  canonical form
- Output (state counts, counterexample format, including the name and position of each step's action, values wider
  than 80 columns broken over lines, error and warning messages) follows TLC, and so do exit codes: 10 = assumption (false or failing to
  evaluate), 11 = deadlock, 12 = invariant, 13 = temporal or action property. An evaluation error exits with 76 in an
  invariant, 75 in the initial states, and otherwise 255 for a failed arithmetic operation (such as `\div` by zero) and
  75 for the rest
- When a module holds a PlusCal algorithm whose translation line records checksums (`\* BEGIN TRANSLATION
  (chksum(pcal) = ... /\ chksum(tla) = ...)`), the checker warns, as TLC does, that the algorithm or its translation
  changed since the translator wrote them. tla2rs computes TLC's PlusCal checksum for algorithms without procedures,
  macros or PlusCal options; for the others it prints a note instead (see Limitations)

### TLC's options

tla2rs takes TLC 2.19's command-line options that mean something for an exhaustive, deterministic search, with
TLC's meaning, output and exit codes (each is cross-checked against TLC by a configuration in `tests/tlc/Opt*`):

| | Options |
|---|---|
| Supported from the start | `-config FILE`, `-deadlock`, `-workers N` (`auto` and the default both use every CPU; TLC's default is 1) |
| Supported now | `-continue`, `-difftrace`, `-view`, `-nowarning`, `-dump FILE`, `-dump dot[,actionlabels][,colorize][,snapshot] FILE`, `-userFile FILE` |
| Accepted with no effect | `-cleanup`, `-gzip`, `-metadir DIR`, `-checkpoint N`, `-fp N`, `-fpbits N`, `-fpmem X`, `-lncheck S`, `-modelcheck` |
| Not supported (refused) | `-simulate`, `-depth`, `-seed`, `-aril`, `-dfid`, `-generateSpecTE`, `-tool`, `-debug`, `-recover`, `-coverage`, `-terse`, `-maxSetSize` |

- `-continue` reports every state that violates an invariant (the first invariant it violates, in the order of the
  cfg) and every step that violates an action property, each with its behavior, and searches on. As in TLC, the run
  then ends with `No error has been found` and exit 0; a deadlock or an evaluation error still stops it, and a
  failed invariant stops it with TLC's "unexpected exception" and exit 255. Temporal properties are checked at the end
- `-difftrace` prints, for each state of a behavior after the first, only the variables that changed. TLC 2.19
  prints the last state of a behavior of three states or more in full, and so does tla2rs
- `-view` prints the `VIEW` of each state of a behavior instead of the state, without the empty line after it, and
  labels the nodes of `-dump dot` with it, as TLC does. Without a `VIEW` it changes nothing
- `-nowarning` leaves out TLC's own warnings (an EXCEPT on a missing argument, SYMMETRY or constraints with temporal
  properties). The parser's warnings and the PlusCal checksum warning stay, as in TLC
- `-dump FILE` writes the distinct states in the order found (`State N:` and the state); `-dump dot FILE` writes the
  state graph (as `-dumpgraph`), each edge has the attributes of a label as in TLC, `actionlabels` labels it with its
  action, and `snapshot` changes nothing (TLC's snapshots during the run are not written). `colorize` gives each edge
  the color of its action and ends the graph with a legend of the actions, as TLC does: the colors are numbered from 2
  by action name, in the order an edge of each is first written, and the legend lists them in the order TLC's Java
  hash map holds them. As in TLC, `.dump` or `.dot` is added to a name without it. With one worker the order of
  `-dump FILE` and the colors are TLC's; `-dump FILE` and `-continue` run without `-batched`
- `-userFile FILE` writes the lines the spec prints (Print and PrintT, also in ASSUMEs and constant definitions) to
  FILE instead of the standard output, which keeps TLC's own messages and warnings. As in TLC, each value is written
  as is on one line, without the pretty-printing of the standard output
- The options accepted with no effect change only TLC's files on disk (`-cleanup`, `-gzip`, `-metadir`,
  `-checkpoint`; TLC also prints a line at each checkpoint, every 30 minutes by default, which tla2rs does not),
  its fingerprints and their memory (`-fp`, `-fpbits`, `-fpmem`; tla2rs has fingerprints of its own), or when it
  checks temporal properties (`-lncheck`; tla2rs checks them at the end, as TLC's `final`). `-modelcheck` is the
  default mode
- Not supported, and why: `-simulate`, `-depth`, `-seed` and `-aril` belong to random simulation, which is not an
  exhaustive search. `-dfid` searches depth-first with iterative deepening, which reaches states in another order
  and reports other counts and counterexamples; tla2rs searches breadth-first only. `-generateSpecTE` and `-tool`
  serve the Toolbox and its trace explorer (a SpecTE module, output wrapped in message codes). `-debug` is TLC's own
  debugging output. `-recover` resumes from a checkpoint in TLC's own format, which tla2rs does not write.
  `-coverage` counts how often TLC's interpreter evaluated each subexpression; a compiled checker evaluates
  constants once and fuses expressions, so the counts depend on TLC's evaluator. `-terse` prints sets in the lazy
  form TLC holds them in (`SUBSET S`, `[S -> T]`), which a compiled checker does not keep. `-maxSetSize` bounds the sets TLC's interpreter enumerates, and where its error appears depends on
  where the interpreter enumerates

## Speed

Measured on a MacBook Pro (Apple silicon, 10 cores, 16 GB). TLC ran with `-workers auto`, tla2rs with its default thread
count. tla2rs times cover the search only; the one-off build per spec (a few seconds) is not included.

On a large real-world spec (767 bits per state, with `VIEW` and `SYMMETRY`), tla2rs reached in 12 minutes the point
TLC reached in 50, and finished the full search (about 590 million distinct states, depth 73) in 54 minutes. TLC did
not finish.

## How it works

1. **Parsing** (`parser.rs`): the commonly used subset of TLA+. `/\` and `\/` bullet lists are delimited by column
2. **Expansion** (`expand.rs`): every operator definition is inlined. Bound variables are renamed to avoid capture,
   and each call site keeps a trace (name and arguments)
3. **Types** (`types.rs`): a finite type per variable, taken from `x \in S` / `x \subseteq S` in `TypeOK`.
   Strings and model values become `u16`, integers `i64`, records and tuples Rust tuples, functions arrays (or sorted
   (key, value) pairs over a large domain type), and sets `u128` bitmasks
4. **Code generation** (`codegen.rs`): constant subexpressions are evaluated at compile time and become literals,
   except that a constant set of more than 1024 elements built from `[D -> R]`, `\X`, `[a : S]` and `SUBSET` is
   enumerated by the checker from its parts, in TLC's order, where it iterates over it.
   Actions are generated in continuation-passing style, threading "the remaining conjuncts" through; every `\/`,
   `\E`, and `IF` becomes a branch, and `x' = e` becomes a `let`
5. **Runtime** (`runtime.rs`): BFS, level by level, with each level split across threads. States are bit-packed to fit
   their types, and the visited set holds only 64-bit fingerprints. A state of 64 bits or fewer has a reversible
   fingerprint, so it cannot collide
6. **Liveness** (`live.rs`, `ltl.rs`): a property becomes a formula over state predicates, `ENABLED`, and action
   predicates, whose negation is turned into a Büchi automaton (tableau). During the search each state records which
   predicates hold and which fair actions are enabled, and each edge which action predicates and fair actions it
   satisfies. Afterwards the checker looks for a strongly connected component of the product of the state graph and
   the automaton that is accepting and fair (WF: a step of the action or a state where it is disabled; SF: a step, or
   no state where it is enabled, narrowing the component otherwise). When the automaton would be too large (many
   `[]<>` conjuncts in the spec, say), each disjunct of the negation's normal form is checked on its own, as TLC
   does, with its `[]<>` and `<>[]` parts as conditions on the component. Counterexamples are lassos printed as TLC does

### Memory

When only invariants are checked, states themselves are not kept. The checker holds just

- the visited fingerprints, each paired with the fingerprint of the state it was first reached from (16 bytes per
  slot of a hash table kept between 3/8 and 3/4 full, so 21 to 43 bytes per state; half that with `-notrace`)
- the queues for the current and next level (anything beyond `-memlimit` spills to a temp file and is read back in
  chunks)

When a violation is found, the checker walks the fingerprints back to an initial state and rebuilds the counterexample
by replaying `next` from there. Memory stays within "fingerprint table plus a capped queue", whatever the state width
or model size.

Checking temporal properties needs the whole state graph for the SCC search. The checker keeps it in columns:

- per state, the packed state, the state it was first reached from, where its edges start, and a class: the state
  atoms that hold there, the fairness conditions enabled there and the action atoms of its stuttering step, numbered
  among the distinct combinations, which are few (a byte while there are at most 256)
- per edge, the target and a class (the action, the action atoms and the fairness conditions of the step), 5 bytes;
  while the search runs the target is still a fingerprint, 9 bytes in all

Once the columns hold more than `-memlimit`, each column that grows moves to a temp file in `-tmpdir`, unlinked as
soon as it is opened, which the checker maps into memory. The kernel keeps in its page cache what fits and reads the
rest back from the disk, much as TLC keeps its liveness graph on disk. What stays in memory is the visited
fingerprints while the search runs, and then, for each property, the search of its product with the property's
automaton: 4 bytes per state and automaton node, and about 30 bytes per product node it reaches. That part is what
bounds the size of a model with temporal properties (one property per thread, so several at once take more).

## What is supported

| | |
|---|---|
| Expressions | logic, arithmetic (`+ - * \div % ^`), comparison, sequences (`Seq`, `Len`, `Append`, `Head`, `Tail`, `SubSeq`, `SelectSeq`, `\o`, indexing, a tuple and a function over 1..n being the same value), sets of sets and of functions as values, `IF` / `CASE` / `LET`, `\E` / `\A` (also `<<x, y>> \in S`), `CHOOSE` (also over sets in the state, picking what TLC picks), `\E x : P`, `\A x : P` and `CHOOSE x : P` without a set (accepted, and an evaluation error where TLC evaluates them), `RECURSIVE` operators (also with `ENABLED` inside) and recursive function definitions, operator parameters and `LAMBDA`, infix operators defined by the spec (`a \oplus b == ...`), `Assert` / `Print` / `PrintT` / `:>` / `@@` from TLC, `UNION`, `SUBSET` and `\X` of sets in the state, sets (literals, `\cup \cap \`, `\subseteq`, `{x \in S : P}`, `{e : x \in S}`, `Cardinality`, `SUBSET`), functions (`[x \in S \|-> e]`, `[x \in S, y \in T \|-> e]`, also with `<<a, b>> \in S` among them, non-recursive definitions `f[x \in S] == e`, `f[x]`, `[f EXCEPT ![a] = @ + 1]`, `[S -> T]`; a function over Nat, Int, STRING, `Seq(S)` or a set of more than 65536 elements, such as `[n \in Nat \|-> 2 * n][k]`, is evaluated only where it is applied, as TLC does), records (`[a \|-> 1]`, `r.a` or `r["a"]`, `[a : S]`, `!.a`), labels (`l :: e`), subexpressions of a definition named by label or position as SANY names them (`Op!lab`, `Op(a)!lab(b)`, `Op!1!2`, `Op!<<`, `Op!>>`, `Op!:`, `Op!(e)` for a quantifier's body at e, `Op!i!j` for a CASE arm), a tuple compared with a string (as in TLC, the value on the left decides: a tuple compares with the string's characters, a string asked about a tuple is an evaluation error), numbers in base 2, 8 and 16 (`\b101`, `\o17`, `\hFF`), fixed-length tuples (`<<a, b>>`, `t[1]` with a constant index, `![k][1]`, `A \X B`) |
| Actions | `x' = e`, `x' \in S`, `UNCHANGED` (of any expression), action-level `\/` `\E` `IF` `CASE`, `\A` (over a constant set or one from the state, as the conjunction over its elements in order), `[A]_v`, recursive operators that assign variables (with constant arguments or arguments from the state), guards that read an already assigned `x'`, `ENABLED` (also in Init) |
| Specs | `SPECIFICATION` (`Init /\ [][Next]_v /\ fairness`, split as TLC splits it: through conjunctions and definitions without arguments, also of an instance; its other temporal conjuncts, such as `[]P`, are not checked, but temporal properties are checked under them, as in TLC) or `INIT` / `NEXT`. `CONSTANT` values may be model values, natural numbers, strings, booleans, or sets of them, nested to any depth (as in TLC). A model value may share a type with integers (`1..4 \cup {None}`), and arithmetic on such a value is an evaluation error only when it is a model value; a variable may also hold an integer or a string, and comparing the two is an evaluation error, as in TLC. `Name <- Def` substitutes a definition (also from a module that EXTENDS the spec, such as an MC.tla) for a constant, and `<-` / `=` on a defined name replace that definition, also for `Nat`, `Int` and `Seq` (`Nat <- SmallNat`, as specs do to bound them for TLC), and `name = [Module] value` replaces a definition of that module, also of each instance of it. A cfg without SPECIFICATION, INIT and NEXT for a module without variables checks the ASSUMEs only, as in TLC. `ASSUME` is checked. `INSTANCE` (unnamed, `LOCAL`, `N(p) == INSTANCE M WITH x <- e` used as `N!Op`, also with operator parameters, inside LET, of standard modules as in `S!Len`, and with operator symbols in `WITH`). `EXTENDS RealTime` gives the variable `now`; RTnow and RTBound are treated as TLC treats them (not checked in SPECIFICATION, refused once there is a temporal property), and `Real` is the string `"Reals"`, so using it as a set is an evaluation error. `ASSUME` and `THEOREM` may name their formula (`ASSUME A == ...`). Theorems, proofs, `USE` / `HIDE` are skipped, as TLC does |
| Properties | `INVARIANT` (may use `ENABLED`). `PROPERTY` takes temporal formulas built from state predicates, `ENABLED A`, action predicates (`<<A>>_v`, `[A]_v`), `[]`, `<>`, `~>`, `/\ \/ ~ =>`, `IF`, `WF` / `SF`, and `\A` / `\E` over constant sets (also of records). As in TLC, `[]P` for a state predicate P is checked as an invariant, `[][A]_v` while exploring, and a state predicate on the initial states. Formulas TLC refuses (SANY's level rules, an action not in the form `<>[]A` or `[]<>A`, `<=>` between temporal formulas, a quantifier over a non-constant set) are refused with TLC's message and exit code |
| Fairness | `WF_v(A)` and `SF_v(A)`, on named or inline actions, optionally quantified with `\A` (also inside `\/`, `=>`, `~`, `IF` or `\E`, as an assumption of the temporal properties). Whether `<<A>>_v` is enabled is decided on A itself, as in TLC |
| State space | `CONSTRAINT`, `ACTION_CONSTRAINT`, `VIEW`, `SYMMETRY` (`TYPE` / `TYPE_CONSTRAINT` are accepted and ignored, as in TLC) |

### Limitations

- **Every variable needs `x \in S` (or `x \subseteq S`) in `TypeOK`**, with `S` finite and written in terms of
  constants only. This is where the representation (bit width) comes from. If a variable leaves its type, the checker
  stops with a type error right there (TLC only stops if `TypeOK` is listed as an invariant), and so it does when a
  `SYMMETRY` permutation moves a value out of its type (a type over part of the symmetric set). A variable missing from
  `TypeOK`, or whose `S` gives no type (such as `[D -> Int]`), gets a type inferred from Init and Next; an integer
  range that settles (a `Cardinality`, `x % 3`) stays finite, one that keeps growing becomes unbounded. When the
  types from `TypeOK` do not fit Init or Next (a module that extends another and adds a record field), every type is
  inferred and `TypeOK` is checked as an ordinary invariant. A variable may hold records of different fields and model
  values together (`[P -> Reqs \cup {NoVal}]`); its `TypeOK` is then checked on every state. A model value may also
  share a variable with tuples (of different lengths), sets, functions or booleans (`Seq(S) \cup {NoVal}`, a
  function holding model values and sets of them), and a variable may hold functions over domains of different sizes
  (`[i \in 0..n |-> e]` for different n)
- A set whose element type has at most 128 values is a bitmask; a larger one (including sets of sets) is a sorted array
  of a fixed capacity, and a sequence is an array of a fixed maximum length, so that states can be copied and
  packed without allocating. A set's capacity starts at 8 (or `Cardinality(x) <= K` in `TypeOK`, or the largest
  constant set Init assigns), and never exceeds the number of values of its element type. A sequence's starts at
  one more than a bound `Len(x) <= N` in `TypeOK` or a `CONSTRAINT` (or `UNION {[1..n -> S] : n \in 0..N}`);
  otherwise at the longest length Init and Next reach, computed until it stops growing (a length test such as
  `Len(q) < N` in an action bounds `q` there); otherwise at a length test in the spec, or 8. When a value outgrows
  its capacity, tla2rs prints `tla2rs: a set grew beyond N elements; checking again from the start with room for
  2N` (or a sequence), builds the checker again and runs it from the start; output printed before that line
  (progress, and Print in ASSUMEs) is repeated. Each rebuild costs a build (a few seconds), and a spec that stays
  within its capacities runs as fast as before. Both are at most 65535; beyond that a value is an evaluation error
- Standard modules: `Naturals`, `Integers`, `FiniteSets`, `Sequences` (with `SortSeq`; strings are sequences of
  characters for `\o`, `Len`, `Head`, `Tail`, `Append`, `SubSeq`, and, giving tuples as in TLC, `SelectSeq`,
  `SortSeq` and a tuple followed by a string in `\o`), `Bags`, `STRING`, and from `TLC` `Print`, `PrintT`, `Assert`,
  `ToString`, `TLCEval`, `Any`, `:>`, `@@`, `Permutations`, `SortSeq`. `\div` of a negative number follows the module
  the spec loads, as in TLC: the floor of the quotient with Integers, and with Naturals only, rounded toward zero
  and then down when that is negative (`(0 - 1) \div 3` is 0)
- Modules of the [CommunityModules](https://github.com/tlaplus/CommunityModules), which tla2rs provides itself
  when no module of that name is next to the spec: `Folds`, `Functions`, `FiniteSetsExt`, `SequencesExt`,
  `UndirectedGraphs` (but `Path`, `SimplePath`, `AreConnectedIn`, `ConnectedComponents` and `IsStronglyConnected`,
  which TLC 2.19 cannot evaluate either; see below), `Graphs` (but the same operators over paths and
  `IsTreeWithRoot`), `Relation`, `BagsExt`, `Bitwise`, `Combinatorics`, `Statistics`, `GraphViz`, `DyadicRationals`,
  `VectorClocks`, `Quorum`, `HTML` and `SVG` (but `NodesOfDirectedMultiGraph` and `SVGSerialize`, on whose
  definitions TLC 2.19 stops), and what TLC 2.19 evaluates of `Json` and `IOUtils`: `ToJson`, `ToJsonArray`,
  `ToJsonObject` and `zeroPadN` on constants only (they build strings by recursion, which a checker cannot do while
  it runs, so they are refused on values from the state), and `JsonSerialize`, `ndJsonSerialize` and `IOSerialize`,
  which are TRUE in the modules' definitions and write no file. Their operators that read files, run commands or read
  the environment (`JsonDeserialize`, `IOExec`, `IOEnv`, `atoi` and the like) are refused, with the reason TLC 2.19
  stops on their definitions. HTML's operators evaluate at once in the constant definitions and ASSUMEs, and compile
  quickly in Init, the actions and the invariants too: a LET definition or an argument is computed once, where it is
  first used, as TLC computes it (see CLAUDE.md, "Arguments written out at each use"). Not provided: `CSV` and `CBOR`,
  which read or write files, and `ShiViz` and `DifferentialEquations`, whose definitions TLC 2.19 cannot evaluate (see
  CLAUDE.md, "CommunityModules").
  TLC 2.19 cannot load the Java overrides in the CommunityModules jar, so it evaluates the modules' TLA+
  definitions, and tla2rs's give the same values (what CHOOSE picks, the order a fold takes elements in) and the
  same error (the position TLC gives for the CASE of `Interleave` in `SequencesExt` when none of its conditions
  holds). Strings equal to the names and strings of these modules are ordered as TLC orders them, which creates
  them when it parses the release's modules. An operator not provided is refused where it is used
- Records are ordered as TLC orders them (by their number of fields first), model values come before strings, and
  `Print` / `PrintT` break a value wider than 80 columns over lines, as TLC does
- Records are compared and printed with their fields in TLC's order (the order TLC first created the field names),
  and functions over strings print as records when every string of the domain is an identifier, and as
  `("a-b" :> 1 @@ ...)` otherwise, as in TLC. A record and the function over its field names built with `:>`, `@@`,
  `[x \in S |-> e]` or EXCEPT are one value (`[f EXCEPT !.a = e]` updates such a function too), also as elements of a set the compiler evaluates, and a variable may hold both
  (one that holds records of different fields and such a function is refused). ToString of a value from the state interns the string of every value
  of its type at compile time, as the 16-bit string ids leave room for 65536 strings and model values in all. A type
  with more values (integers whose range the type inference leaves unbounded) gets the strings of the values whose
  integers are nearest 0, at most 256 at first; when the checker meets another, tla2rs prints `tla2rs: ToString met a
  value whose string is not among the N listed for its type; checking again from the start with room for M`, builds
  it with more for that type and checks again from the start, as for capacities. ToString of a record whose fields the spec writes in another order than
  TLC's is refused: TLC prints such a record in the written order until it first compares it, so the string depends
  on when that happens
- A function over part of a type (and a bag) is an array over the whole type when the type has at most 65536 values.
  Over a larger or unbounded type (Nat, a large integer range, sets, records of those) it is the sorted list of its
  (key, value) pairs, whose capacity grows as a set's does (`Cardinality(DOMAIN f) <= K` in `TypeOK` sets where it
  starts). A tuple literal has at most 99,999 elements (each is a field of the generated
  type)
- A function over a set that cannot be enumerated (Nat, Int, STRING, `Seq(S)`) is supported applied to an argument
  (also after EXCEPT with one index per update), in `x \in DOMAIN f`, and in `ToString`, `Print` and `PrintT`, where
  TLC evaluates it without enumerating its domain (it prints `[n \in Nat |-> <expression line 5, col 26 to line 5, col
  30 of module M>]`, with the position of the body). Used as a value otherwise (assigned to a variable, compared,
  inside another value) it is refused: TLC stops with an error on most such uses
- In ASSUMEs and constant definitions, `[D -> R]`, `\X`, `[f : S]` and `SUBSET S` of more than a million elements
  are gone through without building them in `\E`, `\A` and `{x \in S : P}`, and in CHOOSE over SUBSET, in TLC's
  order, as TLC does; CHOOSE over the others and `{e : x \in S}` over any of them stop with TLC's error. Over several
  bound variables (`\E a \in S, b \in T`) TLC varies the first fastest and tla2rs the last, which shows only where
  printing or an error depends on the order
- Functions over a set from the state (`[x \in S |-> e]`, `[S -> T]`, `:>`, `@@`, `Permutations`) are functions over
  part of a type; nested modules can be instantiated; user-defined postfix operators (`^+`, `^*`, `^#`) and the
  infix operators `--`, `|-`, `??`, `!!` and `\bigcirc` are accepted; `Print` and `PrintT` write to stdout as TLC
  does, those in definitions of constant level without arguments and in ASSUMEs once, when the checker starts
- Print and PrintT in the initial predicate, an action, an invariant, a constraint or an action property print in
  TLC's order with one worker, as many times as TLC prints them: each state's lines before its checks, nothing
  past the state that stops the search, the lines TLC prints again while it rebuilds a counterexample (a liveness
  one too) and while it evaluates again after an invariant fails to evaluate, and in a function `[x \in S |-> e]`
  only where TLC evaluates e (at the argument where it is applied, at every element where it is used as a value,
  also through EXCEPT), and in what TLC evaluates while it builds its liveness graph (the steps of fair actions,
  the predicates of the properties, the particles of its tableau, the successors of a state its tableau adds a
  node to). Such specs are searched without `-batched`. Not followed: this under a VIEW or a SYMMETRY, and a few
  uses of EXCEPT; see CLAUDE.md, "Messages and printed lines"
- As SANY does, the level of `Print(out, val)` is that of val, and `PrintT(out)` is of constant level, so in a
  temporal formula a part that reads a variable only in what it prints stops TLC with exit 151, as in TLC
- `TLCGet` / `TLCSet` with one worker, with the values TLC 2.19 gives, also where it evaluates again to rebuild a
  counterexample: the registers `TLCGet(i)` / `TLCSet(i, v)` holding integers, `TLCGet("level")`, `("diameter")`,
  `("distinct")`, `("queue")` and `TLCSet("exit", TRUE)` (see CLAUDE.md, "TLCGet and TLCSet"). With them, several
  workers and temporal properties are refused
- Not supported: `RandomElement` of more than one element, `JavaTime`, `TLCGet("duration")`, the forms of `TLCGet` /
  `TLCSet` TLC 2.19 does not define, and `TLCSet("pause", ...)` (each is rejected with a reason), sets that may hold both strings and integers (a set of strings compared with a set of integers is
  supported: unequal when the sizes differ, an evaluation error otherwise, as in TLC), `Name <- [Module] Def` for a
  CONSTANT (TLC rejects it too), and `Op!@`
- Specs that SANY refuses stop with exit 150, as in TLC, for these reasons: operators of overlapping precedence next
  to each other without parentheses, also prefix and postfix ones (`a /\ b \/ c`, `a = b = c`, `[]x = 1`, `ENABLED
  x' = 1`, `a * -b`, `DOMAIN f + 1`, `UNCHANGED x'`); a name used where nothing declares or defines it before, in
  any definition, used or not (an operator of a standard module the spec does not extend, such as `Len`, `+` or
  unary minus); a declaration, definition, parameter, LET definition or bound variable named like something in
  scope at that point (also a definition of an extended or instantiated module, or of a standard module extended);
  labels that do not list the bound variables around them; LAMBDA anywhere but as an argument; wrong positional
  subexpression names, also in definitions nothing uses; an operator used with another number of arguments than it
  takes; invalid string escapes. These are reported in SANY's words with its positions: parse errors (precedence,
  string escapes, LAMBDA), the level errors of temporal formulas, and the semantic errors, all of a module in SANY's
  order with the position of the declaration a name clashes with (also in a standard module), then SANY's warnings.
  A name is in scope only after the statement that introduces it, as in SANY: an operator parameter may be named
  like a VARIABLE declared later. Not repeated: names inside `\EE` and `\AA`, and SANY's other checks (see CLAUDE.md,
  "What SANY refuses"). An operator passed where a parameter takes none, or anything but an operator of the right
  arity where it takes some, is refused, and so is a subexpression of a CONSTANT, VARIABLE or parameter (`x!1`) or of
  an operator named without its arguments (`Op!1`). A CONSTANT or VARIABLE declared twice (`VARIABLE x, x`) gets
  SANY's warning, as in TLC
- TLC's warning that a PlusCal algorithm changed since its translation is reproduced only for algorithms without
  procedures, calls, returns, macros, PlusCal options, names the translator would rename (two equal labels, say) or
  labels it would add; for the others tla2rs prints a note on stderr and no warning
- TLC's warning that an EXCEPT names an argument or field the value does not have is printed as TLC prints it (each
  text once, the first with TLC's note about `-nowarning`; for an EXCEPT applied to @, at the pair @ belongs to), also for an EXCEPT of constant level inside Init, an
  action or an invariant, which the compiler evaluates once: the checker warns each time TLC would evaluate it, and
  when it starts for the set of a `\E` that TLC splits the next-state relation through (TLC evaluates that set once).
  TLC prints it as it computes and checks each state, so a warning of a later successor comes after the error on an
  earlier one: a checker that meets a warning of Init, an action or an invariant while exploring makes tla2rs print
  `tla2rs: an EXCEPT warned while exploring; checking again from the start with the lines printed in TLC's order`,
  build the checker again to print its lines as it does for `Print` and `PrintT`, and run it from the start (output
  printed before the line is repeated); a spec that never warns keeps the faster search
- Recursion stops with an evaluation error when it has used 1 MB of a worker's stack (about 9,000 levels for a small
  body; 50,000 levels at compile time). TLC overflows its JVM stack much earlier (500 to 900 levels for small
  bodies), so a recursion between the two depths passes here where TLC reports a stack overflow
- Once a state exceeds 64 bits, the visited set holds fingerprints, so, as with TLC, there is a small chance of a
  collision (an estimate is printed at the end)
- Liveness checking keeps the whole state graph, beyond `-memlimit` in temp files, and the search over its product
  with a property's automaton keeps about 30 bytes per product node it reaches in memory (see Memory above)
- Strings are ordered as TLC orders them, by when TLC first creates them: those of the cfg and the modules (names,
  numbers as written, string literals) as TLC parses them, then those made by operations (`\o`, `Append`, `Head`,
  `Tail`, `SubSeq`, `ToString`) in the order TLC makes them, first when it starts (it evaluates every definition of
  constant level, used or not, the sets of the `\E` it splits the next-state relation through, then the ASSUMEs)
  and then while it explores. The checker's strings are numbered when
  it is built, so with one worker it notes the order it makes them in; when that differs from their numbers, tla2rs
  prints `tla2rs: strings were made in another order than they were numbered in; checking again from the start with
  them in that order`, builds the checker again with that order and runs it from the start (at most 8 times; output
  printed before the line is repeated). Not followed: with several workers TLC's order depends on scheduling, and the
  checker keeps the order it was built with; the characters of a string taken apart into a tuple (`SelectSeq`,
  `SortSeq`, a string compared with a tuple) keep the order tla2rs meets them in. A string made by a constant
  expression that tla2rs evaluates while it compiles counts where TLC evaluates it (as a value, a set, the condition
  of an IF or of an action, ...). When the strings made while exploring never go into a set, a bag or the domain of
  a function, their order shows nowhere, and the checker is built once
- A set that TLC holds as an interval (`x = 1..3`) prints as `1..3`, and an empty function built by `[x \in S |->
  e]` as `<< >>` where an empty tuple prints `<<>>`, as in TLC, where tla2rs follows how the value was built: in what
  the compiler evaluates (ASSUMEs, constants, also inside tuples, records, functions and sets), and in the state: in
  variables, in the fields of records and tuples, in the elements of sequences, sets and functions over integers,
  model values or strings (also those built by `:>` and `@@`), and in what is taken out of them or of a constant set.
  Elsewhere (a variable whose forms need more than the 128 bits a state keeps for one variable, a record of variants,
  an IF that prints under a bound variable, the operators of the CommunityModules) it prints as `{1, 2, 3}` and
  `<<>>` (see CLAUDE.md, "State graphs"). The comparison with TLC reads intervals as printed
- A liveness counterexample is the one TLC prints with `-fp 0` (TLC's depends on its fingerprints, whose polynomial
  it otherwise picks at random), also for properties TLC checks with its tableau (such as `~>` and `<>P`) and under
  `VIEW` or `SYMMETRY` (a model value is fingerprinted by the number TLC gives its name, under `SYMMETRY` a state by
  its smallest permutation, and under `VIEW` by its view, as TLC does). Otherwise it is a valid lasso of tla2rs's
  own, which TLC checks (`-lassocheck`); the checker says why on stderr. Such a lasso is replayed on actual states,
  as TLC rebuilds a behavior; when a value the view leaves out only grows, the lasso returns to its first state of
  the cycle under the view only, and the check folds states by the same view
- Under `VIEW` or `SYMMETRY`, whether a temporal property holds is decided as TLC decides it: on TLC's liveness
  graph, not on the graph folded by the view or the permutations. TLC keeps each successor as generated (a step that
  changes only what the view leaves out is a step of its action, not stuttering), checks its tableau on the
  successor itself, and keeps only the first step into a state it has already expanded, so its verdict can differ
  from what the spec's behaviors give (`tests/tlc/LiveFold-Twice` has a fair behavior that violates the property,
  and TLC reports no error). The checker builds that graph in memory beside the state graph
- With `VIEW` and `SYMMETRY` together, a state is reduced as TLC reduces it: the smallest of its permutations (values
  compared as TLC compares them, variables in the order TLC prints them), and then the view of that state. This
  compares whole permuted states, which costs more than comparing views did

## Cross-checking against TLC

`scripts/crosscheck.sh` runs the same configuration through TLC (`-workers 1`) and tla2rs and compares the verdict,
generated and distinct state counts, the states left on TLC's queue when it stops at an error, the counterexample, exit code, the messages and printed lines, and the state
graph: the set of states reached
and the set of transitions between them, from TLC's `-dump dot` and tla2rs's `-dumpgraph`, each reduced to a SHA-256
hash (each state with its variables in the order TLC prints them, which the checker follows: the order of SANY's
hash table of the root module's names, replayed by tla2rs). A safety counterexample is
compared step by step: each state and the action that led to it, as TLC names it (with one worker TLC's is the same
on every run). So is a liveness counterexample, as TLC runs with `-fp 0`; where the checker prints a lasso of its own
instead (see above) and it differs from TLC's, TLC is run on the spec `-lassocheck` writes, and must confirm that
tla2rs's lasso is a fair behavior of the spec that violates the properties. The messages are TLC's error and warning lines and what the spec prints with Print and PrintT, in order,
without the progress lines and with the parts that are TLC's internals left out (the stack of nested expressions
TLC was evaluating, Java class names); where tla2rs cannot print all of TLC's text, the cfg can say why, and then
only the error lines are compared (no configuration needs this now). Where the graph
cannot be compared as a whole (TLC stops before ending its graph file when it stops in
the initial states; a successor tla2rs cannot represent), less is compared, and `all.sh` says which rule applied;
CLAUDE.md lists them. A cfg line `\* crosscheck: args -continue` passes those of TLC's options to both TLC and tla2rs;
with `-dump` the file it names is compared instead of the state graph, through `tla2rs --dump FILE` (see
`src/options.rs`). `scripts/all.sh` does this for every
configuration in `examples/` and `tests/tlc/`, passing extra arguments such as `-batched` on to each run. Point
`TLA_TOOLS` at `tla2tools.jar` (default `~/.tla/tla2tools.jar`). A spec that names a module of the CommunityModules
in EXTENDS or INSTANCE needs, for TLC, the release `scripts/crosscheck.sh` pins (202611060952, sha256
`a3b27c40f1fb5085f30c6ead37e918457f8cfc62c1e50a1dc668ef592ad2b5fb`), at `COMMUNITY_MODULES` (default
`~/.tla/CommunityModules-deps.jar`):

```sh
curl -L -o ~/.tla/CommunityModules-deps.jar \
  https://github.com/tlaplus/CommunityModules/releases/download/202611060952/CommunityModules-deps-202611060952.jar
shasum -a 256 ~/.tla/CommunityModules-deps.jar
```

TLC 2.19 cannot load that jar's Java overrides (the releases tried, from 2023-12 to 2026-11, need a class TLC 2.19 does not have, and
TLC stops with `NoClassDefFoundError: tlc2/value/impl/KSubsetValue` on any spec), so `crosscheck.sh` extracts the
jar's modules into `target/community/` and gives TLC only those; the jar's hash is part of the key of such a spec's
expected file. Comparing against `tests/expected/` does not need the jar. `all.sh` runs four configurations at a time
(`JOBS=N` to change). TLC's result for each configuration is committed in `tests/expected/`: the verdict, the
state counts, the length and a hash of the counterexample, the exit code, the hashes of the state graph and of the
messages, with a hash of the jar, the cfg, the arguments, the modules the spec reads, `src/graph.rs`, `src/trace.rs`
and `src/messages.rs`. Times and the random seed vary between TLC runs and are not
recorded, so the files are the same for every TLC run. `crosscheck.sh` and `all.sh` only compare against these
files and never run TLC on the configurations themselves (only on a lasso check whose confirmation is not yet cached in `target/crosscheck/lasso`); a missing or stale file fails
the check. `scripts/expected.sh [cfg ...]` is what
runs TLC: it writes missing and stale files and leaves the others alone, so a second run changes nothing.
`expected.sh -check` reruns TLC and reports any file that differs, without writing; `-force` rewrites them all.
Built checkers are kept in `target/crosscheck/build` under a hash of the generated code and the rustc version
(`CROSSCHECK_NO_CACHE=1` builds them from scratch).

```
$ scripts/all.sh
ok    examples/DieHard.cfg
ok    examples/Peterson-Live.cfg
ok    examples/TwoPhase.cfg
...
ok    tests/tlc/AssumeFalse.cfg  (graph not compared: TLC stopped before ending it)
...
```

### A public corpus

The configurations above test the forms someone thought of. `scripts/corpus.sh` also cross-checks tla2rs, in the
same way, against the models of the tlaplus/Examples repository (https://github.com/tlaplus/Examples), at the commit
pinned in `tests/corpus.txt`. It fetches the corpus into `target/corpus/<commit>/` and only lets TLC and tla2rs read
it; nothing of the corpus is copied into this repository except TLC's results for it (`tests/expected/corpus/`,
written by `scripts/expected.sh -corpus`). `tests/corpus.txt` lists every model of the corpus's manifests: those
selected (the exhaustive searches that TLC 2.19 finishes, with `tla2tools.jar` and the CommunityModules' modules, in
60 seconds or less with one worker) and, for each of the others, why it is skipped. A selected model that tla2rs does
not match yet is listed as a gap, with the reason measured. The run is separate from `all.sh`, which keeps its cost.
Of the 106 selected models, all 106 match TLC (7 of them on everything but the generated count, which TLC counts once
per `\/` branch).
23 more models, on which TLC takes longer than the selection allows (up to hours), are listed as `large`: `scripts/corpus.sh -large` checks
them against TLC's results kept the same way, except for the state graph, which is too big to compare (see "Large
models" in CLAUDE.md). `scripts/corpus.sh -only RE` checks only the models whose cfg path matches RE.

```sh
scripts/corpus.sh                       # the 106 selected models
scripts/corpus.sh -large                # the 23 large ones (tla2rs: up to 77 minutes and 19 GB on one)
scripts/corpus.sh -large -only bosco    # only those whose cfg path matches bosco
```

| Example | What it is |
|---|---|
| `DieHard` | The water jug puzzle. The counterexample to `NotSolved` is the answer |
| `Peterson` | Mutual exclusion. `-Live` shows freedom from starvation under weak fairness; `-Unfair` shows it fails when only one process is fair |
| `TwoPhase` | Two-phase commit (5 RMs). Messages are a set of records |
| `Features` | A small spec that exercises the supported subset (`SeenOK` is violated) |
| `Liveness` | `<>`, `[]<>`, `<>[]`, `~>`, with stuttering and cycling counterexamples |

### Speed against TLC

`scripts/bench.sh` runs every configuration in `examples/` and `tests/tlc/` (with `-corpus`, the selected models
of the corpus) through TLC and tla2rs, and measures the wall time and peak memory of TLC with one worker and of
tla2rs's three steps apart: generating the Rust code, building it from scratch, and running the checker alone with
one worker (`-auto` adds TLC's `-workers auto` and the checker's default workers). It writes one row per
configuration to `target/bench/results.tsv`, and lists in `target/bench/summary.txt`, by ratio, the configurations
where tla2rs is slower than TLC, for the check alone and in total with the build. A second run skips the rows
already measured, so an interrupted run resumes (`-force` measures again). It measures one configuration at a time;
`JOBS=N` runs N at once, with less accurate times.

```sh
scripts/bench.sh                  # examples/ and tests/tlc/
scripts/bench.sh -corpus          # the corpus (-norun adds the models too costly for corpus.sh)
scripts/bench.sh -corpus MCbtree  # only the models whose cfg path contains MCbtree
```

## Roadmap

- Sequences (`Sequences`) and sets of sets
- Take constants as run-time arguments, so changing the configuration does not need a rebuild

## License notices

Parts of tla2rs are derived from TLC, from the TLA+ Examples and from the CommunityModules, all under the MIT
License; see
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
