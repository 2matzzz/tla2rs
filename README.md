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
- `-memlimit MB` caps how much of the BFS queue stays in memory (default 256 MB); the rest spills to a temp file (`-tmpdir`)
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
4. **Code generation** (`codegen.rs`): constant subexpressions are evaluated at compile time and become literals.
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
   no state where it is enabled, narrowing the component otherwise). Counterexamples are lassos printed as TLC does

### Memory

When only invariants are checked, states themselves are not kept. The checker holds just

- the visited fingerprints, each paired with the fingerprint of the state it was first reached from (16 bytes per
  state, 8 with `-notrace`)
- the queues for the current and next level (anything beyond `-memlimit` spills to a temp file and is read back in
  chunks)

When a violation is found, the checker walks the fingerprints back to an initial state and rebuilds the counterexample
by replaying `next` from there. Memory stays within "fingerprint table plus a capped queue", whatever the state width
or model size.

Checking temporal properties needs the whole state graph for the SCC search, so in that case everything is kept in
memory.

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
  stops with a type error right there (TLC only stops if `TypeOK` is listed as an invariant). A variable missing from
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
- Records are ordered as TLC orders them (by their number of fields first), model values come before strings, and
  `Print` / `PrintT` break a value wider than 80 columns over lines, as TLC does
- Records are compared and printed with their fields in TLC's order (the order TLC first created the field names),
  and functions over strings print as records. ToString of a value from the state interns the string of every value
  of its type at compile time, so the type must have at most as many values as the 16-bit string ids leave room for
  (65536 strings and model values in all). ToString of a record whose fields the spec writes in another order than
  TLC's is refused: TLC prints such a record in the written order until it first compares it, so the string depends
  on when that happens
- A function over part of a type (and a bag) is an array over the whole type when the type has at most 65536 values.
  Over a larger or unbounded type (Nat, a large integer range, sets, records of those) it is the sorted list of its
  (key, value) pairs, whose capacity grows as a set's does (`Cardinality(DOMAIN f) <= K` in `TypeOK` sets where it
  starts). A tuple literal has at most 99,999 elements (each is a field of the generated
  type)
- A function over a set that cannot be enumerated (Nat, Int, STRING, `Seq(S)`) is supported only applied to an argument
  (also after EXCEPT with one index per update) or in `x \in DOMAIN f`, where TLC evaluates it without enumerating its
  domain. Used as a value (assigned to a variable, compared, printed, passed to `ToString`) it is refused: TLC stops
  with an error on most such uses, and prints its source text for `ToString`
- Functions over a set from the state (`[x \in S |-> e]`, `[S -> T]`, `:>`, `@@`, `Permutations`) are functions over
  part of a type; nested modules can be instantiated; user-defined postfix operators (`^+`, `^*`, `^#`) and the
  infix operators `--`, `|-`, `??`, `!!` and `\bigcirc` are accepted; `Print` and `PrintT` write to stdout as TLC
  does, those in definitions of constant level without arguments and in ASSUMEs once, when the checker starts
- Print and PrintT in the initial predicate, an action or an invariant print in TLC's order with one worker: each
  state's lines before its checks, nothing past the state that stops the search, and the lines TLC prints again
  while it rebuilds a counterexample (see CLAUDE.md, "Messages and printed lines"). Such specs are searched without
  `-batched`
- Not supported: `RandomElement` of more than one element, `JavaTime`, `TLCGet` / `TLCSet` (each is rejected with a
  reason), sets that may hold both strings and integers, `Name <- [Module] Def` for a CONSTANT (TLC rejects it too),
  `Op!@`, and a recursive operator that assigns variables called in Init with arguments that are not constant. `\A`
  over a set from the state whose body assigns a variable for some elements only needs the set's element type to have
  at most 16 values
- Specs that SANY refuses stop with exit 150, as in TLC, for these reasons: operators of overlapping precedence next
  to each other without parentheses, also prefix and postfix ones (`a /\ b \/ c`, `a = b = c`, `[]x = 1`, `ENABLED
  x' = 1`, `a * -b`, `DOMAIN f + 1`, `UNCHANGED x'`); a name used where nothing declares or defines it before, in
  any definition, used or not (an operator of a standard module the spec does not extend, such as `Len`, `+` or
  unary minus); a declaration, definition, parameter, LET definition or bound variable named like something in
  scope at that point (also a definition of an extended or instantiated module, or of a standard module extended);
  labels that do not list the bound variables around them; LAMBDA anywhere but as an argument; wrong positional
  subexpression names, also in definitions nothing uses; invalid string escapes. Parse errors (precedence, string
  escapes, LAMBDA) and the level errors of temporal formulas are reported in SANY's words with its positions; for
  the other checks the wording and positions differ from SANY's. A name is in scope only after the
  statement that introduces it, as in SANY: an operator parameter may be named like a VARIABLE declared later. Not
  repeated: names inside `\E x : P`, `CHOOSE x : P` without a set, `\EE` and `\AA`; positional names of LET
  definitions; and SANY's other checks (see CLAUDE.md, "What SANY refuses")
- TLC's warning that a PlusCal algorithm changed since its translation is reproduced only for algorithms without
  procedures, calls, returns, macros, PlusCal options, names the translator would rename (two equal labels, say) or
  labels it would add; for the others tla2rs prints a note on stderr and no warning
- Recursion stops with an evaluation error when it has used 1 MB of a worker's stack (about 9,000 levels for a small
  body; 50,000 levels at compile time). TLC overflows its JVM stack much earlier (500 to 900 levels for small
  bodies), so a recursion between the two depths passes here where TLC reports a stack overflow
- Once a state exceeds 64 bits, the visited set holds fingerprints, so, as with TLC, there is a small chance of a
  collision (an estimate is printed at the end)
- Liveness checking keeps the whole state graph in memory (about 40 bytes per edge), and the search over its product
  with a property's automaton uses hash maps sized by the reachable product. For invariants only, see Memory above
- Strings are ordered as TLC orders them (by when TLC first creates them) for strings that appear in the spec, its
  modules, or the cfg. Strings created during the search (by `\o`, `ToString`, ...) can be ordered differently: TLC's
  order for those depends on its evaluation order and, with several workers, on scheduling
- A liveness counterexample is a valid lasso, but not always the one TLC prints. TLC's own differs from run to run (it
  depends on a fingerprint polynomial TLC picks at random), so cross-checks do not compare it with TLC's; TLC checks
  it instead (`-lassocheck`)
- With `VIEW` and `SYMMETRY` together, the distinct count can be lower than TLC's. TLC sometimes keeps states with
  identical views as separate states (its choice of representative depends on the state itself), while tla2rs folds
  by orbits of the view. With only one of the two, counts match TLC exactly

## Cross-checking against TLC

`scripts/crosscheck.sh` runs the same configuration through TLC (`-workers 1`) and tla2rs and compares the verdict,
generated and distinct state counts, the states left on TLC's queue when it stops at an error, the counterexample, exit code, the messages and printed lines, and the state
graph: the set of states reached
and the set of transitions between them, from TLC's `-dump dot` and tla2rs's `-dumpgraph`, each reduced to a SHA-256
hash (with the variables of each state sorted, since TLC's order comes from a hash table). A safety counterexample is
compared step by step: each state and the action that led to it, as TLC names it (with one worker TLC's is the same
on every run). A liveness counterexample depends on TLC's random fingerprint polynomial, so instead TLC is run on the
spec `-lassocheck` writes, and must confirm that tla2rs's lasso is a fair behavior of the spec that violates the
properties. The messages are TLC's error and warning lines and what the spec prints with Print and PrintT, in order,
without the progress lines and with the parts that are TLC's internals left out (the stack of nested expressions
TLC was evaluating, Java class names); where tla2rs cannot print all of TLC's text (a position it does not keep,
a message TLC prints by an internal rule), the cfg says why and only the error lines are compared. Where the graph
cannot be compared as a whole (TLC stops before ending its graph file when it stops in
the initial states; a successor tla2rs cannot represent), less is compared, and `all.sh` says which rule applied;
CLAUDE.md lists them. `scripts/all.sh` does this for every
configuration in `examples/` and `tests/tlc/`, passing extra arguments such as `-batched` on to each run. Point
`TLA_TOOLS` at `tla2tools.jar` (default `~/.tla/tla2tools.jar`). `all.sh` runs four configurations at a time
(`JOBS=N` to change). TLC's result for each configuration is committed in `tests/expected/`: the verdict, the
state counts, the length and a hash of the counterexample, the exit code, the hashes of the state graph and of the
messages, with a hash of the jar, the cfg, the arguments, the modules the spec reads, `src/graph.rs`, `src/trace.rs`
and `src/messages.rs`. Times, the fingerprint seed and the shape of a liveness counterexample vary between TLC runs and are not
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
selected (the exhaustive searches that TLC 2.19 finishes, with only `tla2tools.jar`, in 60 seconds or less with one
worker) and, for each of the others, why it is skipped. A selected model that tla2rs does not match yet is listed as
a gap, with the reason measured. The run is separate from `all.sh`, which keeps its cost. Of the 98 selected models,
95 match TLC (6 of them on everything but the generated count, which TLC counts once per `\/` branch); the 3 gaps,
none of them run for now, and their reasons are in `tests/corpus.txt` and CLAUDE.md.

| Example | What it is |
|---|---|
| `DieHard` | The water jug puzzle. The counterexample to `NotSolved` is the answer |
| `Peterson` | Mutual exclusion. `-Live` shows freedom from starvation under weak fairness; `-Unfair` shows it fails when only one process is fair |
| `TwoPhase` | Two-phase commit (5 RMs). Messages are a set of records |
| `Features` | A small spec that exercises the supported subset (`SeenOK` is violated) |
| `Liveness` | `<>`, `[]<>`, `<>[]`, `~>`, with stuttering and cycling counterexamples |

## Roadmap

- Sequences (`Sequences`) and sets of sets
- Take constants as run-time arguments, so changing the configuration does not need a rebuild

## License notices

Parts of tla2rs are derived from TLC and from the TLA+ Examples, both under the MIT License; see
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
