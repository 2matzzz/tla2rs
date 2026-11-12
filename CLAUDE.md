# CLAUDE.md

tla2rs is a compiler that takes a TLA+ spec and a TLC `.cfg` and generates a Rust model checker dedicated to that spec.
It has no crate dependencies.

## Common commands

- `cargo build --release` builds the compiler (`target/release/tla2rs`)
- `target/release/tla2rs Spec.tla [-config X.cfg] [-deadlock] [-workers N] [-memlimit MB] [-notrace] [-setcap N] [-seqcap N] [-fp128] [-metal] [-batched] [-dumpgraph FILE] [-lassocheck DIR] [--emit-only] [-o DIR]`
  - `-setcap` / `-seqcap` only set where the capacities of sets held as arrays and of sequences start; a value that
    outgrows one makes tla2rs build the checker again with twice the room (see "Capacities")
  - The generated crate goes to `<spec dir>/.tla2rs/<cfg name>/` by default; it is built with
    `cargo build --release --offline` and then run
  - `-workers`, `-memlimit`, `-notrace`, `-tmpdir`, `-metal`, `-batched`, `-dumpgraph`, `-lassocheck` and
    `-deadlock` are passed on to the generated checker, which also accepts them directly
- `target/release/tla2rs --graph FILE` reduces a state graph (TLC's `-dump dot FILE` or a checker's `-dumpgraph
  FILE`) to `states N <sha256>` and `edges M <sha256>`; `--graph-text FILE` prints the canonical form itself, for
  diffing two graphs (see "State graphs")
- `target/release/tla2rs --trace FILE` reduces the counterexample in an output of TLC or of a checker to `trace N
  <sha256>`; `--trace-text FILE` prints its canonical form (see "Counterexamples")
- `target/release/tla2rs --messages FILE` reduces the messages and printed lines in such an output to `messages N
  <sha256>` and its error lines to `errors M <sha256>`; `--messages-text FILE` prints the canonical form (see
  "Messages and printed lines")
- `target/release/tla2rs --pcal-text FILE` prints the text TLC hashes for the PlusCal algorithm in FILE and its
  CRC-32 (see "PlusCal checksums")
- `scripts/all.sh` cross-checks every configuration in `examples/` and `tests/tlc/` against TLC (all 680 currently
  pass). Run it after every change, and also as `scripts/all.sh -batched` and `scripts/all.sh -metal` when you touch
  either search path (extra arguments are passed on to every run)
- `scripts/crosscheck.sh Spec.tla [X.cfg] [-deadlock]` cross-checks one configuration. Both TLC and tla2rs run with
  one worker, and it compares the verdict, generated and distinct state counts, the states left on
  TLC's queue (see "The states left on queue"), the counterexample (its states and
  the action of each step; see "Counterexamples"), exit code, the messages and printed lines (see "Messages and
  printed lines"), and the state graph (the set of states and the set of transitions; see "State graphs"). A liveness counterexample is instead checked by TLC (it runs TLC on the
  `-lassocheck` output). If TLC produces no verdict, the check fails. `all.sh` prints, after `ok`, the rule that
  narrowed a comparison, if any
- TLC's summary for each configuration (verdict, counts, the length and hash of its counterexample, exit code, the
  hashes of its state graph and of its messages, and a key hashing the jar, cfg, arguments, the modules the spec
  reads, `src/graph.rs`, `src/trace.rs` and `src/messages.rs`) is committed in
  `tests/expected/`. `crosscheck.sh` and `all.sh` compare
  against these files only (they run TLC only on a lasso check not yet confirmed, cached in `target/crosscheck/lasso` by a hash of the check, its modules and the jar) and fail on a missing or stale one. After adding or changing a test, run
  `scripts/expected.sh` (it runs TLC for missing and stale files only) and commit the files with the test.
  `expected.sh -check` reruns TLC and reports differences without writing. Built checkers are cached in
  `target/crosscheck/build` (key: generated code and rustc version; `CROSSCHECK_NO_CACHE=1` rebuilds); `JOBS=N`
  sets how many configurations `all.sh` and `expected.sh` run at once. `CROSSCHECK_GRAPH_DIR=DIR` keeps the graphs
  of a run as `DIR/<cfg>.tlc.dot` (with `expected.sh`) and `DIR/<cfg>.rs.dot`, and the outputs as `DIR/<cfg>.tlc.out`
  and `DIR/<cfg>.rs.out`
- The TLC jar comes from `TLA_TOOLS` (default `~/.tla/tla2tools.jar`). For a spec that names a module of the
  CommunityModules in EXTENDS or INSTANCE (without a module of that name next to it), TLC also needs the release
  `crosscheck.sh` pins (`cm_version`, `cm_sha256`), from `COMMUNITY_MODULES` (default
  `~/.tla/CommunityModules-deps.jar`); see "CommunityModules"
- `scripts/corpus.sh` cross-checks the models selected from a public corpus, the tlaplus/Examples repository
  at the commit pinned in `tests/corpus.txt`, against TLC's results in `tests/expected/corpus/` (see "The
  corpus"). It is separate from `all.sh`, which it does not slow down. `scripts/expected.sh -corpus` writes
  those results; `JOBS` defaults to 2 for both

## Layout

| File | Role |
|---|---|
| `src/lexer.rs` `src/parser.rs` | Lexing and parsing. `/\` and `\/` bullet lists are delimited by column. Also SANY's precedence checks and string escapes (see "What SANY refuses"); an error marked with `lexer::SANY` makes the compiler stop with exit 150. The statements of a module are kept in the order written (`Module::units`). The positions TLC names actions by are kept in POS labels (`ast::POS`, see "Counterexamples") |
| `src/sany.rs` | SANY's checks of names (see "What SANY refuses"): what is in scope at each statement, what each module exports, labels and LAMBDA. Run on each module read from a file once the modules it extends and instantiates are loaded (`compile::load_parsed`), and on the modules nested in it |
| `src/cfg.rs` | `.cfg` files (SPECIFICATION / INIT / NEXT / CONSTANT, including `<-` / INVARIANT / PROPERTY / CONSTRAINT / ACTION_CONSTRAINT / VIEW / SYMMETRY / CHECK_DEADLOCK; TYPE / TYPE_CONSTRAINT are ignored as in TLC) |
| `src/expand.rs` | Inlines every operator definition. Bound variables are renamed, and each EXCEPT's `@` gets a unique name too. Call sites are kept as `Expr::Label`. A subexpression named by label or position (`Op!lab`, `Op!1`, `Op!(e)`) is found in the definition as written and expanded as a definition with the bound variables and label parameters on the way as extra parameters (`subexpr`). Operator parameters are bound to the operator (or LAMBDA) passed, with its environment. A RECURSIVE operator called again inside its own expansion becomes `Expr::RecCall`, evaluated at compile time or compiled into a Rust function (`Gen::rec_fn`, which takes the variables it reads, primed or not, as arguments); it is expanded once per combination of operator arguments |
| `src/value.rs` | Compile-time values and constant evaluation (set order follows TLC: smaller sets first) |
| `src/types.rs` | Finite types `Ty`. A set whose element type has at most 128 values is a `u128` bitmask; otherwise it is an `SSet` (sorted fixed-size array). `Opt` is an optional field of a record whose variants have different fields. A value that is a record or a model value (`[op : S] \cup {NoVal}`) is a record type whose fields are all optional, with the model values in a field of its own (`ATOM_FIELD`); a type invariant giving such a type is checked on every state, since packing does not check which records it lists. A value that is a model value or a value of another kind (a sequence, tuple, set, function, bag or boolean: `Seq(S) \cup {NoVal}`, `SUBSET P \cup P`) is such a record type too, with that value in a field of its own (`VAL_FIELD`, named to sort before `ATOM_FIELD`, so model values come first as in TLC); an operation that takes the value apart (application, DOMAIN, iteration, set operations, Cardinality, the sequence operators) takes it out of that field (`Gen::gen_val`), and fails on a model value. A record type with optional fields of at most 4096 values is numbered in TLC's order of records (`tlc_perm`: the number of fields first), so sets of such records print, CHOOSE and enumerate as in TLC. A record's fields are kept in TLC's order of names (`field_cmp`: the order TLC first creates each name, from `compile::tlc_string_ranks`), which is how TLC compares and prints records. A tuple is a `Rec` with fields `#00001`, `#00002`, ... (`tuple_ty`); a record of more than 12 fields is held as nested groups of 12 (`rec_build`, `rec_field`), since Rust tuples implement `Eq`/`Hash`/`Ord` only up to 12 elements. `IntAtom` holds integers and atoms (model values, also strings) in one `i64` (atom a is `i64::MIN + a`). `Seq` is a sequence (`Sq`, at most QCAP elements; `seq_cap` derives QCAP, from `src/seqlen.rs` when no bound is written). An `SSet` holds at most SCAP elements, and never more than its element type has values (`set_cap`); both capacities grow at run time (see "Capacities"). `Bag` is a bag, a count per element (packed as a function to 0..BIG). `PFun` is a function over part of a type (an optional value per element); functions over different domains (other than 1..n, which are sequences) join into one. Over a domain type of more than `DENSE_MAX` (65536) values, or one that is not enumerable, both are sparse (`is_sparse_fun`): an `SSet` of <<key, value>> tuples (`fun_pairs`), which sorts by key, so lookups are binary searches and packing, SYMMETRY and equality are those of sparse sets. `BIG` is an unbounded integer |
| `src/codegen.rs` | Rust generation. Actions are continuation-passing, threading "the remaining conjuncts". The next-state relation is first split into actions as TLC splits it, which names the successors in traces (`gen_split`). As in TLC, `\/` and `\E` branch while some variable is still unassigned. `\A` over a set from the state walks the elements at run time (`gen_forall`), and a recursive operator that assigns variables, called with arguments from the state, becomes a Rust function returning the states its body builds (`gen_rec_action`) |
| `src/compile.rs` | The overall pipeline. Types come from `x \in S` in TypeDecl / TypeOK; for variables without one (or whose S gives no type, such as `[D -> Int]`) they are inferred from Init/Next (`infer_types`; an integer range that settles within a few rounds stays finite, one that keeps growing is widened to unbounded). When the types from TypeOK fail in Init or Next (a module that extends another and adds a record field its type invariant lacks), the spec is compiled again with every type inferred (`INFER_ALL`). ASSUMEs are evaluated here. `instantiate` turns each definition of an INSTANCE'd module into a hidden definition that takes the module's constants and variables as leading parameters, so expansion substitutes them without capture (a call site's arguments are only a trace: whether it is constant is decided by its body, `Gen::is_const`). `Nat <- D`, `Int <- D` and `Seq <- D` in the cfg define those operators of the standard modules, as TLC replaces them |
| `src/community.rs` | The modules of the CommunityModules tla2rs provides (see "CommunityModules"): TLA+ source written for tla2rs, loaded by `compile::find_module` when no module of that name is next to the spec |
| `src/std_modules.rs` | The identifiers and strings of TLC's standard modules in TLC's reading order (generated from tla2tools.jar), for ordering strings as TLC does |
| `src/seqlen.rs` | Without a written length bound, runs Init and Next over sequence lengths (with `Len(q) < k` tests in a conjunction as bounds) until the variables' lengths settle, giving QCAP |
| `src/live.rs` `src/ltl.rs` | Liveness at compile time: properties become formulas over atoms (state predicates, ENABLED, action predicates), the negation becomes a Büchi automaton by tableau (`ltl.rs`), and fairness becomes per-condition ENABLED / step functions |
| `src/graph.rs` | `--graph`: reduces a state graph file to its canonical form and hashes it (SHA-256 written out, as there are no crate dependencies) |
| `src/trace.rs` | `--trace`: reduces the counterexample in an output of TLC or of a checker to its canonical form and hashes it |
| `src/messages.rs` | `--messages`: reduces the messages and printed lines in an output of TLC or of a checker to their canonical form and hashes it, and its error lines (see "Messages and printed lines") |
| `src/pcal.rs` | TLC's check of the checksums a PlusCal translator wrote: the warnings for the root module and the modules it extends, and the algorithm's syntax tree as TLC's translator prints it (see "PlusCal checksums") |
| `src/lasso.rs` | The spec's parts written back as TLA+ (`tla`) for the module `-lassocheck` writes (see "Counterexamples") |
| `src/ppr.rs` | TLC's pretty printer for values (`ppr`, ported from `tlc2.pprint` and checked against TLC's on 25,000 random values): used by the compiler for what Print and PrintT print when TLC starts, and pasted into every generated checker, which prints states and printed values with it |
| `src/runtime.rs` | The runtime pasted into generated code: level-by-level parallel BFS, bit-packed states, 64-bit fingerprints (with VIEW / SYMMETRY, of the canonical key), and liveness (per state and edge, which property atoms and fairness conditions hold; then an SCC search in the product with each property's automaton, with WF / SF as conditions on components; counterexamples are lassos). Also the `-dumpgraph` output |

### Memory use (`runtime.rs`)

There are two paths, depending on what is checked.

| | What is kept | Per state |
|---|---|---|
| Invariants only (`run_safety`) | The fingerprint and the fingerprint of the state it was first reached from, plus the states of the current and next level | 16 bytes (8 with `-notrace`) |
| With temporal properties (`run_liveness`) | The whole state graph (states, parents, edges with their atom and fairness bits) | State width + a few dozen bytes, plus hash maps over the product with each property's automaton during the search |

The safety path never keeps states. A counterexample is rebuilt by walking fingerprints back to an initial state and
replaying `next` from there (`fp_chain` → `replay`). Liveness needs the whole graph for the SCC search, so it is kept in
memory.

The parts of a level beyond `-memlimit` spill to a temp file. The file is unlinked as soon as it is opened, so nothing is
left behind even when the checker is killed. A failed read of the spilled queue is a fatal error: skipping it could turn
an incomplete search into "no error".

### Capacities

A set held as an array (`SSet`, also the (key, value) pairs of a sparse function or bag) and a sequence (`Sq`) are
fixed-size arrays, so that states stay `Copy` and pack at known widths; TLC has no such bound. Where they start:

| | Starts at |
|---|---|
| SCAP (sets) | `-setcap N`, else 8; raised to `Cardinality(x) <= K` in TypeOK and to the size of the largest constant set Init assigns to a variable of such a set type (`set_cap_start`). A set type never gets more than its element type has values (`types::set_cap`, emitted as `set_cap(n)` in the checker) |
| QCAP (sequences) | `-seqcap N` (at least the longest tuple literal), else one more than `Len(x) <= N` in TypeOK or a CONSTRAINT, else the longest length Init and Next reach when they settle (`seqlen.rs`), else the longest tuple literal if nothing grows sequences, else a length test anywhere in the spec plus 2, else 8 (`seq_cap`) |

When a value outgrows its capacity (`capacity_exceeded` in the runtime, from `SSet::insert`, `SSet::put` and
`seq_too_long`) and tla2rs runs the checker, the checker exits at once with 70 (sets) or 71 (sequences); tla2rs
(`main.rs`) prints `tla2rs: a set grew beyond N elements; checking again from the start with room for 2N`, compiles
with that capacity doubled, builds (the build cache applies) and runs again from the start. `TLA2RS_GROW` tells the
checker which kinds may still grow (both stop at 65535, `types::MAX_CAP`); run directly, or at the maximum, the
checker reports an evaluation error as before. Output before the line is repeated by the next run, so
`crosscheck.sh` compares only what follows the last such line, and says how many rebuilds there were. A spec that
stays within its capacities builds and runs exactly as before.

Measured on the models that used to need `-setcap` / `-seqcap` (rebuilds, and the capacity they end with):

| Model | Needed | Now |
|---|---|---|
| `MCCheckpointCoordinationFailure`, `ReadersWriters` `MC`, `AllocatorImplementation`, `AllocatorRefinement`, `SchedulingAllocator` | `-seqcap` 8, 6, 6, 6, 3 | No rebuild: sequences start at 8 |
| `MCDisruptor_MPMC`, `-liveliness`, `MCDisruptor_SPMC` | `-seqcap 10` | 1 rebuild (16) |
| `SlidingPuzzles` | `-setcap 64` | No rebuild: Init assigns a constant set of 10 |
| `SimplifiedFastPaxos` `Paxos` | `-setcap 1024` | 5 rebuilds (256; its message set holds more than 128): about 30 s in all, but the search takes 0.5 s instead of 2.1 s with 1024 |
| `tests/tlc/SubBags` | `-setcap 32` | 1 rebuild (16) |
| `tests/tlc/LongSeq` | `-seqcap 140 -setcap 140` | Sequences settle at 140 (`seqlen.rs`); `DOMAIN q` takes 5 rebuilds (sets of `1..140`, capped at 140) |
| `tests/tlc/SeqCap` | `-seqcap 3` | No rebuild: lengths settle |

Not done, measured: starting SCAP at |T| for `x \subseteq T` in TypeOK with T constant would have raised it for 15
configurations of `tests/tlc/` and 2 corpus models that run at 8 (to 36 to 5002; `RecMix` 5002, `SetsOfSets` 512)
and widened every set held as an array there, and for `SlidingPuzzles` to 2^20. The bounds a spec implies by its logic (a queue that holds
each process at most twice, the messages a protocol can send) are not derived: the Init/Next analysis of `seqlen.rs`
covers sequence lengths only.

### The states left on queue

When TLC stops at an error it reports `N states left on queue`. Measured on TLC 2.19 with one worker
(`tests/tlc/QueueLeft*`, and every configuration and corpus model since): N is the states of the
level being expanded that come after the one whose expansion stopped, plus the states queued for
the next level so far, without the state that stopped the search. A new state that violates an
invariant is not queued, and neither is a successor that violates an action property (it is added
to the visited states first). The three searches count the same (`SChunk::expanded`,
`Collected::expanded` and `bad`, `Chunk::expanded` and `unqueued`); with several workers the
number depends on what the others had taken off the queue. When the search ends it is 0.

### TLC counts generated states per `\/` branch

When TLC computes successors, it follows each branch of a `\/` inside an action separately. If both branches can be
true, the same successor is counted once per branch, even inside a quantifier as in `\A x \in S : (A \/ B)`. Distinct
counts and verdicts are unaffected (duplicates collapse), but TLC's generated count ends up higher than tla2rs's.

To confirm: rewrite the same condition with De Morgan (`~(~A /\ ~B)`) or as `IF A THEN TRUE ELSE B`, and TLC's
generated count matches tla2rs. Measured on a real spec's timing assumption, the gap equaled exactly the number of
states where both A and B held.

A line `\* crosscheck: distinct-only` in a cfg makes `scripts/crosscheck.sh` skip the generated-count comparison
(`tests/tlc/OrDup.cfg` is an example). A line like `\* crosscheck: rsargs -memlimit 0` passes extra arguments to
tla2rs only. The default stays strict: generated-count mismatches have caught real bugs before (a difference in when
`\/` and `\E` branch), so mark only configurations whose gap is understood.

### The order of strings

TLC orders strings by when it first creates them (`UniqueString` ids), not alphabetically, and that order decides how a
set of strings is enumerated, which element CHOOSE picks, and how sets print. Measured on TLC 2.19 (`tests/tlc/StrRank*`),
it creates: the strings and model values of the cfg; SANY's built-in names; the identifiers, keywords and numbers (as
written: `007`, `\b101`; `StrRankNum`) of each module as it parses them (root module first, then the modules it extends
or instantiates, breadth first; a string equal to an identifier such as an operator name, or to a name or number in a
standard module, takes that identifier's place); a few more built-in names; the string literals of each module,
dependencies first. `tlc_string_ranks` reproduces this, with the standard modules' names and numbers in
`src/std_modules.rs` (generated from TLC's jar; Sequences has the numbers 1 and 0, Integers 0, TLC 1, Randomization 1
and 5). TLC orders every model value before every string (`{"zz", m1}` prints as `{m1, "zz"}`, a function over both
lists the model values first, CHOOSE picks `m1`; `tests/tlc/ModelStr*`), so model values get the lower atom numbers.

Strings made by operations (`\o`, `Append`, `Head`, `Tail` and `SubSeq` on strings, `ToString`) come after those, in
the order TLC first makes them. Measured on TLC 2.19 (`tests/tlc/StrMade*`), with one worker:

- When it starts, TLC evaluates the constants, every definition of constant level without arguments (used or not),
  the constant invariants and properties, and the ASSUMEs, in that order; the strings these make come first
  (`StrMadeStart`: an unused `Words == {"c" \o w : w \in {"a", "b"}}` puts `"ca"` before `"cb"`)
- Then the strings made while exploring, in the order the search makes them: a string made and dropped counts (a
  comparison, a branch that fails later), and so does one made by a constant expression inside an action or an
  invariant, which TLC evaluates there each time (`StrMadeConst`). TLC checks the invariants on each successor as
  soon as it computes it, so what they make comes before what the next successors make (`StrMadeInv`)
- A string equal to a name or number of a module was created when TLC parsed it and keeps that place
  (`StrMadeName`; `StrMadeToString`: `ToString(1)` is `"1"`, a number in the TLC module)

The checker's strings are 16-bit ids fixed when it is built (and sets of them bit masks over those ids), so it cannot
number a string when it makes one. tla2rs numbers them in an order measured instead:

- The compiler evaluates the constant definitions that can make strings (`makes_strings`), the constant invariants
  and properties and the ASSUMEs in TLC's order, noting the strings made (`Atoms::made`), and numbers those right after
  the strings TLC knows from parsing. That order is known only after evaluating, which itself iterates sets in the
  order of their strings, so `compile` compiles again until it does not change (`MADE_ORDER`, `Startup::made`)
- The strings the checker may make while exploring are numbered from `TRACK_FROM`, first in the order a checker built
  before made them, then as the compiler meets them. Code generation notes each such string the checker makes
  (`Gen::note_made` for the operations on strings from the state and ToString, `Gen::note_folded` for a constant
  expression TLC evaluates there: as a value, a set a quantifier ranges over, or a set tested for membership).
  When tla2rs runs the checker with one worker, it names a file in `TLA2RS_ORDER`, and the checker records the
  first time it makes each such string, where TLC would: what it makes while computing a successor counts after the
  invariants of the successors before it (held like the printed lines, see "Messages and printed lines"), and the
  search takes the default path, not `-batched`. A string made after one numbered later, or one a module names
  (`RANKED_LATE`), means the order differs from TLC's: the checker explores to the end, writes the order it made the
  strings in to the file and exits with 72; `main.rs` prints `tla2rs: strings were made in another order than they
  were numbered in; checking again from the start with them in that order`, compiles with that order, and runs again
  (at most 8 times). `crosscheck.sh` compares only what follows the last such line, as for capacities. A spec that
  makes no strings while exploring generates the same checker as before, but for the calls that mark the states
  pushed and the actions started, which do nothing then

Not followed:

- With several workers the order depends on thread scheduling: CHOOSE over `{ToString(n) \o "w" : n \in 1..2000}`
  after the search created those strings gave `"4w"`, `"1w"`, `"2w"` and `"4w"` in four runs with `-workers 4`, and
  `"1w"` every time with one worker. The checker notes nothing then and keeps the order it was built with
- A string made by a constant expression that the compiler evaluates elsewhere (the condition of an IF, the set of a
  `\A` that assigns variables in an action, ...), and the characters TLC makes when it takes a string apart
  into a tuple (`SelectSeq`, `SortSeq`, a string compared with a tuple), are numbered as the compiler meets them and
  not noted

### How TLC reads SPECIFICATION

Measured on TLC 2.19 (`tests/tlc/SpecConj*`, `SpecShape*`, `SpecInst*`, `RtSpec*`):

- TLC splits the formula through conjunctions and definitions without arguments (also those of an instance, after
  substitution), but not through LET, `\E`, labels or operators with arguments. A conjunct of level 0 or 1 belongs to
  the initial predicate, `[][A]_v` gives the next-state action (a second one is refused, exit 151), and any other
  temporal conjunct (`[]P`, `<>P`, `WF` inside `\/`, `RTnow(v)`, ...) is checked by nothing. When there are temporal
  properties, TLC checks them under all those conjuncts (so `[](x < 3)` in the spec can make `<>[](x < 3)` hold), and a
  property `[]P` with P a state predicate is still checked as an invariant on every state. `resolve_spec` follows this;
  WF / SF conjuncts become conditions on the cycles, the others are conjoined to each property's negation (`live.rs`)
- Without an initial predicate TLC stops (exit 151). Without a next-state action it stops (exit 151) if anything must
  be checked on steps (an invariant, `[]P`, an action or temporal property); otherwise it computes and checks the
  initial states and then stops with exit 75
- A module without variables, with a cfg that has no SPECIFICATION, INIT or NEXT (one that only checks its ASSUMEs),
  is not refused: TLC evaluates the ASSUMEs and reports no error with no states, and writes an empty state graph
  (`compile::NO_BEHAVIOR`, `tests/tlc/NoBehavior*`). With variables, it is refused for lack of an initial predicate
- Before anything else TLC evaluates the definitions of constant level, then the invariants and properties of
  constant level, then reads the spec (refusing it without an initial predicate), and only then evaluates the
  ASSUMEs (`tests/tlc/NoBehavior*`, `NoBehaviorVar*`): a false constant invariant hides the ASSUMEs' prints
- An invariant or property of constant level is evaluated once before exploring; if it is not TRUE, TLC stops (exit
  151). TLC also evaluates every definition of constant level without arguments when it starts, then the ASSUMEs, and
  keeps the values: `Print` / `PrintT` in them print once, before anything else (`STARTUP_PRINTS`), and not when the
  definition is used later

### ENABLED in an instantiated module

While TLC computes whether an action is enabled, it binds each primed variable by its name in a partial state
(`TLCStateFun`). For an ENABLED, WF or SF written in an instantiated module, a variable the INSTANCE substitutes
(`total <- a + b`) is bound the same way, as if it were a variable of its own: `total' = e` and `total' \in S` bind
it, UNCHANGED total binds it to what it stands for, and `total'` elsewhere reads the binding (an error when it is not
bound), never the substitution, so an action that can never take a step can be enabled. An ENABLED written in the
instantiating module reads the substitution. Measured on TLC 2.19 (`tests/tlc/EnSubst*`). Expansion marks a
substituted variable with an `ast::SUBVAR` label and the action of such an ENABLED, WF or SF with `ast::ENINST`;
`Gen::gen_phantom` binds them. Whether a fair action is enabled is computed with its subscript test as the last
conjunct, as for WF in a property, so a successor may leave variables the subscript does not read undetermined
(`tests/tlc/FairSub*`).

### Functions over sets that cannot be enumerated

TLC evaluates `[x \in S |-> e]` lazily. Measured on TLC 2.19 with S = Nat (`tests/tlc/LazyFun*`, `NatDom-InNat`):

- `f[k]` checks that k is in S and evaluates e at k; outside S it stops ("In applying the function ... which is not
  in its domain", exit 75). `[f EXCEPT ![k] = v]` with k outside S is a no-op (TLC warns), so applying it at k fails
- Storing it in a variable fails ("Attempted to compute the number of elements in the overridden value Nat.", exit
  75), and so do comparing it, `DOMAIN f = Nat` and `f \in [Nat -> Nat]` in an invariant (when TLC fingerprints it).
  A finite function in `[Nat -> Nat]` fails too ("Attempted to check equality of the set ... with the value: Nat")
- `ToString(f)`, `Print` and `PrintT` print `[n \in Nat |-> <expression line 5, col 26 to line 5, col 30 of module
  M>]` (`tests/tlc/LazyFunText`): the bound variables, each group with the domain as TLC prints its value (`Seq({1,
  2})`, `(Nat \X {1, 2})`), but only the first name of `a, c \in Nat`; then the position of the body without the
  parentheses around it, or the body itself when it is a number (`<expression 007>`). EXCEPT changes nothing in it.
  Over a set TLC can enumerate (`-5..-3`, or 0..200000), it prints the function as a value

tla2rs compiles `f[k]` (also after EXCEPT with one index per update) and `k \in DOMAIN f` to the membership test and
the body (`Gen::lazy_apply`), also over a constant set of more than 65536 elements (`lazy_domain`). The parser keeps
how TLC prints a function in an FN label around it (`ast::FN`), which `codegen::lazy_fun_string` fills in for
ToString, Print and PrintT, with the domains Nat, Int, STRING, `Seq(S)` and products of those and finite sets. Such a
function over an infinite set is refused anywhere else, as are those three over another domain. Constant folding applies `[x \in S |-> e][k]` the same way (`value.rs`).

### Tuples compared with strings

TLC asks the value on the left of `=` whether it equals the one on the right. Measured on TLC 2.19
(`tests/tlc/TupleStr*`): a tuple asked about a string compares itself with the string's characters (`<<"a", "b">> = s`
is TRUE for s = "ab"), a string asked about a tuple stops with an error, and a model value is unequal to both. For
`x \in S`, a set written out where it is used asks each element in the order written (`s \in {<<"a", "b">>}` is
TRUE), while a set from a definition or the state has been sorted, and comparing a string with a tuple then fails.
`Gen::tuple_str_eq` follows this. TLC also builds some sets where they are used without sorting them, and then asks
each element (`Gen::member_unsorted`, `tests/tlc/TupleStrCup*`): `{f(y) : y \in S}`, and `A \cup B` when A is held as
the set of its elements (written out, from the state or a definition, such a set, or a union with one), which TLC
unites with B by copying A's elements and adding B's (`SetEnumValue.cup`). So `s \in TS \cup {}` is TRUE where `s \in
TS` fails. When A is empty the union is B itself, and `s \in {} \cup TS` fails as `s \in TS` does.

A set of strings compared with a set of integers (`{x} = {5}`, x a string) cannot be held as one type, so `Gen::str_int_eq`
compares them as TLC does, measured on TLC 2.19 (`tests/tlc/StrIntSet*`): sets of different sizes are unequal;
otherwise TLC compares the elements in its order pair by pair and stops at the first unequal pair, where a model
value is unequal to anything but itself and a string meeting an integer is an error worded by the left one
(`Attempted to check equality of string "a" with non-string:` or `... of integer 5 with non-integer:`). A set written
out on the left adds TLC's `TLC was unable to fingerprint.` (see "Messages and printed lines"). Tuples of such sets
compare element by element; other values holding them are still refused.

### `\div` in Naturals

TLC evaluates `\div` with a Java method of the module it loaded. Integers' is the floor of the
quotient; Naturals' rounds toward zero and then down only when that is negative and the division is
not exact, so `(0 - 1) \div 3` and `10 \div (0 - 11)` are 0 under Naturals and -1 under Integers,
while `(0 - 7) \div 2` is -4 under both (measured on TLC 2.19, `tests/tlc/NatDiv`, `IntDiv`). When
the spec does not load Integers (or Reals), tla2rs follows Naturals: `tla_div_nat` in the checker,
`value::nat_div` in constant evaluation (`value::NAT_DIV`).

### What SANY refuses

TLC stops with exit 150 before checking anything when SANY refuses a spec (its report on a parse error
or a level error is reproduced word for word, see "Messages and printed lines"). tla2rs repeats these of SANY's checks
(measured on SANY 2.19 with small specs; `tests/tlc/RejSany*`, `SanyScope*`):

- Scope (`sany.rs`). A name is in scope only after the statement that declares or defines it: an operator
  parameter, bound variable or LET definition may be named like a VARIABLE, CONSTANT or definition written later
  in the module (issue #43). In scope from the start are TRUE, FALSE, BOOLEAN, STRING and what the modules in
  EXTENDS export: their CONSTANTs, VARIABLEs and definitions that are not LOCAL, and what they extend in turn. The
  standard modules export what TLC's jar defines in them; those that instantiate Naturals LOCALly (Sequences,
  FiniteSets, TLC, Bags) do not export Nat or `+`. An INSTANCE brings the instantiated module's definitions into
  scope at that point (a LOCAL INSTANCE too, without exporting them), `N == INSTANCE M` only N. A RECURSIVE
  declaration puts its name in scope, and is exported even when the definition is LOCAL. A nested module sees what is in scope where it starts
- Every name used must be in scope (`Unknown operator`, `Could not find declaration or definition of symbol`),
  in every definition, used or not; this covers the operators of standard modules not extended (`Len`, `+`, unary
  minus as `-.`, `:>`). The sets of `\E x \in S, y \in T` are read outside the quantifier, so T cannot use x
- No declaration, definition, parameter, LET definition, bound variable or LAMBDA parameter may reuse a name in
  scope. A definition's own name is in scope in its parameters (`F(F)` is refused) but not in its body (`F == \E F
  \in S : P` is accepted), unless it is a function definition `f[x \in S] == e` or declared RECURSIVE. The same
  definition reached twice is one symbol: a module extended along two paths, or a module without constants or
  variables both extended and instantiated (or instantiated twice). An INSTANCE of a module with constants or
  variables gives new definitions, so instantiating it twice without names is refused. Two different definitions
  of one name in two extended modules are only a warning for SANY, and are not refused
- A label `l(p, q) :: e` must list exactly the bound variables introduced between it and the enclosing label or
  definition, each once; a LET definition starts afresh, and operator parameters and LET names do not count. LAMBDA
  is accepted only as an argument of an operator or in a WITH substitution
- Precedence (`parser.rs`): two infix operators whose ranges in the TLA+ table overlap, next to each other without
  parentheses, unless they are the same operator and it associates (`a + b + c` is fine, `a = b = c`, `a % b % c`,
  `a /\ b \/ c` and `a * b \div c` are not). The parser checks each operator against the one before it at the same
  level and the one it is the right operand of (`parser::sany_range`). A prefix operator conflicts with an infix
  operator after its operand whose range overlaps its own: `[]`, `<>`, ENABLED and UNCHANGED have 4-15, so
  `[]x = 1` and `ENABLED x' = 1` are refused, and so is a postfix operator on their operand (`UNCHANGED x'`); unary
  minus has 12 (`-a \X b` is refused); SUBSET, UNION and DOMAIN behave as if their range were 10-13, measured
  over every pair: `SUBSET a + b` is refused, `SUBSET a \cup b` is `(SUBSET a) \cup b` and `SUBSET 1..2` is
  `(SUBSET 1)..2` (TLC then fails to evaluate it). Unary minus as the operand of an infix operator whose range
  starts above 12 is refused (`a * -b`, `a ^ -b`); `~` never conflicts
- Positional subexpression names (`Op!3`, `Op!(1, 2)`, `Op!lab`) that name nothing, in every definition and ASSUME
  (`Expander::check_subexprs`), also in definitions nothing uses
- String escapes other than `\\ \" \n \t \r \f`

LOCAL definitions of a module read for EXTENDS or INSTANCE are renamed (`compile::hide_locals`), since they are not
in scope in the module that reads it, which may define the same name (`tests/tlc/SanyScope`, `SanyLocalRec`).

Not repeated: names inside `\E x : P`, `\A x : P` and `CHOOSE x : P` without a set, and inside `\EE` and `\AA`
(their bodies are not kept); the WITH substitutions of an INSTANCE inside LET; positional names whose operator is
a LET definition; and SANY's checks of other kinds (operator arities, levels outside temporal formulas, the
warning for two definitions of one name in two extended modules).

### Quantifiers and CHOOSE without a set

`\E x : P`, `\A x : P` and `CHOOSE x : P` parse into a call that fails with TLC's message ("TLC attempted to evaluate an
unbounded \E") when evaluated; their bodies are dropped. TLC accepts them and fails in the same places
(`tests/tlc/Unbounded*`): an invariant, an action, the initial predicate, a property, an ASSUME (exit 10). A definition
that is never used is no error.

### Positional subexpression names

SANY reads infix `/\` and `\/` as binary and left-associative (the first operand of `a /\ b /\ c` is `a /\ b`), while
the parser flattens them into one conjunction. A module that uses positional names (`!` followed by a number, `<<`,
`>>`, `:`, `(` or `@`) is parsed with infix junctions kept binary inside an `INFIX_JUNCTION` label, which expansion
flattens as before. `Op!@` is not supported (SANY refuses it without arguments: "Expected 1 arguments but found 0").

### Actions that assign through `\A` or recursion over values from the state

TLC evaluates `\A x \in S : B` in an action as the conjunction of B over the elements of S in order, and a recursive
operator as its body with the arguments bound; either can assign variables (`tests/tlc/ForallState*`, `RecState*`,
counts match TLC). Over a constant set or with constant arguments, tla2rs unrolls them at compile time. Otherwise:

- `\A`: the checker collects the elements when it evaluates the quantifier. While B can still assign a variable, each
  element is one level of generated code, up to the number of values of the set's element type when that is at most
  16; once B only reads what is assigned, the remaining elements are a test (`Gen::gen_forall`). Over a larger type,
  the elements after the first are walked at run time by a recursive operator made for the quantifier, `F(S, k) == IF
  k > Cardinality(S) THEN TRUE ELSE B(k-th element) /\ F(S, k + 1)` (`Gen::forall_rec`; `tests/tlc/ForallLarge`)
- A recursive operator becomes a Rust function that evaluates its body as an action and returns each state it builds
  with the number of the set of variables assigned by then (`Gen::assigned_sets`, so any number of variables:
  `RecManyVars`). The action continues from each returned state, once per set. A call of the operator in its own body
  uses the sets found so far, and the body is generated again until they settle (`Gen::gen_rec_action`,
  `rec_action_fn`). In Init the function starts from the state under construction, whose assigned variables are all
  it reads of the variables (`RecInit`)

### The order of variables

TLC prints a state's variables in the order of `ModuleNode.getVariableDecls` of the root module: SANY's context of
the module, a Java `Hashtable` keyed by name, enumerated and then reversed. `String.hashCode` is deterministic, so the
order is too, and it depends only on the names and on how many names were in the table when each variable came, which
decides when the table grew (11 slots, then 2n+1 once it holds three quarters; growing walks the old slots from the
last and each chain from the front, and a new name goes to the front of its chain). Measured on SANY 2.19 with a
dump of the context (a small Java program calling SANY's classes, not kept here): 72 built-in operators come first,
then what each module in EXTENDS exports, in order and without repeats, then each statement of the module (a
declaration, definition, theorem, named ASSUME, RECURSIVE declaration or nested module adds its name; `N == INSTANCE
M` adds `N!d` for each definition d that M exports, then N; an unnamed INSTANCE adds the definitions M exports that
are not there yet); a module exports all of these but the LOCAL ones. `sany::var_order` replays this, and the
checker prints in that order (`Gen::print_order`; `tests/tlc/VarOrder*`, where 151 names grow the table to 383
slots). The order agreed with SANY's on every root module of `examples/`, `tests/tlc/` and the corpus, and on 94
generated modules (random names, 0 to 120 definitions, extended and instantiated modules). TLC lists the variables
an action leaves unassigned in the order of their names instead (`VarOrder-Partial`). With VIEW and SYMMETRY the
order also decides which permuted state is the smallest (see "VIEW and SYMMETRY together").

### State graphs

Matching counts does not show that tla2rs reached the same states or took the same transitions, so the cross-check
also compares the state graph. TLC writes it with `-dump dot FILE`, and a generated checker with `-dumpgraph FILE` in
the same form (`runtime.rs`, "state graph dump"; without the option nothing is written and the search is unchanged).
What TLC 2.19 writes, measured (`tlc2.util.DotStateWriter`, called from `Worker`):

- A node per state, labelled with the state as TLC prints it in a trace; the initial states are filled. Ids are
  fingerprints, so they mean nothing outside the file. With SYMMETRY or VIEW the id is the fingerprint of the
  canonical form or the view, and the label is the first state of that class reached
- An edge for each successor that satisfies the CONSTRAINT and ACTION_CONSTRAINT, written when it is generated:
  self-loops included, and once per time it is generated (so twice when two `\/` branches give it). A successor
  outside the model gets no edge
- When the search stops at a violation or deadlock, the graph ends at the successor that stopped it (its edge and
  label are there). With one worker this point is deterministic, and every such configuration is compared
- After an error in evaluating an invariant on a new state, TLC evaluates the state it was expanding again to show
  where the error is, and that pass writes too: an edge to every successor of that state, adding those not yet seen,
  until a new successor fails an invariant or any fails an action property. `dump_replay` repeats this
  (`tests/tlc/BagOps-Lit.cfg`, `FunMember-NotFun.cfg`, `StrSeqOps-StrLeft.cfg` need it)
- For liveness checking, TLC also writes a dashed stuttering edge from each state it expands to itself
- The values are pretty-printed to 80 columns (`tlc2.pprint`, ported as `ppr` and checked against TLC's on 25,000
  random values). A spec with a single variable prints `x = 1`, without `/\`
- When TLC stops while computing the initial states or before (an ASSUME, a constant-level invariant, a refused
  formula, a violation in an initial state), it never ends the file, and what it had buffered (the initial states)
  is lost

The canonical form (`src/graph.rs`) is the sorted set of state texts, each marked initial or not, and the sorted
set of edges as pairs of those texts; the expected file keeps `states N <sha256>` and `edges M <sha256>` of them,
not the graphs. Reducing to it:

- The `/\ var = value` lines of a state stay in the order printed, which a checker prints in TLC's order (see "The
  order of variables")
- `<<>>` is read as `<< >>`. TLC prints the empty function as `<<>>` when it is held as a function and as `<< >>`
  when it is held as a tuple, depending on the expression that built it (`DynDomain`, `NatDom`, `PartFuns`,
  `SparseFun`, ...)
- Duplicate edges collapse, and dashed stuttering edges are dropped (they are not transitions of the next-state
  relation)
- An interval `a..b` outside strings is read as the set it denotes. TLC prints a value in the form it holds it, so a
  variable assigned `1..3` prints as `1..3` until an operation turns it into an enumerated set, while tla2rs prints
  `{1, 2, 3}` (measured on the corpus's `DiningPhilosophers`). This applies to a variable printed on one line whose
  value fits in 80 columns once expanded, where TLC's pretty printer would also keep it on one line; a longer one is
  kept as printed and then differs (no configuration has one). tla2rs does not print intervals as TLC does, because
  the form depends on how the value was built, not on the value. Measured on TLC 2.19 (`tests/tlc/IntervalShow`):
  `s = 1..3` prints `1..3` and, after `s' = {1, 2, 3}`, the same value prints `{1, 2, 3}`; a function built as `[i \in
  1..2 |-> 1..i]` prints `<<1..1, 1..2>>`, and keeps `1..2` through an EXCEPT of the other entry; `s \cup {4}`
  enumerates; an empty interval prints `{}`. A state graph labels each state by the first way it was reached. To
  follow this, a checker would have to carry, for every set inside a state, whether TLC holds it as an interval,
  outside the fingerprint and through every operation, while states are packed to fixed widths by type and sets of
  integers are bit masks. Of the 671 configurations, only `IntervalShow` prints an interval (TLC's graphs and outputs
  of all of them, searched), and of the corpus `DiningPhilosophers`

Where the graph cannot be compared as a whole, `crosscheck.sh` compares less, and says so after `MATCH` (the counts
are for the 483 configurations at the time of writing):

| Rule | Applies to | Compared |
|---|---|---|
| TLC did not end the file (automatic: no closing `}`) | 56 (stops in or before the initial states, and SANY or temporal refusals) | Not the graph; verdict, counts and exit code as before |
| tla2rs stopped at a successor that left its declared type while `next` built it (automatic: "a successor that tla2rs cannot represent" in its output) | 1 (`SetOut`) | The numbers of states and edges and the length of the counterexample (tla2rs writes a placeholder node and state for the successor TLC adds) |

`distinct-only` (three configurations) leaves the graph compared: duplicate edges collapse anyway.

### Counterexamples

A safety counterexample (invariant, action property, deadlock, an evaluation error with a behavior) is compared
with TLC's as a whole: each step's first line, `State N: <Name line L, col C to line L2, col C2 of module M>`, and
its state. `src/trace.rs` reduces both to that list, each state in the canonical form of the state graphs (its
variables in the order printed, `<<>>` read as `<< >>`), and the expected file keeps `trace N <sha256>` of it.

With one worker TLC's counterexample is deterministic: for all 186 configurations that have one, four runs (two with
random fingerprint seeds, `-fp 1`, `-fp 50`) gave the same text. TLC rebuilds it from fingerprints, taking for each
step the first action, in its order of actions, that yields the next state (`Tool.getState`); tla2rs replays `next`
the same way (`replay`), and its successors come in TLC's order, so every counterexample matches. Only
`tests/tlc/SetOut.cfg` compares the length alone: its last state is the successor tla2rs cannot represent.

How TLC names actions, measured on TLC 2.19 (`tests/tlc/ActName*`, `Tool.getActions`), which `Gen::gen_split`
follows:

- It splits the next-state relation through `\/`, `\E` over a set that does not depend on the state (once per
  element), LET, labels, and calls of definitions (also LET and recursive ones) whose arguments do not depend on the
  state. What it reaches otherwise is one action: a conjunction, `IF`, `[A]_v`, `\E` over a set from the state, ...
- An action is named by the innermost definition called on the way (`Action` if none, as for `[][x' = x + 1]_x`),
  and for a call with an argument from the state, by the definition called. Its position is that of the part
  where splitting stopped: a definition's body, a disjunct, the body of `\E`, LET or a label, or the call. SANY's
  positions run from the first to the last token, without the parentheses around a whole expression
- A definition of an INSTANCE with substitutions is not split: its actions are named `N!Op` (or `Op` for an unnamed
  INSTANCE, or `Action` for the next-state relation of a SPECIFICATION inside the instance) at the position of the
  INSTANCE statement

The parser keeps these positions in POS labels; expansion drops them except while expanding the next-state relation
(`Expander::keep_pos`). One case is not followed: a recursive operator called with an argument bound by a split
`\E` is split further by TLC (the argument is a constant to it), while tla2rs names the call after the operator at
the position of its body; no configuration has this.

A liveness counterexample (lasso) cannot be compared with TLC's: TLC takes the successors of a state in its liveness
graph out of a hash set keyed by fingerprint (`tlc2.util.SetOfStates`), and picks the fingerprint polynomial at
random on each run. For `tests/tlc/LiveForms-NoneImplies.cfg`, ten runs gave 5 states eight times and 4 states
twice. TLC checks tla2rs's lasso instead. With `-lassocheck DIR`, the checker writes `DIR/Tla2rsLasso.tla` and
`.cfg` (`write_lasso_check` in the runtime, `src/lasso.rs`): a module that EXTENDS the spec with a variable for the
position on the lasso, whose initial predicate is the first state and the spec's own, whose next-state relation
moves to the next position's state (from the last back to where the lasso returns, or to itself when it ends
stuttering) conjoined with the spec's `[Next]_vars`, and whose spec adds WF of that relation to the spec's temporal
conjuncts. The only fair behavior is then the lasso, so TLC reports the properties violated, with one distinct state
per position, exactly when the lasso starts in an initial state, every step is a step of Next (otherwise it
deadlocks, or a state is missing), it satisfies the spec's fairness (otherwise no behavior is fair) and it violates a
property. Fairness stays that of the spec: its actions do not mention the new variable. Altering a confirmed lasso
gave the expected refusals (a wrong state: deadlock; a wrong first state: no initial state; a wrong return: deadlock;
fairness for both processes in `Peterson-Unfair`: no error). VIEW and SYMMETRY are left out of the cfg, so the
lasso is checked as a behavior of the spec itself (`LiveSym` passes). `crosscheck.sh` runs this for each of the 37
liveness violations (about a second of TLC each) and fails if TLC does not confirm it, or if the spec's parts cannot
be written out (`lasso::tla` refuses a SPECIFICATION split inside an INSTANCE, and LET or LAMBDA in its conjuncts).

### Messages and printed lines

What TLC prints besides its progress and the counterexample is compared too: its error and warning
messages and the lines the spec prints (Print, PrintT), in order. `src/messages.rs` reduces an output
to a canonical text; the expected file keeps `messages N <sha256>` of it and `errors M <sha256>` of
its error lines (the lines that start with `Error:`). `tla2rs --messages-text FILE` prints the text,
for diffing.

Measured on TLC 2.19, two runs of every configuration with one worker (as `expected.sh -check`,
each with its own random fingerprint seed) gave the same canonical text for all of them. What varies
between runs is in lines that are dropped anyway: the banner (fingerprint seed, process id), the
temporary paths of the modules TLC parses, times and dates, and the shape of a liveness
counterexample. No configuration printed a Java stack trace. The rules:

| Part of the output | Rule |
|---|---|
| Banner, modules parsed, progress, statistics (counts, depth, outdegree, collision estimates), times, and a checker's equivalents | Dropped (the counts are compared on their own) |
| Counterexample (`State N:` / `Back to state N:` and the state after it) | Dropped (compared by `trace.rs`) |
| TLC's evaluation stacks: `The error occurred when TLC was evaluating the nested expressions at the following positions:` with its numbered positions, and `Fingerprint Stack Trace:` with its frames | Dropped: deterministic, but they list TLC's own nested evaluations, which a checker that inlines every definition does not have |
| SANY's parser stack (`Residual stack trace follows:` and its lines) and `tla2sany.semantic.AbortException` | Dropped (SANY's internals) |
| `The exception was a java.lang.RuntimeException` and a Java class name before the message on the next line (`: tlc2.tool.EvalException: ...`) | The class lines are dropped and the message kept: they say how TLC passed the error on |
| A state after a message (`... is violated by the initial state:`, `While working on the initial state:`) | One line, in the canonical form of a state |
| Empty lines | Dropped |

How TLC words an evaluation error depends on where it happens, measured on the `ErrCon*`, `EvalNext*`,
`InvEval*`, `LiveErr*` and `Unbounded*` configurations, and `runtime.rs` (`report_eval_as`) follows it:

- While computing successors, TLC reports its own evaluation errors (a failed arithmetic operation,
  a false Assert; the exit code is then 255 or that of Assert) as `Error: <message>`, and any other
  error as an exception it did not expect: `Error: TLC threw an unexpected exception.`, two more
  lines, the Java class, then the message. In the CONSTRAINT, ACTION_CONSTRAINT, VIEW and the
  liveness checks, every error is reported that way
- While computing or checking the initial states every error is plain. One that is not TLC's own
  evaluation error, raised while checking an initial state (CONSTRAINT, invariant, property), is
  followed by `While working on the initial state:` and the state
- TLC gives the position of a CASE with no true condition (`In computing next states, TLC
  encountered a CASE ...` for a CASE among the conjuncts of an action, `In computing ENABLED, ...`
  while computing whether an action is enabled), of a CHOOSE no element satisfies, of an unbounded
  quantifier, of a temporal formula it refuses, and names a part of a property by position. The
  parser keeps these positions in AT labels (`ast::AT`), which expansion keeps
- tla2rs's own notes (which state it cannot represent, what it was evaluating) go to stderr

TLC warns that SYMMETRY and constraints are dangerous when it checks temporal properties. It prints
these warnings after the Print and PrintT of the constant definitions and before those of the
ASSUMEs, and the note `(Use the -nowarning option to disable this warning.)` after the first warning
of a run only (`compile::Startup`; with its default garbage collector, TLC's first warning is about
that instead, which `-XX:+UseParallelGC` avoids).

Printed lines: with one worker TLC prints them in a fixed order, which tla2rs follows (measured on
TLC 2.19, `tests/tlc/PrintNext`, `PrintOrder*`). Print and PrintT in the constant definitions and
ASSUMEs print once, when TLC starts. In Init, the actions and the invariants:

- TLC checks each initial state and each successor as soon as it computes it: what Init or an action
  prints before a state comes before what the invariants print on it, and nothing is printed past the
  state that stops the search
- To show a behavior it rebuilds it from fingerprints. When the state it was expanding is the k-th of
  the behavior, it first rebuilds states 1 to k-1 (Init evaluated again, all of it, then for each step
  the actions in order up to the one that yields the next state, that action as a whole), prints
  `The behavior up to this point is:` and those states, and then evaluates the step to state k (if
  k > 1) and to the successor that stopped the search the same way, each before its state. No
  invariant is evaluated again. After an evaluation error in the actions it evaluates the failing
  step once more (to find where the error is), printing again up to the error

When Init, Next or an invariant prints (`PRINT_ORDER` in the generated checker, set by
`compile.rs`), the checker marks each state `init` or `next` pushes and the start of each action
(`mark_push`, `mark_action`, generated only then), holds what Print and PrintT print while it
computes states, and prints those lines as it handles the states (`Capturing`, `Held` in
`runtime.rs`); `print_states_tlc` shows a behavior as above. Such specs are searched without
`-batched` (on the default path), and a spec that prints nowhere else generates the same code as
before. A property `[]P` checked as an invariant is not covered: with `-batched` / `-metal`, when it
prints, phase 1 first skips a candidate already visited or collected in the level (`INV_PRINTS`),
since TLC checks new states only.

Other messages tla2rs words as TLC does, measured on TLC 2.19:

- A successor that leaves variables unassigned (`tests/tlc/Unassigned*`): `Successor state is not
  completely specified by the next-state action.` when the next-state relation is one action, `by
  action A of the next-state relation.` otherwise (counting each element of a split `\E` as an
  action), then `The following variable(s) is (are) not assigned: a, b.` in the order of the names.
  TLC counts the successor as generated and shows it last in the behavior with those variables
  `null` (exit 75). An initial state that leaves a variable unassigned: `current state is not a legal
  state`, the state with the variable `null`, and no counts (exit 255)
- After an error raised inside a value TLC built from an expression written there (a set `{...}`, a
  tuple `<<...>>`, a product `S \X T`, a set of functions or records it cannot enumerate, set
  operations on those), TLC reports a second error after the behavior (or the initial state): `TLC
  was unable to fingerprint.` with the same reason (and its `Fingerprint Stack Trace`, dropped). Not
  after `x \in S` for S from the state or a constant definition, `x \in 5..6`, `\E y \in {5, 6} : y =
  x`, `t[i]` for t from the state, or `k \notin [{1} -> {1}]`, nor when a string's or a tuple's own
  comparison fails (`<<"a">> \in {"ab"}`, `<<1, 2>> # s`) (`tests/tlc/FpErr*`). Code generation
  wraps such an operation in an `FpSource` when it can fail (`Gen::fp_source`)
- A tuple compared with an integer: `Attempted to check equality of the function <<1, 3>> with the
  value:` and the integer when the tuple is on the left, `... of integer 1 with non-integer:` and the
  tuple otherwise; a non-tuple in a product: `Attempted to check if non-tuple`, the value, `is in the
  set of tuples:` and the product (`tests/tlc/TupleVals*`)
- A tuple or a string in a set it cannot be compared with, when the set is sorted (from the state or
  a definition): TLC searches the set and fails on its first comparison, with the element at index
  n/2 in its order: `Attempted to compare the function <<1, 3>> with the value:` or `Attempted to
  compare string "x" with non-string:`, then that element (`tests/tlc/SortedCmp*`). A set written
  out where it is used is compared with element by element instead
- A value that is not an integer in an interval: `Attempted to check if the value:`, the value, `is
  in the integer interval 5..6`
- A model value in `+`, `-`, `*`, `\div`, `%`, `^`, unary minus or `..`: TLC evaluates these with Java
  methods and names the one that failed, `public static tlc2.value.impl.IntValue
  tlc2.module.Naturals.Plus(tlc2.value.impl.IntValue,tlc2.value.impl.IntValue)` (`Minus`, `Times`,
  `Divide`, `Mod`, `Expt`, `Neg` with one argument, `DotDot` giving an `IntervalValue`), in `Integers`
  when the spec loads Integers or Reals, then `Cannot cast tlc2.value.impl.ModelValue to
  tlc2.value.impl.IntValue` (`tests/tlc/ModelArith*`, `Gen::gen_int_of`). In a comparison it is TLC's
  own error (exit 255): `The first argument of < should be an integer, but instead it is:` (or
  `second`) and the value, with `>` for `>=` under Naturals (`Gen::int_cmp`)
- SANY's reports. A precedence conflict, a bad string escape and LAMBDA outside an operator's argument
  stop SANY while it parses (`***Parse Error***` or `Lexical error at line L, column C.`, then
  `Fatal errors while parsing TLA+ spec in file M`, `*** Abort messages: 1`, `In module M`, `Could
  not parse module M from file M.tla`): a conflict names SANY's operators (`\land`, `\lor`, `/=`,
  `\leq`, `\geq`, `\equiv`, `\union`, `\intersect`, `\times`, `-.` for unary minus) with the position
  of the first `in block`, indented two spaces, or of the postfix operator without indent; an escape
  gives the character, its code and the string read up to it (as Java escapes it); LAMBDA gives the
  token before it, and `Was expecting "Expression or Instance"` after `==` (the parser marks these
  with `lexer::SANY_ABORT`). A level error of a temporal formula gives the position of the innermost
  operator whose arguments break the rules, infix junctions read as binary and to the left, and a
  bulleted list is a `Conjunction list` or `Disjunction list`: the root module is parsed again with
  SPAN labels (`parser::parse_module_spans`) and the definition checked as written

Where tla2rs cannot print all of TLC's text, a line `\* crosscheck: error-lines (reason)` in the cfg
makes `crosscheck.sh` compare the error lines only, and `all.sh` says so. Without it everything is
compared. The error lines leave out TLC's `Error: TLC was unable to fingerprint.` (above). 39
configurations, by reason:

| Reason | Configurations |
|---|---|
| SANY's semantic errors give the position of each name involved (also of the declaration it clashes with, in a standard module, or `--TLA+ BUILTINS--`) and add follow-on errors (an operator's arity, an infix symbol it cannot resolve) and warnings; tla2rs's syntax tree keeps no positions of names | 20: `RejSanyBuiltin`, `-Choose`, `-DupDef`, `-ExtDef`, `-FunName`, `-InfixStd`, `-InstDef`, `-Label`, `-LocalRec`, `-Minus`, `-OwnParam`, `-QuantSet`, `-RecParam`, `-Shadow`, `-StdName`, `-StdUnext`, `-Subexpr`, `-TlcOps`, `-Unknown`, `SubexprBad` |
| TLC gives the position of an identifier it fails to evaluate (also a substituted variable in ENABLED, and a variable a fair action leaves unspecified, which tla2rs reports in its own words) or of an `x' \in S` it cannot enumerate; tla2rs keeps no positions of identifiers | 11: `ActForms-AllFn`, `-InitEnFirst`, `-UnchFirst`, `-UnchMix`, `-UnchSum`, `RejPrimeExpr`, `RejTempBound`, `EnSubst-EEarly`, `-Outer`, `FairPartial`, `RealSet-NextE` |
| TLC warns, with the position of the function, about an EXCEPT outside the domain only on its first evaluations: twice whether 3 or about 100 evaluations do one (measured), once when only one does, by a rule not found; `LazyFun*` also print a lazy function with the position of its body | 7: `ExceptDom`, `SparseFun`, `SparseFun-Viol`, `LazyFun`, `-Below`, `-Except`, `-Next` |
| TLC reports the error from ENABLED of the fair action, tla2rs from the step of that action, which it evaluates first; why TLC does not is not found | 1: `LiveErr-Fair` |

### The corpus

The configurations in `tests/tlc/` cover the forms someone thought of. `scripts/corpus.sh` also cross-checks the
models of the tlaplus/Examples repository (https://github.com/tlaplus/Examples, commit
334c3983a2f44ac78fce89d1d20aa79ceb3e6987, pinned in `tests/corpus.txt`). The corpus is fetched into
`target/corpus/<commit>/` and only read by TLC and tla2rs. No spec text of it is copied into this repository: only
TLC's results (`tests/expected/corpus/<path>.txt`, the same summaries as for `tests/tlc/`), and the tests added for
the gaps it showed are written from scratch, reproducing only the form that failed.

`tests/corpus.txt` lists all 243 models of the corpus's manifests. Selected are the exhaustive searches that TLC 2.19
finishes with `tla2tools.jar` and the CommunityModules' modules, in 60 s or less with one worker and `-dump dot`
(measured; the manifest's runtimes are for several workers). Skipped, with the reason on each line: 46 symbolic
(Apalache), 6 random generation or simulation, 2 that need a TLC flag for action composition, 33 that need a module
neither in `tla2tools.jar` nor in the CommunityModules (the proof system's library: TLAPS, NaturalsInduction,
FiniteSetTheorems; TLCExt), 36 that take longer (from the manifest's runtime, or measured), 7 whose cfg TLC 2.19
refuses (an `ALIAS` section), 2 where TLC picks values at random (two TLC runs differed), 5 where TLC 2.19 stops in a
CommunityModules definition that needs its Java override (IOUtils, and quantifiers over `Seq(S)` in Graphs and
UndirectedGraphs), and 1 that reads `TLCGet("config")`, which TLC 2.19 does not define. That leaves 105 selected.

The cfgs of the corpus are not edited, so a line of the list gives what a `\* crosscheck:` line would: `rules=`
(narrowing rules, passed as `CROSSCHECK_RULES`) and `rsargs=` (arguments for tla2rs only, `CROSSCHECK_RSARGS`; no
model needs one now that capacities grow, see "Capacities"). A selected model tla2rs does not
match is listed as `gap` with the reason measured; `corpus.sh` still runs it and says when it starts to match, and
fails only on a `check` that differs. A gap marked `norun` is not run, as running it costs too much (see the table
below).

Results at the time of writing (`scripts/corpus.sh`, JOBS=2): 101 match, of which 6 with `distinct-only`. Only the generated count differs in those 6: TLC generates the same successor of a state
more than once (once per `\/` branch or binding that yields it), and so does tla2rs, but not equally often. Measured
with `-dump dot` on two of them, where the generated count is the number of edges with duplicates, plus the initial
states and the successors a CONSTRAINT removes: `2PCwithBTM` has 5840 edges in TLC and 5290 in tla2rs, and the same
4682 distinct edges; `MCCheckpointCoordinationFailure` has 1297994 and 1297595 edges, and the same 611225 distinct
edges. The graph hashes compare the distinct edges, so the state space and transitions match. `StaleViewShrink` (4) is
not measured this way. 4 are gaps, 3 of them `norun`:

| Gap | Model |
|---|---|
| A liveness counterexample under a VIEW: verdict, counts and state graph match, but tla2rs's lasso goes through the first state reached of each view, which is not always a successor of the state before it, so TLC deadlocks on the lasso check | `MCDistributedReplicatedLog` |
| `norun`: the generated checker is 6 MB of Rust; rustc ran for over 9 minutes on it | `GameOfLife` |
| `norun`: evaluating its ASSUMEs at compile time took 1.5 GB in 2.5 minutes (LET definitions are expanded at each use, so recursion through them repeats work) | `BlockDagTest` |
| `norun`: the system killed tla2rs for memory in a corpus run | `TLCSailfish1` |

Forms the corpus showed, each with a test in `tests/tlc/`: the CommunityModules (`CmFun`, `CmSet`, `CmSeq`,
`CmGraph`, `CmBits`; see "CommunityModules"), `[1..n -> S]` with n from the state as a set of sequences
(`SeqFunSet`), a definition of an instantiated module passed as an operator argument (`InstOpArg`), a recursive
operator called inside the operator passed to it (`RecNestOp`), the field of an element of a set that starts empty
(`EmptyField`), records of different fields in TLC's
order (`RecMix`), a value that is a record or a model value (`RecAtom`), primed substituted variables in ENABLED
written in an instance (`EnSubst`), a fair action leaving variables its subscript does not read undetermined
(`FairSub`), `x \in UNION {S}` without enumerating S (`UnionMem`), recursive functions typed from a set, function or
base-case seed (`RecSetFn`, `RecFunApp`, `RecBase`), Print and PrintT pretty-printed (`PrintWide`), ASSUMEs over
`Nat \X S` and `\subseteq Nat \ {0}` (`AssumeNatFn`), the function over an empty domain (`EmptyDomFn`), types
inferred when TypeOK's fail (`ExtType`), an infix `&` (`AmpOp`), `name = [Module] value` in a cfg (`ModVal`), LET
definitions of an instance renamed (`InstLet`), in-place EXCEPT on a function over part of a type (`PartExcept`), model
values before strings (`ModelStr`), records compared field by field in an array (`RecNest`), up to 128 fairness
conditions (`ManyFair`), tuples of different lengths or sets held beside model values (`SeqAtom`, `SetAtom`),
functions over domains of different sizes (`DomGrow`), and TLC's warning that a PlusCal algorithm changed since its
translation (`PcalSum`).

### CommunityModules

The CommunityModules (https://github.com/tlaplus/CommunityModules) are modules TLC finds on its class path. Every
release tried (2023-12 to 2026-11) carries Java overrides that need a class TLC 2.19 does not have: with the jar on
the class path TLC 2.19 stops on any spec (`NoClassDefFoundError: tlc2/value/impl/KSubsetValue`). TLC 2.19 is built
from the 1.7 line of TLC, which branched before that class was added. So `crosscheck.sh` gives TLC the release's
modules only, extracted into
`target/community/<sha256>/`, and TLC evaluates their TLA+ definitions. The release is pinned by version and sha256
in `crosscheck.sh` (202611060952, the one current at the corpus's commit); a spec that uses it has the hash in the
key of its expected file.

tla2rs provides `Folds`, `Functions`, `FiniteSetsExt`, `SequencesExt`, `UndirectedGraphs` and `Bitwise` itself
(`src/community.rs`), as TLA+ source written for tla2rs, read when no module of that name is next to the spec.
Since TLC evaluates the modules' own definitions, these give the same values: CHOOSE over the same set with the
same predicate (`SetToSeq`, `Max`, `LongestCommonPrefix`, `Inverse`), and folds that take the elements in the same
order (`MapThenFoldSet` applies `op(f(x), rest)` with x chosen first, so `FoldFunction` takes the smallest index
first, `FoldLeft` the largest). Each module exports the same names in the same order as the release's, with what it
extends (`SequencesExt` extends Bags and TLC, for example), since SANY's context, and the order TLC prints variables
in, depend on them (see "The order of variables"). Operators listed in `community::UNSUPPORTED` are refused where
they are used: five of SequencesExt not written yet, and UndirectedGraphs' operators over paths, which quantify over
`Seq(S)`, so TLC 2.19 stops on them too ("non-enumerable quantifier bound").

Not followed: the identifiers and strings of these modules are not in `tlc_string_ranks` (TLC creates them when it
parses the modules), so a string literal of the spec equal to one of their identifiers, and not to one of the spec's,
may be ordered differently; no configuration has one. Errors inside the modules' definitions (Max of an empty set,
Last of an empty sequence) are reported with positions in TLC's modules that tla2rs does not have.

### PlusCal checksums

When the translator writes a PlusCal algorithm's translation, it records two checksums in the line that opens it:
`\* BEGIN TRANSLATION (chksum(pcal) = "..." /\ chksum(tla) = "...")`. TLC computes both again while SANY loads the
root module and each module reached through EXTENDS (not a module only instantiated), and prints right after
parsing that module, before anything else that is compared:

- `!! WARNING: The PlusCal algorithm in module M has changed since its last translation.` when only the PlusCal one
  differs, `... The TLA+ translation in module M has changed since its last translation.` when only the TLA+ one
  differs, and `... The PlusCal algorithm and its TLA+ translation in module M filename since the last translation.`
  (sic) when both do. These are printed directly, so TLC's note about `-nowarning` does not follow them
- Nothing when the line has no checksums or writes one as `\in STRING` (that one is not checked), or when the module
  has no `--algorithm` / `--fair` or no BEGIN / END TRANSLATION lines

What is hashed, measured on TLC 2.19 (`tests/tlc/PcalSum*`, and the corpus) and read from the published TLC sources
(`pcal.Validator`, tlaplus/tlaplus, MIT licence); `src/pcal.rs` is written for tla2rs:

- Both are CRC-32 values written in lowercase hexadecimal without leading zeros (`a163d78`)
- The TLA+ checksum covers the lines strictly between BEGIN TRANSLATION and END TRANSLATION, joined without line
  breaks, as written: a space added inside the translation changes it, an empty line does not
- The PlusCal checksum covers the text TLC's translator prints for its syntax tree of the algorithm: TLA+ tokens of
  each expression, line by line, inside a record per statement. Spaces and comments inside a line do not change it,
  nor do comment lines between statements or declarations; a line break or a comment line inside an expression does
  (`PcalSumSpace`, `PcalSumBreak`). The tree is printed after the translator has split the body into labeled steps
  and expanded them, and that expansion changes the tree it prints: an if or either without labels inside becomes a
  plain one, and in the statement lists it does not copy first, a last labeled if or either, or goto, is replaced
  and `pc := "next label"` is appended where control leaves the step. `tla2rs --pcal-text FILE` prints this text;
  for the corpus, comparing it with the translator's own (a small Java program calling TLC's classes, not kept here)
  found every one of the 22 algorithms tla2rs reads equal

Not followed: algorithms with procedures, calls, returns or macros, a `PlusCal options` line, names the translator
renames (two equal labels or variables, as in the corpus's `Sailfish`), or labels it would add (an algorithm without
labels). For those tla2rs prints a note on stderr and no warning. A spec TLC's translator cannot parse gets the
warning from TLC; tla2rs then prints the note too. A module reached through two EXTENDS is checked once.

### VIEW and SYMMETRY together

With both, TLC fingerprints a state by first taking the smallest of its permutations and then the VIEW of that state
(`TLCStateMut.fingerPrint`): it compares the permuted states value by value in its order of values, the variables in
the order it prints them (see "The order of variables"). Two states with equal views can have smallest states whose
views differ, and TLC keeps both. `fresh_fp` in the runtime does the same with `tlc_state_cmp` (generated by
`Gen::gen_perms` from `Gen::tlc_cmp`), so counts and state graphs match TLC (`tests/tlc/ViewSym-Both`,
`ViewSymSet-Both`; `ViewSymOrder` keeps 26 states where taking the smallest view would keep 10, and 10 when the
variable left out of the view is printed after the other). Without a VIEW, the smallest packed state is taken: any
representative of the orbit gives the same count.

With VIEW (in particular together with CONSTRAINT) and several workers, the distinct count can vary slightly from run
to run, for TLC as well as tla2rs, because which state becomes the representative depends on search order. With one
worker the counts are stable and match TLC.

## Verification rules

- Every semantic change is cross-checked against TLC. When adding syntax or a feature, add a small spec and `.cfg` to
  `tests/tlc/` so `scripts/all.sh` covers it
- Wrongly reporting "no error" is the worst outcome. Never let unsupported constructs through silently; reject them at
  compile time or fail at run time
- **Correctness comes before speed.** Phase 1 evaluates invariants 355.76 million times for 73.17 million distinct
  states. Moving the check to phase 3 (after insertion) would cut that to a fifth, but the generated count at a
  violation would no longer match TLC, so it is not done. Cross-checks keep matching TLC down to generated counts
- Checking only a speed benchmark spec is not enough. Also cross-check specs with runtime-sized sets, VIEW, and
  inferred types: two bugs introduced by speed work slipped past the regression suite and were caught only that way
  (see below)

## Running long checks

- On a 16 GB machine, a state space of roughly 200 million states and up starts swapping; throughput then drops to a
  fraction and system time approaches user time. Watch for this before reading anything into a slow run
- A process started with `&` from a non-interactive shell ignores SIGINT. To stop a background checker, send SIGTERM
- Before measuring, make sure nothing resident (for example a status-line tool) is eating CPU

## Speed and energy (benchmark spec A, 73,167,327 distinct states, M2 Pro 10 cores)

| | Wall time | CPU time |
|---|---|---|
| Before the speed work | 11.8 s | 97.4 s |
| Default path | 8.59 s | 66.6 s |
| `-metal` | 6.11 s (**1.93x**) | 41.0 s (**2.38x**) |

The goal was 3x on both, so neither was reached. Energy uses CPU time as a proxy (`powermetrics` needs admin rights).

### What worked (in order)

1. Per-thread prefilter table (84.8 → 69.6 s)
2. Bit packing at constant offsets (69.6 → 65.9 s)
3. **Dropping the run-time `TypeOK` check** (`pack` already validates the same thing; 21% on this spec)
4. Iterating domains by index (removes the `enc`/`dec` round trip; `idx_` call sites went from 50 to 1)
5. Building successors by copying the state once and overwriting only what changes (phase 1: 5.10 → 3.65 s)
6. Offloading lookups to the GPU (lookups 1.58 → 0.1 s, freeing the CPU meanwhile)
7. Prefetching the slot 12 entries ahead in the insert phase (insert 1.91 → 1.36 s)
8. Rebuilding the table shard by shard in parallel (serially it took 40% of a 6-second run)

### What did not work (do not retry)

- Grouping the fingerprint table into 64-byte buckets (3% slower; linear probing already touched adjacent slots)
- Buffering writes per shard before flushing (8% slower; the repacking costs more)
- Dispatching on condition values (match / jump tables). Few branches could be pruned on this spec
- Running phases 1 and 3 concurrently (7% slower; 20 threads on 10 cores)
- Pinning to efficiency cores (`taskpolicy -c background`; 11x wall time, 4x CPU)
- A larger per-thread prefilter table (16 → 21 bits only cut candidates from 356 to 343 million; duplicates come from
  distant states, so a thread cannot catch them locally)
- Growing the table 4x at a time (worse than 2x on wall time, CPU, and memory alike: 5.98 s / 36.9 s / 3.73 GB vs
  5.55 s / 36.5 s / 2.87 GB)
- Removing set-layout conversions by narrowing to "the expected type". The expected type is not always the declared
  one (during inference it can be a sibling branch's type), so correct specs got type errors. Narrowing only to the
  declared TypeOK type, with out-of-range values as errors, should get this back safely

### Bugs introduced by the speed work

- Unpacking read the fields after a runtime-sized set from the start of the bit string. The search continued from
  corrupted states, missed violations, and reported "no error". The benchmark spec has no such set
- Record fields were narrowed to "the expected type" (see above)
- With `-batched` / `-metal`, whether to grow the table was decided from the count at the start of a level. When a
  level split into many batches, later batches were inserted without counting earlier ones, and a shard filled up.
  Counts are now updated per batch (`tests/tlc/WideLevel.cfg`)
- With `-batched` / `-metal`, an error found in a later batch of a level stopped the level before that batch went
  through phases 2 and 3, so the trace could not be rebuilt and the distinct count came out low
  (`tests/tlc/BatchViol.cfg`)
- With `-batched` / `-metal` and a VIEW, phase 1 packed and checked every successor, so a state whose view had already
  been visited could be reported as out of type or as violating an invariant. TLC checks only new states. A candidate
  that would stop the search is now first looked up among the states visited or collected so far
  (`tests/tlc/ViewOutOfType.cfg`, `tests/tlc/ViewInv.cfg`)
