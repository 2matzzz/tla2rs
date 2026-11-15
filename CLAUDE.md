# CLAUDE.md

tla2rs is a compiler that takes a TLA+ spec and a TLC `.cfg` and generates a Rust model checker dedicated to that spec.
It has no crate dependencies.

## Common commands

- `cargo build --release` builds the compiler (`target/release/tla2rs`)
- `target/release/tla2rs Spec.tla [-config X.cfg] [-deadlock] [-workers N] [-memlimit MB] [-notrace] [-setcap N] [-seqcap N] [-fp128] [-metal] [-batched] [-dumpgraph FILE] [-lassocheck DIR] [--emit-only] [-o DIR]`
  - `-setcap` / `-seqcap` only set where the capacities of sets held as arrays and of sequences start; a value that
    outgrows one makes tla2rs build the checker again with more room (see "Capacities")
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
- `scripts/all.sh` cross-checks every configuration in `examples/` and `tests/tlc/` against TLC (all 1170 currently
  pass). Run it after every change, and also as `scripts/all.sh -batched` and `scripts/all.sh -metal` when you touch
  either search path (extra arguments are passed on to every run)
- `scripts/crosscheck.sh Spec.tla [X.cfg] [-deadlock]` cross-checks one configuration. Both TLC and tla2rs run with
  one worker, and it compares the verdict, generated and distinct state counts, the states left on
  TLC's queue (see "The states left on queue"), the counterexample (its states and
  the action of each step; see "Counterexamples"), exit code, the messages and printed lines (see "Messages and
  printed lines"), and the state graph (the set of states and the set of transitions; see "State graphs"). TLC runs with `-fp 0`, so its liveness counterexample is the same on every run and is
  compared too; where the checker prints a lasso of its own (see "Counterexamples"), TLC checks it instead (it runs
  TLC on the `-lassocheck` output). If TLC produces no verdict, the check fails. `all.sh` prints, after `ok`, the rule that
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
  those results; `JOBS` defaults to 2 for both. `-large` (`corpus.sh -large`, `expected.sh -corpus -large`) takes
  the models listed as `large` instead, one at a time unless `JOBS` says otherwise (see "Large models"), and
  `corpus.sh -only RE` only the models whose cfg path matches RE
- `scripts/bench.sh` measures speed against TLC on every configuration in `examples/` and `tests/tlc/`
  (`-corpus`: the corpus's selected models, `-norun` adds those marked norun): TLC with one worker, and tla2rs
  split into generation, a build from scratch (no build cache) and the checker alone with one worker, each with
  its peak memory, and the size of the generated code (`-auto` adds TLC's `-workers auto` and the checker's
  default workers). One row per configuration goes to `target/bench/results.tsv`, and `target/bench/summary.txt`
  lists, by ratio, those where tla2rs's check, or its total with the build, is slower than TLC. Rows are kept in
  `target/bench/rows/` and skipped by the next run (`-force` measures again). `JOBS` defaults to 1 for accurate
  times; with `JOBS=N`, `-serial` still runs the measured steps one at a time. It writes nothing outside
  `target/bench/` (and `target/community/`)

## Layout

| File | Role |
|---|---|
| `src/lexer.rs` `src/parser.rs` | Lexing and parsing. `/\` and `\/` bullet lists are delimited by column. Also SANY's precedence checks and string escapes (see "What SANY refuses"); an error marked with `lexer::SANY` makes the compiler stop with exit 150. The statements of a module are kept in the order written (`Module::units`). The positions TLC names actions by are kept in POS labels (`ast::POS`, see "Counterexamples") |
| `src/sany.rs` | SANY's checks of names (see "What SANY refuses"): what is in scope at each statement, what each module exports, labels and LAMBDA. Run on each module read from a file once the modules it extends and instantiates are loaded (`compile::load_parsed`), and on the modules nested in it. It collects every error of the module; when there are any, the module is parsed again with the positions SANY reports (`parser::parse_module_sany`) and checked again for SANY's report |
| `src/cfg.rs` | `.cfg` files (SPECIFICATION / INIT / NEXT / CONSTANT, including `<-` / INVARIANT / PROPERTY / CONSTRAINT / ACTION_CONSTRAINT / VIEW / SYMMETRY / CHECK_DEADLOCK; TYPE / TYPE_CONSTRAINT are ignored as in TLC) |
| `src/expand.rs` | Inlines every operator definition. Bound variables are renamed, and each EXCEPT's `@` gets a unique name too. Call sites are kept as `Expr::Label`. A subexpression named by label or position (`Op!lab`, `Op!1`, `Op!(e)`) is found in the definition as written and expanded as a definition with the bound variables and label parameters on the way as extra parameters (`subexpr`). Operator parameters are bound to the operator (or LAMBDA) passed, with its environment. A RECURSIVE operator called again inside its own expansion becomes `Expr::RecCall`, evaluated at compile time or compiled into a Rust function (`Gen::rec_fn`, which takes the variables it reads, primed or not, as arguments); it is expanded once per combination of operator arguments. For the constant evaluator (`expand_def_bound`) and for code generation (`expand_def_code`), arguments and LET definitions are bound to names instead (see "Arguments written out at each use") |
| `src/value.rs` | Compile-time values and constant evaluation (set order follows TLC: smaller sets first). A record and the function over its field names (`:>`, `@@`, a function constructor, EXCEPT) are one value: a record compares as that function, with the field names as the atoms of `Atoms::register` (`tests/tlc/RecFunEq`). In an EXCEPT path `.a` of such a function is `["a"]`, and a name that is no string of the spec is outside its domain (`tests/tlc/ExceptDotFun`). The names a BIND label binds are evaluated where first used and kept (`register_bound`, `eval_bound`) |
| `src/types.rs` | Finite types `Ty`. A set whose element type has at most 128 values is a `u128` bitmask; otherwise it is an `SSet` (sorted fixed-size array). `Opt` is an optional field of a record whose variants have different fields. A value that is a record or a model value (`[op : S] \cup {NoVal}`) is a record type whose fields are all optional, with the model values in a field of its own (`ATOM_FIELD`); a type invariant giving such a type is checked on every state, since packing does not check which records it lists. A value that is a model value or a value of another kind (a sequence, tuple, set, function, bag or boolean: `Seq(S) \cup {NoVal}`, `SUBSET P \cup P`) is such a record type too, with that value in a field of its own (`VAL_FIELD`, named to sort before `ATOM_FIELD`, so model values come first as in TLC); an operation that takes the value apart (application, DOMAIN, iteration, set operations, Cardinality, the sequence operators) takes it out of that field (`Gen::gen_val`), and fails on a model value. A record type with optional fields of at most 4096 values is numbered in TLC's order of records (`tlc_perm`: the number of fields first), so sets of such records print, CHOOSE and enumerate as in TLC. A record's fields are kept in TLC's order of names (`field_cmp`: the order TLC first creates each name, from `compile::tlc_string_ranks`), which is how TLC compares and prints records. A tuple is a `Rec` with fields `#00001`, `#00002`, ... (`tuple_ty`); a record of more than 12 fields is held as nested groups of 12 (`rec_build`, `rec_field`), since Rust tuples implement `Eq`/`Hash`/`Ord` only up to 12 elements. `IntAtom` holds integers and atoms (model values, also strings) in one `i64` (atom a is `i64::MIN + a`). `Seq` is a sequence (`Sq`, at most QCAP elements; `seq_cap` derives QCAP, from `src/seqlen.rs` when no bound is written). An `SSet` holds at most SCAP elements, and never more than its element type has values (`set_cap`); both capacities grow at run time (see "Capacities"). `Bag` is a bag, a count per element (packed as a function to 0..BIG). `PFun` is a function over part of a type (an optional value per element); functions over different domains (other than 1..n, which are sequences) join into one, and so does the empty function (`[x \in {} |-> e]`, typed as `<<>>`) with one over a domain other than 1..n (`tests/tlc/EmptyFunJoin`). Over a domain type of more than `DENSE_MAX` (65536) values, or one that is not enumerable, both are sparse (`is_sparse_fun`): an `SSet` of <<key, value>> tuples (`fun_pairs`), which sorts by key, so lookups are binary searches and packing, SYMMETRY and equality are those of sparse sets. `BIG` is an unbounded integer |
| `src/codegen.rs` | Rust generation. Actions are continuation-passing, threading "the remaining conjuncts". The next-state relation is first split into actions as TLC splits it, which names the successors in traces (`gen_split`). As in TLC, `\/` and `\E` branch while some variable is still unassigned. `\A` over a set from the state walks the elements at run time (`gen_forall`). A constant set of more than 1024 elements built from `[D -> R]`, `\X`, `[f : S]` and SUBSET is enumerated from its parts where the checker iterates over it (`big_set_iter`, see "Large constant sets"), and a recursive operator that assigns variables, called with arguments from the state, becomes a Rust function returning the states its body builds (`gen_rec_action`). A name a BIND label binds is a `OnceCell` computed on first use (`gen_bind`). A record applied to, or updated at, a key of strings that is not constant reads or writes the field the key names at run time; a key that names none is TLC's evaluation error when applied and, in an EXCEPT, changes nothing and warns (`rec_apply`, `split_dynamic_index`; `tests/tlc/RecVarKey`) |
| `src/compile.rs` | The overall pipeline. Types come from `x \in S` in TypeDecl / TypeOK; for variables without one (or whose S gives no type, such as `[D -> Int]`) they are inferred from Init/Next (`infer_types`; an integer range that settles within a few rounds stays finite, one that keeps growing is widened to unbounded). When the types from TypeOK fail in Init or Next (a module that extends another and adds a record field its type invariant lacks), the spec is compiled again with every type inferred (`INFER_ALL`). ASSUMEs are evaluated here. `instantiate` turns each definition of an INSTANCE'd module into a hidden definition that takes the module's constants and variables as leading parameters, so expansion substitutes them without capture (a call site's arguments are only a trace: whether it is constant is decided by its body, `Gen::is_const`). A name a definition binds (a parameter, bound variable or LET definition) stays its own where the module defines the same name later, and a parameter named like a name the substitutions read, or like a parameter of the instance, is renamed in the visible definition (`InstRename`; `tests/tlc/InstShadow`, `InstShadowParam`). `Nat <- D`, `Int <- D` and `Seq <- D` in the cfg define those operators of the standard modules, as TLC replaces them |
| `src/community.rs` | The modules of the CommunityModules tla2rs provides (see "CommunityModules"): TLA+ source written for tla2rs, loaded by `compile::find_module` when no module of that name is next to the spec |
| `src/std_modules.rs` | The identifiers and strings of TLC's standard modules in TLC's reading order (generated from tla2tools.jar), for ordering strings as TLC does; and where SANY places each definition they export (`STD_DEFS`), for its report of a name that clashes with one |
| `src/community_modules.rs` | The identifiers and strings of the CommunityModules' modules tla2rs provides, as TLC reads the release's files (generated from them), for ordering strings as TLC does |
| `src/seqlen.rs` | Without a written length bound, runs Init and Next over sequence lengths (with `Len(q) < k` tests in a conjunction as bounds) until the variables' lengths settle, giving QCAP |
| `src/live.rs` `src/ltl.rs` | Liveness at compile time: properties become formulas over atoms (state predicates, ENABLED, action predicates), the negation (with the spec's other temporal conjuncts) becomes a Büchi automaton by tableau (`ltl.rs`), and fairness becomes per-condition ENABLED / step functions. An automaton may have 4096 states and take 256 steps per state to build (a conjunction of n `[]<>` formulas branches 2^n ways at each state); a larger one is split as TLC splits its plan: each disjunct of the normal form is checked as a property of its own, its `[]<>S`, `[]<>A` and `<>[]A` parts as conditions on the components of the product (a state, a step in it, every step of the cycle) and only the rest in an automaton (`split_disjuncts`; `tests/tlc/LiveAssumed`: 13 `[]<>` conjuncts in the spec, for which building one automaton gave up after 400 s with more than 4096 states) |
| `src/graph.rs` | `--graph`: reduces a state graph file to its canonical form and hashes it (SHA-256 written out, as there are no crate dependencies) |
| `src/trace.rs` | `--trace`: reduces the counterexample in an output of TLC or of a checker to its canonical form and hashes it |
| `src/messages.rs` | `--messages`: reduces the messages and printed lines in an output of TLC or of a checker to their canonical form and hashes it, and its error lines (see "Messages and printed lines") |
| `src/pcal.rs` | TLC's check of the checksums a PlusCal translator wrote: the warnings for the root module and the modules it extends, and the algorithm's syntax tree as TLC's translator prints it (see "PlusCal checksums") |
| `src/lasso.rs` | The spec's parts written back as TLA+ (`tla`) for the module `-lassocheck` writes (see "Counterexamples") |
| `src/ppr.rs` | TLC's pretty printer for values (`ppr`, ported from `tlc2.pprint` and checked against TLC's on 25,000 random values): used by the compiler for what Print and PrintT print when TLC starts, and pasted into every generated checker, which prints states and printed values with it |
| `src/runtime.rs` | The runtime pasted into generated code: level-by-level parallel BFS (threads started once per search take pieces of a level as they finish, `Pool`), bit-packed states, 64-bit fingerprints (with VIEW / SYMMETRY, of the canonical key), and liveness (per state and edge, which property atoms and fairness conditions hold; then an SCC search in the product with each property's automaton, with WF / SF as conditions on components, one property per thread, the first violated in order reported; counterexamples are lassos). Also the `-dumpgraph` output. `LIVE_SIM_RT` is pasted, with hooks that `compile.rs` writes into the runtime, only for a spec that prints (see "Messages and printed lines") |

### Memory use (`runtime.rs`)

There are two paths, depending on what is checked.

| | What is kept | Per state |
|---|---|---|
| Invariants only (`run_safety`) | The fingerprint and the fingerprint of the state it was first reached from, plus the states of the current and next level | 16 bytes (8 with `-notrace`) |
| With temporal properties (`run_liveness`) | The whole state graph (states, parents, edges with their atom and fairness bits) | State width + a few dozen bytes, plus hash maps over the product with each property's automaton during the search |

The safety path never keeps states. A counterexample is rebuilt by walking fingerprints back to an initial state and
replaying `next` from there (`fp_chain` → `replay`). Liveness needs the whole graph for the SCC search. It is kept in
columns (`Col`: the states, their parents, and `LiveGraph`: where each state's edges start, the edges' targets, and
class numbers into tables of the distinct (state atoms, enabled fairness, stuttering atoms) and (label, action atoms,
fairness steps), a byte each while there are at most 256, `ClassCol`). Once the columns hold more than `-memlimit`,
each column that grows moves to an unlinked temp file in `-tmpdir` that is mapped for reading, so the kernel's page
cache holds what fits. A level is expanded a slice of `LEVEL_SLICE` states at a time, so what the threads find before
it is merged stays small. The search in the product with a property's automaton numbers the product nodes in BFS
order in arrays (`Rank`, dense over all product nodes for an automaton of at most 16 nodes), and its Tarjan keeps a
cursor per node on its stack (`At`) instead of the node's successors; the BFS keeps only each node's parent, and the
label of a step on the counterexample's prefix is found again from the parent's successors. Under a VIEW or a SYMMETRY the verdict comes from
TLC's liveness graph instead (see "Counterexamples"), which `tlc_lasso` builds in memory: per node of a state and a
particle, a vector of its transitions.

The parts of a level beyond `-memlimit` spill to a temp file. The file is unlinked as soon as it is opened, so nothing is
left behind even when the checker is killed. Without `-tmpdir` it goes to the system's temp dir, or, when that is a
tmpfs (`/tmp` on many Linux systems, where a file takes memory), to the directory of the checker's executable
(`default_tmpdir`). A failed read of the spilled queue is a fatal error: skipping it could turn
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
(`main.rs`) prints `tla2rs: a set grew beyond N elements; checking again from the start with room for M`, compiles
with that capacity, builds (the build cache applies) and runs again from the start. M is twice N the first time a kind
grows, four times N the second, eight times the third and so on (a value that keeps outgrowing its capacity is
usually far beyond it, and each build costs seconds), and at least what the value needs, which the checker writes to the file `TLA2RS_NEED` names: one more
than N, or the size of a whole union or concatenation. `TLA2RS_GROW` tells the
checker which kinds may still grow (both stop at 65535, `types::MAX_CAP`); run directly, or at the maximum, the
checker reports an evaluation error as before. Output before the line is repeated by the next run, so
`crosscheck.sh` compares only what follows the last such line, and says how many rebuilds there were. A spec that
stays within its capacities builds and runs exactly as before.
A constant filter `{x \in S : P}` too large to compute when compiling is no such array where it is only iterated
over (as in `v \in` it in Init): the checker computes it once into a vector (`tests/tlc/Staircase`).

ToString of a value from the state needs the string of every value it can make numbered when the checker is built
(`Gen::gen`, `("ToString", [x])`). A type with more values than strings can still be added (integers whose range the
type inference leaves unbounded, as under `n < 3 /\ n' = n + 1`, which it does not read) gets the strings of the
values whose integers lie in the widest window nearest 0 (`types::int_window`; sets held as arrays of at most SCAP
elements) that gives at most 256 of them (`TOSTR_START`, per type by its Debug text: `Gen::tostr_window`). A value
outside makes the checker write its type to the file `TLA2RS_NEED` names and exit with 73 (`tostring_miss`, emitted
only where used); tla2rs prints `tla2rs: ToString met a value whose string is not among the N listed for its type;
checking again from the start with room for M` and builds again with M for that type, growing as capacities do,
until no wider window fits in the strings that can be added, where the miss is an evaluation error
(`tests/tlc/ToStringWide*`: 3, 3, 2 and 0 rebuilds). A type with few enough values is listed whole, as before.
An empty function over part of a type (`PFun`) prints `<< >>` in a checker, which is TLC's text for one it holds
as a function, so ToString lists that text for it (`Gen::shows_empty_fun`; `tests/tlc/EmptyFunToString*`). The
empty tuple and the empty function over a constant empty set (`[x \in {} |-> e]`) share one type with no fields,
which the checker prints by what the spec may build (`Gen::empty_text`): `<< >>` in a spec that builds no empty
tuple (`<<>>`, Tail, SubSeq, `\o`, SelectSeq or SortSeq in any definition, or a constant holding one:
`compile::makes_empty_tuples`), and `<<>>` in one that builds no such empty function (`[x \in S |-> e]`, `[S -> T]`
or Permutations(S) over an S not written to have an element, or `@@` of two values that may both be empty:
`compile::makes_empty_funs`). This holds alone and inside sets, records, tuples, functions and optional fields of
records, in states, Print, PrintT and ToString (`tests/tlc/EmptyTupleShow*`, `EmptyFunShow*`). Where TLC may hold a
value of either type as a tuple, which it prints `<<>>` when empty (a function over part of a type in a spec that may
build an empty tuple, the type with no fields in one that may build both), the value has a bit of shape for it (see
"State graphs"; `Gen::tuple_at`): set by `<<>>` and kept where the value is copied, taken out of a set or put in one,
while `:>`, `@@` and a function constructor build a function. The bit is no part of the value, which TLC finds equal
to the empty function: the first state reached keeps its text, and a set holding both keeps the one written first,
as in TLC (`tests/tlc/EmptyBothShow*`). ToString lists both texts for such a value. ToString of a bag from the state
is refused when compiling: its counts are unbounded, and the window of values nearest 0 does not cut them.

Measured on the models that used to need `-setcap` / `-seqcap` (rebuilds, and the capacity they end with):

| Model | Needed | Now |
|---|---|---|
| `MCCheckpointCoordinationFailure`, `ReadersWriters` `MC`, `AllocatorImplementation`, `AllocatorRefinement`, `SchedulingAllocator` | `-seqcap` 8, 6, 6, 6, 3 | No rebuild: sequences start at 8 |
| `MCDisruptor_MPMC`, `-liveliness`, `MCDisruptor_SPMC` | `-seqcap 10` | 1 rebuild (16) |
| `SlidingPuzzles` | `-setcap 64` | No rebuild: Init assigns a constant set of 10 |
| `SimplifiedFastPaxos` `Paxos` | `-setcap 1024` | 3 rebuilds (512; its message set holds more than 128): 14 s in all, the search 0.7 s (2.1 s with 1024) |
| `SimplifiedFastPaxos` `FastPaxos` (skipped in the corpus) | | 3 rebuilds (512): 32 s in all with one worker (four builds of 7 s, the search 4.5 s), TLC 37 s; twice and then four times each time, it took 4 rebuilds to 1024 and 39 s |
| `tests/tlc/SubBags` | `-setcap 32` | 1 rebuild (16) |
| `tests/tlc/LongSeq` | `-seqcap 140 -setcap 140` | Sequences settle at 140 (`seqlen.rs`); `DOMAIN q` takes 3 rebuilds (sets of `1..140`, capped at 140) |
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
tla2rs only, and `\* crosscheck: args -continue` passes TLC's options to both (see "TLC's options"). The default stays strict: generated-count mismatches have caught real bugs before (a difference in when
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
and 5), and those of the CommunityModules' modules tla2rs provides in `src/community_modules.rs` (generated from the
release's files, with the modules each reads; `CmNames`). TLC orders every model value before every string (`{"zz", m1}` prints as `{m1, "zz"}`, a function over both
lists the model values first, CHOOSE picks `m1`; `tests/tlc/ModelStr*`), so model values get the lower atom numbers.

Strings made by operations (`\o`, `Append`, `Head`, `Tail` and `SubSeq` on strings, `ToString`) come after those, in
the order TLC first makes them. Measured on TLC 2.19 (`tests/tlc/StrMade*`), with one worker:

- When it starts, TLC evaluates the constants, every definition of constant level without arguments (used or not),
  the constant invariants and properties, the sets of the `\E` it splits the next-state relation through (once,
  `StrMadeSplit`; `Gen::split_strs`), and the ASSUMEs, in that order; the strings these make come first
  (`StrMadeStart`: an unused `Words == {"c" \o w : w \in {"a", "b"}}` puts `"ca"` before `"cb"`)
- Then the strings made while exploring, in the order the search makes them: a string made and dropped counts (a
  comparison, a branch that fails later), and so does one made by a constant expression inside an action or an
  invariant, which TLC evaluates there each time (`StrMadeConst`). TLC checks the invariants on each successor as
  soon as it computes it, so what they make comes before what the next successors make (`StrMadeInv`)
- A string equal to a name or number of a module was created when TLC parsed it and keeps that place
  (`StrMadeName`; `StrMadeToString`: `ToString(1)` is `"1"`, a number in the TLC module)

The checker's strings are 16-bit ids fixed when it is built (and sets of them bit masks over those ids), so it cannot
number a string when it makes one. tla2rs numbers them in an order measured instead:

- The field names of the records the spec writes are identifiers TLC created when it parsed them, so they are
  numbered with the strings TLC knows from parsing, and DOMAIN of such a record evaluated when compiling gives them
  in that order, not alphabetically (`CmJson`: CHOOSE over `DOMAIN [b |-> 1, a |-> 2]` picks `"b"`)
- The compiler evaluates the constant definitions that can make strings (`makes_strings`), the constant invariants
  and properties and the ASSUMEs in TLC's order, noting the strings made (`Atoms::made`), and numbers those right after
  the strings TLC knows from parsing. That order is known only after evaluating, which itself iterates sets in the
  order of their strings, so `compile` compiles again until it does not change (`MADE_ORDER`, `Startup::made`)
- The strings the checker may make while exploring are numbered from `TRACK_FROM`, first in the order a checker built
  before made them, then as the compiler meets them. Code generation notes each such string the checker makes
  (`Gen::note_made` for the operations on strings from the state and ToString, `Gen::note_folded` for a constant
  expression TLC evaluates there: as a value, a set a quantifier ranges over, or a set tested for membership;
  `Gen::fold_notes` for one the compiler evaluates without generating code for it: a condition of an action or of
  an IF, the set of a `\A` that assigns variables, and the argument of a recursive operator unrolled in an action
  when its body reads the parameter, since TLC evaluates an argument only there; `StrMadeCond*`).
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
- The order of those strings shows only where they are enumerated, chosen from or printed together: in a set, a bag
  or the domain of a function. When no type of the generated code (nor of a variable) holds such a string there
  (`Gen::made_order_shows`), they are only compared for equality, printed alone and kept, so the checker notes
  nothing and is built once (`ShowState*`: ToString of values from the state compared with literals)

Not followed:

- With several workers the order depends on thread scheduling: CHOOSE over `{ToString(n) \o "w" : n \in 1..2000}`
  after the search created those strings gave `"4w"`, `"1w"`, `"2w"` and `"4w"` in four runs with `-workers 4`, and
  `"1w"` every time with one worker. The checker notes nothing then and keeps the order it was built with
- A string made by a constant expression that the compiler evaluates elsewhere than above (the size of the set of a
  split `\E`, say), and the characters TLC makes when it takes a string apart into a tuple (`SelectSeq`, `SortSeq`,
  a string compared with a tuple), are numbered as the compiler meets them and not noted

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
- A NEXT of constant level (`FALSE`, `1 = 2`) is refused when TLC reads the spec (`The next state action Next cannot
  be a constant.`, exit 151; `[][FALSE]_x` in a SPECIFICATION is not, and deadlocks). A next-state relation that TLC
  splits into no action (`\E` over an empty constant set, also in `[][...]_v`) is not refused: TLC computes and
  checks the initial states and then stops with `No next state actions defined to generate successor states
  from.` (exit 75), as for a spec without a next-state action (`NO_NEXT` in the checker; `tests/tlc/NoActions*`)
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

TLC stops with exit 150 before checking anything when SANY refuses a spec (its report on a parse error,
a level error or semantic errors is reproduced word for word, see "Messages and printed lines"). tla2rs repeats these of SANY's checks
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
  minus as `-.`, `:>`). SANY does not look at the arguments of an operator it cannot find (`(1 :> 0) @@ (2 :> 0)`
  without TLC reports `@@` only). The sets of `\E x \in S, y \in T` are read outside the quantifier, so T cannot
  use x. An operator that takes arguments, named without them, is refused (`The operator F requires 1 arguments.`),
  except as an argument, and so is a call with another number of arguments, whose arguments SANY then does not look
  at; a RECURSIVE declaration needs a definition
- No declaration, definition, parameter, LET definition, bound variable or LAMBDA parameter may reuse a name in
  scope. A definition is checked once its parameters are in scope (`F(F)` is refused: `Operator F already defined
  or declared.`, and `f[f \in S] == e` gives `Function name`), then its body; after the body, a clash with a
  definition of as many parameters is only a warning, any other a second error (`Multiply-defined symbol`, not for a
  function definition), and the definition is then not in scope. A definition's own name is not in its body (`F ==
  \E F \in S : P` is accepted), unless it is a function definition `f[x \in S] == e` or declared RECURSIVE. The same
  definition reached twice is one symbol: a module extended along two paths, or a module without constants or
  variables both extended and instantiated (or instantiated twice). An INSTANCE of a module with constants or
  variables gives new definitions, so instantiating it twice without names is refused. Two different definitions
  of one name in two extended modules are only a warning for SANY (`Semantic errors in global context:`, before the
  module's own warnings, and again for each module that extends that one), and TLC uses the one extended first
  (`tests/tlc/SanyTwoDefs*`; `compile::load_parsed` keeps it)
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
  (`Expander::check_subexprs`, also of a LET definition: `RejSanySubLet*`), also in definitions nothing uses. One whose operator is not a definition (a
  CONSTANT, VARIABLE, parameter or bound variable: `Cannot take subexpression of `x'.`), or is named without the
  arguments it takes (`Op!1`, `Lab!lab`: `The operator Op requires 1 arguments.`, placed from the name to the last
  selector) is refused (`tests/tlc/RejSanySubOp`)
- What an operator is passed must fit the parameter (`Walker::args`, from the number of arguments each parameter
  takes: `Sym::params`; `tests/tlc/RejSanyOpArg*`): where the parameter takes none, an operator's name that takes
  some (`The operator Len requires 1 arguments.`) or a LAMBDA (`LAMBDA expression used where an expression is
  required.`); where it takes some, a name of another arity (`Expected arity 1 but found operator of arity 0.`, also a
  CONSTANT or VARIABLE), a LAMBDA of another arity (placed at the operator's name) or any other expression (`An
  expression appears as argument number 1 ...`, whose own names SANY does not look at), each followed, after the
  other arguments' errors, by `Argument number 1 to operator 'B' should be a 1-parameter operator.` placed from the
  name to the closing parenthesis. This covers the operators of the module, LET, the standard modules (SelectSeq,
  SortSeq and BagOfAll take operators) and of a named INSTANCE without parameters (`I!Op`, also named alone). The
  parser gives each argument its position in an ARG_AT label (`parser::ARG_AT`) when it parses again for SANY's report
- A CONSTANT or VARIABLE declared again as the same kind (`VARIABLE x, x`, also one of an extended module) is a
  warning (`Multiple declarations or definitions for symbol x.`), and the two are one; as another kind it is an
  error (`tests/tlc/SanyDupDecl`, `RejSanyDupKind`). SANY prints the warnings of a module without errors and goes on
  (`sany::take_warnings`, printed first by `compile::Startup`)
- String escapes other than `\\ \" \n \t \r \f`

LOCAL definitions of a module read for EXTENDS or INSTANCE are renamed (`compile::hide_locals`), since they are not
in scope in the module that reads it, which may define the same name (`tests/tlc/SanyScope`, `SanyLocalRec`).

Not repeated: names inside `\EE` and `\AA` (their bound variables are not kept, so `D == \EE y : y = Unknown` in a
definition nothing uses passes, where SANY reports `Unknown operator`; those of `\E x : P`, `\A x : P`
and `CHOOSE x : P` without a set are checked from `parser::unbounded_body`, `tests/tlc/RejSanyUnbounded`); the WITH
substitutions of an INSTANCE inside LET; what is passed to an operator of an INSTANCE with parameters; and SANY's
checks of other kinds (levels outside temporal formulas). The warnings in global context are not printed when the
module has errors. A positional name that names nothing is reported only when the module has no other semantic
error, and only the first one (SANY reports them all, among the others in the order of the module).

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
  until a new successor fails an invariant or any fails an action property. `eval_replay` repeats this
  (`tests/tlc/BagOps-Lit.cfg`, `FunMember-NotFun.cfg`, `StrSeqOps-StrLeft.cfg` need it), and counts the states it
  adds, which TLC queues (`AgainCount`; see "Messages and printed lines")
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
- `<<>>` is read as `<< >>`. TLC prints the empty function as `<< >>` when it is held as a function and as `<<>>`
  when it is held as a tuple, depending on the expression that built it (`DynDomain`, `NatDom`, `PartFuns`,
  `SparseFun`, ...). A checker follows this where it follows intervals (below), so the reading matters only where it
  does not
- Duplicate edges collapse, and dashed stuttering edges are dropped (they are not transitions of the next-state
  relation)
- Intervals are compared as printed. TLC prints a value in the form it holds it, so a variable assigned `1..3`
  prints as `1..3` until an operation turns it into an enumerated set (measured on the corpus's
  `DiningPhilosophers`). The form depends on how the value was built, not on the value. Measured on TLC 2.19
  (`tests/tlc/IntervalShow`): `s = 1..3` prints `1..3` and, after `s' = {1, 2, 3}`, the same value prints `{1, 2,
  3}`; a function built as `[i \in 1..2 |-> 1..i]` prints `<<1..1, 1..2>>`, and keeps `1..2` through an EXCEPT of
  the other entry; `s \cup {4}` enumerates; an empty interval prints `{}`. A state graph labels each state by the
  first way it was reached. More measured on TLC 2.19 (`tests/tlc/IntervalConst`, `EmptySeqShow`): an interval
  keeps its form inside a tuple, record, function or set and when taken out again (application, CHOOSE, a bound
  variable, Head, Tail, SubSeq, `\o`, SelectSeq); a set keeps the first of equal elements as written (`{1..2, {1,
  2}}` prints `{1..2}`, `\cup` keeps the left one); `(1..2) \cap (1..2)` enumerates, and so does DOMAIN of a function
  built by `[x \in S |-> e]`; an empty function built by `[x \in S |-> e]`, `:>` or `@@` prints `<< >>`, and an empty
  tuple from `<<>>`, Tail, SubSeq, `\o` or SelectSeq prints `<<>>`. The same holds inside the values a state holds
  (`tests/tlc/IntervalHeld`, `IntervalCase`): an interval in a function, sequence or set keeps its form through
  EXCEPT (also one that reads `@`), Append, Tail, SubSeq, `\o`, `\cup`, `\cap`, `\` and a filter (`\cup` and `\cap`
  keep the elements of their left side), and when taken out again (application, Head, CHOOSE, `\E`, `\in`); CASE
  gives the form of the arm taken. The compiler follows these forms for the values it evaluates (`value::Form`):
  what TLC prints when it starts, ToString of a constant, and a constant printed while exploring. A checker follows
  them for the variables that some assignment may give such a value (`Gen::plan_shapes`): beside each state it keeps
  a shape, laid out by `Gen::shape_slots`: one bit per set of integers (set while TLC holds it as an interval); one
  per sequence (set while TLC holds it as a function), then those of its elements up to QCAP when they fit; those
  of each value of a function over integers, model values or strings, also over part of them (`:>`, `@@`); one per
  interval a set of sets of integers may hold (when its elements range over at most 10 integers); for another set
  whose elements have bits of shape, those of the element in each slot (its index in the array, or its number in
  the element type for a bitmask: `Gen::set_find`), so records, tuples and sequences in a set keep their forms; and
  those of the fields of a record or tuple. Each shaped variable takes its bits in one word, the first with room
  (the shape is a word per group of variables, kept after the state in the queue); words are 64 bits, or 128 when
  a variable needs more (`Gen::sh_bits`; `tests/tlc/IntervalWide`). A variable gets its shape from the expression
  assigned, also from a constant (a constant function's value, CHOOSE over a constant set, a constant set of records)
  and, for `x' \in S`, CHOOSE from S and a name bound by `\E` over S, from the element taken when S is constant,
  written as a set of elements or a set from the state (`tests/tlc/IntervalElem`, `IntervalExists`,
  `IntervalSetElem`). A function constructor gives each value the shape its body has there, and an index from the
  state into a tuple whose elements are laid out alike finds its part. SelectSeq keeps the shapes of the elements it
  keeps (`tests/tlc/IntervalSelect`). An IF whose condition prints is evaluated once for both the value and its
  shape: assigned whole, by evaluating the condition first; inside a value (where it is evaluated at most once),
  the checker keeps its outcome while computing the value and the shape reads it, also where the shape evaluates
  parts of the value again (`Gen::if_sites`; `IntervalSelect`, `IntervalMerge`). The shape is no part of the
  fingerprint, so the first state reached keeps its form, as in TLC. States, `Print`, `PrintT` and `ToString` use
  it, so `ToString(s)` makes `"1..2"` where TLC does, and an invariant comparing that text holds in both
  (`tests/tlc/IntervalToString`); a tuple written out in `Print` or `PrintT` whose parts have more bits than one
  shape holds prints part by part. Not followed, and printed as enumerated sets and `<<>>`: a variable whose shape
  needs more than 128 bits (a function over more than 128 values, a set of records holding intervals once its
  capacity grows past 128 / the bits of an element, a bitmask set whose element type has more values than that); a
  record of variants (optional fields) or a value mixed with model values; a function over a domain of other values
  (booleans, tuples, records) or of more than 65536; the elements of a set built by `{e : x \in S}` when e's shape
  depends on x; an index from the state into a tuple whose elements are laid out differently; an IF whose condition
  prints under a bound variable (in a function constructor, a set map, a quantifier); a set of records holding
  intervals inside a constant of another structure; and the operators of the CommunityModules tla2rs provides (TLC
  computes many of them in Java, which builds values in forms of its own; `community::defines`). No configuration
  has one of these

Where the graph cannot be compared as a whole, `crosscheck.sh` compares less, and says so after `MATCH` (the counts
are for the 483 configurations at the time of writing):

| Rule | Applies to | Compared |
|---|---|---|
| TLC did not end the file (automatic: no closing `}`) | 56 (stops in or before the initial states, and SANY or temporal refusals) | Not the graph; verdict, counts and exit code as before |
| The cfg's own `-dump`, and TLC's file is empty (automatic: it stopped before writing what it had buffered) | `OptDumpInit` | Not the dump |
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

A liveness counterexample (lasso) depends on TLC's fingerprints: TLC takes the successors of a state in its liveness
graph out of a hash set keyed by fingerprint (`tlc2.util.SetOfStates`), and picks the fingerprint polynomial at
random on each run (for `tests/tlc/LiveForms-NoneImplies.cfg`, ten runs gave 5 states eight times and 4 states
twice). With `-fp 0` it is the same on every run, so `crosscheck.sh` runs TLC that way and compares the lasso like
any other counterexample. The checker follows TLC's search on its own graph to print the same lasso (`tlc_lasso` in
the runtime; `tlc_live` in `src/live.rs` writes TLC's plan as `TLC_LIVE`). What TLC 2.19 does, read from
`tlc2.tool.liveness` and measured on the liveness violations of `examples/` and `tests/tlc/`:

- Its plan (`Liveness.processLiveness`): fairness /\ ~(the properties) in disjunctive normal form, each disjunct a
  possible error model of `<>[]A` parts (EAAction), `[]<>S` parts (AEState) and `[]<>A` parts (AEAction), the
  conjunction of its other parts a formula for a tableau. The disjuncts with equal tableau formulas (or none) make an
  order of solution, in the order first met, with predicates numbered of its own; the orders are searched in turn,
  and within one its models. TLC numbers each state predicate it makes from the formula (`tagExpr`), and two are
  equal only when their numbers are, also when written alike (the second field of `TExpr::State` in `src/live.rs`)
- The tableau (`TBGraph`, `TBPar`; `tableau` in `src/live.rs`): the formula made binary (`makeBinary`: a junction
  split into halves), its particles (`particleClosure`: the alpha rules of `/\` and `[]`, then the first beta rule
  of `\/` or `<>` that applies splits it in two, the particles of the first branch not among the second's coming
  first), then for each particle in turn the particles of the bodies of its `()` formulas, each new one appended.
  A node pairs a state with a particle whose state predicates hold in it (boolean constants are ignored). The
  promises are the `<>` subformulas; a particle fulfils `<>P` when it lacks `<>P` or has `P`
- The liveness graph: the initial states in the order found; each state, expanded in BFS order, gets one transition
  per distinct successor in the model and one to itself (stuttering), in the order of the slots of a hash table of
  states (`SetOfStates`: linear probing from `(int) fp & 0x7FFFFFFF` modulo the length, which starts at 16 times a
  multiplier and grows to 2n+1 when half full, by inserting the old slots in order; the multiplier grows by one for
  the next state each time a set had to grow). Duplicates and self-loops count as puts at their place among the
  successors, since a put checks the threshold first. With a tableau (`LiveCheck.TableauLiveChecker`,
  `tableau_graph` in the runtime) the initial nodes are each initial state with each of the formula's particles
  that hold in it; each state, expanded in BFS order, gives each of its nodes recorded so far (in the order
  recorded) a transition per successor in the set's order and per particle that can follow and holds in it, unless
  the node has that transition already. A node new to a state already expanded gets its transitions at once, depth
  first: the stuttering step first, then the successors in the order the actions generate them
  (`Tool.getNextStates`, without the set); TLC writes it only if it has some, and leaves a node it did not write out
  of the search. The dot file of `-dump dot` shows the latter dotted but not the stuttering ones (read with jdb in
  `LiveWorker`: `tests/tlc/Live-SpecSpin-Starve` ends on such a step).
  The fingerprint is TLC's (`FP64` over each value's bytes: a
  tag, the size, the elements in TLC's order; functions, tuples and records all as pairs; strings by their
  characters; a model value by the number TLC gives its name, `TLC_MODEL_VALUES`). TLC numbers names from 1 as it
  first creates them (`UniqueString`), the strings and model values of the cfg first, in the order written (measured
  with `-dump dot`, whose nodes are fingerprints: `P = {a, b}` gives a 1 and b 2, `Q = "zz"`, `R = idle` and then
  `P = {b, a}` give idle 2, b 3, a 4). Under a SYMMETRY the fingerprint is that of the smallest permuted state in
  TLC's order of values (`TLCStateMut.fingerPrint`), and a state of the lasso is rebuilt as the first successor with
  the next node's fingerprint, so the cycle can return to another member of its start's class (`LiveSymTurn`)
- The search (`LiveWorker.checkSccs`): from each initial state, then from each node a skipped step led to, a
  depth-first search that pushes all successors at once and keeps a low link per frame, skipping a step that breaks
  the model's EAAction (it queues the target instead). A component popped from the stack is checked if it has more
  than one node or its node's self-loop keeps EAAction; the first one with every AEState and AEAction (on steps
  within it that keep EAAction), with every promise fulfilled by a node of it, is the counterexample
- The path to it (`DiskGraph.getPath`, `TableauDiskGraph.getPath`): breadth first from the initial nodes,
  successors in slot order, a node's step to itself skipped
- The cycle (`LiveWorker.dfsPostFix`, then `bfsPostFix`): from the component's start, take the first step that
  fulfils a []<> part not yet fulfilled (a node fulfils []<>S parts and promises), else go on to an unvisited node
  (backtracking when there is none), until all are fulfilled; then breadth first back to the start, over states:
  each state takes the steps of all its nodes in the component, and a state is entered when any node of it is in
  the component. A cycle that comes back to the start's state on another node prints as stuttering
  (`tests/tlc/LiveTab-NestedEv`). Each state is rebuilt from the one before by the first action that yields it. The lasso ends `Stuttering` when it ends on the start, otherwise `Back to state N`, N the
  number of the start

Under a VIEW or a SYMMETRY TLC's liveness graph is not the folded state graph, and a search on the folded graph can
give another verdict (measured on TLC 2.19, `tests/tlc/LiveFold`; read from `SetOfStates.put`, `LiveCheck`,
`DiskGraph`):

- The set of a state's successors tells states apart by their values (`TLCStateMut.equals`), not by fingerprint. A
  successor with the fingerprint of the state itself is a transition beside the stuttering one, with the action atoms
  and fairness steps of its own step (`LiveFold-ViewLoop`, `SymLoop`: weak fairness of an action whose steps only
  change what the view or the permutation hides holds on that self-loop). Two successors with the same fingerprint are
  two entries, the later one put after the earlier
- A node's check_state ([]<>S parts and the ENABLED of fairness) is evaluated on the state TLC expands, the first
  reached of its fingerprint; a step's action atoms on that state and the actual successor; and a particle of the
  tableau is checked on the actual successor, not on the state kept for its fingerprint (`LiveFold-ViewSucc`; in
  `SfWf-View` this removes the self-loop the view makes, whose successor has `x = 1`)
- Without a tableau, a transition to a state already expanded is added only if the node has none to it yet
  (`DiskGraph.getPtr`, `GraphNode.transExists`), so of two entries the first in the set's order decides
  (`LiveFold-Twice` and `TwiceGo` differ only in the order of the actions); to a state not yet expanded, every entry
  is a transition. With a tableau, the first entry consistent with each particle
- A node new to a state already expanded gets its transitions, and its check_state, from the actual successor that
  made it, not from the state kept for its fingerprint

So under a VIEW or a SYMMETRY the verdict is TLC's search on this graph (`tlc_lasso`, which generates each state's
successors again for it, `fold_puts`), not the checker's own search on the folded graph. The checker follows TLC's
search when there are at most 128 predicates in an order of solution (held as `u128` bit masks when there are more
than 64, `ManyFair-Viol`), a tableau of at most 4096 particles and 64 promises, no value that `tlc_fp` cannot
fingerprint as TLC does, and no `-fp` other than 0 among TLC's options (`crosscheck.sh` passes `-fp 0` unless a cfg's
`args` choose one), and otherwise prints its own lasso and says why on stderr ("the counterexample is tla2rs's own,
not TLC's", with the reason; under a VIEW or a SYMMETRY also "the liveness verdict under VIEW or SYMMETRY is tla2rs's
own"). `crosscheck.sh` then confirms that lasso with TLC when it differs from TLC's, and says so
after `MATCH` (`lasso confirmed instead: <reason>`). All 69 liveness violations of `examples/` and `tests/tlc/` print
TLC's lasso (most by following TLC's search, some by coincidence), 19 of them through a tableau (`LiveTab`,
`LiveTabSym`, `LiveFold-ViewLoopEv`, `SymLoopEv`, `ViewSucc`, `Late`, `Live-Spec*-Starve`, `Live-SpillNext-Starve`, `LiveForms-NoneImplies`, `Peterson-Unfair`, `OptDiffTrace-Live`,
`LiveConst-Leads`, `LiveAssumed-Leads`).

TLC checks such a lasso as follows. With `-lassocheck DIR`, the checker writes `DIR/Tla2rsLasso.tla` and
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
lasso is checked as a behavior of the spec itself (`LiveSym` passes).

The state graph keeps the first state reached of each fingerprint, which under a VIEW or a SYMMETRY need not be a
successor of the state before it on the lasso. TLC prints each state of its lasso as the first successor of the state
before it with the next node's fingerprint (`tlc_print_lasso` does the same). Where the checker prints a lasso of its
own, it replays the lasso on actual states, as TLC rebuilds a
behavior from fingerprints (`lasso_states` in the runtime): from the initial state, each step takes the successor
whose fingerprint is the next node's, by the same action if one is. Under a SYMMETRY the cycle can come back to
another member of the entry's class; it is followed again until it repeats an actual state, which takes at most one
round per permutation (`tests/tlc/LiveSymTurn`: two rounds). Under a VIEW the actual states need not repeat at all:
in `tests/tlc/LiveView` and the corpus's `MCDistributedReplicatedLog` a value the view leaves out only grows. The
lasso then returns to its entry under the VIEW only. Its last step goes to the actual successor (`Tla2rsGoBack`), and
the cfg gets the spec's VIEW with the position added (`Tla2rsView == <<tla2rsAt, V>>`, and the spec's SYMMETRY if it
has one), so TLC folds that successor into the entry as its own search does. A step with no successor of the right
fingerprint (TLC cannot rebuild such a behavior either, tlaplus/tlaplus#1045) leaves the states the graph keeps,
which TLC then refuses. `crosscheck.sh` runs this for each liveness violation whose lasso differs from TLC's
(about a second of TLC each) and fails if TLC does not confirm it, or if the spec's parts cannot
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
temporary paths of the modules TLC parses, times and dates, and (without `-fp`) the shape of a
liveness counterexample. No configuration printed a Java stack trace. The rules:

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
  while computing whether an action is enabled), of the whole `x' \in S` when it cannot enumerate S
  (a string such as Real; when S names a definition, expansion keeps the end of the name in an AT
  label around what replaces it), of a CHOOSE no element satisfies, of an unbounded
  quantifier, of a temporal formula it refuses, and names a part of a property by position. The
  parser keeps these positions in AT labels (`ast::AT`), which expansion keeps
- tla2rs's own notes (which state it cannot represent, what it was evaluating) go to stderr
- In the liveness checks after a state's successors, TLC computes whether each fair action is
  enabled before it evaluates the steps, and the step of a fair action before the action predicates
  of the properties (the same on every run; `tests/tlc/LiveErr-Fair`, `LiveOrder`), so an error in
  both is reported from ENABLED. Between the state and the action predicates of the properties its
  order changes from run to run (three runs each of a property `[]<><<A>>_v \/ []<>Q` and of two
  properties gave both orders); the checker evaluates the state predicates first
- TLC stops computing whether an action is enabled (ENABLED, and the fair actions in the liveness
  checks) at the first successor it finds, in the order it computes successors, so an error that
  only a later successor would raise is not reached (`tests/tlc/EnFirst*`: a later disjunct, `x'
  \in S` taken in TLC's order of S, `\E` over a constant set or one from the state, a recursive
  operator). The checker leaves the block of such a computation at its first successor
  (`Env::en_exit`)

TLC prints a warning only when it has not printed the same text before, and its first warning of
a run carries the note `(Use the -nowarning option to disable this warning.)`, so the same warning
can come a second time, without the note, and then never again; any other text comes once (measured
on TLC 2.19, `tests/tlc/ExceptWarn*`, `ExceptLive-Two`, `SparseFun`, `LazyFun`). The checker prints warnings so (`put_line`,
starting from those among STARTUP_PRINTS), and so does `compile::Startup::lines` for what TLC prints
when it starts. The warnings:

- An EXCEPT that names an argument or field the value does not have (of a function, a function over
  a set TLC does not enumerate, a tuple or a record, written `!["z"]` or `!.z`, also an inner index;
  `tests/tlc/ExceptRecMiss`) changes nothing there, and
  TLC warns `The EXCEPT was applied to non-existing fields of the value at` with the position of
  the value the EXCEPT changes, once per such argument (two in one evaluation print it twice). For
  an EXCEPT applied to @ (`![1] = [@ EXCEPT ![5] = 0]`) the position is that of the pair @ belongs
  to, `![1] = [...]` (`tests/tlc/ExceptWarnAt`). The
  parser keeps that position in an EXCEPT_AT label when the value is not an identifier, and
  expansion when a name is replaced by what it stands for (`ast::except_pos`); the checker warns
  with the printed lines (`except_warning`), the constant evaluator records it with them. TLC
  evaluates a definition of constant level when it starts and keeps its value, so such a definition
  with an EXCEPT warns then, and not again where it is used (`uncache_prints`); a constant invariant
  or property warns when TLC evaluates it before exploring (`Startup::invs`). An EXCEPT of constant
  level inside Init, an action or an invariant, which the compiler folds, warns where it is
  evaluated: folding notes the warnings (`Gen::try_const_made`, with the definitions TLC evaluated
  when it started not warning again) and the folded code calls `except_warning` for each
  (`Gen::note_folded`; also a constant condition of an action or of an IF, the set of a `\A` that
  assigns variables, an empty set of `\E`, the arguments of a recursive operator unrolled in an
  action whose parameters its body reads; `tests/tlc/ExceptFold*`). A LET definition or an
  argument whose constant value warns is computed where first used, as one that is not constant
  (`Gen::gen_bind`), so it warns once for the evaluation of the LET or the call, and an argument
  that is the value an EXCEPT changes keeps the position of the parameter
  (`expand::subst_ident`; `tests/tlc/ExceptFoldOnce*`). The set of a `\E` that TLC splits the
  next-state relation through is evaluated once, when TLC reads the spec, so its warnings come
  when TLC starts, after the constant invariants and before the ASSUMEs (`Gen::split_warns`,
  `tests/tlc/ExceptSplit*`).
  TLC prints a warning of Init, an action or an invariant where it evaluates it, as it computes and
  checks each state, so a warning of a later `\E` or `\/` branch comes after the error on an earlier
  successor, while TLC rebuilds the behavior (`tests/tlc/ExceptWarnEx*`). The checker follows it
  with PRINT_ORDER, like the printed lines below; to keep the faster search (and `-batched`) for a
  spec that can warn but never does, a checker whose code can warn without PRINT_ORDER
  (`WARN_RERUN`) exits at its first warning when tla2rs runs it (`WARN_EXIT`, `w` in TLA2RS_GROW),
  and tla2rs builds it again with PRINT_ORDER (`compile`'s `warn_order`) and checks from the start.
  A warning of what TLC evaluates for its liveness graph (the predicates of a property, a fair
  action and its subscript) comes where TLC evaluates it, among the lines of the actions: a checker
  whose liveness code can warn exits at its first warning in the same way, and is built again with
  `LIVE_SIM_RT` (see below; `live::compile`'s `warn_order`; `tests/tlc/ExceptLive*`).
  Not followed: other places where the compiler evaluates a constant without the warnings it notes
  (`Gen::try_const`)

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
- After a new successor fails to evaluate an invariant, it shows the behavior and then generates
  every successor of the state it was expanding once more (`eval_replay`): the actions print again
  in order, a successor not seen yet is added and queued (so it counts as distinct and left on
  queue) and its invariants are checked, up to the first that fails; one that fails to evaluate
  again makes it exit with 255. With `-continue` it reports the exception it did not expect before
  that pass, and one that fails to evaluate again there as a failed invariant with its behavior,
  then as the error itself with the behavior again (`again_failed`; `tests/tlc/AgainTwice`,
  `PrintAgain-TwiceContinue`, `PrintAgain-LiveTwice`). After the CONSTRAINT, the ACTION_CONSTRAINT
  or the VIEW fails to evaluate on a successor, it reports the error and then generates the
  successors once more in the same way, up to the error (`tests/tlc/AgainCon*`, also with liveness
  checking). After an error while computing or checking
  the initial states (in Init, the CONSTRAINT, an invariant or a property), it reports the error
  and then computes and checks them again from the start, printing again up to the error
  (`init_again_prints`; `tests/tlc/PrintAgain*`). In a spec that reads TLCGet these passes handle
  each state as Init or an action computes it, as the search does (see "TLCGet and TLCSet")
- TLC evaluates the CONSTRAINT, then the ACTION_CONSTRAINT, on each successor as soon as an action
  yields it (also one already seen), and the invariants of a successor outside them right after:
  what they print comes after what the action printed before the successor. When a constraint
  prints with the rest, the checker holds those lines in that place among what the actions printed
  (`CONS_PRINT_RT`, hooked into the runtime by `compile::cons_print_runtime`; `tests/tlc/PrintCon*`).
  Rebuilding a behavior does not evaluate them
- The action properties are checked on the step to a successor after the successor is added (if
  new) and its invariants are checked: what they print comes then, before the next action is
  evaluated, and with `-continue` before their violation is reported (`Held::after`; the liveness
  search evaluates them after the invariants; `tests/tlc/PrintAct*`)
- To show a liveness counterexample it rebuilds the lasso from fingerprints too: it first evaluates
  Init and the steps up to the state the cycle starts at, then shows those states, then evaluates
  each step of the cycle just before the state it leads to, and the step back before `Back to
  state` (`lasso_prefix_prints`; `tests/tlc/PrintLasso*`)

When Init, Next, an invariant, an action property or what TLC evaluates for its liveness graph prints
(`PRINT_ORDER` in the generated checker, set by `compile.rs`; also once an EXCEPT of Init, Next, an
invariant or what TLC evaluates for its liveness graph warned, see above), the checker marks each state `init` or `next` pushes and the start of each action
(`mark_push`, `mark_action`, generated only then), holds what Print and PrintT print while it
computes states, and prints those lines as it handles the states (`Capturing`, `Held` in
`runtime.rs`); `print_states_tlc` shows a behavior as above. Such specs are searched without
`-batched` (on the default path), and a spec that prints nowhere else generates the same code as
before. An invariant that prints is evaluated once per state, not again to find which one failed. A property `[]P` checked as an invariant is not covered: with `-batched` / `-metal`, when it
prints, phase 1 first skips a candidate already visited or collected in the level (`INV_PRINTS`),
since TLC checks new states only.

How many times a line is printed, measured on TLC 2.19 with one worker (each with a test in `tests/tlc/`):

- `[y \in S |-> e]` is kept unevaluated (`PrintFun`): applied, TLC evaluates e at the argument only, at
  each application; used as a value (compared, printed, ToString, DOMAIN, a variable's value) it
  evaluates e at every element. Where it evaluates a LET definition or an argument once, it keeps the
  function computed the first time it is used as a value; once applied, DOMAIN computes nothing and
  printing computes it without keeping it. Code generation applies such a function as its body at
  the argument (as for `lazy_apply`) and binds such a name to a cell with a flag for whether it was
  applied (`Gen::gen_bind`, `lazy_cells`, `shown_once`). A function definition of constant level is
  computed when TLC starts, but a recursive one is not: it is evaluated where it is applied, the
  recursion too, at each application (`compile.rs`, and `Gen::is_const` for `RecCall`)
- TLC evaluates what tla2rs decides without evaluating (`PrintFold`): the elements of a set written
  out where membership is tested (it builds the set first), the tuple or function DOMAIN is taken
  of, and, when it starts, the argument of Head (`value::is_str` evaluates it quietly)
- SANY takes the level of `Print(out, val)` from val and that of `PrintT(out)` as constant (TLC.tla
  defines them so), so a part of a temporal formula that reads a variable only in what it prints is
  of constant level: TLC evaluates it when it converts the formula, before the ASSUMEs, printing
  then, and stops with exit 151 on the variable (`live::level_parts`, `take_live_prints`;
  `PrintLevel`). A call of a definition that reads the state is one predicate of the formula, but
  TLC goes through its body when it starts, printing what its parts of constant level print and
  ignoring an error there (`live_const_error`; `PrintLive-Def`); a part of constant level written in
  the formula prints when TLC starts and again each time the predicate around it is evaluated
  (`PrintLive-Inline`)
- `[f EXCEPT ![a] = v]` of such a function (`PrintExcept`): where the result is applied, TLC keeps f
  unevaluated, so evaluating the EXCEPT evaluates e at each argument it updates (the value `@` stands
  for, also when v does not use it; an earlier update's value if it names the same argument, and
  nothing, with the warning, outside the domain, where v is not evaluated either), then v; applying
  the result evaluates e at the argument unless an update names it. Where the result is used as a
  value, TLC computes f whole first, then the new values. A name bound to such an EXCEPT keeps the
  updates from its first application (`Gen::print_except`, `print_except_updates`, `lazy_upd`)
- While it builds its liveness graph (`tlc2.tool.liveness.LiveCheck`; `PrintLive*`), TLC evaluates,
  for each order of solution in turn, after a state's successors: the step predicates of its
  `check_action` on the step to each successor in TLC's set of them (the state itself put last; see
  `tlc_lasso`), its `check_state` on the state, then each particle of the tableau on each
  successor; and a node of the tableau new to a state already expanded makes it evaluate at once
  that state's `check_state`, its stuttering step and its successors, generated again an action at
  a time (what an action prints comes before its successors are taken, with the CONSTRAINT on each).
  `WF_v(A)` is the step predicate `~ENABLED <<A>>_v \/ <<A>>_v`, so ENABLED is evaluated once per
  step, and a step predicate `<<A>>_v` (also `[A]_v`) compares v first and does not evaluate A on a
  step that leaves it unchanged. On each new initial state, before its invariants, it evaluates the
  formula's particles. When any of this prints, or warns about an EXCEPT once the checker met such a
  warning (`live::compile`), the checker evaluates it the same
  way (`LIVE_SIM_RT`, hooked into the runtime by `compile::live_sim_runtime`) and its own
  evaluations of the same predicates quietly

The code pasted for this (`LIVE_SIM_RT`) is generated only for a spec that prints (or warns there),
so the code of other specs is the same as before.

Not followed:

- An EXCEPT whose function is a name already applied, used as a value (TLC keeps the name
  unevaluated, evaluates e at the updated arguments, then everywhere); and a name bound to such an
  EXCEPT, applied and later used as a value, evaluates its new values again (TLC keeps them)
- What TLC evaluates for its liveness graph under a VIEW or a SYMMETRY (not measured with printing;
  the checker evaluates on the successors as generated), and with several orders of solution, which
  TLC takes in an order that changes from run to run
- For a spec that prints nowhere, an invariant that fails to evaluate again in the pass after the
  behavior with `-continue` is still reported once (its code is kept as it was)

Other messages tla2rs words as TLC does, measured on TLC 2.19:

- An identifier TLC fails to evaluate (a variable read primed before it is assigned, also under
  UNCHANGED or in the subscript of a fair action; a variable ENABLED reads in Init before it is
  assigned; a substituted variable of an instance in ENABLED, see "ENABLED in an instantiated
  module"; a variable in the bound of a quantifier over a temporal formula): `In evaluation, the
  identifier x is either undefined or not an operator.` and the position of x where it is written,
  also as an operator's argument, in a LET or under a quantifier (`tests/tlc/IdentPos*`). Every
  `Expr::Ident` keeps where it is written (`ast::Pos`, set by the parser and kept when expansion
  renames a bound variable; a SUBVAR label gets it after `SUBVAR_AT`). It never takes part in
  comparing expressions, so only the text of these errors changes in the generated code
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
  was unable to fingerprint.` with the same reason (and its `Fingerprint Stack Trace`, dropped), but
  not after a failed invariant on a successor, which it reports with the message alone
  (`tests/tlc/TupleFunConst-Late*`). Not
  after `x \in S` for S from the state or a constant definition, `x \in 5..6`, `\E y \in {5, 6} : y =
  x`, `t[i]` for t from the state, or `k \notin [{1} -> {1}]`, nor when a string's or a tuple's own
  comparison fails (`<<"a">> \in {"ab"}`, `<<1, 2>> # s`) (`tests/tlc/FpErr*`). Code generation
  wraps such an operation in an `FpSource` when it can fail (`Gen::fp_source`). Such an error while
  checking an initial state does not stop TLC from generating the remaining initial states, which it
  counts as generated without keeping or checking them, with what Init prints for them
  (`tests/tlc/TupleFunFail`: 3 generated, 1 distinct; `TupleFunPrint`; TLC's own exceptions stop it
  at once). In a spec that reads TLCGet, where each initial state is checked as Init computes it
  (`TLCGET`), Init goes on after
  the error and the states it still computes are only counted (`initial_states`, `TupleFunGet`),
  after the pass that computes and checks them again up to the error (`TlcGetAgain-Fp`)
- A tuple compared with a function over keys that are not all integers (`<<1, x>> = (1 :> 1 @@ m :>
  x)`, `<<x>> = ("a" :> x)`), with either on the left: unequal when the sizes differ, otherwise TLC
  walks the function's keys in its order, and the first that is not an integer stops it with
  `Attempted to compare an integer with non-integer:` and the key followed by `.`, while an integer
  key that is not the next index, or whose value differs, makes them unequal. A value built there on
  the left adds `TLC was unable to fingerprint.` (`tests/tlc/TupleFunFail*`, `Gen::tuple_fun_eq`).
  Such a pair inside tuples of one length, records of the same fields or sets of one size is reached
  part by part in order (sets in TLC's order of their elements), and the first part that differs
  makes them unequal (`tests/tlc/TupleFunNest*`, `Gen::walk_eq`). In a set written out, TLC asks each
  element in turn whether it equals the value, with the same error and a fingerprint error from the
  set (`tests/tlc/TupleFunIn*`). A sorted set of such functions (from a definition or the state) is
  searched by halves in TLC's order instead, starting at index n/2: the tuple (also one held as a
  sequence, `Append(s, 1)`: `tests/tlc/SeqFunSorted*`) compares with each
  element it visits by size, then key by key in TLC's order (model values before integers), where a
  key that is not an integer stops it with `Attempted to compare integer with non-integer:` (no
  "an") and the key followed by `.`, raised inside the tuple (a fingerprint error when the tuple is
  written there, not when it comes from a definition), and an integer key against the index, then
  the values, decide which half it goes on in (`tests/tlc/TupleFunSorted*`,
  `Gen::tuple_fun_search`). So the search may pass every element without an error. All of this
  holds when every operand is constant: the compiler evaluates such a test as TLC does
  (`ConstEval::tuple_fun_scan`, `tuple_fun_search`), and the checker raises the error where TLC
  evaluates it, in Init, an action or an invariant, and in an ASSUME when it starts
  (`tests/tlc/TupleFunConst*`, `TupleFunAssume*`). Such a function in a sorted set of tuples (of one
  length or several) is searched the same way from the function's side: by size, then its keys in
  TLC's order against the indices, a key that is not an integer stopping it with `Attempted to
  compare integer with non-integer` (no colon) and the key followed by `.`, without a fingerprint
  error even for a function constructor (`tests/tlc/FunTupleSorted*`)
- A tuple compared with an integer: `Attempted to check equality of the function <<1, 3>> with the
  value:` and the integer when the tuple is on the left, `... of integer 1 with non-integer:` and the
  tuple otherwise, also when a set written out asks each tuple in turn whether it equals an integer
  (`x \in {<<1>>}`, with a fingerprint error from the set except in an invariant on a successor:
  `tests/tlc/IntTupleIn*`); a non-tuple in a product: `Attempted to check if non-tuple`, the value, `is in the
  set of tuples:` and the product (`tests/tlc/TupleVals*`)
- A tuple, a string or an integer in a set it cannot be compared with, or a record in a set of
  tuples, when the set is sorted (from the state or a definition): TLC searches the set and fails on
  its first comparison, with the element at index n/2 in its order: `Attempted to compare the
  function <<1, 3>> with the value:`, `Attempted to compare string "x" with non-string:` or
  `Attempted to compare integer 1 with non-integer:`, then that element (`tests/tlc/SortedCmp*`,
  `IntTupleIn-Trio`, `IntTupleIn-State`); `Attempted to compare record:`, the record, `with
  non-record`, then that element (`tests/tlc/RecTupleSorted*`). A set written
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
  SPAN labels (`parser::parse_module_spans`) and the definition checked as written. Semantic
  errors come under `Semantic errors:` and `*** Errors: N`, each with its position, in the order
  SANY meets them, then `*** Warnings: N` (`sany::SEMANTIC`): the position of a name, a bound
  variable or a parameter; of a whole definition or declaration (LOCAL included, `F(_)` of a
  RECURSIVE declaration); of an operator's symbol and then of the whole expression (`Couldn't
  resolve infix operator symbol`); of a subexpression selector. A clash names the other
  declaration, also in a standard module as SANY reads the jar's file (`std_modules::STD_DEFS`:
  Sequences' `Len` is at line 25, col 1 to 44) or `In module --TLA+ BUILTINS--`, after `conflicts `
  and a line break

Where tla2rs cannot print all of TLC's text, a line `\* crosscheck: error-lines (reason)` in the cfg
makes `crosscheck.sh` compare the error lines only, and `all.sh` says so. Without it everything is
compared. The error lines leave out TLC's `Error: TLC was unable to fingerprint.` (above). No
configuration needs it now.

### TLCGet and TLCSet

What TLC 2.19 gives with one worker, measured on `tests/tlc/TlcGet*` and `TlcGetReg*` (each value printed with
PrintT in the ASSUMEs, Init, the actions, the invariants and the CONSTRAINT), and what the checker does:

| Form | TLC 2.19 | tla2rs |
|---|---|---|
| `TLCGet(i)`, `TLCSet(i, v)` | One store of registers, which the ASSUMEs, Init, the actions, the invariants and the constraints share in TLC's order of evaluation, also while it shows a behavior; reading one never set is TLC's own error, `TLCGet(3) was undefined.` | Supported for integer registers and values (`tg_get`, `tg_set`); what the ASSUMEs set is where the checker starts (`REG_INIT`) |
| `TLCGet("level")` | The level of the state being expanded (an initial state's is 1); 0 in the ASSUMEs, in Init and in the checks of an initial state; a successor's CONSTRAINT and invariants see the level of the state it comes from | Supported |
| `TLCGet("distinct")` | The states added so far: a state counts from after its CONSTRAINT and before its invariants | Supported |
| `TLCGet("queue")` | The states waiting to be expanded: an initial state is queued before its invariants are checked, a successor after them | Supported |
| `TLCGet("diameter")` | The largest level of a state added so far, 1 before any (in the ASSUMEs too) | Supported |
| `TLCSet("exit", TRUE)` | The search ends without an error once Init, or the expansion of the state being expanded, is done, with the states left on queue | Supported (`tg_exit`) |
| `TLCGet("duration")` | Seconds since the start | Refused: no two runs agree |
| `TLCGet("generated")`, `("config")`, `("stats")`, `("action")`, `("spec")` | Undefined (`TLCGet(config) was undefined.`) | Refused |
| `TLCSet("pause", TRUE)` | Waits for a key | Refused |

A definition of constant level that reads them is not evaluated once when TLC starts (`Level == TLCGet("level")`
changes from state to state), so neither the compiler nor code generation folds them (`constant_level`,
`Gen::is_const`). When TLC shows a behavior, the counts stay where the search stopped (`queue` is the number of
states left on queue), the level is that of the state each step starts from (0 for Init, and for the step
evaluated once more after an evaluation error), and the registers go on changing as TLC evaluates again.

The values depend on when TLC handles each state: as soon as Init or an action computes it, before the rest of the
action is evaluated. A spec that uses them (`TLCGET` in the generated checker, which implies `PRINT_ORDER`) is checked
so: the generated code calls `pushed` after each state it computes, and the runtime adds and checks that state
there (`expand_eager_one`, and the initial states in `initial_states`); the step to a state that stops the search
unwinds out of the action. To show a behavior, each step evaluates the actions in order up to the one that yields
the next state and stops at the start of the next action (`step_prints`, `mark_action`); the checker's own
replays of a behavior leave the registers as they were (`tg_quiet`). With TLCGET an invariant is evaluated once
per state (`eval_invariants`), and an expansion that fails is not evaluated again (`expand_caught`).

The passes TLC makes again after an evaluation error (see "Messages and printed lines") handle each state as it is
computed too, and the registers go on changing, so they can compute states the first pass did not
(`tests/tlc/TlcGetAgain*`, `TlcGetReplay*`). Generating the successors again (`eval_replay_eager`) runs at level 0
and adds, queues and checks a new successor as the search does, the counts it reads following. Computing the
initial states again (`init_again_eager`) adds and queues a new one and reports an invariant it violates (with
`-continue` it goes on, also reporting again a state the first pass reported); TLC then gives the states this pass
generated, the distinct states of both passes, and exit 0 unless the pass stops at an error.

Refused at run time: several workers (TLC's counts and registers are then those of its threads and shared queue),
and temporal properties (TLC's liveness checking evaluates the spec again in an order of its own). Without
`-workers`, such a checker runs one worker. `-batched` and `-metal` run the default path, as with PRINT_ORDER.

Not followed: rebuilding a behavior where the registers make the actions yield other states than the search
found. TLC then shows the states up to the step it cannot rebuild (with `-continue` it then reports a
`NullPointerException`); the checker shows the behavior the search found, or fails to rebuild it (`TlcGetReplay`'s
`Reg` stops changing so that its behaviors are rebuilt). None of the corpus's models is affected: the skipped ones that read
them use TLCGet("config") or a simulation mode, and `MCKVsnap`'s `BaitInv` is not in its cfg.

### Arguments written out at each use

Expansion substitutes each argument of a call into the body, and inlines a LET definition at each use, so an argument
the body uses k times is written out k times, and a definition that passes it on multiplies that at each level. The
constant evaluator then evaluates every copy. Measured on tla2rs before the change below: `HTMLAttribute("color", "blue")` with the
release's HTML.tla went past 4 GB in 7 s (HTML evaluates `HTMLDefaultStyle` when it starts, which nests folds through
`ReplaceFirstSubSeq`), and the corpus's `BlockDagTest` took 1.5 GB in 2.5 minutes on its ASSUMEs.

For what the compiler evaluates when TLC would start (the constants substituted with `<-`, the definitions of
constant level without arguments, the constant invariants and properties, the ASSUMEs), `compile.rs` expands with
`Expander::expand_def_bound` / `expand_top_bound`: an argument that is of constant level and not a name or literal,
and a LET definition without arguments (not a function `f[x \in S]`), is expanded once and bound to a fresh name in a
BIND label (`ast::BIND`); the body refers to the name. The evaluator reads the name's expression where the name is
used: the value is computed there, as the copy written out there would be (so the strings it makes and its errors
come in the same order), and kept for the values of the names it depends on (`value::eval_bound`, `bound_free`); one
whose computation printed is kept only while the BIND label is evaluated (`PRINTED_VALUES`), so it prints once
each time TLC evaluates the LET or the call, as TLC does where it starts (`tests/tlc/PrintFold`). Where the evaluator reads
how a set or function is written (`x \in Nat`, `[x \in S |-> e][k]`, `Seq(S)`, a lazy function printed), it reads
the bound expression (`value::shape`). Fresh names while binding come from a counter of their own, and the
recursive definitions expanded while binding are kept apart from those code generation uses. `tests/tlc/ArgShare` (an
argument used twice through 24 calls), `LetShare` (24 LET definitions each used twice by the next) and `RecShare` (a
recursion whose result a definition reads per element of a set) show it: before, the first two went past 3 GB within
5 s and the third took 22 s; now each takes well under a second.

Code generation reads Init, Next, the invariants and the constraints expanded with `Expander::expand_def_code`, which
binds in the same way an argument of state level (without a prime, ENABLED or a temporal operator) that is not a name
or literal, and a LET definition without arguments. A call site keeps the argument written out as its trace, which
`Gen::gen_split` reads to name actions. `expand::float_binds` then moves each BIND label to where code generation
evaluates its names, drops a name not used, and writes out a name used once outside a part evaluated per value of a
bound variable. What TLC does, measured on TLC 2.19 with PrintT (`tests/tlc/LazyLet`, `LazyArg`, `LazyAction`):

- In an expression (an invariant, the value assigned to a primed variable, the condition of an IF, and the rest of an
  action once every variable is assigned), TLC evaluates a LET definition or an argument where it is first used and
  keeps the value for the rest of the LET or the call; one never used is never evaluated, nor fails, and what it
  prints or fails on comes where it is first used. `Gen::gen_bind` makes each name a `OnceCell` and a closure that
  computes the value on first use
- Where TLC computes the successors of an action and some variable is still unassigned (in Init too), a LET or a call
  it goes through (a conjunct, a disjunct, the body of `\E`, a branch of IF or CASE) evaluates its names again at each
  use: there `LET d == PrintT(1) IN d /\ d` prints twice. Such a label stays where it is, renamed BIND_ACT, and code
  generation writes its names out as before

A name is also written out where it is used when its value is constant (code generation folds it there; not when
computing it warns about an EXCEPT, see "Messages and printed lines"), when TLC
keeps the value unevaluated so that only what is used is computed (`codegen::lazy_value`: a function constructor, a
range, SUBSET, UNION, a set of functions, records, sequences or tuples), in Init while a variable it reads is still
unassigned (the closure would hold the state being built), and when code generation cannot generate its value on its
own (a set only tested for membership). A name the body of a recursive operator reads from outside the operator is
passed to its Rust function as a value, computed at the call (`Gen::rec_free`). The constant evaluator keeps with
each bound value the strings its computation made and notes them again at each later use, since code generation
notes the strings a constant part makes where it folds the part (`value::eval_bound`). The checks made on every
definition when TLC starts (the levels of temporal formulas, which definitions are of constant level) read the
expansion for code generation as well, which does not write out arguments of state level either.

Not followed: a LET definition or an argument that reads a primed variable is still written out at each use (once
every variable is assigned, `LET d == PrintT(x') IN d /\ d` prints once in TLC and twice in tla2rs).

Measured on a machine with 32 cores, before and after: generating the checker of the corpus's `TLCSailfish1` went from
100 s and 17 GB to 0.15 s and 18 MB, the generated code from 3.5 MB to 245 KB, and the call sites of `Descendants`'s
functions from 652 to 8; building each checker from 3.7 minutes to about 4.5 s; the search no longer stalls at
level 8 and finishes in 45 s (tla2rs takes 74 s in all, building the checker 4 times as its sets
grow from 8 to 64 elements; TLC takes 37 s with one worker). A spec with `HTMLAttribute("color", "blue")` in Init and
`HTMLAttribute("color", "red")` in an action took 209 s to generate and now 0.3 s.

### Large constant sets

A constant set the checker iterates over (`x \in S` in Init or an action, `\E`, `\A`, CHOOSE, `{e : x \in S}`, `{x \in S : P}`) is evaluated at compile time, and was written out element by element. `GameOfLife` (corpus) has `grid \in [Pos -> BOOLEAN]` with 16 positions: its 65536 functions became a 6 MB array, and rustc took about half an hour on it. A constant set of more than 1024 elements (`BIG_SET`) built from `[D -> R]`, `S1 \X ... \X Sn`, `[f1 : S1, ...]` and `SUBSET S`, nested in any way, is instead enumerated by the checker from its parts, which are written out (`Gen::big_set_iter`, `BigSet`). Element i is decoded from i in mixed radix with the first part varying slowest (for `[D -> R]` the value at the last element of D varies fastest; for records, the last field in TLC's order of names), and the subsets of S come in the order of `subsets_tlc`. That is the order of the set's value (`value::Value` orders as TLC does), so the elements come in the order they were written out in, and they have the type `ty_of_value` gives the whole set (computed from a few elements, `BigSet::reps`). A set that is the whole of its element type still iterates over the type's indices. Measured on GameOfLife (on a machine with 32 cores): the generated code went from 6.2 MB to 187 KB, generating it from 2.3 s to 0.6 s, and building it from about 32 minutes (6.4 GB of memory) to 1.9 s; the search takes 0.14 s, and tla2rs about 3 s in all.

Checked by setting the bound to 0 and comparing, at run time, each set enumerated this way with the same set written out: the checkers of every configuration of `examples/` and `tests/tlc/` (7 have such a set) and of every selected corpus model but GameOfLife (18 have one; GameOfLife's set written out is what takes half an hour to build) gave the same elements in the same order, and matched TLC. `tests/tlc/BigSets` puts each form in Init (its `-...Viol` configurations stop at the first initial state that violates an invariant, which depends on the order), and `BigSteps` uses them in an action, in CHOOSE, and in quantifiers and set constructors of an invariant.

Not done: a large constant set of another form (a filter, a set of images, a union) is still written out, also where its membership is tested (`x \in {f \in [D -> R] : P}` compares x with each element), and an `\A` over a constant set in an action that assigns variables is unrolled per element.

When compiling, the constant evaluator (`value.rs`, for ASSUMEs and constant definitions) goes through such a set without building it as TLC does: `[D -> R]`, `\X`, `[f : S]` and `SUBSET S` (`BigSet`, from parts that are sets) are enumerated from their parts in `\E`, `\A` and `{x \in S : P}` (`each_elem`), in the order of their values, which is TLC's. Measured on TLC 2.19 (`tests/tlc/BigConst`, `BigConstErr`): of more than its limit of a million elements (its `-maxSetSize`), TLC enumerates them there and in CHOOSE over SUBSET, and stops with "Attempted to construct a set with too many elements (>1000000)." for CHOOSE over the others and for `{e : x \in S}` over any (`TOO_MANY`). A filter of one of these (of any size, but a name a BIND label binds, whose value is kept) is gone through element by element, its condition evaluated as each element is taken, while TLC builds a filter of an interval or of a set it holds element by element first (as the evaluator does). A quantifier over one variable takes the next element before it evaluates its body for one, as TLC does (seen where taking it evaluates a filter's condition that prints). Not done: over several variables (`\E a \in S, b \in T`), TLC varies the first fastest and takes the next combination ahead, while the evaluator varies the last fastest; this shows only where printing or an error depends on the order. `CarTalkPuzzle` `Model_3` (corpus, `skip`) is the case that needed it: `{B \in [1..5 -> 1..121] : ...}` has 121^5 (about 2.6 * 10^10) functions; the ASSUME now evaluates, but the evaluator goes through about 50,000 of them a second (67 million, 0.26%, in the first 22 minutes of a run capped at 30), so it would take about six days; TLC did not finish in 2 hours either.

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
(Apalache), 6 random generation or simulation, 2 that need a TLC flag for action composition, 37 that need a module
neither in `tla2tools.jar` nor in the CommunityModules (the proof system's library: TLAPS, NaturalsInduction,
FiniteSetTheorems; TLCExt), 31 that take longer (from the manifest's runtime, or measured; 23 of them are listed as
`large` and checked apart, see "Large models"), 7 whose cfg TLC 2.19
refuses (an `ALIAS` section), 2 where TLC picks values at random (two TLC runs differed), 5 where TLC 2.19 stops in a
CommunityModules definition that needs its Java override (IOUtils, and quantifiers over `Seq(S)` in Graphs and
UndirectedGraphs), and 1 that reads `TLCGet("config")`, which TLC 2.19 does not define. That leaves 106 selected.

The cfgs of the corpus are not edited, so a line of the list gives what a `\* crosscheck:` line would: `rules=`
(narrowing rules, passed as `CROSSCHECK_RULES`) and `rsargs=` (arguments for tla2rs only, `CROSSCHECK_RSARGS`; no
model needs one now that capacities grow, see "Capacities"). A selected model tla2rs does not
match is listed as `gap` with the reason measured; `corpus.sh` still runs it and says when it starts to match, and
fails only on a `check` that differs. A gap marked `norun` is not run, as running it costs too much (see the table
below).

Results at the time of writing (`scripts/corpus.sh`, JOBS=2): 105 match, of which 7 with `distinct-only`. Only the generated count differs in those 7: TLC generates the same successor of a state
more than once (once per `\/` branch or binding that yields it), and so does tla2rs, but not equally often. Measured
with `-dump dot` on two of them, where the generated count is the number of edges with duplicates, plus the initial
states and the successors a CONSTRAINT removes: `2PCwithBTM` has 5840 edges in TLC and 5290 in tla2rs, and the same
4682 distinct edges; `MCCheckpointCoordinationFailure` has 1297994 and 1297595 edges, and the same 611225 distinct
edges. The graph hashes compare the distinct edges, so the state space and transitions match. `StaleViewShrink` (4) is
not measured this way. `TLCSailfish1` generates 314144 states in TLC and 300492 in tla2rs, with the same 109604
distinct states and 300491 distinct edges; with its three `\/` lists of conditions (a branch of IF, and the right of
`=>`) rewritten as `IF A THEN TRUE ELSE B` in a copy, TLC generates 300492 too (see "TLC counts generated states per
`\/` branch"). No selected model is a gap.

Forms the corpus showed, each with a test in `tests/tlc/`: the CommunityModules (`CmFun`, `CmSet`, `CmSeq`,
`CmGraph`, `CmBits`, and since then `CmSeqSub`, `CmRel`, `CmDigraph`, `CmBag`, `CmMisc`; see "CommunityModules"),
`[1..n -> S]` with n from the state as a set of sequences (`SeqFunSet`), a definition of an instantiated module passed as an operator argument (`InstOpArg`), a recursive
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
functions over domains of different sizes (`DomGrow`), TLC's warning that a PlusCal algorithm changed since its
translation (`PcalSum`), a parameter of an instantiated module named like a definition written after it (`InstShadow`), constant sets of many elements that the checker enumerates (`BigSets`, `BigSteps`; see "Large constant sets"), fairness
under a constant guard (`\A i, j \in P : i # j => WF_v(A(i, j))`, `FairPairs`), and a pair of a record-or-model value
and a record against pairs of records (`PairSource`).

### Large models

23 of the models left out for TLC's run time match TLC, and are listed as `large` in `tests/corpus.txt`, each with TLC's
time with one worker (from 19 s to 4524 s, and more than 2 h for `MCKVSSafetyLarge`) and tla2rs's time and peak
memory. `scripts/corpus.sh -large` checks them against their files in `tests/expected/corpus/` and fails on one that
differs, as on a `check`; `rules=` work as for the selected models. Their state graphs (up to 595 million states) are
too big for TLC's `-dump dot` and for comparing, so their files keep only what is compared cheaply and does not vary
from run to run: TLC's verdict, its counts, the length and hash of its counterexample, its exit code and the hashes of
its messages, without the `states` and `edges` lines. For them `crosscheck.sh` runs TLC without `-dump` and tla2rs
without `-dumpgraph`, and their key leaves out `-dump` and `src/graph.rs`. A TLC run longer than 30 minutes writes a
checkpoint every 30 minutes (`Checkpointing of run <dir>`, `Checkpointing completed at (<time>)`); `crosscheck.sh`
drops those lines from a large model's output before hashing its messages (`src/messages.rs` keeps them, so that the
keys of the other files stay the same).

`scripts/expected.sh -corpus -large` writes their files by running TLC, which takes hours and up to tens of GB: it is
meant for a big machine. The files committed were written instead from TLC runs made before, with
`scripts/crosscheck.sh --expected-from TLC.OUT RC <tla> <cfg>` (the output and exit code of a run of the same jar on
the same model). Those runs used one worker but not `-fp 0`; none of the 23 violates a property, so the fingerprints
change nothing in the file. `MCKVSSafetyLarge` did not finish in 2 h with one worker, and its file comes from a run
with 32 workers (5582 s): without a violation the verdict and the counts do not depend on the number of workers, and
tla2rs with one worker gives the same 13385471536 generated and 594616815 distinct states. The other 8 models left
out for time stay `skip`, with what was measured on their lines.

Four use a rule. `MCCheckpointCoordination`, `ElevatorSafetyMedium` and `PaxosCommit` use `distinct-only`: only the
generated count differs, as in "TLC counts generated states per `\/` branch". `MultiPaxos_MC_small` uses `error-lines`:
its algorithm has a macro or a procedure, so tla2rs does not check its PlusCal checksum (see "PlusCal checksums"),
and TLC's warning that the algorithm changed is the one message tla2rs does not print. Measured on a Linux machine
with 32 cores, `scripts/corpus.sh -large` with JOBS=8 on the 20 models other than `MCKVSSafetyLarge`, `MCNanoLarge`
and `ElevatorSafetyLarge` (`-only`) took 165 s, and all 20 match.

### CommunityModules

The CommunityModules (https://github.com/tlaplus/CommunityModules) are modules TLC finds on its class path. Every
release tried (2023-12 to 2026-11) carries Java overrides that need a class TLC 2.19 does not have: with the jar on
the class path TLC 2.19 stops on any spec (`NoClassDefFoundError: tlc2/value/impl/KSubsetValue`). TLC 2.19 is built
from the 1.7 line of TLC, which branched before that class was added. So `crosscheck.sh` gives TLC the release's
modules only, extracted into
`target/community/<sha256>/`, and TLC evaluates their TLA+ definitions. The release is pinned by version and sha256
in `crosscheck.sh` (202611060952, the one current at the corpus's commit); a spec that uses it has the hash in the
key of its expected file.

tla2rs provides `Folds`, `Functions`, `FiniteSetsExt`, `SequencesExt`, `UndirectedGraphs`, `Bitwise`, `Relation`,
`BagsExt`, `Graphs`, `Combinatorics`, `Statistics`, `GraphViz`, `DyadicRationals`, `VectorClocks`, `Quorum`, `HTML` and
`SVG`, and parts of `Json` and `IOUtils` (below), itself (`src/community.rs`), as TLA+ source written for tla2rs, read when no module of that name is next to the spec.
Since TLC evaluates the modules' own definitions, these give the same values: CHOOSE over the same set with the
same predicate (`SetToSeq`, `Max`, `LongestCommonPrefix`, `Inverse`, `CausalOrder`), and folds that take the elements
in the same order (`MapThenFoldSet` applies `op(f(x), rest)` with x chosen first, so `FoldFunction` takes the
smallest index first, `FoldLeft` the largest; `MapThenFoldBag` applies op once per copy of each element). Where the
definition gives a value its documentation does not, the definition wins: `AllSubSeqs` lists each subsequence
backwards (it folds with `Snoc` from the smallest index), `ReplaceAllSubSeqs` replaces the leftmost occurrences
(measured on every sequence over {1, 2} up to length 3, and over {1} up to 4, against the module's definition, which
enumerates sequences of sequences), `ChiSquare` and `DotDiGraph` are TRUE, and `DyadicRationals` fails on a
numerator of 0 or less when it reduces (`Half(Zero)`), as the definition's divisors of 0 are none. Each module
exports the same names in the same order as the release's, with what it extends (`SequencesExt` extends Bags and
TLC, for example), since SANY's context, and the order TLC prints variables in, depend on them (see "The order of
variables"). Operators listed in `community::UNSUPPORTED` are refused where they are used: the operators over paths
of UndirectedGraphs and Graphs (and Graphs' `IsTreeWithRoot`, which uses one), which quantify over `Seq(S)`, so TLC
2.19 stops on them too ("non-enumerable quantifier bound").

Of `Json` and `IOUtils`, tla2rs provides what TLC 2.19 evaluates (`CmJson`, `CmPad`): `ToJson`, `ToJsonArray` and
`ToJsonObject` print each value with ToString (ToJson lists a record's values as an array, ToJsonObject quotes each key
twice, as the definitions do), `zeroPadN` puts "0" before ToString of n, and `JsonSerialize`, `ndJsonSerialize` and
`IOSerialize` are TRUE in the definitions and write nothing. ToJson's family and zeroPadN build strings by recursion,
and the checker numbers its strings when it is built (see "The order of strings"), so they are evaluated when
compiling and refused on a value from the state (`community::CONST_ONLY`, refused in code generation). The operators
that read or write files, run commands or read the environment are in `community::UNSUPPORTED`, with what TLC 2.19
stops on in their definitions: an unbounded CHOOSE (`JsonDeserialize`, `ndJsonDeserialize`, `IODeserialize`,
`Deserialize`), a CHOOSE over records with an Int field (`Serialize`, `IOExec`, `IOEnvExec`, `IOExecTemplate`,
`IOEnvExecTemplate`), a CHOOSE over `[STRING -> STRING]` (`IOEnv`) and a CHOOSE over Int (`atoi`). `Quorum`'s
`QuorumSystem` is the set of sets of subsets that meet pairwise and are closed under supersets (`CmQuorum`). `HTML`
fills templates by replacing each `%key%` in turn, the first occurrence in the text replaced so far, and joins parts
with a separator left out while the text built so far is empty, as the module's definitions do (`CmHtml`, in the
constant definitions and ASSUMEs; in Init or an action too, see "Arguments written out at each use").
`SVG`'s constructors build records whose attributes are the element's own joined with `@@` to those the caller gives
(a record or `<<>>`), so code generation takes a record given to `@@` as the function over strings it is; the numbers
are turned into strings in the order the module's definitions take them (`CmSvg` when TLC starts, `CmSvgRun` in
Init, actions and invariants). A function over strings prints as a record only when every string of its domain is an
identifier (`compile::field_name`, `StrFieldName`), so the attributes of `Image` and `SVGDoc` (`"xlink:href"`) print
as `("x" :> "5" @@ ...)`. `NodesOfDirectedMultiGraph` (a CHOOSE over functions into records with Int fields) and
`SVGSerialize` (IOUtils' `Serialize`) are in `community::UNSUPPORTED`. Not followed: an element printed while
exploring (Print, PrintT) shows its empty children as `<< >>` where TLC prints `<<>>` (the graphs and counterexamples
read both alike, see "State graphs").

TLC gives the position of a CASE without OTHER when none of its conditions holds, and for a CASE in a module of the
release that is a position in the release's file, which tla2rs's module does not have. `community::CASE_AT` holds the
position measured on TLC 2.19 for `Interleave` of `SequencesExt` (from CASE to the last character of its last arm),
and `compile::community_module` puts it on that CASE (`CmCase`, in Init, an action and an invariant).

The other modules of the release are not provided, so a spec that names one is refused. Measured on TLC 2.19 with the
release's modules only, or on tla2rs:

| Module | Why |
|---|---|
| `CSV`, `CBOR` | They read or write files. Their definitions stop TLC 2.19: CHOOSE without a set (`CSVRecords`), `Assert(FALSE, ...)` (`ToCBOR`) |
| `ShiViz` | `Host` and `Clock` read `TLCGet` and the Toolbox module; TLC 2.19 stops on `Host` ("Attempted to enumerate S \ T when S: Nat is not enumerable") |
| `DifferentialEquations` | `Integrate` is a CHOOSE without a set over functions of reals; TLC 2.19 stops ("TLC attempted to evaluate an unbounded CHOOSE") |

TLC creates the identifiers and strings of the release's modules when it parses them, so `tlc_string_ranks` reads
those of the modules tla2rs provides from `src/community_modules.rs` (`CmNames`: a string equal to a name only those
modules write comes before the spec's own strings). Not followed: errors inside the modules' definitions (Max of an
empty set, Last of an empty sequence) are reported with positions in TLC's modules that tla2rs does not have.

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

### TLC's options

`main.rs` takes TLC's options and passes them on to the checker (README.md lists which are supported and why the
others are not). Measured on TLC 2.19 (`tests/tlc/Opt*`):

- `-continue`: TLC reports the first invariant a new state violates (cfg order), with the behavior, and queues the
  state; a violation by an initial state is reported once (`INITS_REPORTED`: `initial_states` also runs to rebuild
  behaviors). A step violating an action property is reported after its successor is added and checked
  (`SWork::acts`, reported in `insert_candidates` in successor order) and the search goes on. The run ends as a run
  without errors (exit 0). A deadlock stops it as before; a failed invariant is reported as before and then as an
  unexpected exception, exit 255 (`continued_inv_eval`). `-batched` is not used with it
- `-difftrace`: each state after the first shows the conjuncts that differ from the previous state (`trace_text`),
  except that TLC prints the last state of a behavior of three states or more in full (`diff_prev`); a behavior of
  two states has its second state diffed
- `-view`: a behavior shows `show_view` (the VIEW printed with TLC's pretty printer) and no empty line after it, and
  `-dump dot` labels nodes with it. `trace.rs` cannot read such a behavior (a state would run on to the statistics,
  which hold times), so `crosscheck.sh` reads it with `tla2rs --trace-view` (`options.rs`), keyed into the expected
  file only for those configurations, so the other keys stay as they were
- `-nowarning`: the warnings marked `WARNING_MARK` go (`put_line`, `STARTUP_PRINTS_NOWARN`); SANY's and the PlusCal
  warning stay
- `-dump FILE`: `State N:` per distinct state, numbered when written (TLC's order with one worker, so not with
  `-batched`). `-dump dot[,...]`: TLC 2.19 gives each edge `[label="...",color="black",fontcolor="black"]`
  (empty label without `actionlabels`) and adds `{rank = same; ...}` lines, which the comparison ignores. TLC takes
  only one `-dump`, so `crosscheck.sh` leaves out its own and compares the cfg's file with `tla2rs --dump`.
  `colorize` (`-dumpcolors`): the edge gets a placeholder (`COLOR_MARK` around its label) that `dump_write` turns into
  the action's color as it writes the edge to the file, so an edge buffered for a successor TLC never reaches does not
  number one (measured: TLC numbers by name from 2, in the order first written, `tests/tlc/OptDumpColor-Inv`);
  `dump_finish` writes the legend in the order of a Java `HashMap<String, _>` (`java_hash_order`: buckets of
  `String.hashCode` spread, default capacity, resized at 3/4 and on a bucket of more than 8). `options.rs` keeps the
  colors with the edges and lists the legend in file order
- `-userFile FILE` (`-userfile`): what Print and PrintT print is kept as the values as TLC shows them, marked
  (`compile::USER_MARK`, the values separated by `USER_SEP`), and only the standard output pretty-prints them, since
  TLC writes them to the file as is (measured, `tests/tlc/OptUserFile-Wide`); `user_line` in the checker, and
  `main.rs` for the lines of a spec TLC refuses before exploring. `crosscheck.sh` compares the file (its lines and
  their hash)

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
