# CLAUDE.md

tla2rs is a compiler that takes a TLA+ spec and a TLC `.cfg` and generates a Rust model checker dedicated to that spec.
It has no crate dependencies.

## Common commands

- `cargo build --release` builds the compiler (`target/release/tla2rs`)
- `target/release/tla2rs Spec.tla [-config X.cfg] [-deadlock] [-workers N] [-memlimit MB] [-notrace] [-setcap N] [-seqcap N] [-fp128] [-metal] [-batched] [--emit-only] [-o DIR]`
  - The generated crate goes to `<spec dir>/.tla2rs/<cfg name>/` by default; it is built with
    `cargo build --release --offline` and then run
  - `-workers`, `-memlimit`, `-notrace`, `-tmpdir`, `-metal`, `-batched`, and `-deadlock` are passed on to the
    generated checker, which also accepts them directly
- `scripts/all.sh` cross-checks every configuration in `examples/` and `tests/tlc/` against TLC (all 469 currently
  pass). Run it after every change, and also as `scripts/all.sh -batched` and `scripts/all.sh -metal` when you touch
  either search path (extra arguments are passed on to every run)
- `scripts/crosscheck.sh Spec.tla [X.cfg] [-deadlock]` cross-checks one configuration. Both TLC and tla2rs run with
  one worker, and it compares the verdict, generated and distinct state counts, counterexample length, and exit code.
  If TLC produces no verdict, the check fails
- TLC results and built checkers are cached under `target/crosscheck/` (keys: jar, cfg, arguments and the modules
  the spec reads; generated code and rustc version). A cached TLC result that does not match is rechecked with a
  fresh TLC run. `CROSSCHECK_NO_CACHE=1` disables both; `JOBS=N` sets how many configurations `all.sh` runs at once
- The TLC jar comes from `TLA_TOOLS` (default `~/.tla/tla2tools.jar`)

## Layout

| File | Role |
|---|---|
| `src/lexer.rs` `src/parser.rs` | Lexing and parsing. `/\` and `\/` bullet lists are delimited by column. Also the checks of SANY that tla2rs repeats (see "What SANY refuses"); an error marked with `lexer::SANY` makes the compiler stop with exit 150 |
| `src/cfg.rs` | `.cfg` files (SPECIFICATION / INIT / NEXT / CONSTANT, including `<-` / INVARIANT / PROPERTY / CONSTRAINT / ACTION_CONSTRAINT / VIEW / SYMMETRY / CHECK_DEADLOCK; TYPE / TYPE_CONSTRAINT are ignored as in TLC) |
| `src/expand.rs` | Inlines every operator definition. Bound variables are renamed, and each EXCEPT's `@` gets a unique name too. Call sites are kept as `Expr::Label`. A subexpression named by label or position (`Op!lab`, `Op!1`, `Op!(e)`) is found in the definition as written and expanded as a definition with the bound variables and label parameters on the way as extra parameters (`subexpr`). Operator parameters are bound to the operator (or LAMBDA) passed, with its environment. A RECURSIVE operator called again inside its own expansion becomes `Expr::RecCall`, evaluated at compile time or compiled into a Rust function (`Gen::rec_fn`, which takes the variables it reads, primed or not, as arguments); it is expanded once per combination of operator arguments |
| `src/value.rs` | Compile-time values and constant evaluation (set order follows TLC: smaller sets first) |
| `src/types.rs` | Finite types `Ty`. A set whose element type has at most 128 values is a `u128` bitmask; otherwise it is an `SSet` (sorted fixed-size array). `Opt` is an optional field of a record whose variants have different fields. A record's fields are kept in TLC's order of names (`field_cmp`: the order TLC first creates each name, from `compile::tlc_string_ranks`), which is how TLC compares and prints records. A tuple is a `Rec` with fields `#00001`, `#00002`, ... (`tuple_ty`); a record of more than 12 fields is held as nested groups of 12 (`rec_build`, `rec_field`), since Rust tuples implement `Eq`/`Hash`/`Ord` only up to 12 elements. `IntAtom` holds integers and atoms (model values, also strings) in one `i64` (atom a is `i64::MIN + a`). `Seq` is a sequence (`Sq`, at most QCAP elements; `seq_cap` derives QCAP, from `src/seqlen.rs` when no bound is written). `Bag` is a bag, a count per element (packed as a function to 0..BIG). `PFun` is a function over part of a type (an optional value per element). Over a domain type of more than `DENSE_MAX` (65536) values, or one that is not enumerable, both are sparse (`is_sparse_fun`): an `SSet` of <<key, value>> tuples (`fun_pairs`), which sorts by key, so lookups are binary searches and packing, SYMMETRY and equality are those of sparse sets. `BIG` is an unbounded integer |
| `src/codegen.rs` | Rust generation. Actions are continuation-passing, threading "the remaining conjuncts". As in TLC, `\/` and `\E` branch while some variable is still unassigned. `\A` over a set from the state walks the elements at run time (`gen_forall`), and a recursive operator that assigns variables, called with arguments from the state, becomes a Rust function returning the states its body builds (`gen_rec_action`) |
| `src/compile.rs` | The overall pipeline. Types come from `x \in S` in TypeDecl / TypeOK; for variables without one they are inferred from Init/Next (`infer_types`; an integer range that settles within a few rounds stays finite, one that keeps growing is widened to unbounded). ASSUMEs are evaluated here. `instantiate` turns each definition of an INSTANCE'd module into a hidden definition that takes the module's constants and variables as leading parameters, so expansion substitutes them without capture |
| `src/std_modules.rs` | The identifiers and strings of TLC's standard modules in TLC's reading order (generated from tla2tools.jar), for ordering strings as TLC does |
| `src/seqlen.rs` | Without a written length bound, runs Init and Next over sequence lengths (with `Len(q) < k` tests in a conjunction as bounds) until the variables' lengths settle, giving QCAP |
| `src/live.rs` `src/ltl.rs` | Liveness at compile time: properties become formulas over atoms (state predicates, ENABLED, action predicates), the negation becomes a Büchi automaton by tableau (`ltl.rs`), and fairness becomes per-condition ENABLED / step functions |
| `src/runtime.rs` | The runtime pasted into generated code: level-by-level parallel BFS, bit-packed states, 64-bit fingerprints (with VIEW / SYMMETRY, of the canonical key), and liveness (per state and edge, which property atoms and fairness conditions hold; then an SCC search in the product with each property's automaton, with WF / SF as conditions on components; counterexamples are lassos) |

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
it creates: the strings and model values of the cfg; SANY's built-in names; the identifiers and keywords of each module
as it parses them (root module first, then the modules it extends or instantiates, breadth first; a string equal to an
identifier such as an operator name, or to a name in a standard module, takes that identifier's place); a few more
built-in names; the string literals of each module, dependencies first. `tlc_string_ranks` reproduces this, with the
standard modules' names in `src/std_modules.rs` (generated from TLC's jar).

Strings created while exploring (by `\o`, `Append`, `ToString`, ...) are not ordered as in TLC: tla2rs computes them at
compile time and numbers them after the others. Reproducing TLC is not possible in general (Refs #23):

- TLC creates such a string the first time it evaluates the expression, which depends on its evaluation of everything:
  a definition of constant level that nothing uses changes the order, because TLC evaluates those at startup (with
  `Words == {"c" \o s : s \in {"a", "b"}}` present, `{x \o "b", x \o "a"}` prints as `{"ca", "cb"}` and CHOOSE picks
  `"ca"`; without it, `{"cb", "ca"}` and `"cb"`). tla2rs folds constant expressions at compile time and evaluates
  others in its own order
- With several workers the order depends on thread scheduling: CHOOSE over `{ToString(n) \o "w" : n \in 1..2000}`
  after the search created those strings gave `"4w"`, `"1w"`, `"2w"` and `"4w"` in four runs with `-workers 4`, and
  `"1w"` every time with one worker

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
- An invariant or property of constant level is evaluated once before exploring; if it is not TRUE, TLC stops (exit
  151). TLC also evaluates every definition of constant level without arguments when it starts, then the ASSUMEs, and
  keeps the values: `Print` / `PrintT` in them print once, before anything else (`STARTUP_PRINTS`), and not when the
  definition is used later

### Functions over sets that cannot be enumerated

TLC evaluates `[x \in S |-> e]` lazily. Measured on TLC 2.19 with S = Nat (`tests/tlc/LazyFun*`, `NatDom-InNat`):

- `f[k]` checks that k is in S and evaluates e at k; outside S it stops ("In applying the function ... which is not
  in its domain", exit 75). `[f EXCEPT ![k] = v]` with k outside S is a no-op (TLC warns), so applying it at k fails
- Storing it in a variable fails ("Attempted to compute the number of elements in the overridden value Nat.", exit
  75), and so do comparing it, `DOMAIN f = Nat` and `f \in [Nat -> Nat]` in an invariant (when TLC fingerprints it).
  A finite function in `[Nat -> Nat]` fails too ("Attempted to check equality of the set ... with the value: Nat")
- `ToString(f)` succeeds and prints the source text of the function

tla2rs compiles `f[k]` (also after EXCEPT with one index per update) and `k \in DOMAIN f` to the membership test and
the body (`Gen::lazy_apply`), also over a constant set of more than 65536 elements (`lazy_domain`), and refuses such a
function over an infinite set anywhere else. Constant folding applies `[x \in S |-> e][k]` the same way (`value.rs`).

### Tuples compared with strings

TLC asks the value on the left of `=` whether it equals the one on the right. Measured on TLC 2.19
(`tests/tlc/TupleStr*`): a tuple asked about a string compares itself with the string's characters (`<<"a", "b">> = s`
is TRUE for s = "ab"), a string asked about a tuple stops with an error, and a model value is unequal to both. For
`x \in S`, a set written out where it is used asks each element in the order written (`s \in {<<"a", "b">>}` is
TRUE), while a set from a definition or the state has been sorted, and comparing a string with a tuple then fails.
`Gen::tuple_str_eq` follows this. One case is not matched: TLC finds `s \in TS \cup {}` TRUE where TS is such a sorted
set (`s \in TS` fails); tla2rs fails on both.

### What SANY refuses

TLC stops with exit 150 before checking anything when SANY refuses a spec. tla2rs repeats these of SANY's checks
(measured on SANY 2.19, `tests/tlc/RejSany*`):

- Precedence conflicts: two infix operators whose ranges in the TLA+ table overlap, next to each other without
  parentheses, unless they are the same operator and it associates (`a + b + c` is fine, `a = b = c`, `a % b % c`,
  `a /\ b \/ c` and `a * b \div c` are not). The parser checks each operator against the one before it at the same level
  and the one it is the right operand of (`parser::sany_range`)
- Names: a bound variable, operator parameter or LET definition named like a CONSTANT or VARIABLE, a definition before
  it in the module, Nat / Int (when extended), or an enclosing bound variable. A LET definition is in scope only after
  its own body (`LET i == CHOOSE i \in S : P` is fine). A CHOOSE body extends as far as it can, so a second CHOOSE with
  the same bound name later on the same line is inside the first and refused
- Unary minus without Integers (or Reals), `:>` and `@@` without TLC (or Bags, which extends it) unless defined. The
  other standard modules instantiate theirs LOCALly, so extending them gives nothing
- String escapes other than `\\ \" \n \t \r \f`

Not repeated: names that clash with definitions of other modules the spec extends, other operators of standard modules
used without extending them, prefix operators in precedence conflicts, and SANY errors in definitions nothing uses
(SANY checks every definition; tla2rs finds a bad subexpression name only when it expands it).

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
  element is one level of generated code, up to the number of values of the set's element type (refused beyond 16);
  once B only reads what is assigned, the remaining elements are a test (`Gen::gen_forall`)
- A recursive operator becomes a Rust function that evaluates its body as an action and returns each state it builds
  with the bit mask of the variables assigned by then (at most 64 variables). The action continues from each returned
  state, once per mask. A call of the operator in its own body uses the masks found so far, and the body is generated
  again until they settle (`Gen::gen_rec_action`, `rec_action_fn`). In Init, arguments must still be constant

### Liveness counterexamples are not compared

For a violated temporal property, `scripts/crosscheck.sh` compares the verdict, the counts and the exit code, but not
the lasso. TLC's lasso is not reproducible from the spec alone: the successors of a state in its liveness graph come
out of a hash set keyed by fingerprint (`tlc2.util.SetOfStates`), and TLC picks the fingerprint polynomial at random on
each run (`with fp N` in its banner). The same configuration then gives different lassos. For
`tests/tlc/LiveForms-NoneImplies.cfg`, ten runs gave 5 states eight times and 4 states twice; with `-fp 1` it is 4
states every time, with `-fp 50` 5 states every time. Matching TLC would take its FP64 fingerprint of every value for a
fixed polynomial, its hash-set order, and a port of its tableau, normal form, SCC search and trace construction
(`tlc2.tool.liveness.LiveWorker`), and would still hold only for that `-fp`.

What is checked instead: the verdict and exit code of every liveness configuration, including the formulas TLC refuses
(`tests/tlc/RejTemp*.cfg`), and the counts at which liveness checks stop on an evaluation error.

### VIEW and SYMMETRY together

TLC sometimes keeps states whose views are identical as separate states (its choice of representative depends on the
state, not the view; changing `-fp` does not avoid it). tla2rs folds by orbits of the view, so its distinct count is at
most TLC's. VIEW alone and SYMMETRY alone both match TLC exactly (`tests/tlc/ViewSym-NoSym.cfg` and
`ViewSym-SymOnly.cfg`).

So when a cfg has both VIEW and SYMMETRY, `scripts/crosscheck.sh` compares only the verdict and prints
`MATCH(verdict only; VIEW+SYMMETRY)`. To compare counts, run a cfg without SYMMETRY.

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
