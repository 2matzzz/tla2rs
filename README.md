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
- `-setcap N` sets the capacity of sets whose size is only known at run time
- `-seqcap N` sets the maximum length of sequences (at most 1024), when the spec does not bound them with
  `Len(x) <= N` in `TypeOK` or a `CONSTRAINT`, or `UNION {[1..n -> S] : n \in 0..N}`. Otherwise the lengths are
  computed from Init and Next until they stop growing (a length test such as `Len(q) < N` in an action bounds `q`
  there); if they keep growing, the length tests in the spec suggest the bound
- `-fp128` uses 128-bit fingerprints instead of 64-bit ones
- `-metal` runs the "already seen?" lookups on the GPU (Apple Metal); `-batched` runs the same three-phase pipeline on
  the CPU
- Output (state counts, counterexample format) follows TLC, and so do exit codes: 10 = assumption (false or failing to
  evaluate), 11 = deadlock, 12 = invariant, 13 = temporal or action property. An evaluation error exits with 76 in an
  invariant, 75 in the initial states, and otherwise 255 for a failed arithmetic operation (such as `\div` by zero) and
  75 for the rest

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
   Strings and model values become `u16`, integers `i64`, records and tuples Rust tuples, functions arrays, and sets
   `u128` bitmasks
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
| Expressions | logic, arithmetic (`+ - * \div % ^`), comparison, sequences (`Seq`, `Len`, `Append`, `Head`, `Tail`, `SubSeq`, `SelectSeq`, `\o`, indexing, a tuple and a function over 1..n being the same value), sets of sets and of functions as values, `IF` / `CASE` / `LET`, `\E` / `\A` (also `<<x, y>> \in S`), `CHOOSE` (also over sets in the state, picking what TLC picks), `RECURSIVE` operators and recursive function definitions, operator parameters and `LAMBDA`, infix operators defined by the spec (`a \oplus b == ...`), `Assert` / `Print` / `PrintT` / `:>` / `@@` from TLC, `UNION`, `SUBSET` and `\X` of sets in the state, sets (literals, `\cup \cap \`, `\subseteq`, `{x \in S : P}`, `{e : x \in S}`, `Cardinality`, `SUBSET`), functions (`[x \in S \|-> e]`, `[x \in S, y \in T \|-> e]`, non-recursive definitions `f[x \in S] == e`, `f[x]`, `[f EXCEPT ![a] = @ + 1]`, `[S -> T]`), records (`[a \|-> 1]`, `r.a`, `[a : S]`, `!.a`), fixed-length tuples (`<<a, b>>`, `t[1]` with a constant index, `![k][1]`, `A \X B`) |
| Actions | `x' = e`, `x' \in S`, `UNCHANGED`, action-level `\/` `\E` `IF` `CASE`, guards that read an already assigned `x'` |
| Specs | `SPECIFICATION` (`Init /\ [][Next]_v /\ fairness`) or `INIT` / `NEXT`. `CONSTANT` values may be model values, natural numbers, strings, booleans, or sets of them, nested to any depth (as in TLC). A model value may share a type with integers (`1..4 \cup {None}`), and arithmetic on such a value is an evaluation error only when it is a model value; a variable may also hold an integer or a string, and comparing the two is an evaluation error, as in TLC. `Name <- Def` substitutes a definition (also from a module that EXTENDS the spec, such as an MC.tla) for a constant, and `<-` / `=` on a defined name replace that definition. `ASSUME` is checked. `INSTANCE` (unnamed, `LOCAL`, `N(p) == INSTANCE M WITH x <- e` used as `N!Op`, also with operator parameters, inside LET, of standard modules as in `S!Len`, and with operator symbols in `WITH`). `EXTENDS RealTime` gives the variable `now` (RTBound and RTnow are refused, as TLC does). Theorems, proofs, `USE` / `HIDE` are skipped, as TLC does |
| Properties | `INVARIANT` (may use `ENABLED`). `PROPERTY` takes temporal formulas built from state predicates, `ENABLED A`, action predicates (`<<A>>_v`, `[A]_v`), `[]`, `<>`, `~>`, `/\ \/ ~ =>`, `IF`, `WF` / `SF`, and `\A` / `\E` over constant sets (also of records). As in TLC, `[]P` for a state predicate P is checked as an invariant, `[][A]_v` while exploring, and a state predicate on the initial states. Formulas TLC refuses (SANY's level rules, an action not in the form `<>[]A` or `[]<>A`, `<=>` between temporal formulas, a quantifier over a non-constant set) are refused with TLC's message and exit code |
| Fairness | `WF_v(A)` and `SF_v(A)`, on named or inline actions, optionally quantified with `\A`. Whether `<<A>>_v` is enabled is decided on A itself, as in TLC |
| State space | `CONSTRAINT`, `ACTION_CONSTRAINT`, `VIEW`, `SYMMETRY` (`TYPE` / `TYPE_CONSTRAINT` are accepted and ignored, as in TLC) |

### Limitations

- **Every variable needs `x \in S` (or `x \subseteq S`) in `TypeOK`**, with `S` finite and written in terms of
  constants only. This is where the representation (bit width) comes from. If a variable leaves its type, the checker
  stops with a type error right there (TLC only stops if `TypeOK` is listed as an invariant). A variable missing from
  `TypeOK` gets a type inferred from Init and Next; an integer range that settles (a `Cardinality`, `x % 3`) stays
  finite, one that keeps growing becomes unbounded
- A set whose element type has at most 128 values is a bitmask; a larger one (including sets of sets) is a sorted array
  of up to `-setcap` elements. A sequence holds up to `-seqcap` elements (see above); growing past it is an
  evaluation error
- Standard modules: `Naturals`, `Integers`, `FiniteSets`, `Sequences` (with `SortSeq`; strings are sequences of
  characters for `\o`, `Len`, `Head`, `Tail`, `Append`, `SubSeq`), `Bags`, `STRING`, and from `TLC` `Print`, `PrintT`,
  `Assert`, `ToString` (of a value from the state when it is a Boolean, integer, string, model value or tuple of
  them, with at most 4096 possible values), `TLCEval`, `Any`, `:>`, `@@`, `Permutations`, `SortSeq`
- Functions over a set from the state (`[x \in S |-> e]`, `[S -> T]`, `:>`, `@@`, `Permutations`) are functions over
  part of a type; nested modules can be instantiated; user-defined postfix operators (`^+`, `^*`, `^#`) and the
  infix operators `--` and `|-` are accepted; `Print` and `PrintT` write to stdout as TLC does
- Not supported: `RandomElement` of more than one element, `JavaTime`, `TLCGet` / `TLCSet` (each is rejected with a
  reason), sets that may hold both strings and integers, ENABLED inside a recursive operator, and
  `Name <- [Module] Def` for a CONSTANT (TLC rejects it too)
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
  depends on a fingerprint polynomial TLC picks at random), so cross-checks compare only the verdict, counts and exit
  code
- With `VIEW` and `SYMMETRY` together, the distinct count can be lower than TLC's. TLC sometimes keeps states with
  identical views as separate states (its choice of representative depends on the state itself), while tla2rs folds
  by orbits of the view. With only one of the two, counts match TLC exactly

## Cross-checking against TLC

`scripts/crosscheck.sh` runs the same configuration through TLC (`-workers 1`) and tla2rs and compares the verdict,
generated and distinct state counts, counterexample length, and exit code. `scripts/all.sh` does this for every
configuration in `examples/` and `tests/tlc/`, passing extra arguments such as `-batched` on to each run. Point
`TLA_TOOLS` at `tla2tools.jar` (default `~/.tla/tla2tools.jar`).

```
$ scripts/all.sh
ok    examples/DieHard.cfg
ok    examples/Peterson-Live.cfg
ok    examples/TwoPhase.cfg
...
```

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
