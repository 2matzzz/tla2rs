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
Temporal properties hold (3 properties, 2 fairness instances, 62 edges).
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
- `-fp128` uses 128-bit fingerprints instead of 64-bit ones
- `-metal` runs the "already seen?" lookups on the GPU (Apple Metal); `-batched` runs the same three-phase pipeline on
  the CPU
- Output (state counts, counterexample format) follows TLC, and so do exit codes: 10 = assumption, 11 = deadlock,
  12 = invariant, 13 = temporal property, 255 = evaluation error

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
   Strings and model values become `u16`, integers `i64`, records tuples, functions arrays, and sets `u128` bitmasks
4. **Code generation** (`codegen.rs`): constant subexpressions are evaluated at compile time and become literals.
   Actions are generated in continuation-passing style, threading "the remaining conjuncts" through; every `\/`,
   `\E`, and `IF` becomes a branch, and `x' = e` becomes a `let`
5. **Runtime** (`runtime.rs`): BFS, level by level, with each level split across threads. States are bit-packed to fit
   their types, and the visited set holds only 64-bit fingerprints. A state of 64 bits or fewer has a reversible
   fingerprint, so it cannot collide
6. **Liveness**: each edge is recorded with the fairness instance it belongs to (e.g. `WF(Create(d1))`). After the
   search, the checker takes the SCCs of the subgraph made of states that can keep violating the property and looks
   for a fair one (or fair stuttering). Counterexamples are lassos, as in TLC

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
| Expressions | logic, arithmetic (`+ - * \div %`), comparison, `IF` / `CASE` / `LET`, `\E` / `\A`, sets (literals, `\cup \cap \`, `\subseteq`, `{x \in S : P}`, `{e : x \in S}`, `Cardinality`, `SUBSET`), functions (`[x \in S \|-> e]`, `f[x]`, `[f EXCEPT ![a] = @ + 1]`, `[S -> T]`), records (`[a \|-> 1]`, `r.a`, `[a : S]`, `!.a`) |
| Actions | `x' = e`, `x' \in S`, `UNCHANGED`, action-level `\/` `\E` `IF` `CASE`, guards that read an already assigned `x'` |
| Specs | `SPECIFICATION` (`Init /\ [][Next]_v /\ fairness`) or `INIT` / `NEXT`. `CONSTANT` values may be model values, numbers, strings, booleans, or sets of them. `ASSUME` is checked |
| Properties | `INVARIANT`. `PROPERTY` supports `<>P`, `[]<>P`, `<>[]P`, `P ~> Q`, `[]P`, and `[][A]_v` (optionally quantified with `\A x \in S :`) |
| Fairness | `WF_v(A)` (optionally quantified with `\A`). `A` must be a named definition called from `Next` |
| State space | `CONSTRAINT`, `VIEW`, `SYMMETRY` |

### Limitations

- **Every variable needs `x \in S` (or `x \subseteq S`) in `TypeOK`**, with `S` finite and written in terms of
  constants only. This is where the representation (bit width) comes from. If a variable leaves its type, the checker
  stops with a type error right there (TLC only stops if `TypeOK` is listed as an invariant)
- Set elements may have at most 128 possible values. Sets of sets and sets of functions cannot be held as values
  (`SUBSET` and `[S -> T]` in `TypeOK` are fine)
- Not supported: sequence and tuple values (`Sequences`), state-dependent `CHOOSE`, recursion, strong fairness (SF),
  `ENABLED`, `<<A>>_v`, function definitions (`f[x \in S] == ...`), and `<-` in the cfg
- Once a state exceeds 64 bits, the visited set holds fingerprints, so, as with TLC, there is a small chance of a
  collision (an estimate is printed at the end)
- Liveness: whether a fair action is enabled is decided by whether the `Next` branch that calls it produces a
  successor. If `Next` narrows the call (`A /\ extra condition`), enabledness is underestimated and a spurious
  counterexample may appear (the checker never wrongly reports that a property holds)
- Liveness checking keeps the whole state graph in memory (about 24 bytes per edge). For invariants only, see Memory
  above
- With `VIEW` and `SYMMETRY` together, the distinct count can be lower than TLC's. TLC sometimes keeps states with
  identical views as separate states (its choice of representative depends on the state itself), while tla2rs folds
  by orbits of the view. With only one of the two, counts match TLC exactly

## Cross-checking against TLC

`scripts/crosscheck.sh` runs the same configuration through TLC (`-workers 1`) and tla2rs and compares the verdict,
generated and distinct state counts, counterexample length, and exit code. `scripts/all.sh` does this for every
configuration in `examples/` and `tests/tlc/`. Point `TLA_TOOLS` at `tla2tools.jar` (default `~/.tla/tla2tools.jar`).

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
- Strong fairness
