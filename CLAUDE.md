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
- `scripts/all.sh` cross-checks every configuration in `examples/` and `tests/tlc/` against TLC (all 190 currently
  pass). Run it after every change, and also as `scripts/all.sh -batched` and `scripts/all.sh -metal` when you touch
  either search path (extra arguments are passed on to every run)
- `scripts/crosscheck.sh Spec.tla [X.cfg] [-deadlock]` cross-checks one configuration. Both TLC and tla2rs run with
  one worker, and it compares the verdict, generated and distinct state counts, counterexample length, and exit code.
  If TLC produces no verdict, the check fails
- The TLC jar comes from `TLA_TOOLS` (default `~/.tla/tla2tools.jar`)

## Layout

| File | Role |
|---|---|
| `src/lexer.rs` `src/parser.rs` | Lexing and parsing. `/\` and `\/` bullet lists are delimited by column |
| `src/cfg.rs` | `.cfg` files (SPECIFICATION / INIT / NEXT / CONSTANT, including `<-` / INVARIANT / PROPERTY / CONSTRAINT / ACTION_CONSTRAINT / VIEW / SYMMETRY / CHECK_DEADLOCK; TYPE / TYPE_CONSTRAINT are ignored as in TLC) |
| `src/expand.rs` | Inlines every operator definition. Bound variables are renamed, and each EXCEPT's `@` gets a unique name too. Call sites are kept as `Expr::Label`. Operator parameters are bound to the operator (or LAMBDA) passed, with its environment. A RECURSIVE operator called again inside its own expansion becomes `Expr::RecCall`, evaluated at compile time or compiled into a Rust function (`Gen::rec_fn`) |
| `src/value.rs` | Compile-time values and constant evaluation (set order follows TLC: smaller sets first) |
| `src/types.rs` | Finite types `Ty`. A set whose element type has at most 128 values is a `u128` bitmask; otherwise it is an `SSet` (sorted fixed-size array). `Opt` is an optional field of a record whose variants have different fields. A tuple is a `Rec` with fields `#01`, `#02`, ... (`tuple_ty`). `IntAtom` holds integers and atoms (model values, also strings) in one `i64` (atom a is `i64::MIN + a`). `Seq` is a sequence (`Sq`, at most QCAP elements; `seq_cap` derives QCAP). `BIG` is an unbounded integer |
| `src/codegen.rs` | Rust generation. Actions are continuation-passing, threading "the remaining conjuncts". As in TLC, `\/` and `\E` branch while some variable is still unassigned |
| `src/compile.rs` | The overall pipeline. Types come from `x \in S` in TypeDecl / TypeOK; for variables without one they are inferred from Init/Next (`infer_types`; an integer range that settles within a few rounds stays finite, one that keeps growing is widened to unbounded). ASSUMEs are evaluated here. `instantiate` turns each definition of an INSTANCE'd module into a hidden definition that takes the module's constants and variables as leading parameters, so expansion substitutes them without capture |
| `src/runtime.rs` | The runtime pasted into generated code: level-by-level parallel BFS, bit-packed states, 64-bit fingerprints (with VIEW / SYMMETRY, of the canonical key), and liveness (SCC search with WF; counterexamples are lassos) |

### Memory use (`runtime.rs`)

There are two paths, depending on what is checked.

| | What is kept | Per state |
|---|---|---|
| Invariants only (`run_safety`) | The fingerprint and the fingerprint of the state it was first reached from, plus the states of the current and next level | 16 bytes (8 with `-notrace`) |
| With temporal properties (`run_liveness`) | The whole state graph (states, parents, edges, fairness marks) | State width + a few dozen bytes |

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
