# Benchmarking performance changes

This document describes the curated set of benchmarks we use when evaluating
a performance-sensitive change (data structure refactor, propagator rewrite,
search heuristic change, etc.) and how to run them. It is **not** a continuous
performance test suite — it is a checklist for when a maintainer needs to
quantify the wall-time impact of a non-trivial change.

The set was settled on while doing Phase 2 of issue #134. The intent is that
future performance work re-uses it, so that results are comparable across
PRs over time.

## What to run

Eight benchmarks, picked to cover a mix of search-heavy / propagation-heavy
workloads, large/holey domains, and runtime ranges. Build with `cmake --preset
release`; binaries land in `build/`.

| Benchmark               | Command                                       | Approx wall time |
|-------------------------|-----------------------------------------------|------------------|
| `magic_series_300`      | `./build/magic_series --size=300`             | ~6 s             |
| `qap_12`                | `./build/qap --size=12`                       | ~7 s             |
| `langford_11`           | `./build/langford --size=11 --stats`          | ~12 s            |
| `n_queens_14_all`       | `./build/n_queens --size=14 --all`            | ~18 s            |
| `ortho_latin_6_all`     | `./build/ortho_latin --size=6 --all --stats`  | ~20 s            |
| `magic_square_5`        | `./build/magic_square --size=5`               | ~32 s            |
| `tsp_default`           | `./build/tsp`                                 | ~50 s            |
| `n_queens_88`           | `./build/n_queens --size=88`                  | ~5 min           |

The first four cover under-30 s workloads that are quick to iterate on. The
last four (`ortho_latin` onwards) push out further, with `n_queens_88` being
the long pole — keep it in the set even though it dominates total runtime,
because it is the only one that exercises a large search tree at scale.

`magic_series` and `magic_square` are worth keeping for their
linear-arithmetic-heavy propagation, which the others don't exercise.
(`magic_square --size=5` is one of the longer runs in the set — its default
search explores ~6 M nodes — despite the small board.)

### Notes on individual benchmarks

- **`langford --size=11`** finds all solutions by default (the example's
  callback always returns `true`); the `--all` flag is parsed but does not
  change behaviour. `--size=10` has zero solutions and explores a smaller
  space; `--size=11` is large enough to be a useful search benchmark. Bigger
  sizes (`12`, `13`) jump quickly into hours.
- **`ortho_latin --size=6 --all`** exhaustively searches with no solutions
  (Euler's 36 officers — provably no orthogonal pair of order 6 exists), so
  the entire search space is explored. `--size=7` is well over an hour.
- **`n_queens --size=88`** is the canonical MiniCP first-solution-with-default-
  heuristic workload (~49 M recursions). The solver finds the first solution;
  there is no `--all`. Use `--size=14 --all` for a faster all-solutions
  workload.
- **`qap --size=12`** is at the maximum size the example supports.
- **`tsp`** has no `--size` argument; it runs a fixed instance with a
  configurable propagator (`--propagator=prevent` is the default; `scc` is
  the alternative).
- **`magic_series` / `magic_square`** print stats by default; the `--stats`
  flag is for the `examples/` binaries only (not the `minicp_benchmarks/`
  ones).

### Why we don't include certain examples

A few of the `examples/` binaries are not in the set, even though the issue
#134 plan listed them:

- **`knapsack`** has a fixed 6-item instance — solves in <1 ms.
- **`talent`**, **`sudoku`**, **`regex`** all solve their default instances
  in milliseconds. Useful as smoke tests, not as performance signals.

If you want to add one of these to a future benchmarking exercise, use a
larger custom instance — don't rely on the default that the binary ships
with.

## How to compare two builds

Build the baseline (e.g. `main`) in a separate worktree so you can keep both
binaries side-by-side without rebuilding between trials:

```shell
git worktree add ../baseline-worktree main
cd ../baseline-worktree && cmake --preset release && cmake --build --preset release --parallel 32
```

Then run a script that alternates trials between the two builds. Per-build
3-trial sweep is usually enough; the long benchmarks (`tsp`, `n_queens_88`)
have low variance anyway, the short ones can be noisy. Take the median.

A minimal harness:

```bash
#!/bin/bash
set -u
BASELINE=/path/to/baseline-worktree/build
AFTER=/path/to/glasgow-constraint-solver/build
TRIALS=3

bench() {
    local name="$1"; shift
    local cmd="$*"
    for build in baseline after; do
        local dir
        if [ "$build" = baseline ]; then dir=$BASELINE; else dir=$AFTER; fi
        for trial in $(seq 1 $TRIALS); do
            local out
            out=$(/usr/bin/time -f "WALL=%e" $dir/$cmd 2>&1)
            local solve recs props wall
            solve=$(echo "$out" | grep "solve time" | awk '{print $3}' | tr -d 's')
            recs=$(echo "$out"  | grep "^recursions:" | awk '{print $2}')
            props=$(echo "$out" | grep "^propagations:" | awk '{print $2}')
            wall=$(echo "$out" | grep WALL= | sed 's/WALL=//')
            printf "%-22s %-9s t=%d wall=%5ss solve=%6ss recs=%-10s props=%s\n" \
                "$name" "$build" "$trial" "$wall" "$solve" "$recs" "$props"
        done
    done
}

bench magic_series_300   "magic_series --size=300"
bench magic_square_5     "magic_square --size=5"
bench qap_12             "qap --size=12"
bench tsp_default        "tsp"
bench n_queens_88        "n_queens --size=88"
bench langford_11        "langford --size=11 --stats"
bench n_queens_14_all    "n_queens --size=14 --all"
bench ortho_latin_6_all  "ortho_latin --size=6 --all --stats"
```

Total wall time for the full sweep at 3 trials per build is ~50 minutes,
dominated by `n_queens_88` (~30 minutes alone).

## What to capture

- **`solve time`** (printed by every binary in the set) — solver-internal
  wall time, excluding setup and output. This is the primary number.
- **`recursions`** and **`propagations`** — must match exactly between
  builds for any change that does not alter solver semantics. A divergence
  here means the change has affected what the search does, not just how
  fast it does it. Treat that as a correctness signal first, performance
  signal second.
- **External wall time** (`/usr/bin/time -f %e`) — for cross-checking. If
  external wall is much larger than `solve time`, the difference is setup
  / proof I/O / output, which is usually outside the change being measured.

## Benchmarking proof-shape changes

The set above is for *solver* performance. Proof-logging work — a new
constraint variant, a refactor of how a propagator emits scaffolding,
moving from per-call to upfront derivation — is a different kind of
performance change with different signals and different traps.

### What to capture

- **`solve` time** — usually goes up modestly (more proof I/O), but
  it's not the headline.
- **`.pbp` file size** (`stat -c %s …`) — primary signal for proof
  shape. Bigger proof = more lines emitted; smaller is generally better
  but isn't the whole story.
- **VeriPB verify time** (`/usr/bin/time -f %e veripb foo.opb
  foo.pbp`) — primary signal for proof checkability. Slow verify
  matters even when the proof is small (wider proof DB makes each RUP
  more expensive).
- **`recursions` and `propagations`** — must be reported alongside the
  above. They tell the reader how much of the proof reflects search vs
  initialisation. Two propagator variants making identical decisions
  will have identical `recursions` and `propagations[0]`; that's the
  property to sanity-check, and the property that lets the reader
  judge whether the change actually exercised per-call cost.

### The default-mode trap

Most example binaries in `examples/` stop at the first solution by
default. For some constraints and instance generators (e.g.
`regular_random`) that means the search tree is essentially `n+1`
recursions and a few tens of propagations — the bench reflects
initialisation cost only. A proof-shape change that *only* affects
per-call emission cost will be invisible.

Before drawing a conclusion, look at `recursions` and `propagations[0]`
from `--stats`. If they're in the tens, you have a no-search bench.

The fix is to use `--all`, which makes the solution callback return
`true` and enumerates every solution. Some example binaries already
have it (`langford`, `n_queens`, `ortho_latin`, `regular_random` since
issue #215). For binaries without it, adding the flag is a one-line
change to the solution callback.

`--all` typically forces a much smaller `n` to stay under a few
minutes of wall time: solution counts grow exponentially, and each
solution adds proof lines. For the `RegularBacchus` work in PR #216,
the no-`--all` bench at `n=22` produced shallow-search numbers that
mislead about Bacchus's per-call value; the `--all` bench at `n=4..6`
showed the per-call shape clearly (and reversed the proof-size verdict).

### What size to pick

For `--all` mode, scale `n` down until a single trial finishes in
under a minute. The relationship between `n` and recursion count is
combinatorial — `n=10` for `regular_random --all` runs for many
minutes; `n=6` takes ~0.5 s. Useful sizes for proof-shape comparison
sit in the 10³–10⁵ recursion range, which is large enough that the
per-call shape difference between variants is the dominant signal but
small enough that VeriPB finishes verifying both proofs in reasonable
time.

### A structured `Regular` instance: nonogram

`regular_random` is the stress test; `examples/nonogram` is the
structured counterpart, and a better proxy for how `Regular` behaves on
real problems. It posts one automaton per row and per column of a
nonogram, so the search tree has genuine cross-line interaction rather
than a single automaton's near-linear sweep. It takes the same
`--legacy` / `--bacchus` / `--all` knobs, so all three implementations
can be compared on one instance:

```shell
./build/nonogram --dzn 2013/nonogram/dom_10.dzn --all --stats            # default Regular
./build/nonogram --dzn 2013/nonogram/dom_10.dzn --all --stats --bacchus  # RegularBacchus
./build/nonogram --random 20 --seed 1 --all --stats                      # scalable, no data file
```

The MiniZinc Challenge `dom_06`..`dom_14` data files are fixed
instances of increasing size; `--random N` scales continuously without
needing a data file. Enumerating all solutions (`--all`) of an
under-clued or random instance is the proof-shape regime here, exactly
as for `regular_random --all`.

### Cross-variant invariants

When comparing two implementations of the same constraint that should
make identical propagator decisions:

- `recursions` and the first integer of `propagations:` must match
  exactly between the variants on every instance. A divergence
  means the propagator decisions diverged, and the proof-size /
  verify-time difference is no longer measuring just proof shape.
- The number of solutions must match on `--all` runs (sanity check).
- VeriPB must accept both proofs (`s VERIFIED *`). A proof shape
  that's faster but unverifiable is not faster.

### Case study

`dev_docs/regular.md` has both shallow-search and `--all` tables for
the three-way `Regular` / `RegularBacchus` / `RegularLegacy`
comparison, plus a discussion of when each pattern wins. It's a useful
template for similar three-variant proof-logging work.

## Reproducibility caveats

- Pin CPU governor to `performance` if available; thermal throttling on
  longer runs (`n_queens_88`) can produce 5–10 % drift between trials.
- Don't run other CPU-heavy work in parallel.
- Don't include proof verification (`--prove`) in performance numbers —
  proof I/O dominates and is not what the change usually targets. Keep
  proof verification for correctness checks via `ctest`.
- Build flags must match between baseline and after. Both should be
  `--preset release` (default flags); don't mix optimisation levels.
- Use the same machine for both. If you must move, re-run the baseline on
  the new machine — absolute numbers don't transfer.
