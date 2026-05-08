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
| `magic_square_5`        | `./build/magic_square --size=5`               | ~7 s             |
| `langford_11`           | `./build/langford --size=11 --stats`          | ~12 s            |
| `n_queens_14_all`       | `./build/n_queens --size=14 --all`            | ~18 s            |
| `ortho_latin_6_all`     | `./build/ortho_latin --size=6 --all --stats`  | ~20 s            |
| `qap_12`                | `./build/qap --size=12`                       | ~33 s            |
| `tsp_default`           | `./build/tsp`                                 | ~60 s            |
| `n_queens_88`           | `./build/n_queens --size=88`                  | ~5 min           |

The first four cover under-30 s workloads that are quick to iterate on. The
last four (`ortho_latin` onwards) push out further, with `n_queens_88` being
the long pole — keep it in the set even though it dominates total runtime,
because it is the only one that exercises a large search tree at scale.

`magic_series` and `magic_square` are fast but worth keeping: they exercise
linear-arithmetic-heavy propagation that the others don't.

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
