# Benchmarking performance changes

This document describes the curated set of benchmarks we use when evaluating
a performance-sensitive change (data structure refactor, propagator rewrite,
search heuristic change, etc.) and how to run them. It is **not** a continuous
performance test suite — it is a checklist for when a maintainer needs to
quantify the wall-time impact of a non-trivial change.

The set was settled on while doing Phase 2 of issue #134. The intent is that
future performance work re-uses it, so that results are comparable across
PRs over time.

**If the question is how gcs compares with another solver** rather than how one
build of gcs compares with another, use
[cross-solver-benchmarking.md](cross-solver-benchmarking.md): a cross-solver time
ratio only means something where the search trees are identical, and that
document covers how to pin one and how to tell when you have not.

**If the change under test is on the proof side**, use
[proof-benchmarks.md](proof-benchmarks.md) instead: it curates a separate set
of instances for measuring proof-writing cost, proof size and VeriPB checking
time. The two sets are almost disjoint, because sizes that make a good solve
benchmark are usually far too large to proof-log — `ortho_latin --size=6 --all`
and `tsp` from the table below both write more than 4 GB of `.pbp`. The
"Benchmarking proof-shape changes" section further down remains the methodology
for that work; proof-benchmarks.md is the instance set to apply it to.

## What to run

Eight benchmarks, picked to cover a mix of search-heavy / propagation-heavy
workloads, large/holey domains, and runtime ranges. Build with `cmake --preset
release`; binaries land in `build/`.

| Benchmark               | Command                                       | Approx wall time |
|-------------------------|-----------------------------------------------|------------------|
| `qap_12`                | `./build/qap --size=12`                       | ~1.5 s           |
| `magic_series_300`      | `./build/magic_series --size=300`             | ~5 s             |
| `langford_11`           | `./build/langford --size=11 --stats`          | ~8 s             |
| `tsp_default`           | `./build/tsp`                                 | ~10 s            |
| `n_queens_14_all`       | `./build/n_queens --size=14 --all`            | ~12 s            |
| `magic_square_5`        | `./build/magic_square --size=5`               | ~18 s            |
| `ortho_latin_6_all`     | `./build/ortho_latin --size=6 --all --stats`  | ~23 s            |
| `n_queens_88`           | `./build/n_queens --size=88`                  | ~3.5 min         |

Wall times re-measured on the dev VM (2026-07); they are much lower than in
earlier revisions of this doc thanks to accumulated propagation/search work
(`qap` and `tsp` are ~4–5× faster than when the set was first curated).
Absolute numbers are machine-dependent — see Reproducibility caveats — so
treat them as rough ranges, not a fixed baseline.

Every benchmark except `n_queens_88` now finishes in well under half a minute,
so they are quick to iterate on. `n_queens_88` is the long pole — keep it in
the set even though it dominates total runtime, because it is the only one
that exercises a large search tree at scale.

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

### The `benchmarks/` tree

The eight benchmarks above are drawn from `examples/` and
`minicp_benchmarks/`, which are the binaries with fixed instances worth
timing end to end. Separately, `benchmarks/` holds the programs whose only
purpose is measurement — propagator and mechanism micro-benchmarks such as
`linear_prop_cost`, `wake_cost`, `slack_watch` and the random-table
harnesses. They take a size or repeat count and print timings, so none of
them is a ctest and none belongs in the curated set above; reach for them
when you are attributing a change to a specific mechanism rather than
measuring end-to-end solve time.

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

Total wall time for the full sweep at 3 trials per build is ~30 minutes,
dominated by `n_queens_88` (~20 minutes alone).

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

## Choosing the metric

The list above is what to capture. Which of those numbers carries the answer
depends on what the change did to the search, and getting that wrong has
produced more retracted results here than measurement noise ever has.

### When the search is identical, count instructions, not seconds

If two builds run the same search — same `recursions`, same `propagations`, so
that the only difference is how the same work gets executed — compare
**instructions retired**. On one machine `langford --size=11` retires 47.587e9
instructions with a spread of 0.002% across five runs, while wall time and
cycles for the *same* binary move about 1% within a single interleaved batch and
about 3% between one hour and the next. A 1% effect is invisible to wall time and
unmissable in instructions.

```shell
perf stat -e instructions,cycles,branch-misses,L1-icache-load-misses -x, \
    taskset -c 4 ./build/langford --size=11
```

Read cycles *alongside* instructions rather than instead of them — the pair is
what diagnoses. On #878 the variant that retired **fewer** instructions burned
2–3% **more** cycles, and that is what rejected it; a wall-time-only run would
have called the whole thing noise. The first wall-time batch on that issue (five
repeats, pinned, interleaved) reported the variant 0.8% *slower*, where the
instruction count said +0.11% and a reversed-order batch then agreed with the
instruction count.

Instructions are load-insensitive; cycles are not. Interleave the variants within
each repeat, and check what else is running before believing a cycles figure.

If the search shape *does* change, none of this applies: the two runs are then
doing different amounts of work, and no per-unit figure can be read off them.
`propagator-performance.md` ("Is it the propagator, the strength, or the
search?") is the separation to do first.

### "Search is unchanged" is a claim about the corpus, not about the change

When a change touches something every search reads — variable degree, trigger or
scope accounting, wake order — "all N tests pass and the search is unchanged" is
evidence about the shapes the corpus happens to contain.

Commit `d9a8dc93` (#506) switched degree accounting from per-trigger-slot to
per-distinct-scope-variable, justified in its own commit message with "no real
constraint does that". `ReifiedCompareLessThanOrMaybeEqual` does exactly that
whenever the reified expression mentions its own condition variable, because the
dispatcher appends an `on_change` trigger to the propagator's own `on_bounds`
one. On CPMpy's `p <-> (p <= BV113)` the root branch flipped and the model went
from 25 to 7,085,707 nodes. All 517 tests still passed.

Before claiming the search is unchanged, name the shape the change *could* alter
and go and find one. Grepping for constructs that add triggers **implicitly**
(reification dispatchers, umbrella installers) is the cheap version.
Frontend-generated models are the good hunting ground, because CPMpy and MiniZinc
flattening alias variables in ways hand-written tests never do. Note that the
change above was kept — it is the principled accounting — so the lesson is about
the justification, not the change.

### Nothing that divides by time means anything on a capped row

On a row where the run hit a timeout, both configurations ran the same wall time,
so anything divided by time is a constant away from the node count. That kills
two figures, and #788 published both before spotting either: "throughput falls
10× to 30×" was the node count divided by 60 s, and — less obviously — the *node
ratio* between two configurations was the same quantity wearing the other hat.
"Node counts fall 34.8× at n=100" was two runs that had both hit the cap; across
the instances where both arms actually finished, the reduction was 1.09× to
1.38×. Those two numbers lead to completely different decisions, and the wrong
one is the exciting-looking one.

- On a capped row, only the **objective reached** and the **absolute node count**
  mean anything. Nodes/s, node ratios, per-node cost and speed-ups all need every
  configuration in the comparison to have finished.
- If too few finish, shorten the instances rather than the reasoning: a cut-down
  family that finishes beats a real one that caps.
- Say in the table which rows are capped, and put derived columns only on the
  uncapped ones. A footnote is not enough.
- Declare the selection effect: the instances both arms finish are the easy ones,
  so "1.09–1.38×" is not evidence that the reduction is small on the hard ones.
  It is evidence that there is no *measured* support for a large one.
- The giveaway is a "throughput ratio" or "node reduction" that equals the node
  ratio to two significant figures on every capped row. That is not a striking
  finding, it is arithmetic.

### A per-node figure is a product of two independent things

Calls per node and cost per call vary independently, so a per-node cost can move
without either one behaving the way you read it. #788's walk looked "1.0× on
`tpp` at n=35 but 10× on `mario` at n=30", which reads as "the cost is not a
function of n". It is: per *call* it is 7.7 µs at n=15 and 30.7 µs at n=35 on the
same family, and `tpp` merely wakes the propagator 676 times in a 7.5-million-node
search. Never conclude anything about per-call cost from a per-node figure; split
it with `GCS_PROPAGATOR_STATS` first (see
[propagator-performance.md](propagator-performance.md)).

## Benchmarking proof-shape changes

The set above is for *solver* performance. Proof-logging work — a new
constraint variant, a refactor of how a propagator emits scaffolding,
moving from per-call to upfront derivation — is a different kind of
performance change with different signals and different traps.

The rest of this section is the methodology. For the instances to apply it
to, see [proof-benchmarks.md](proof-benchmarks.md), which curates a set sized
so that VeriPB takes minutes rather than milliseconds, and which separates
instances that stress proof *writing* from those that stress proof
*checking* — the two are close to opposites, and a change that helps one
routinely hurts the other.

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

### The bare-model trap, for anything about hints

A hint-free `rup` propagates over the whole live constraint database, so
what it costs depends on what else is standing — and a harness built to
exercise one derivation deliberately has nothing else standing. Measure
a hinting change that way and you will conclude it is not worth doing.

Worked example (issue #676): hinting the lifted cover cut replay was
worth 25 % of checking time against a model that was one capacity row
per time point, and **six to fourteen times** against real RCPSP
models, where the standing database is the whole model. Same code, same
proof shape, two orders of magnitude apart in how the answer reads. The
checker's peak memory went the other way — two thirds off on the bare
model, nothing on the real one, where the model sets it.

So for any change to hints, or to what lives at `ProofLevel::Top`,
**bench against a real instance as well as a harness**, and report both.
A root refutation is the cheap way to get one: it is a proof of the
derivation and nothing else, with no search in it to confound the
reading (`examples/rcpsp --deadline <bound-1> --prove`, and see
`dev_docs/certified-makespan-bounds.md`).

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

**`--random N` does not deliver that regime, though.** The generator
builds the clues from a random picture, so the puzzle it poses is very
nearly determined and `--all` barely searches: `--random 20 --seed 1
--all` measures **17 recursions and 3 solutions**, which is inside the
"tens of recursions means a no-search bench" band described two sections
above. `--seed 3` gives 3 recursions. Use the `--dzn` instances, which
are genuinely under-clued, and treat `--random` as a smoke test only.

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

## Profiling with `perf`

When a benchmark says a change is slower but not *why*, `perf` gives the
per-function self-time.

A Release build carries `-g1` debug info: function names and line-number
tables, but no inline-expansion records (see the debug-info comment in
the top-level `CMakeLists.txt`). `perf` handles that level comfortably,
with one attribution caveat: with no inline records, every sample is
credited to the outermost function that survived inlining, so a hot
propagator absorbs the self-time of everything inlined into it. The
line-number tables do still cover the inlined code, so `perf annotate`
(or `perf script -F ip,sym,srcline`) can usually tell you *what* inside
the big function is hot.

If you genuinely need per-inlined-frame attribution, raise the Release
debug level temporarily (edit the `$<IF:...>` debug-level generator
expression in the top-level `CMakeLists.txt`) — and know the trap that
comes with it, because it will waste an afternoon if you hit it
unprepared. On a binary carrying full DWARF from heavy template inlining
(`fzn-glasgow` was ~380 MB back when Release used `-g3`), `perf report` /
`perf script` resolve every sample's *inlined* frames by default, and on
that much `debug_info` the resolution is pathologically slow: it can take
many minutes to process a few tens of thousands of samples, so
`perf report` looks **hung** and `perf script` appears to emit only a few
hundred startup samples before you give up. The symbols are all there;
the inline expansion is the bottleneck. Skip it whenever you don't need
it — one flag:

```shell
perf record -F 2000 --call-graph fp -o out.perf -- taskset -c 4 ./build/fzn-glasgow model.fzn
perf report  -i out.perf --stdio --inline=no          # completes in seconds
perf script  -i out.perf -F ip,sym --no-inline        # full, fast output
```

(On a `-g1` build those flags are harmless no-ops — there are no inline
records to resolve — so the recipes above are safe defaults everywhere.)

For a clean self-time (leaf) histogram from `perf script`, take the first
line of each blank-separated sample block and aggregate:

```shell
perf script -i out.perf -F ip,sym --no-inline \
  | awk 'BEGIN{want=1} /^[[:space:]]*$/{want=1;next} want{print;want=0}' \
  | sed -E 's/^\s*[0-9a-f]+\s+//' | sort | uniq -c | sort -rn | head
```

Two more notes:

- `fzn-glasgow` is launched by MiniZinc as a subprocess, which perf can't
  easily follow. Flatten once (`minizinc --solver <glasgow.msc> -c --fzn
  model.fzn model.mzn data.dzn`) and run `fzn-glasgow model.fzn` directly
  under perf. It has a `-t <ms>` timeout, so an optimisation instance that
  never finishes still gives a usable sample window.
- Kernel-mode samples show up as `[unknown]` unless you can read
  `/proc/kallsyms` (needs `kptr_restrict=0` or root). For a CPU-bound
  solver these are a small minority and don't obscure the userspace hot
  path.

If perf is unavailable or a subprocess is genuinely unreachable, a couple
of `getenv`-gated static counters around the suspected hot lines (printed
from a destructor) will tell you a call-count distribution in one run —
crude, but enough to distinguish "expensive once" from "cheap but called a
billion times".

## Reporting the numbers

Every defect in this section was caught by review of a numbers-heavy document
that was otherwise correct, and each one survived because it sat *next to* the
evidence rather than in it.

- **Quote rows that are printed.** A figure whose instance appears in no table
  cannot be checked by anyone, and drifts out of agreement with the set as the
  set changes underneath it. `proof-benchmarks.md` once headlined a
  cost-per-byte range with an instance that was in no group, and took the other
  end of the range from a different campaign's artefacts. If you state a range
  over a selection, either print the whole selection or say what the selection
  rule was: "every group A and B row except the four measured after the pilot" is
  checkable, "twenty of the rows" with eight shown is not.
- **A superlative next to a table is a claim about that table.** Read the column
  and confirm the row is the one you named. Where only a tendency exists, say so,
  give the coefficient, and name the concrete pair that makes it vivid.
- **A "mean" is a division.** Compute it (`awk '{s+=$1} END {print s/NR}'`),
  never eyeball it from a sorted listing — that samples the large end. Where a
  per-item measurement is all you have, either keep it labelled as that one item
  or convert it to a fraction and apply that to a measured total. Cross-check any
  derived figure against another number in the same table before it lands
  anywhere permanent: one such figure, multiplied back out, came to more than the
  whole tree it was describing.
- **An "X out of Y" must count one unit.** Write both as products and check they
  share a factor set. `large-domains.md` once said a run over 31 instances leaves
  "six artefacts to compare out of 124", where 124 was 31 instances × 4 extensions
  and six was 3 basenames × 2 extensions; the real answer was twelve.
- **Name the population, especially when an older draw is still around.** Two
  numbers for one quantity with no populations attached read as a contradiction.
  If the prose keeps quoting a ratio the table only implies, make it a column so
  it is read off rather than remembered — that is how a figure from stage zero's
  30,000-instance draw ended up quoted in a section whose own table reported a
  20,000-instance one, in five places including two class comments.
- **Fix the commit message too.** The same sentence usually lives in both.

## Reproducibility caveats

- Pin CPU governor to `performance` if available; thermal throttling on
  longer runs (`n_queens_88`) can produce 5–10 % drift between trials.
- Don't run other CPU-heavy work in parallel. This is not only about core
  contention, and `taskset` does not protect you from it: figures taken while a
  9 GB-RSS run was in flight on another core read **2× slow** (21.3 s against
  10.8 s idle) for a deep enumeration with allocation churn, while cache-resident
  workloads measured alongside it reproduced within 1%. Adding a spinning burner
  on another core changed nothing, so the variable was memory bandwidth. The
  cheap discriminator: repeat the measurement three times on an idle machine, and
  if it moves by 2×, load was the variable rather than the code.
- **Put exact counts in a comment, never in an assertion.** Recursion counts and
  per-rule counters are deterministic for a given build and *not* across
  toolchains — different standard libraries break ties differently, so sweep order
  and intermediate work differ even where the fixpoint does not. A ctest pinning
  `recursions: 963` and another pinning a counter triple both failed on macOS and
  on ubuntu-24.04 (#776); `examples/rcpsp/CMakeLists.txt` has exact counts all
  through it and not one of them is an assertion. Assert an invariant that
  travels instead: for a counter, "switched off reports four zeroes" plus
  "switched on reports firings" pins each counter to the rule it is named after,
  which is the failure worth catching, and holds everywhere.
- Don't include proof verification (`--prove`) in performance numbers —
  proof I/O dominates and is not what the change usually targets. Keep
  proof verification for correctness checks via `ctest`.
- Build flags must match between baseline and after. Both should be
  `--preset release` (default flags); don't mix optimisation levels.
- Use the same machine for both. If you must move, re-run the baseline on
  the new machine — absolute numbers don't transfer.
