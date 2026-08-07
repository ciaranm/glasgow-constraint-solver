# Benchmarks for proof writing and proof checking

This document curates a set of instances whose **proofs** are the object of
measurement: how long the solver takes to write a proof, how large that proof
is, and how long VeriPB takes to check it.

It is the counterpart to [benchmarking.md](benchmarking.md), which curates a
different set for a different purpose — *solve* speed with proof logging off.
That document explicitly says not to put `--prove` in its numbers, and its
instances are sized accordingly: several of them cannot be proof-logged at all
on a development machine (see "Instances that do not fit", below). Reach for
this document when the change under test is on the proof side — a new
constraint's proof logging, a propagator's scaffolding, upfront versus per-call
derivation, RUP hinting, proof-level assignment, an encoding change, or a VeriPB
upgrade.

`benchmarking.md` also has a "Benchmarking proof-shape changes" section. That
section is the *methodology* — what to capture, the default-mode trap, how to
pick a size. This document is the *instance set* that section never had.

## What to run

Build with `cmake --preset release`; binaries land in `build/`. Every command
below is completed by `--prove --proof-files-basename <path>`.

The set is grouped by what each entry is for, because the groups have different
runtimes on purpose and a sweep that only ran one group would be misleading.

### Group A — proof checking (the 1–10 minute band)

These verify slowly enough that a single-digit-percent change is resolvable.

Measured solo, pinned to one core with ASLR off, minimum of three runs, on the
local SSD. `veripb` 3.0.2. The `rcpsp_dl21` row is a later sitting than the rest
— see "`rcpsp`'s options" below for why — so read its verify time as a size
guide, not as a figure to compare against the others to within a few percent.

| benchmark | command | outcome | recs | `.opb` | `.pbp` | solve | +proof | verify |
|---|---|---|--:|--:|--:|--:|--:|--:|
| `odb_eq1000` | `order_deletion_bench --problem pairwise --size 6 --domain 1000 --window 1000 --tightness 90 --unsat --value-order smallest` | UNSAT | 49 352 | 11 KB | 37 MB | 0.10 s | ×2.0 | **139.5 s** |
| `odb_split2000` | `order_deletion_bench --problem pairwise --size 8 --domain 2000 --window 2000 --tightness 90 --unsat` | UNSAT | 6 979 | 20 KB | 17 MB | 0.10 s | ×1.0 | **106.1 s** |
| `odb_cumulative8` | `order_deletion_bench --problem cumulative --size 8 --domain 250 --window 250 --tightness 90 --unsat` | UNSAT | 33 959 | 1.9 MB | 454 MB | 0.10 s | ×9.0 | **314.7 s** |
| `rcpsp_dl21` | `rcpsp --size 20 --seed 1 --deadline 21 --stats` | UNSAT | 42 058 | 0.3 MB | 1 242 MB | 0.30 s | ×7.0 | **139.5 s** |
| `qap10` | `qap --size=10` | optimal | 10 985 | 3.5 MB | 504 MB | 0.20 s | ×6.0 | **283.8 s** |
| `colour46` | `colour --file <46-vertex random graph>` | optimal | 313 109 | 0.4 MB | 736 MB | 12.31 s | ×1.2 | **347.6 s** |
| `nqueens12` | `n_queens --size=12 --all` | enum, 14 200 | 232 163 | 0.2 MB | 208 MB | 0.50 s | ×2.2 | **219.8 s** |
| `langford11` | `langford --size=11 --stats` | enum, 35 584 | 256 593 | 0.4 MB | 669 MB | 3.80 s | ×1.9 | **662.9 s** |
| `langford10` | `langford --size=10 --stats` | UNSAT | 43 514 | 0.3 MB | 101 MB | 0.60 s | ×1.8 | **60.4 s** |
| `freqsq6_gac` | `frequency_square 6 --all --stats --consistency gac` | enum, 53 220 | 105 825 | 44 KB | 205 MB | 0.90 s | ×2.0 | **83.6 s** |
| `freqsq6_bc` | `frequency_square 6 --all --stats --consistency bc` | enum, 53 220 | 105 825 | 44 KB | 80 MB | 1.10 s | ×1.3 | **81.2 s** |
| `pdisp10_tuple` | `p_dispersion --grid 10 -p 4 --variant tuple --stats` | optimal | 1 037 | 12.6 MB | 158 MB | 0.10 s | ×4.0 | **88.8 s** |
| `hitori` | `hitori --size 5 --seed 1 --quiet --stats` | optimal | 72 361 | 1.0 MB | 937 MB | — | — | **260.5 s** |
| `table_layout` | `table_layout --size 15 --seed 1 --stats` | optimal | 17 768 | 1.8 MB | 146 MB | — | — | **102.6 s** |
| `seat_moving` | `seat_moving --dzn sm-10-12-00.dzn --quiet --stats` | first solution | 15 610 | 2.4 MB | 645 MB | — | — | **119.5 s** |

`solve` is wall time with proof logging off; `+proof` is the multiplier when it
is on. Note how far that varies — from ×1.2 on `colour46`, whose search dominates,
to ×9.0 on `odb_cumulative8`. One pass over group A costs about 50 minutes.

The three `odb_*` rows drive `order_deletion_bench`, which is **not on `main`**:
it is added by the order-encoding-deletion branch. They are kept because they
are the set's only synthetic knob on domain size and branching order, and
because `odb_split2000` holds the expensive end of the cost-per-byte range
below; skip them where that binary is not built.

The last three rows are three of the four native ports from issues #633–#636 —
the fourth is `rcpsp`, which is `rcpsp_dl21` above — and they carry no
`solve`/`+proof` column because they were measured after the pinned pass.
`hitori` and `seat_moving` replaced `fzn-glasgow` entries and were validated
against them on the *same* instance, read through `--dzn`: **recursion counts
match exactly**, 113 671 for `hitori --dzn h5-1.dzn` against the flattened
`hitori.fzn`, and 15 610 for `seat_moving --dzn sm-10-12-00.dzn`. The ports
reproduce the search, not merely the answer.

Only one of those two rows is that validated run, and it is worth being clear
which. `seat_moving` above **is** the `--dzn` run, because generated
`seat_moving` instances are still unusable (see "Known gaps"). `hitori` above is
**not**: it is the self-contained generated instance, `--size 5 --seed 1`, whose
72 361 recursions are a different and smaller search than the 113 671 of the
Challenge puzzle the port was validated against. Prefer it for exactly that
reason — it needs no external data.

`table_layout` gives `Table` a size where proof shape is measurable at all;
`examples/tables` is 10 recursions.

`langford11` at 11.0 minutes sits just outside the nominal ceiling. It is kept
deliberately as the largest entry; with `langford10` at 60.4 s the pair brackets
the whole band from one binary, one as an enumeration and one as a refutation.

### Group B — proof writing

These verify in seconds but write hundreds of megabytes. They are the only
entries that isolate emission cost, and they must not be dropped for being
quick to check — see "The axis that matters most".

| benchmark | command | outcome | recs | `.pbp` | solve | +proof | verify | s/MB |
|---|---|---|--:|--:|--:|--:|--:|--:|
| `polynomial10` | `random_polynomial -n 10 -d 5 --seed 1 --stats` | optimal | 1 577 | 426 MB | 0.10 s | **×13** | 26.0 s | 0.06 |
| `nfractions` | `n_fractions --unsat --stats` | UNSAT | 112 | 146 MB | 0.10 s | ×5.0 | 3.2 s | **0.02** |
| `knapsack2` | `knapsack_bench --instance 2 --stats` | enum, 328 | 655 | 138 MB | 0.10 s | ×9.0 | 2.4 s | **0.02** |

All three check in seconds and cost between five and thirteen times the bare
solve to write. `polynomial10` writes 426 MB from 1 577 recursions; `nfractions`
writes 146 MB from **112**. Group A's `odb_eq1000`, by contrast, writes 37 MB
and spends 139 s checking it. That is the whole point of keeping both groups.

### Group C — controls

Pairs that differ in one controlled way, for attributing a difference.

| pair | what it controls for |
|---|---|
| `frequency_square 6 --all --consistency gac` vs `bc` | **Identical search** — 105 825 recursions and 53 220 solutions both ways — with the GAC proof **2.6× larger** (204.6 MB against 80.2 MB) and **the same verify time** (83.6 s against 81.2 s). The cleanest same-search pair in the set, and a SIZE≠TIME case on its own. |
| `knapsack_bench --instance 1` vs `--instance 1 --upfront` | **The clearest SIZE≠TIME demonstration in the set.** Identical search — 907 recursions, 454 solutions both ways — but `--upfront` writes a **5.9× smaller** proof (20.7 MB against 121.3 MB) that takes **3.5× longer** to check (7.0 s against 2.0 s). One flag, one instance, and the two axes move in opposite directions. |
| `p_dispersion --grid 8 -p 4 --variant tuple` vs `--variant min-distance-ps` | Identical search — 551 recursions, 7 solutions — through a decomposition and through the global propagator: **42.9 MB / 9.7 s against 0.8 MB / 0.7 s**. At `--grid 10` the proof-size gap widens to 91×, and at `--grid 12` the decomposition stops verifying inside 1200 s while the global takes 15 s. |
| `langford --size=11` vs `--size=10` | Enumeration against UNSAT refutation on one model, and the pair brackets the whole target band: 662.9 s and 60.4 s. |
| `magic_square --size=4 --all-different gac` vs `vc` | **Not** a same-search pair, despite looking like one: GAC searches 77 983 recursions against VC's 87 377. Listed so nobody mistakes it for one — `--all-different` defaults to `vc`, so comparing the default against explicit `vc` gives a spurious match. |

### Group D — opt-in, needs a big machine

| benchmark | command | why separate |
|---|---|---|
| `mzn_aircraft06` | `fzn-glasgow -s -a aircraft.fzn` (Challenge 2024, `B737NG-600-06-Anon.json.dzn`) | Needs about **19 GB of veripb resident memory**. It cannot share a 30 GB machine with anything else and will exhaust a smaller one. |
| `rcpsp20_opt` | `rcpsp --size 20 --seed 1 --stats` | The makespan-optimisation form of the group A entry above: **4.1 GB `.pbp`**, 702.7 s. Superseded for routine use by `rcpsp_dl21`, which proves infeasibility at the same instance for under a third of the proof. Keep it only when the *optimisation* proof shape is what is under test. |

### `rcpsp`'s options, and what they are worth

The example grew `--variant`, `--machine`, `--unary`, `--simplify`,
`--incremental`, `--deadline` and an RCPSP/max generalisation, and **none of
them changed the instance**: `--variant=decomposed` is the original
linear-per-edge posting, `--machine=disjunctive` the `Disjunctive` global, and
`--max-lag-density` defaults to zero and *draws no random numbers*, so a seeded
instance is untouched by the new options.

The search moved anyway, and not from the generator. These rows were re-measured
against `main` at `d3c9e58b` (2026-08-07), and `--size 20 --seed 1` now takes
**171 423** recursions where the first pass recorded 171 480; `--deadline 21` is
**42 058** against 42 115. Both are 57 recursions shorter, and the cause is the
`Cumulative` work merged in between, not anything in this example — every other
row in this document still reproduces its recorded count exactly.

That is the failure mode to watch for here, and nothing errors when it happens.
Re-check the recursion counts after a change to either the generator or
`Cumulative`: one extra random draw or one extra inference stales every seeded
row silently.

Measured across the options at `--size 20 --seed 1`:

| configuration | recursions | `.pbp` | verify | outcome |
|---|--:|--:|--:|---|
| default (optimise) | 171 423 | 4 104 MB | 702.7 s | `BOUNDS 22 ≤ obj ≤ 22` |
| `--variant global` | 171 423 | 4 134 MB | — | same |
| `--variant presolved` | 171 423 | 4 118 MB | — | same |
| `--value-order split` | 185 247 | 3 500 MB | — | same |
| **`--deadline 21`** | 42 058 | **1 242 MB** | **139.5 s** | **UNSAT** |
| `--deadline 21 --value-order split` | 41 507 | 996 MB | 112.3 s | UNSAT |
| `--infeasible` | **1** | 0.1 MB | — | UNSAT at the root |

The two `--deadline` rows are minimum-of-three; the 702.7 s is a single run,
because at 4.1 GB three of them cost most of an hour to say the same thing.

Three things worth knowing:

- **`--deadline` is the good entry.** The optimum is 22, so `--deadline 21` asks
  a decision question the solver has to search to refute — under a third of the
  proof, a fifth of the verify time, and a *scheduling UNSAT*, which no other
  entry provides. This is why it is in group A and the optimisation form is not.
- **The three `--variant` postings make identical search and near-identical
  proofs** (within 0.8 %), despite posting the temporal network three completely
  different ways. That makes them a same-search control triple; it does *not*
  make `global` a route to a smaller proof.
- **`--infeasible` refutes at the root in one recursion.** It closes a negative
  cycle the initial propagation already sees, so it is a smoke test for the
  difference reasoning, not a search benchmark. Use `--deadline` for a searched
  refutation.

`mzn_aircraft06` is worth the trouble because it is the only entry where the
checker is bound by the **model encoding** rather than the derivation: a 2.5 GB
`.opb` against an 8 MB `.pbp`. The largest `.opb` anything else in the set
produces is 12.6 MB.

## Why these instances

Two derived ratios separate proofs far better than any qualitative label, and
the set is chosen to span both.

**Verify seconds per megabyte of `.pbp`** ranges over about **360×** within the
chosen set: `odb_split2000` writes 17 MB and spends 106.1 s checking it
(6.2 s/MB), while `knapsack_bench --instance 2` writes 138 MB and checks in
2.4 s (0.017 s/MB). Across everything screened it is wider still — over 1200×,
since the `regular_random` candidates exceed 21 s/MB (see "Known gaps"). High
values mean the checker is working through long RUP chains over a wide resident
database; low values mean it is streaming a large but individually-trivial
derivation.

**Kilobytes of `.pbp` per recursion** ranges over roughly **1700×**, from about
0.8 KB (`odb_eq1000`, `freqsq6_bc`, `nqueens12`) to 1.3 MB (`nfractions`, which
writes 146 MB from 112 recursions). This is the wide-versus-deep axis: high
values mean the proof is dominated by upfront definitional material rather than
by search. Note that it separates the two `frequency_square` rows, which are the
same search: 0.8 KB under BC against 1.9 KB under GAC.

Beyond those two, the set spans:

- **proof outcome** — UNSAT refutation, complete enumeration, and proved
  optimality all produce differently-shaped proofs, and a change can help one
  and hurt another;
- **model versus derivation** — `.opb` from about ten kilobytes to 2.5 GB;
- **propagator cost** — from `n_queens`, which posts nothing but `NotEquals`, to
  `Knapsack`, `GlobalCardinality`, `MinDistance`, `Cumulative` and chained
  `Multiply`;
- **realistic versus degenerate** — puzzle and MiniZinc Challenge instances
  against random generators and the synthetic `order_deletion_bench` driver.

### The axis that matters most

Group A and group B are not "big" and "small". They are opposite failure modes,
and a change that improves one commonly worsens the other — trading proof bytes
for checking time is the normal shape of a proof-side optimisation. Measuring
only group A rewards writing more proof to check it faster; measuring only
group B rewards the reverse.

`knapsack_bench --instance 1` versus the same instance under `--upfront` shows
this on one binary with one flag, at **identical search**: the `--upfront` proof
is 5.9× smaller and takes 3.5× longer to check. Whichever axis a sweep measures,
that pair moves the other way.

## What to capture

In addition to the signals listed in `benchmarking.md`'s proof-shape section:

- **`.opb` bytes as well as `.pbp` bytes.** They move independently and mean
  different things — the static model encoding against the derivation. A change
  that grows one is not the same change as one that grows the other.
- **The full verdict string**, not just an exit status. `s VERIFIED
  UNSATISFIABLE`, `s VERIFIED BOUNDS x <= obj <= x` and `s VERIFIED COMPLETE
  ENUMERATION OF n SOLUTIONS` are what say the run proved the thing it was meant
  to prove. An exit code alone is satisfied by an unparseable proof.
- **`recursions` and `propagations[0]`**, so a reader can see how much of the
  proof is search and how much is initialisation, and can check that two
  variants really did make identical decisions.
- **veripb peak resident memory**, which tracks the resident constraint
  database. This is *not* comparable across VeriPB's `59d948fb` "Remove mmap"
  (merged 2026-05-28): the version string is 3.0.2 on both sides, so compare
  build dates, not versions.
- **Evidence that the change under test actually fired.** An optional or
  additive proof feature satisfies solution-equivalence, an `.opb` byte-diff and
  VeriPB by doing nothing at all. Whatever counter or diagnostic the change
  exposes, record it per row; a timing table alone cannot tell "measured
  neutral" from "never engaged".

## Reproducibility

The rules in `benchmarking.md` under "veripb timing: contention and run-to-run
noise" apply in full, and the important ones are worth repeating because they
are easy to get wrong:

- **Time veripb runs one at a time**, on an otherwise quiet machine.
- **Measure every row of a comparison in one contiguous sitting.** Ratios within
  a sitting are sound; absolute times across sittings are not.
- **Take the minimum of several runs**, not the mean.

One refinement this set adds, and it is stronger than "small proofs degrade
worse": **a verify time measured under load cannot be corrected, only
discarded.** Measured against solo baselines on this set, the inflation under a
three- or four-way load ran from **1.07×** (`colour` g40, 188 MB) to **2.99×**
(`freqsq6_gac`, 205 MB) — two proofs of similar size at opposite ends of the
range. Proof size does not predict it. Budget for running a sweep solo end to
end; there is no shortcut that scales a parallel pass back down.

A worked example of why it matters: under pilot load `freqsq6_gac` and
`freqsq6_bc` looked 27 % apart. Solo they are **3 % apart** (83.6 s against
81.2 s) despite the GAC proof being 2.6× larger. The entire apparent difference
was contention.

**On filesystems: it does not matter, and tmpfs is mildly counterproductive.**
Measured directly — the same proof verified from the local SSD and from tmpfs,
solo, pinned, minimum of three each, all in one sitting:

| proof | SSD | tmpfs | difference |
|---|--:|--:|--:|
| `odb_split2000`, 17 MB | 110.52 s | 110.72 s | +0.2 % |
| `pdisp10_tuple`, 158 MB | 82.26 s | 82.41 s | +0.2 % |
| `qap10`, 504 MB | 276.05 s | 286.59 s | +3.8 % |

These six numbers are their own sitting, so read only along the rows: the
absolute times are not the group A ones and are not meant to be, by the rule
directly above.

tmpfs is never faster and is slightly *slower* at every size. So write the
proofs wherever is convenient. The advice elsewhere to put timed proof I/O on
tmpfs was formed where the alternative was network storage; on a machine with a
local SSD it buys nothing, and on the larger entries it is actively the wrong
choice because it competes with veripb for the same RAM — `mzn_aircraft06`
wants about 19 GB resident *plus* room for a 2.5 GB `.opb`.

Always cap proof output. A `ulimit -f` on the `.pbp` is the difference between a
mis-sized run costing a minute and it filling the disk; several candidates
below write tens of gigabytes before anyone notices.

## Instances that do not fit

Every entry here was measured, not guessed. `cap` means it exceeded an 8 GB
`ulimit -f` on the `.pbp` and was killed. Recorded so the screening does not get
repeated.

| candidate | outcome |
|---|---|
| `ortho_latin --size=6 --all` | cap; `--size=5` is 6 MB, and there is no size in between |
| `tsp` (fixed default instance) | cap at 4 GB, and there is no size knob |
| `qap --size=12` | cap; `--size=11` stays under it, at 2.0 GB, but does not finish verifying inside 900 s |
| `regular_random -n 9 --all`, `-n 10 --all` | cap |
| `regular_random -n 7 --all` | 172–282 MB, but **over an hour** to verify, with `--bacchus` as well as without; `-n 6` is under a second |
| `skeleton_puzzle` at 4×3, 4×4, 5×3, 5×4, 6×3 and the default 7×5 | cap or over 1200 s at every shape tried, with `--seed` and without |
| `random_polynomial -n 12 -d 6` | cap; `-n 10 -d 5` is 426 MB |
| `colour` on 42-vertex (50 % density) and 60-vertex graphs | cap — but a 46-vertex graph verifies in the band; see below |
| `rcpsp --size` 12–19 and 22–24, several seeds | either trivial (≤139 MB, under 10 s) or cap. Only `--size 20 --seed 1` lands, at 4.1 GB |
| `seat_moving --seats` 20, 30, 60, 100 | cap in find-first mode; `--optimise` caps from 20 seats up. 16 seats is 11 MB |
| `hitori --size` 6, 7, 8, and `--size 6 --density 0.2` | cap. `--size 5` is 937 MB, `--size 4` is 5.7 MB |
| `order_deletion_bench --problem cumulative --size 10 --domain 500` | cap |
| Challenge `atsp`, `triangular`, `chessboard`, `tiny-cvrp`, `table-layout` | cap or over 1200 s, despite each solving in under 12 s with proofs off |
| `nonogram --random N --all` | no search — 17 recursions at the size `benchmarking.md` suggests |
| `multiply_random` at any `-n` | 3 recursions and about 1 MB even at `-n 1000000000` |
| `sudoku`, `regex`, `tables`, `auto_table`, `rostering`, `money`, `cake`, `crystal_maze`, `knapsack`, `circuit_random`, `smart_table_*` | verify in well under a second; smoke tests, not measurements |
| `examples/cumulative` | a fixed five-task toy |

Two parameters turn out not to be parameters:

- **`colour` is instance-dependent, not size-monotone.** A 41-vertex graph gives
  16 MB, a 42-vertex one 120 MB, a 46-vertex one 736 MB, and a different
  42-vertex one blows the cap. Pick and keep an instance; do not scale the
  vertex count and expect the proof to follow.
- **`regular_random` has no usable size.** n=6 checks in 0.6 s, n=7 takes over
  1200 s, and n=9 blows the cap. `Regular` is consequently not represented at
  scale anywhere in this set — see "Known gaps".

### Argument-shape traps

Found the hard way, all of them producing an immediate parse error:

- The `minicp_benchmarks` binaries (`n_queens`, `magic_square`, `qap`, `tsp`,
  `magic_series`) and `bin_packing_bench` have **no `--stats`** — they print
  statistics unconditionally and reject the flag.
- `ortho_latin` and `magic_square` spell the encoding choice
  `--all-different gac|vc|not-equals`, not `--gac` or `--vc`.
- `skeleton_puzzle` refuses any non-default shape unless `--seed` is given.
- `frequency_square` takes its size positionally, and the size must be divisible
  by `--lambda`.
- **`--seed` defaults to `-1`, meaning a fresh random instance every run**, in
  `regular_random`, `circuit_random`, `multiply_random`, `random_polynomial` and
  `smart_table_random`. Three consecutive `regular_random -n 6 --all` runs give
  32 664, 28 881 and 21 116 recursions — three different problems. Any use of
  these binaries in a benchmark **must** pass an explicit `--seed`, and any two
  numbers being compared must share it. This is easy to miss because the runs
  succeed and the numbers look plausible; it silently turns a strategy
  comparison into a comparison of unrelated instances.

## Known gaps

- **`Regular` at scale, and this one looks closed rather than open.**
  `regular_random --all` has no usable size: n=6 checks in well under a second,
  n=9 exceeds an 8 GB proof cap, and n=7 sits in between in size but not in
  checking cost. Measured seeded, `-n 7 --all --seed 1` under `--bacchus` writes
  a 172 MB proof that **exceeds an hour** to verify — about 21 s/MB, the worst
  cost-per-byte of any derivation-bound proof here. So the smaller-proof strategy
  does not rescue it. `examples/nonogram` is the documented structured
  alternative but does not search (17 recursions), and `examples/rostering` is a
  23-recursion toy. Representing `Regular` at a measurable size probably needs a
  cheaper proof strategy rather than a better instance.
- **A comfortably-sized realistic `Cumulative` / `Disjunctive` instance.**
  `examples/rcpsp` (issue #633) closed the "unreachable natively" half of this,
  but its instances are **bimodal rather than scalable**: across `--size` 12–24
  and three seeds, every instance was either trivial (≤139 MB, under 10 s) or
  explosive (over 3 GB). Only `--size 20 --seed 1` lands in range, and it writes
  4.1 GB. `odb_cumulative8` covers the propagator cheaply but synthetically.
- **A generated `seat_moving` instance.** The port removed the dependence on an
  unversioned flattened `.fzn`, but it still needs the Challenge `.dzn`:
  generated instances jump from 11 MB at 16 seats to over 6 GB at 20, in both
  find-first and `--optimise` modes.

## MiniZinc entries

One entry still comes through `fzn-glasgow`, because nothing native reaches its
shape: `mzn_aircraft06`, the model-encoding-bound extreme. The other two — a
realistic gigabyte-scale optimisation and the deep find-first split search — are
now the native `hitori` and `seat_moving` examples.

The MiniZinc route carries a cost: a flattening step, `mznlib` drift between
MiniZinc releases, and a dependence on a Challenge corpus that is not in this
repository. Flatten once and keep the `.fzn`:

```shell
minizinc --solver <glasgow.msc> -c --fzn model.fzn --no-output-ozn model.mzn data.dzn
fzn-glasgow -s -a model.fzn --prove --proof-files-basename proof
```

Each of these models uses only constraints that already exist in the solver, so
porting them to `examples/` is model-writing rather than propagator work, and
would make the set self-contained. The bar for a port is that it reproduces the
**search** — identical recursion counts against the `fzn-glasgow` run on the
same instance, not merely the same answer. Anything weaker is not a substitute
for the instance it replaces.

Proof and model *sizes* do not come out equal, and should not be expected to:
the flattened model posts a different set of constraints, so the encoding
differs even where the search does not.

| instance | native `--dzn` | via `fzn-glasgow` |
|---|--:|--:|
| `hitori` h5-1 | 1.0 MB `.opb`, 815 MB `.pbp` | 1.2 MB, 1 000 MB |
| `seat_moving` sm-10-12-00 | 2.4 MB `.opb`, 645 MB `.pbp` | 3.1 MB, 629 MB |

Both ports write a smaller `.opb`; the `.pbp` falls 19 % for `hitori` and rises
2 % for `seat_moving`. The recursion counts are exact matches either way, which
is the part that had to hold.

Four such ports were done, as issues #633–#636 and PRs #638–#641:
`examples/rcpsp`, `examples/hitori`, `examples/seat_moving` and
`examples/table_layout`. Each takes a `--size`/`--seed` pair, and `hitori`,
`seat_moving` and `table_layout` also read the original `.dzn` directly, which
is what made the validation above possible.

The remaining MiniZinc dependency is `mzn_aircraft06`, whose 2.5 GB `.opb` is
the point of the entry, and `seat_moving`'s `.dzn` — see "Known gaps".
