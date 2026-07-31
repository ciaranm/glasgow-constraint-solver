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

| benchmark | command | outcome |
|---|---|---|
| `odb_split2000` | `order_deletion_bench --problem pairwise --size 8 --domain 2000 --window 2000 --tightness 90 --unsat` | UNSAT |
| `odb_eq1000` | `order_deletion_bench --problem pairwise --size 6 --domain 1000 --window 1000 --tightness 90 --unsat --value-order smallest` | UNSAT |
| `qap10` | `qap --size=10` | optimal |
| `colour46` | `colour --file <46-vertex random graph>` | optimal |
| `nqueens12` | `n_queens --size=12 --all` | enumeration |
| `langford11` | `langford --size=11 --stats` | enumeration |
| `langford10` | `langford --size=10 --stats` | UNSAT |
| `freqsq6_gac` | `frequency_square 6 --all --stats --consistency gac` | enumeration |
| `freqsq6_bc` | `frequency_square 6 --all --stats --consistency bc` | enumeration |
| `pdisp10_tuple` | `p_dispersion --grid 10 -p 4 --variant tuple --stats` | optimal |
| `mzn_hitori` | `fzn-glasgow -s -a hitori.fzn` (Challenge 2025, `h5-1.dzn`) | optimal |
| `mzn_seatmoving` | `fzn-glasgow -s -n 1 2018_seat-moving.fzn` | first solution |

### Group B — proof writing

These verify in seconds but write hundreds of megabytes. They are the only
entries that isolate emission cost, and they must not be dropped for being
quick to check — see "The axis that matters most".

| benchmark | command | outcome |
|---|---|---|
| `polynomial10` | `random_polynomial -n 10 -d 5 --seed 1 --stats` | optimal |
| `knapsack2` | `knapsack_bench --instance 2 --stats` | enumeration |
| `nfractions` | `n_fractions --unsat --stats` | UNSAT |

### Group C — controls

Pairs that differ in one controlled way, for attributing a difference.

| pair | what it controls for |
|---|---|
| `magic_square --size=4 --all-different gac` vs `--all-different vc` | **Identical search** — same recursions, same solution count — with propagation count differing about 6×. Any proof-side divergence is emission, not search. |
| `p_dispersion --grid 8 -p 4 --variant tuple` vs `--variant min-distance-ps` | The same problem through a decomposition and through the global propagator. |
| `frequency_square 6 --all --consistency gac` vs `bc` | Propagation strength on one instance (also in group A). |
| `langford --size=11` vs `--size=10` | Enumeration against UNSAT refutation on one model. |

### Group D — opt-in, needs a big machine

| benchmark | command | why separate |
|---|---|---|
| `mzn_aircraft06` | `fzn-glasgow -s -a aircraft.fzn` (Challenge 2024, `B737NG-600-06-Anon.json.dzn`) | Needs about **19 GB of veripb resident memory**. It cannot share a 30 GB machine with anything else and will exhaust a smaller one. |

`mzn_aircraft06` is worth the trouble because it is the only entry where the
checker is bound by the **model encoding** rather than the derivation: a 2.5 GB
`.opb` against an 8 MB `.pbp`. The largest `.opb` anything else in the set
produces is 12.6 MB.

## Why these instances

Two derived ratios separate proofs far better than any qualitative label, and
the set is chosen to span both.

**Verify seconds per megabyte of `.pbp`** ranges over roughly 500× across the
set. At one end `order_deletion_bench --domain 2000` writes 17 MB and takes
around 110 s to check; at the other `knapsack_bench --instance 2` writes 138 MB
and checks in under 2 s. High values mean the checker is working through long
RUP chains over a wide resident database; low values mean it is streaming a
large but individually-trivial derivation.

**Kilobytes of `.pbp` per recursion** ranges over roughly 3000×, from under
1 KB (`frequency_square`, `n_queens`) to about 1.3 MB (`n_fractions`). This is
the wide-versus-deep axis: high values mean the proof is dominated by upfront
definitional material rather than by search.

Beyond those two, the set spans:

- **proof outcome** — UNSAT refutation, complete enumeration, and proved
  optimality all produce differently-shaped proofs, and a change can help one
  and hurt another;
- **model versus derivation** — `.opb` from a few tens of kilobytes to 2.5 GB;
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
group B rewards the reverse. The two groups differ by around **550×** in
checking cost per byte, so neither substitutes for the other.

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

One refinement this set adds: **concurrency inflates small proofs far more than
large ones**, so a sweep run in parallel does not merely scale — it reorders.
Measured here against solo baselines, a 17 MB proof inflated about 1.7× under a
four-way load while a 188 MB proof inflated about 1.07×. Extrapolating a solo
time from a loaded one with a single correction factor is therefore wrong across
the range of this set.

**On filesystems**: on a machine with a local SSD, write the proofs wherever is
convenient. The advice elsewhere to put timed proof I/O on tmpfs was formed
where the alternative was network storage, and it does not transfer: disk has
not been the bottleneck in the experiments run here. On the larger entries
tmpfs is actively the wrong choice, because it competes with veripb for the
same RAM — `mzn_aircraft06` wants about 19 GB resident *plus* room for a 2.5 GB
`.opb`. Reach for tmpfs only if you have measured that your storage is slow
enough to matter.

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
| `qap --size=12` | cap; `--size=11` verifies but takes over 900 s |
| `regular_random -n 9 --all`, `-n 10 --all` | cap |
| `regular_random -n 7 --all` | 272 MB, but over 1200 s to verify; `-n 6` is 0.6 s |
| `skeleton_puzzle` at 4×3, 4×4, 5×4 and the default 7×5 | cap at every shape tried |
| `random_polynomial -n 12 -d 6` | cap; `-n 10 -d 5` is 426 MB |
| `colour` on 42-vertex (50 % density) and 60-vertex graphs | cap — but a 46-vertex graph verifies in the band; see below |
| `order_deletion_bench --problem cumulative --size 10 --domain 500` | cap |
| Challenge `atsp`, `triangular`, `chessboard`, `tiny-cvrp`, `table-layout` | cap or over 1200 s, despite each solving in under 12 s with proofs off |
| `nonogram --random N --all` | no search — 17 recursions at the size `benchmarking.md` suggests |
| `multiply_random` at any `-n` | 3 recursions and under 1 MB even at `-n 1000000000` |
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

## Known gaps

- **`Regular` at scale**, for the reason above. `examples/nonogram` is the
  documented structured alternative but does not search; `examples/rostering` is
  a 23-recursion toy.
- **`Cumulative` and `Disjunctive` at scale** are reachable only through the
  MiniZinc frontend, because `examples/cumulative` is a fixed five-task toy.
  This is the most valuable gap to close.

## MiniZinc entries

Three entries come through `fzn-glasgow` because nothing native reaches their
shape: `mzn_hitori` (a realistic optimisation writing a 1 GB proof from under
four seconds of solving), `mzn_aircraft06` (the model-encoding-bound extreme)
and `mzn_seatmoving` (the deep find-first split search).

They carry a cost: a flattening step, `mznlib` drift between MiniZinc releases,
and a dependence on a Challenge corpus that is not in this repository. Flatten
once and keep the `.fzn`:

```shell
minizinc --solver <glasgow.msc> -c --fzn model.fzn --no-output-ozn model.mzn data.dzn
fzn-glasgow -s -a model.fzn --prove --proof-files-basename proof
```

Each of these models uses only constraints that already exist in the solver, so
porting them to `examples/` is model-writing rather than propagator work, and
would make the set self-contained. A port must reproduce the proof *shape* —
`.opb` size, `.pbp` size and recursion count — against the `fzn-glasgow` run,
not merely the answer, or it is not a substitute for the instance it replaces.

Four such ports are tracked:

- **#633** — a scheduling example (`Cumulative`, `Disjunctive`, makespan). The
  most valuable of the four: it closes the gap above rather than replacing an
  existing entry.
- **#634** — `hitori`, which needs only `Count` and `AllDifferentExcept`.
- **#635** — `seat-moving`, which needs only `AllDifferent` and
  `AllDifferentExcept`, and which removes this set's dependence on a flattened
  `.fzn` that is not under version control.
- **#636** — `table-layout`, which would also give `Table` a representation at
  a size where proof shape is measurable; `examples/tables` is a 10-recursion
  toy.
