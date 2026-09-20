# Running the scheduling experiments elsewhere

A runbook for producing the measurements the certified-scheduling work needs, on
a machine that has nothing but this repository and a network connection. It
assumes no local state: every instance family is fetched from its upstream, and
every command below is meant to be run as written.

Read this top to bottom before starting anything long. Steps 1-4 take under an
hour; step 5 is the part that takes real time, and steps 1-4 exist to stop you
spending it on a build that was going to produce wrong numbers.

## What this is for

Every energetic rule in `Cumulative` and `Disjunctive` is off by default and the
reason is always a measurement. The point of a sweep is to produce, per rule:

- what the rule does to the **search** (recursions, and how many instances it
  closes),
- what it **costs** (`calls` against `firings`, and how much of its reach was
  already true),
- what it does to the **proof** (`.pbp` size and VeriPB checking time).

Three instance families, because no one of them exercises the whole rule set:

| family | why it is here |
|---|---|
| RCPSP (`.dzn`) | the cumulative rules' home ground |
| job shop (`.jss`) | **the only family with unary machines.** No RCPSP collection in circulation has a capacity-one resource --- the smallest across `data_bl`, `data_pack`, `data_pack_d` and `data_ksd15_d` is three --- so without this the disjunctive rules measure nothing at all |
| multi-mode (`.mm`) | **the only family with variable durations and demands.** An activity picks a mode and the mode fixes both, which is the case `Cumulative` was taught to reason about and that no single-mode instance reaches |

## 1. Build

Needs a C++23 compiler (GCC 13 on Ubuntu 24.04 is the oldest tested; GCC 15 and
Clang 21 are the development compilers), CMake 3.21+, Python 3.10+, and `veripb`
3.0.2 or later on `PATH` for anything involving proofs. The top-level `README`
has the full list and the FetchContent dependencies.

```shell
cmake --preset release -B build
cmake --build build --parallel
ctest --test-dir build --parallel
```

All tests must pass before going further. **Do not pin your own expectations to
the exact figures quoted in this repository's comments**: recursion counts and
rule counters are stable for a given build but differ between toolchains, so a
number here that your machine does not reproduce is not necessarily a fault.
Test *failures* are.

### If the work is still on branches

At the time of writing five branches carry this, and `main` may or may not have
them yet. Check first:

```shell
./build/rcpsp --help | grep -cE '^\s+--(jss|mm)'          # 2 if the readers are in
./build/rcpsp --help >/dev/null && ls tools/scheduling_sweep.py   # the harness
```

If they are missing, combine them --- they merge cleanly apart from one conflict
that is two branches appending test blocks to the same file, where the
resolution is to keep both:

```shell
git checkout -b experiments main
git merge jobshop-reader          # --jss
git merge multi-mode-reader       # --mm
git merge scheduling-rule-counters   # conflict in examples/rcpsp/CMakeLists.txt: keep both blocks
git merge scheduling-sweep-harness   # tools/scheduling_sweep.py
git merge sweep-certifiable-families # this runbook's corrections, and the -dd arms
```

873 tests pass with all five applied to `main` at `58fad258`. If a flag is
missing the sweep harness says so and skips what depends on it rather than
failing obscurely, so a partial combination still runs --- it just measures
less.

## 2. Fetch the instances

```shell
tools/fetch_scheduling_instances.bash scheduling-instances
```

Public sources, ~100 MB, a few minutes. **Needs network access, so on a cluster
run this on a login node rather than inside a batch job.** It is idempotent:
re-run it if it is interrupted. It prints what it got and what to expect
(`data_bl` 40, `jobshop` 82, `multimode/j10` 536, and so on).

## 3. Check the build against published answers

```shell
tools/check_scheduling_readers.py --binary build/rcpsp --instances scheduling-instances
```

This solves instances whose optimal makespans other people have published ---
PSPLIB ships a table of them for the multi-mode sets, and `ft06` and `la01` are
settled job-shop optima --- and compares. It exits non-zero on any disagreement.

**Do not skip this and do not proceed past a disagreement.** A reader that is
subtly wrong does not crash: it produces a slightly *better* optimum, which is
the one thing nobody double-checks. Both bugs found in the multi-mode support
while it was being written showed up only this way, and neither was visible to a
unit test.

## 4. A smoke run

```shell
tools/scheduling_sweep.py --list-arms

tools/scheduling_sweep.py --binary build/rcpsp --out smoke.jsonl \
    --dzn-dir scheduling-instances/rcpsp --collections data_bl \
    --arms ef,ttef --timeout 10 --jobs 4
```

Expect 80 rows, each carrying `recursions` and a `rules` object with 21 counter
entries. If `rules` is missing, the counters are not in this build.

## 5. The sweeps

Each writes one JSONL row per (instance, arm). `--resume` skips rows already
present, so a killed job is restarted by re-running the same command. Rough
costs assume ~16 cores; scale accordingly.

The figures quoted from here on come from one complete run of this runbook, on
a 96-core machine at a 600 s timeout, in August 2026 --- before `Cumulative`
changed OPB encoding in #943 and before proofs started deleting from VeriPB's
core in #914. They are here to say what to expect and which comparisons are
worth making, not to be reproduced to the digit.

**Every arm runs the solver's default branching**, `in-order` / `smallest`, and
`--list-arms` also shows a `-dd` copy of each with `--branch dom-then-deg
--value-order split`. A table saying what a rule is *worth*, rather than what it
saves the solver as configured, wants both, because the rules do not survive the
change intact. On `data_bl`, `energetic` against `off` is 0.260 summed under the
default and 0.563 under `-dd` --- and where under the default no arm is worse
than the baseline on any instance, under `-dd` every arm but the two that barely
fire (`elastic`, `kaoc`) is worse on five or six. That "never worse" is
substantially an artefact of a weak branching leaving enough redundant search
around that almost any pruning helps.

### 5a. Cumulative, search shape (~2-4 hours)

```shell
tools/scheduling_sweep.py --binary build/rcpsp --out cumulative-shape.jsonl \
    --dzn-dir scheduling-instances/rcpsp --collections data_bl,data_ksd15_d,data_pack \
    --arms off,ef,ttef,energetic,nfnl,nfnlpub,ttef+nfnl,ttef+nfnlpub,elastic,kaoc \
    --timeout 60 --jobs 16 --resume
```

Read the collections by how many instances *every* arm closes, because a ratio
over the closed set is only as good as that set. At 600 s it is 37 of 40 on
`data_bl`, 416 of 480 on `data_ksd15_d` and 2 of 55 on `data_pack`. `data_pack`
is here for its closed counts rather than its ratios: it is where `kaoc` is
decisive, closing 9 instances no other arm does. Two collections are left out on
purpose. `data_pack_d` closes 5 of 55, and on those five every arm is identical
to the digit --- its durations run to 1138, so the search enumerates start times
rather than reasoning about the resource. `data_la_x` closes none of its 80, so
only its incumbents can be compared, and there most strengthenings return a
*worse* schedule than `off` (`kaoc` is worse on 32 instances and better on
none): the wall-clock price of a rule that does not prune, which is worth
knowing but is not a ratio.

### 5b. Disjunctive on job shops (~2-4 hours)

The family that makes these rules measurable at all --- and the one where a
ratio over the instances every arm closes does not work. At 600 s exactly one of
the 82 closes on every arm (`ft06`), so that comparison set has one member.

```shell
tools/scheduling_sweep.py --binary build/rcpsp --out disjunctive-shape.jsonl \
    --jss-dir scheduling-instances/jobshop \
    --arms dj-off,dj-ef,dj-ef-lb,dj-ef-ub,dj-nfnl,dj-nfnlpub,dj-dps,dj-overload,dj-ef+nfnl,dj-ef+dps \
    --timeout 60 --jobs 16 --resume
```

Compare what the arms *found* instead. Every timed-out run under the default
branching still returns an incumbent, so a makespan ratio against `dj-off` over
all 82 instances is available, and at this timeout it is the only thing the
family measures. It is weaker evidence than a recursion ratio and load-dependent
in a way that one is not --- an incumbent is wherever the search had got to when
the clock stopped --- so quote it with `parallel` beside it.

The `-dd` arms do not rescue the family. Under `--value-order split` 969 of the
984 runs found no schedule at all: extraordinary on the two instances it closes,
nothing usable on the other 80.

### 5c. Multi-mode, variable durations and demands (~1-2 hours for j10)

```shell
tools/scheduling_sweep.py --binary build/rcpsp --out multimode-shape.jsonl \
    --mm-dir scheduling-instances/multimode \
    --arms off,ef,ttef,energetic,nfnl --timeout 60 --jobs 16 --resume
```

That is j10 and j20 both. j10 is the family that works best of all: 536 of 536
close on every arm, and these two sets have a published optimum for every
instance. j20 closes 484 of 554 on every arm and costs roughly ten times what
j10 does. On both the median ratio is exactly 1.000 for every arm --- the whole
effect lives in a minority of instances, so quote the summed ratio beside the
median. j20 is also where the rule that removes the most search per node,
`energetic`, closes *fewer* instances than `off`: paying for its sweep in wall
clock, which is what `calls` against `firings` prices and a recursion ratio
cannot show.

### 5d. Proof size and verification time (hours to days)

Much the most expensive: every run writes a proof and then checks it. Start
small and grow. The cap is not optional --- an uncapped proving run on a real
instance has written 128 GB in ten minutes.

```shell
tools/scheduling_sweep.py --binary build/rcpsp --out proofs-generated.jsonl \
    --mode prove --generated 'size=10,12,14;seed=1..10;capacity=3,4,6' \
    --arms off,ef,ttef,energetic,nfnl --timeout 60 --proof-cap-mb 4000 --jobs 8 --resume
```

Then the same over `--dzn-dir ... --collections data_bl`. Not over `--jss-dir`:
at the default branching 5 of 984 job-shop proofs completed, all of them `ft06`,
and under `-dd` 971 of 984 still hit the cap, so a job-shop proof sweep measures
the cap and nothing else. Watch the disk: `--jobs 8` at a 4 GB cap can want
32 GB at once, and rows come back as `proof-too-big` rather than as failures
when they hit it.

**The cap is not only a disk guard: it chooses the sample, and it chooses it by
the quantity being measured.** It admits the instances whose proofs are small,
which are the ones where a strong rule saved least, so a capped sweep
under-reports how much a strong rule shrinks the proof. On `data_bl`, raising
the cap from 4 GB to 16 GB let 76 more runs verify and moved `energetic`'s proof
size against `off` from 0.645 summed (21 instances) to 0.480 (29). Say which cap
a proof-size table was taken at, and raise it where the disk allows --- over the
346 `data_bl` runs that verified at 16 GB the median proof was 0.38 GB and the
largest 15.9 GB.

**Then these two, which this step used to leave to whoever had time.** Both
certify at a usable rate, and between them they are this programme's only
proof-mode coverage of a long duration:

```shell
tools/scheduling_sweep.py --binary build/rcpsp --out proofs-data_ksd15_d.jsonl \
    --mode prove --dzn-dir scheduling-instances/rcpsp --collections data_ksd15_d \
    --arms off,ef,ttef,energetic,nfnl --timeout 60 --proof-cap-mb 4000 --jobs 8 --resume

tools/scheduling_sweep.py --binary build/rcpsp --out proofs-multimode-j20.jsonl \
    --mode prove --mm-dir scheduling-instances/multimode/j20 \
    --arms off,ef,ttef,energetic,nfnl --timeout 60 --proof-cap-mb 4000 --jobs 8 --resume
```

Why they are named rather than left to time. Read the collections by their
longest task: `data_bl`'s is **6** time units and j10's is **10**, while
`data_ksd15_d`'s is **250** and `data_pack_d`'s is **1138**. The families a
"start small and grow" reading reaches first were the two *coarsest* on disk,
and that was not a coincidence --- the time-indexed OPB `Cumulative` wrote when
this was measured was `O(n x horizon)`, so the cheapest instances to certify
were the ones with the shortest durations. Picking by cost picked by duration,
and a step that stopped when the time ran out reported on short tasks only.

Since #943 the OPB is the horizon-free start-checkpoint encoding, which on
`data_ksd15_d` is 0.06x the size. The per-(task, time) flags a proof cites are
still defined, but inside the proof and only where cited, and the proofs came
out 1.56x bigger on that family in exchange. So the model no longer ties cost to
duration; whether the proof still does, closely enough to bias a "start small"
reading, has not been re-measured. On a 150-run sample of each collection, the
runs that certify did not change between the two encodings.

Measured over the whole of both collections, on the time-indexed encoding,
eleven arms, 4 GB cap, 600 s:

| collection | verified | capped | verify-timeout | rejected |
|---|---|---|---|---|
| `data_ksd15_d` | 4,478/5,280 (84.8%) | 746 | 56 | 0 |
| multi-mode j20 | 4,611/6,094 (75.7%) | 1,483 | 0 | 0 |

For scale, `data_bl` at the same cap is 270/440 (61.4%) and j10 is 5,439/5,896
(92.2%), so both sit inside the range this programme already works in. Note that
j20 is *not* an easier family than j10 despite the same task durations --- more
activities means bigger proofs, and 1,483 of its runs hit the cap.

**`data_ksd15_d` needs a longer `--verify-timeout` than the default.** Its
median check is 0.53 s, but the tail is very long: 56 runs exceed 7200 s, and
`j309_7` --- whose eleven arms are most of that 56 --- verifies correctly in
**3 h 51 m** when run with no limit at all. A `verify-timeout` on this family is
a statement about the limit, not about the proof. Budget 4-6 hours where the
point is to establish that a family checks rather than how quickly.

The three that do not pay, so nobody spends a night rediscovering it:
`data_pack`, `data_pack_d` and `data_la_x` came back **0/150 verified**, every
run over the cap. `data_pack_d` is the sharpest case --- raising the ceiling to
200 GB shows its proofs reaching 80-118 GB and still growing when the solve
times out, so no cap setting reaches that collection. What is certifiable there
is bounded by the search, not by the cap.

### 5e. Closed counts, serially (long)

Only if a table is going to report *how many instances an arm closed*. Those
counts depend on machine load in a way that recursion ratios do not, so they
need a quiet machine and one run at a time.

```shell
tools/scheduling_sweep.py --binary build/rcpsp --out closed-serial.jsonl \
    --dzn-dir scheduling-instances/rcpsp --collections data_bl \
    --arms off,ef,ttef,energetic --timeout 60 --serial --resume
```

What matters is concurrency against *physical cores*, not against `nproc`. On a
96-core, 192-thread machine, running one CPU-bound solve 96 ways at once moved
its wall time by under 1%, and 144 ways by 44% once SMT contention set in. This
step run strictly serially, against the same four arms from an 88-way sweep,
changed the closed status of 0 of 160 cells, and the recursion count of none of
the 154 that closed both ways. So `--jobs` up to the physical core count is
serial in all but name there, and `--serial` turned a 20-minute sweep into a
two-hour one for nothing. On a machine nobody has calibrated, make that
comparison once rather than assuming either way.

### 5f. The same certificate written two ways (minutes)

`dj-overload-ti` and `dj-overload-sn` pin the disjunctive overload check to its
time-indexed or its sorting-network certificate. `dj-overload` takes the
default, `cheaper`, which picks per firing from the window's shape: the sorting
network once a window's span passes 300 times its task count, a crossover whose
measurement is written up beside `overload_crossover` in
`gcs/constraints/disjunctive/disjunctive.hh`. The inference is held fixed and
only the proof changes, so this is the cleanest comparison the harness offers,
and one closed instance prices it:

```shell
mkdir -p ft06-only && ln -sf "$PWD/scheduling-instances/jobshop/ft06.jss" ft06-only/
tools/scheduling_sweep.py --binary build/rcpsp --out overload-certificates.jsonl \
    --mode prove --jss-dir ft06-only \
    --arms dj-overload-dd,dj-overload-ti-dd,dj-overload-sn-dd --timeout 600 --jobs 3
```

All three should take the same number of recursions; if they do not, the
certificate is changing the search and that is a bug. On `main` at `58fad258`
with the five branches above they take 123 each. `cheaper` never crosses over on
`ft06`, so its proof is byte-identical to `time-indexed`'s, at 865,336 bytes,
against 2,957,000 for the sorting network: 3.4x the proof for an identical
inference, and it takes longer to check. That is one instance with narrow
windows, where the crossover says the network should lose; the same step over a
family whose windows are wide enough to cross is the measurement #730 still
lacks.

## 6. What to bring back

Every `.jsonl` file, plus:

```shell
git rev-parse HEAD > provenance.txt
{ echo; c++ --version; cmake --version | head -1; veripb --version; uname -a; nproc; } >> provenance.txt
```

The rows already record the timeout, the arm and how parallel the sweep was;
`provenance.txt` supplies the rest. **A table of these figures has to name the
build that produced it**, because the counts are not portable across toolchains.

## Traps

**Snapshot the binary before a long sweep, and never rebuild into the tree a
sweep is running from.** A rebuild mid-sweep silently mixes two binaries across
rows, or removes the binary and kills the run. `cp build/rcpsp ./rcpsp-snapshot`
and point `--binary` at that.

**`already_true` does not mean the same thing on every row.** Each rule tests the
live bound and evaluates its own condition in whichever order is cheaper, which
differs between the encodings: on `Disjunctive` edge-finding `firings +
already_true` is a detection count, and everywhere else `already_true` counts
candidates the rule passed over. `dev_docs/rule-counters.md` has the table.

**A simulated firing count and one of these are not the same measurement.**
Figures quoted from standalone simulations of these rules count *detections* on
small random draws; `firings` counts *bound moves* on a benchmark instance. Both
are useful and they are not two halves of one thing.

**An incomplete proof is not a rejected one.** `proof-too-big` and `timeout` mean
the run did not finish, not that VeriPB refused anything. Only `REJECTED` is a
finding --- and it is a serious one, so report it rather than filtering it out.

**Nor is a killed checker.** `verify-killed-N` means VeriPB died on signal N ---
out of memory, or somebody else's `pkill veripb` on a shared machine. It says
nothing about the proof. Every row now carries `verify_rc`, so a run that came
back `REJECTED` can be told apart from one that was killed without re-running
it; a genuine rejection also prints a multi-line `Error: Checking error at ...`
into `verify_says`, where a killed one has said nothing but its banner. If a
whole cohort of rows on one instance rejects at once, suspect the machine before
the solver: they will be the longest-running checks, which is exactly the set a
stray `pkill` catches.

**Filter on `result` and `status`, not on the presence of a makespan.** A row can
be a clean run of an instance that timed out.

**Compare search shape, and sum counters, over closed runs only.** A timed-out
row records `recursions` and the rule counters exactly as a finished one does,
but they measure how far the search got before the clock stopped. Two arms
compared across timed-out rows will "differ" on every one of them --- the
overload-certificate arms, which cannot differ at all, came out different on 81
of 82 job shops that way. And a counter summed over a family is dominated by the
runs that never finished: on `data_bl` under `nfnl` the two runs of forty that
timed out carry 55% of `not_first`'s skipped-candidate total, and on `data_pack`
the unclosed share is 97-99%. A sum over closed runs is a property of finished
searches; a sum over everything is a statement about the timeout.
`dev_docs/rule-counters.md` says the same beside its portability warning.

**`parallel` covers the checking too.** It is the size of the worker pool, and
each worker solves and then checks, so it is the load `verify_s` was measured
under as well as `solve_wall_s`. Verification time is load-dependent in the same
way; quote it with `parallel` beside it.

## One thing worth knowing before you start

On `ft06` --- a 6x6 job shop, the smallest real instance in the set --- the
solver closes the instance in **55 recursions** with `--disjunctive-edge-finding`
and needs **35,142,089** without, under `--branch dom-then-deg --value-order
split` (`dj-ef-dd` against `dj-off-dd`). Under the default branching every other
arm takes, the same pair is **1,588** against **5,465,061**. Both are real: a
factor of 640,000 against one of 3,400, which is why a figure like this has to
name its branching and why the `-dd` arms exist. Either way it is the same rule
that looks marginal on generated instances, and it is the reason the job-shop
family was added. Keep 5b's caveat beside it: the branching behind the 55 finds
no schedule at all on almost every other job shop.

All four are exact on `main` at `58fad258` with the five branches above, and
match the August campaign to the digit:

```shell
mkdir -p ft06-only && ln -sf "$PWD/scheduling-instances/jobshop/ft06.jss" ft06-only/
tools/scheduling_sweep.py --binary build/rcpsp --out ft06.jsonl --jss-dir ft06-only \
    --arms dj-off,dj-ef,dj-off-dd,dj-ef-dd --timeout 1800 --jobs 4
```
