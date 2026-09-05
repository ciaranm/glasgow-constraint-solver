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

At the time of writing four branches carry this, and `main` may or may not have
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
```

756 tests pass with all four applied. If a flag is missing the sweep harness
says so and skips what depends on it rather than failing obscurely, so a partial
combination still runs --- it just measures less.

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

### 5a. Cumulative, search shape (~2-4 hours)

```shell
tools/scheduling_sweep.py --binary build/rcpsp --out cumulative-shape.jsonl \
    --dzn-dir scheduling-instances/rcpsp --collections data_bl,data_pack,data_pack_d \
    --arms off,ef,ttef,energetic,nfnl,nfnlpub,ttef+nfnl,ttef+nfnlpub,elastic,kaoc \
    --timeout 60 --jobs 16 --resume
```

### 5b. Disjunctive on job shops (~2-4 hours)

The family that makes these rules measurable at all. Expect a low closed count:
job shop is hard and the branching here is basic, so compare on the instances
every arm closes.

```shell
tools/scheduling_sweep.py --binary build/rcpsp --out disjunctive-shape.jsonl \
    --jss-dir scheduling-instances/jobshop \
    --arms dj-off,dj-ef,dj-ef-lb,dj-ef-ub,dj-nfnl,dj-nfnlpub,dj-dps,dj-overload,dj-ef+nfnl,dj-ef+dps \
    --timeout 60 --jobs 16 --resume
```

### 5c. Multi-mode, variable durations and demands (~1-2 hours)

```shell
tools/scheduling_sweep.py --binary build/rcpsp --out multimode-shape.jsonl \
    --mm-dir scheduling-instances/multimode/j10 \
    --arms off,ef,ttef,energetic,nfnl --timeout 60 --jobs 16 --resume
```

### 5d. Proof size and verification time (hours to days)

Much the most expensive: every run writes a proof and then checks it. Start
small and grow. The cap is not optional --- an uncapped proving run on a real
instance has written 128 GB in ten minutes.

```shell
tools/scheduling_sweep.py --binary build/rcpsp --out proofs-generated.jsonl \
    --mode prove --generated 'size=10,12,14;seed=1..10;capacity=3,4,6' \
    --arms off,ef,ttef,energetic,nfnl --timeout 60 --proof-cap-mb 4000 --jobs 8 --resume
```

Then the same over `--dzn-dir ... --collections data_bl` and over `--jss-dir`.
Watch the disk: `--jobs 8` at a 4 GB cap can want 32 GB at once, and rows come
back as `proof-too-big` rather than as failures when they hit it.

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
"start small and grow" reading reaches first are the two *coarsest* on disk, and
that is not a coincidence --- the time-indexed OPB is `O(n x horizon)`, so the
cheapest instances to certify are the ones with the shortest durations. Picking
by cost picks by duration, and a step that stops when the time runs out reports
on short tasks only.

Measured over the whole of both collections, eleven arms, 4 GB cap, 600 s:

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

## One thing worth knowing before you start

On `ft06` --- a 6x6 job shop, the smallest real instance in the set --- the
solver closes the instance in **55 recursions** with `--disjunctive-edge-finding`
and has not closed it after **29.6 million** without. That is the same rule that
looks marginal on generated instances, and it is the reason the job-shop family
was added. Expect the disjunctive arms to separate much more sharply here than
any earlier measurement suggested.
