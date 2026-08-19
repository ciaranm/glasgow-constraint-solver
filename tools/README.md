# Developer tools

Scripts that support development but are not built, installed, or run by
the test suite.

## opb_snapshot.bash

Snapshots every registered example test's OPB definition, for byte-diffing a
refactor that is meant to leave the encoding alone. Runs each test with
`--prove`, keeps that run's `.opb` and `.scp`, and deletes the `.pbp` and
`.varmap` immediately: neither the `.opb` nor the `.scp` is branching-seed
dependent, so two snapshots either side of an output-preserving change should
diff empty, while the proof itself would differ on seed alone. Any binary whose
help mentions `--seed` is given one, so the examples that build a random
instance are pinned rather than skipped.

Run from the repository root after a build, once either side of the change:

```shell
./tools/opb_snapshot.bash /tmp/opb-before
# make the change, rebuild
./tools/opb_snapshot.bash /tmp/opb-after
diff -rq /tmp/opb-before /tmp/opb-after
```

Naming ctest targets as extra arguments snapshots only those. This is a
developer tool, not a ctest: it is never run by the test suite.

## capture_encodings.py

Runs the data-driven constraint test binaries found under `./build` and
captures the `.scp` encoding reports they emit, together with metadata
(constraint type, configuration, expected solution count, VeriPB result),
into structured reports under `./build/scp_capture`. Used when checking
OPB encoding conformance against the verified CakePB encodings (see
`verified_encodings/`).

Run from the repository root after a build:

```shell
python3 tools/capture_encodings.py
```

## scheduling_sweep.py

The sweep harness for the `Cumulative` and `Disjunctive` propagation rules: one
script, an arm table, four instance sources and two modes. It replaces a family
of per-issue scripts that each hardcoded their own arms and answered one
question --- measuring a scheduling rule needs an arm to switch it on, an
instance family it actually fires on, a search-shape number and a proof number,
and each of those scripts had two of the four.

```shell
tools/scheduling_sweep.py --list-arms

tools/scheduling_sweep.py --binary build/rcpsp --out shape.jsonl \
    --dzn-dir ~/mzn-bench/rcpsp --collections data_bl,data_pack \
    --arms ef,ttef,energetic,nfnl --timeout 60 --jobs 8

tools/scheduling_sweep.py --binary build/rcpsp --out proofs.jsonl --mode prove \
    --generated 'size=10,12;seed=1..10;capacity=3,4' --arms ef,ttef
```

One JSONL row per (instance, arm), holding the search shape, every per-rule
counter row (see `dev_docs/rule-counters.md`), and in `--mode prove` the `.opb`
and `.pbp` sizes, the line count, the verification time and the verdict.

**Shape and counters come off one run.** The counters are inert --- they change
no inference and no proof byte --- so this replaces the `STATS=0` / `STATS=1`
two-pass split the older harnesses needed, and a timing column and a counter
column can be read from the same row.

### Things it does that are easy to get wrong by hand

**An arm the binary cannot run is skipped and said to be skipped.** Point it at
a build from before half the stack merged and it tells you which arms and which
instance sources it dropped, rather than failing every run identically or ---
worse --- appearing to measure something. An arm silently dropped looks exactly
like an arm that made no difference.

**An incomplete proof is not a rejected one.** A run killed by the file-size cap
leaves a truncated `.pbp`; a run that hits its own `--timeout` leaves one with no
conclusion. Both are non-empty, both make `veripb` exit non-zero, and neither
says anything about the solver. They come back as `proof-too-big` and `timeout`,
and are never handed to `veripb` at all. A harness that cried `REJECTED` at those
would do it on every large instance.

**Every proving run is capped** (`--proof-cap-mb`, default 4000). An uncapped
`rcpsp --prove` on a real Pack instance has written 128 GB in ten minutes and
taken a machine's disk with it.

**Each run gets its own scratch directory**, because proof files are named after
the run and a parallel sweep would otherwise have several runs writing one set.

**Every row records how parallel the sweep was.** Recursion ratios over
instances every arm closed are load-independent; *closed counts* are not --- "38
against 39" at a 60 s timeout is a statement about one machine under one load.
`--serial` is there for when the closed counts are what is being reported, and
the `parallel` field is there so that a row whose provenance is a 12-way sweep
cannot be quoted as though it were not.

**`--resume` skips rows already in the output**, so a killed cluster job can be
restarted without redoing what landed. `--print-jobs` emits one command line per
run instead of running them, for a scheduler that wants to fan out itself.

### Adding an arm

One line in `ARMS`. Name it after the configuration rather than the rule: several
arms are a rule plus the strengthening that *replaces* its detection, which is
how the flags work and how a row has to be read. Disjunctive arms have to carry
`--unary disjunctive --machine disjunctive` themselves --- without them nothing
posts a `Disjunctive` on a file-read instance, and the arm would measure an
unchanged model very convincingly.
