# `cumulative_strengthening`: tighten each `Cumulative` by integrality, as a derived constraint

> **Maturity** experimental: C++ API only, off unless added ·
> **Audited** 2026-10-04 at `7e1c4178` ·
> **Open issues** filed by this audit: #1240 (the pass is `O(horizon)`),
> #1241 (proof budgets), #1242 (raise by contradiction). Already open and
> touching this presolver: #702 (no `with_makespan`). Shared with the other
> derived-Cumulative presolvers and owned by
> [`cumulative.md`](../constraints/cumulative.md): above `Off`, a proof in
> which it installs something fails to parse under the default encoding, and
> over a `Disjunctive2D` donor it would strengthen the solve throws (#1234).
> Tracked under #871 and #976.

`CumulativeStrengthening` is a presolver. It applies Schulz's pre-solving
strengthenings of a `Cumulative`, as recapped by Cloutier and Quimper (CP 2026,
§2.3), and works on each donor: every posted `Cumulative`, and each axis of a
`Disjunctive2D` (#973). For each donor it computes

```
kappa = max over t of (largest subset sum, at most C, of the heights of the tasks
                       that can run at t and can run beside something)
```

Then it installs a **derived** `Cumulative` with capacity `kappa`, in which every
task that cannot run beside anything ("full") has its height set to `kappa`. The
donor stays posted, and the OPB, the `.scp` and the solution set are untouched.
Each per-time capacity row of the derived constraint is *proved* from the
donor's row for that time. The derived constraint runs the energy rules only.

The rewrites are provably neutral for time-tabling, so the presolver changes
nothing unless an energy rule then refutes something the donor's capacity let
through. Five things to know before touching it:

- **Nothing outside a C++ program reaches it.** No front end adds it: not
  MiniZinc, not XCSP3, not the `.scp` solver, not `gcspy`, and not any example.
  `examples/rcpsp` has flags for `InferredDisjunctive` and
  `InferredCumulative`, but none for this presolver.
- **Its own pass walks every time point of the horizon, with proofs off too.**
  - The cost is `O(H · n)` time and memory over the hull of the task windows,
    plus a capacity-sized subset sum at every time point.
  - Measured: 1.1 s and 567 MB at a horizon of 10⁶. The donor alone takes
    0.03 s and 43 MB.
  - At 10⁷ it takes 12 s and 5.6 GB.
  - Every answer depends on the time point only through which tasks can run
    then, so the stretches between window edges are enough. The derived
    constraint's row contract already says exactly that. This is #1240.
- **With proofs on it can do less than with proofs off.** Its two proof
  budgets only apply when a logger is present.
  - Both budgets sum a prediction over **every non-empty time point of the
    window hull**. Rows are derived lazily (one per stretch, plus cited
    times; #1130), so the prediction grows with the horizon where the proof
    need not. The sum is a true upper bound, since search can cite a row at
    any of those points, but a loose one.
  - The dynamic-programming budget also predicts `items × (C + 1)` states per
    time point, which grows with the capacity's *magnitude*. The derivation
    has a state per *reachable* partial sum, and that count does not change
    when every number is scaled.
  - **Magnitude.** A seven-task fixture with its heights and capacity
    multiplied by 20 is declined. The proofs-on search then takes 182 nodes where the proofs-off
    one refutes at the root. The derivations it refused are three rows of
    about 427 lines each, the same at ×1, ×5, ×20 and ×100. Declining made the
    proof *bigger*: 8,405 lines and 0.24 s to check, against 3,446 lines and
    0.03 s with the budget raised.
  - **Horizon.** `deep_gap` with starts in `[0, 1000]` is declined with proofs
    on, though the derivation it needs is one row and a 389-line proof. `r1`
    with starts in `[0, 6000]` is declined by the raise budget, though its
    raise is one line. Both come from the fact-check's `budget_h` probes,
    reproduced here.
  - This is #1241.
- **Raising a height costs proof lines in proportion to the capacity's
  magnitude, and that cost is avoidable.** The raise is a loop of `pol` steps,
  and in the worst case it takes one step per unit of `kappa`. The
  `knapsack_raise` fixture scaled ×100 emits 2,000 raise steps. A proof by
  contradiction reaches the same row in three rule steps (`red`, `pol`,
  `rup`; six lines of text) whatever `kappa` is. It was checked by hand on
  VeriPB 3.0.2, and the over-claim is rejected. This is #1242.
- **Above `AssertionLevel::Off`, a proof in which it installs something fails
  to parse, under the default encoding.**
  - The cause is owned by [`cumulative.md`](../constraints/cumulative.md)
    (#1234). The donor's start-checkpoint flag
    definitions are emitted only at `Off`, but the recovery of a derived row
    cites them.
  - Confirmed for this presolver on the `r1`, `pack`, `two_full` and
    `knapsack_raise` fixtures at `Definitions`, `Inferences` and
    `Backtracking`, and at `Links` too, where the failure is the same parse
    error. Separately, at `Links` every proof of a satisfiable model is
    rejected at its first `solx` (#1210).
  - **Where it does not happen:**
    - A donor it strengthens nothing on (`nothing_to_gain`, `all_full`) gives a
      proof that verifies under assertions.
    - Under `GCS_CUMULATIVE_ENCODING=time-indexed`, an encoding nothing ships
      but which the environment can select, the same four fixtures verify
      under assertions.
  - **Over a `Disjunctive2D` projection donor it is worse, where it would
    strengthen something.** On `bars` the solve throws at every level above
    `Off`, under both encodings. On `strip` it posts nothing, and the proof
    verifies under assertions. See [Robustness](#robustness-and-limits).
  - So the hints-only mode, which the external justifier is to consume, cannot
    carry any strengthening this presolver makes today.

The design note [`cumulative-strengthening.md`](../cumulative-strengthening.md)
stays as the long note. It holds the arithmetic of `kappa`, the full-task rule,
the neutrality theorem, and the cutting-planes raise. This document is the
audit record, and it does not repeat that material.

## What it is

### Semantics

`CumulativeStrengthening::run` visits `innards::cumulative_donors(problem,
propagators)`. That covers every posted `Cumulative`, in posting order, then
every donor a constraint published through `publish_cumulative_donor`. Today
that means each axis of a `Disjunctive2D` whose projection window fits (#973).

For each donor:

1. **Reduce it to constants.** `CumulativeDonor::view` builds a
   `CumulativeDonorView` (see [`cumulative.md`](../constraints/cumulative.md)).
   - A constant height is kept.
   - A plain variable height with a positive lower bound is *converted* to that
     lower bound, the task's guaranteed demand.
   - A height that is a view, or whose lower bound is at most 0, is *set
     aside*: weakened out of every row, with zero length in the derived
     constraint.
   - An optional task whose guaranteed demand exceeds the capacity is set
     aside too.
   - A variable capacity is read at its current upper bound.
   - A capacity that is a *view* makes the whole donor irreducible.
2. **Decline early** on an irreducible capacity, on a capacity above
   `with_subset_sum_capacity_limit` (default 10⁶), or on a *mandatory* usable
   task whose guaranteed demand exceeds the capacity.
3. **Assess** (the `assess` lambda).
   - The window of each usable task is `cumulative_task_window`:
     `[lb(s), ub(s) + ub(l) − 1]`, from bounds only.
   - A task is **full** when, for every other usable task `j`, either the two
     windows are disjoint or `h_i + h_j > C`. A task whose window overlaps
     nobody's is therefore full vacuously.
   - For every integer `t` in the hull of the windows, `kappa_t` is the
     largest subset sum at most `C` of the non-full heights whose windows
     contain `t`.
   - `kappa` is the maximum of the `kappa_t`. A donor where every task is
     full gets `kappa = 0`, and is declined.
   - A donor whose `kappa` equals `C` and which raises no height is declined
     as "nothing to gain".
4. **Choose between converting and setting aside.** If any height was
   converted, the donor is assessed again with those tasks set aside. The
   set-aside version wins when it gives a strictly smaller `kappa`, or when
   the converted one had nothing to gain.
5. **Budget, with proofs on only.**
   - The dynamic-programming states predicted are
     `Σ_t [not by division] |items_t| · (C + 1)`, against a budget of 20,000.
   - The raise steps are those `raise_steps` predicts, against a budget of
     5,000.
6. **Install** one derived `Cumulative` through `install_derived_cumulative`.
   - It has capacity `kappa` and the donor's tasks, with each full task's
     height set to `kappa`.
   - It carries the donor's presences, and runs the rules `with_rules` gave
     (default: `time_table = false`, `overload = true`,
     `profile_overload = true`).
   - Its rows come from the recipe catalogued below.

**Degenerate shapes.**
- **No donor.** The stats block still registers, and its summary says "no
  posted Cumulative to look at".
- **No usable task**, for example every height zero or set aside: declined as
  nothing to gain.
- **A single task**: it is a loner, so it is full, `kappa = 0`, and it is
  declined (by reading the code; the `loners` probe shows the same path).
- **Every task a loner**, as in the `loners` probe of three tasks with disjoint
  windows: declined as nothing to gain. Plain subset-summing would have
  strengthened `8` to `3`.
- **Some tasks loners**, as in the `loners_plus` probe: they are raised.
  `loners_plus` takes the capacity from 8 to 6, raises two heights from 3 to
  6, and verifies.

### Concrete constraints and frontend coverage

This is a presolver, so the table lists its **entry points**: the option or
flag that turns it on, per front end.

| Entry point | C++ API | MiniZinc (`fzn-glasgow`) | XCSP3 | `.scp` solver | `gcspy` / CPMpy | Examples |
|---|---|---|---|---|---|---|
| `CumulativeStrengthening` | `Problem::add_presolver(CumulativeStrengthening{…})` | `frontend gap (#983)` | `frontend gap (#983)` | `frontend gap (#983)` | `frontend gap (#983)` | none; `examples/rcpsp` has no flag[^fe] |

#983 (open) tabulates all three scheduling presolvers as reachable from no
front end, and asks whether each should get a flag or whether there should be
a `--presolve` vocabulary.

[^fe]: Checked by grep at `7e1c4178`. The only callers are its own test,
`disjunctive_2d_presolver_test.cc` and `cumulative_wide_horizon_test.cc`.
`fzn-glasgow` and the XCSP3 solver add `DifferenceLogic` only.
`examples/rcpsp` adds `DifferenceLogic`, `InferredDisjunctive` and
`InferredCumulative`. The audit's measurements on `rcpsp` used a local
one-flag patch (`tmp/fd-sched/cumulative_strengthening/src-rcpsp`, never
committed).

The donors it reads:

| Donor | Read as |
|---|---|
| `Cumulative` (any of its three constructors) | `cumulative_donor_view`: per-task reduction, as above |
| `Disjunctive2D`, each axis | the projection `Disjunctive2D` resolves in `prepare()` and publishes from `install_propagators` (`disjunctive_2d.cc:634`, `:683`): every length, height and the capacity already constants (`PublishedCumulativeDonor`); variable sizes enter at their declared floors |
| `Disjunctive` | not read. A unary resource has nothing to subset-sum |
| a resource written as linear inequalities | not read |

### Options

None of them changes the OPB, and none of them changes what the derived
constraint *says*. Each one decides only whether a donor is strengthened, and
which rules the result runs.

- **`with_dynamic_programming_budget(states)`**, default 20,000. This caps the
  predicted states of the knapsack derivation, summed over every non-empty
  time point of the window hull. It applies only with proofs on. The prediction grows
  with the horizon and with the capacity's magnitude, not with the
  derivation's real size; see [Can it weaken the model?](#can-it-weaken-the-model).
- **`with_raise_budget(lines)`**, default 5,000. This caps the `pol` steps the
  raise is predicted to emit, summed over every non-empty time point of the
  hull. It applies only with proofs on. Like the other budget, it grows with
  the horizon, where the rows actually derived need not.
- **`with_subset_sum_capacity_limit(capacity)`**, default 10⁶. A donor whose
  capacity exceeds it is declined before assessment, with proofs on or off.
  It bounds the *per-time-point* assessment, since the bitset has `C` bits. It
  does not bound the *total*, which is that cost multiplied by the horizon
  (#1240).
- **`with_rules(CumulativeRules)`**, default the energy rules only. Time-tabling
  on a derived constraint is provably redundant (see the neutrality argument
  in the design note). The neutrality test turns it back on so that its
  comparison means something.
- **`with_proof_mutation(...)`**: test-only corruptions, listed under
  [Tests](#tests).

There is no `with_makespan` (#702). The other two derived-Cumulative presolvers
take one, and this is the presolver whose strengthened capacity improves the
energy bound most directly. So **makespan-link detection does not exist here**.
The makespan bound's runtime rule is owned by
[`cumulative.md`](../constraints/cumulative.md).

No `with_consistency()`; `consistency::` tags do not apply.

### Variable kinds and views

These are donor arguments, as `cumulative_donor_view` reads them:

| Argument | Accepted | What happens |
|---|---|---|
| start | any `IntegerVariableID` | only its bounds are read, for the window |
| length | constant, or variable | a variable length is kept, at its upper bound for the window. Its `after` pin goes through the donor's published end proxy (#685). Above `Off` that proxy line is not published, so a task with both a variable start and a variable length is **set aside** (`donor_view.cc`, the `end_lower_bound_role` lookup). The donor is still strengthened over the rest, and counted in `donors_with_set_aside_tasks`. That is a strength change across assertion levels; see [Can it weaken the model?](#can-it-weaken-the-model) |
| height | constant; plain variable with positive lower bound; view, or lower bound at most 0 | constant: kept. Plain variable: converted at its lower bound, or set aside if that strengthens more. View or non-positive lower bound: set aside |
| capacity | constant; plain variable; view | constant: as posted. Plain variable: its upper bound at presolve, with the row reduced through that bound's order literal. View: the donor is declined (`declined_irreducible_capacity`) |
| presence | constant or variable | carried into the derived constraint unchanged; never a restriction |

**The proof** handles everything in that table. The view restrictions exist
*because* the proof cannot cancel a view's bits against the row's, so nothing
is accepted by the pass and then left unjustified.

### Reification

None, and none wanted: a presolver's rewrite is unconditional.

### Relation to other families

- **Into this presolver:** every posted `Cumulative`, and
  `Disjunctive2D`'s projections (#973).
- **What it posts:** nothing *posted*. It installs one derived `Cumulative`
  propagator per strengthened donor, under `CurrentlyUnnamedConstraint`, and
  writes nothing to the OPB. The derived constraint's propagator, its rows'
  install-time probe and its lazy row derivation (#1130) are all
  [`cumulative.md`](../constraints/cumulative.md)'s.
- **Shared code:**
  - `largest_subset_sum_at_most` and `derive_subset_sum_strengthening`
    (`innards/proofs/subset_sum_strengthening`, note
    [`subset-sum-strengthening.md`](../subset-sum-strengthening.md)).
  - `recover_am1_from_row` (`innards/proofs/am1_from_row`).
  - `cumulative_donor_view`, `recover_constant_argument_row` and
    `cumulative_donors` (`constraints/cumulative/donor_view`).
  - `install_derived_cumulative` and `cumulative_task_window`.
  - The subset-sum utility's only other non-test caller is Cumulative's
    knapsack overload (KAOC, `cumulative.cc:2844`).
- **Other presolvers:**
  - `InferredDisjunctive` and `InferredCumulative` read the same donors and
    install the same derived machinery. None of the three reads the others'
    derived constraints as donors.
  - Every presolver's installs are initialised before the next one runs
    (`solve.cc`), and `choose_optional_interior_pruning()` runs after the
    last.
  - "Every task full" is declined here, because it is a disjunctive, and
    finding those from conflict cliques is `InferredDisjunctive`'s job.
  - **Order matters.** The answer depends on earlier presolvers through the
    `State` it reads: start bounds for the windows, a variable capacity's
    upper bound, and variable heights' lower bounds. Those are read after
    every earlier presolver's installs have been initialised. Other presolvers'
    derived constraints are never donors, so they do not feed it, and it does
    not feed them.
    - **`DifferenceLogic` changes it.** That presolver's initialiser
      (`difference_graph.cc:1226–1248`, with root simplification at `:360`)
      infers `¬cond` for a half-reified edge that cannot hold. A condition can
      be a bound literal on a start, so it can tighten a window before this
      presolver reads it.
    - **The counterexample**, from the cross-document re-check
      (`crossdoc2/order/o.cc`), reproduced here:
      - starts `s0, s1 ∈ [0, 5]` and `s3 ∈ [4, 6]`, lengths 2, heights
        `{4, 2, 3}`, capacity 8;
      - with `s1 − s0 ≤ 2` and `LinearLessThanEqualIf(s0 − s1 ≤ −5, s0 ≥ 3)`.
      - This presolver alone takes 1 off the capacity. `DifferenceLogic` then
        this one takes 2 off. This one then `DifferenceLogic` takes 1 off.
      - All three verify.
    - **The `rcpsp` sweep was a weak check of this.** It compared
      `--variant=presolved` against `--variant=decomposed` on 40 seeds and
      found no difference, but only seeds 17 and 27 strengthen anything at
      all, and seed 25 prints no summary even at 300 s.
    - So run `DifferenceLogic` first where both are used. The derived makespan
      initialiser writes only the makespan variable, which this presolver does
      not read.
- **Reachable only by the C++ API**, as above.

## The proof model

### OPB encoding

**None. The presolver writes nothing to the OPB or the `.scp`.**
- **Checked:** `pack`, `r1` and `two_full` give byte-identical `.opb` files
  with and without the presolver (`cmp`), and so does `r1`'s `.scp`.
- **Also in the suite:** the test's negative control and its
  `check_opb_unaffected` assert the same thing.

Everything it adds is derived inside the proof, so the model VeriPB checks
against is the user's.

### Labels

None of its own. A recipe receives the donor's row for `t` as a `ProofLine`
argument, which the derived machinery recovers or looks up. It finds activity
flags by key, `ConstraintProofModelData<Cumulative>::active_flag_key(i, t)`,
under the donor's `ConstraintID`. No OPB label is cited by this presolver's own
code.

### Cake conformity

Not applicable. `cake_pb_cp` re-derives the OPB from the `.scp`, and both are
unchanged, so the presolver is invisible to the chain. No SCP chain case adds
it.

### Proof-time state

What a strengthened donor leaves in the proof, per time point whose row
something cites:

- **When rows are derived.** There is one at the first time point of each
  stretch between window edges, at install. After that there is one per
  further time point a firing cites, during search (#1130).
- **The working lines.** Everything a recipe derives goes inside a
  `ProofScaffoldingScope` at `ProofLevel::Temporary`, and is deleted on the
  way out (`del range …` / `del id …`). That covers:
  - the reduced donor row, from `recover_constant_argument_row`;
  - the subset-sum derivation: two `pol`s by division, or the layered
    programme with three `ProofFlag`s per state (`ssge`, `ssle`, `sseq`), each
    defined by a `red` pair;
  - the pairwise at-most-ones;
  - the raise steps.
- **What stays.** One line per row is kept, at `ProofLevel::Top`: the `ia`
  restating the result as `Σ derived_h_i · active_{i,t} ≤ kappa` over the
  donor's flags. It survives for the solve. There is no extra deletion
  anywhere a later reconstruction would need.
- **Proof comments** mark each derivation, which is how a reader or a test
  finds them:
  - `% presolve cumulative gcd`, `% presolve cumulative kappa` and
    `% presolve cumulative kappa already reached`;
  - `% presolve cumulative amo`, at a raised row;
  - one `% presolve cumulative: strengthened <id> from capacity C to kappa,
    raising k heights to the capacity` per donor.
  - The subset-sum utility adds its own: `% subset sum strengthening by
    divisibility: 8 to 6, divisor 3` and `… by dynamic programming: 6 to 5`.
- **Proof-only auxiliaries** are the dynamic programme's flags, introduced by
  redundance and defined over the donor's activity flags. They are therefore
  determined by unit propagation on a solution. Their definitions are deleted
  with the scaffolding. Enumeration proofs that took the knapsack path verify,
  for example `deep_gap` (24 solutions) and the fuzz campaign below.
- **Nothing proof-only is indexed by something that dangles with proofs off.**
  The recipe captures its own copy of the assessment (`by_time`).

**What the installed machinery asserts in hints-only mode.** The derived
constraint is installed under `CurrentlyUnnamedConstraint`, so its assertions
carry `::cumulative:((constraint_id unnamed) (subhint …))`. At `Inferences`,
`pack` and `knapsack_raise` each carry one, with `(subhint overload)`. A
justifier therefore cannot find the derived constraint by id. It has to
recognise the derived rows, which are the `ia` lines at `Top` that follow a
`% presolve cumulative` comment, by their content. The rows themselves are
derived in full at every level and are not asserted.

**At assertion levels above `Off`.** The presolver has no assertion path of its
own: every rewrite is emitted as a full derivation at every level.
- **Where it installs something,** under the default start-checkpoint encoding,
  the proof nevertheless fails to parse at `Definitions`, `Inferences` and
  `Backtracking`. The recovery of the donor's row cites flag definitions the
  donor emits only at `Off`. That defect is owned by
  [`cumulative.md`](../constraints/cumulative.md) (#1234).
- **At `Links`** the posted-donor runs with an install fail with the same
  parse error. Without the presolver, or with nothing installed, a
  satisfiable model is rejected at its first `solx` (#1210; `r1`), while the
  unsatisfiable `pack` verifies.

Evidence from this audit (`fixtures.cc`) and the cross-document re-check
(`tmp/fd-sched/factcheck/crossdoc2/fx`, `d2`, and `crossdoc3/fx` for the
`Links` and nothing-installed rows):

| Fixture | `Off` | `Definitions` | `Links` | `Inferences` | `Backtracking` |
|---|---|---|---|---|---|
| `r1`, without the presolver | verified | under assertions | rejected (#1210) | under assertions | under assertions |
| `r1`, `pack`, `two_full`, `knapsack_raise`, with it | verified | parse error | parse error | parse error | parse error |
| the same four, with it, `GCS_CUMULATIVE_ENCODING=time-indexed` | verified | under assertions | `r1` rejected (#1210); the other three under assertions | under assertions | under assertions |
| `nothing_to_gain`, `all_full`, with it (nothing installed), either encoding | verified | verified (`nothing_to_gain`: nothing asserted) / under assertions (`all_full`) | `all_full` under assertions | under assertions | under assertions |
| `bars` (a `Disjunctive2D` projection donor, strengthened), either encoding | verified (816 solutions) | **throws** | **throws** | **throws** | **throws** |
| `strip` (a `Disjunctive2D` projection donor, nothing posted), either encoding | verified (48 solutions) | under assertions | rejected (#1210) | under assertions | under assertions |

The error is `The label @v[_1][0_0][ca][r] is not assigned to a constraint ID`.
`InferredCumulative` gives the same errors on all four fixtures.
`InferredDisjunctive` gives them on `two_full`. On `r1` and `pack` its proofs
parse, because it installs nothing there: at `Off` it writes no presolve
comment on either, against 8 on `two_full`.

The `bars` row comes from the fact-check's corrected probe, which maps `Links`
correctly. The copy in this audit's `bars-assert/` ran its `links` case at
`Backtracking`.

## The implementation

### Initialisation and global data

The pass itself is the whole of the root cost. There is no initialiser of its
own.
- **Per donor:** the view; then an `O(n²)` pairwise full-task test; then,
  for every integer `t` in the window hull:
  - an `O(n)` scan to collect the tasks;
  - `largest_subset_sum_at_most` over a fresh `C`-bit bitset,
    `O(|items| · C / 64)` words;
  - a downward per-value scan from `C`, which is `O(C − kappa_t)`.
- **Retained:** a `TimePoint` per non-empty `t`, each holding three vectors.
  These are moved into `by_time`, a `std::map`, and the recipe then captures a
  **copy** of that map. So peak memory holds two maps, and the fact-check found
  the copy to be about 22% of samples at 10⁶. The map is built and copied with
  proofs off too, where nothing will ever read it.
- **Repeated work:** with a converted height the assessment runs twice.

Measured, with proofs off. The probe is `horizon.cc`: three tasks, length 2,
height 2, capacity 5 → `kappa = 4`, starts in `[0, H]`, stopped at the first
solution. Release build at `7e1c4178`, fataepyc-08, 2026-10-04, pinned to one
core, with `GLIBC_TUNABLES` mmap and trim thresholds at 4 GiB:

| `H` | donor alone: s / peak RSS | with presolver: s / peak RSS |
|---|---|---|
| 10⁴ | 0.008 / 4.7 MB | 0.010 / 9.3 MB |
| 10⁵ | 0.003 / 7.7 MB | 0.10 / 60 MB |
| 10⁶ | 0.031 / 43 MB | 1.10 / 567 MB |
| 10⁷ | 0.34 / 395 MB | 12.1 / 5.6 GB |
| 10⁸ | 3.6 / 3.9 GB | not run |

With proofs on at 10⁶ it is the same (1.13 s, 570 MB), and only one capacity
row is derived. The proof side is lazy (#1130). The assessment is not.

**The donor's own horizon cost is `cumulative.md`'s.** The 10⁸ row shows
39 bytes per time point, and at 10⁹ the donor alone hits `bad_alloc` under a
16 GB `ulimit -v`. The presolver multiplies that per-point cost by about 14 in
memory and 35 in time.

**The task-count and capacity axes**, same build and machine:
- **Task count:** at `H = 10⁵`, `n = 3 / 10 / 30` take 0.10 / 0.14 / 0.22 s.
- **Capacity:** `n = 10`, `C = 999,999`, heights 2, so `kappa = 20`.
  - `H = 10³` takes 0.59 s.
  - `H = 10⁴` takes 5.9 s.
  - That is about 0.6 ms per time point, most of it the downward per-value
    scan from `C` to `kappa_t`.

### Propagator inventory

The presolver's own pass has no propagator. What it **installs**, per
strengthened donor:

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| derived `Cumulative` (`install_derived_cumulative`) | `on_bounds` on each start and variable length; `on_instantiated` on each variable presence | derived (none) | [`cumulative.md`](../constraints/cumulative.md)'s rules under the given `CumulativeRules` | a successful install | see `cumulative.md` | see `cumulative.md` |

The derived constraint's rules, state, idempotence and self-disabling are
documented in [`cumulative.md`](../constraints/cumulative.md) and not repeated
here.

### Mutable state and incrementality

**The pass:** none. It runs once.

**The recipe:** it holds immutable captures (`by_time`, the view, the heights,
`kappa`), plus a `shared_ptr` to the stats block. During search it bumps
`rows_by_division`, `rows_by_dynamic_programming`, `rows_with_a_raise` and
`raise_lines_emitted` as rows are cited, so those counters grow during the
solve. That is by design (#1130), but a reader comparing two runs' stats must
compare at the end of the solve.

The installed propagator's state is `cumulative.md`'s.

### Interior values and optional pruning

**What this presolver offers.** None. It installs no optional-interior-pruning
pair.

**What it observes.** Its whole vocabulary is bounds.
- **The pass** reads a start's bounds, a length's upper bound, a height's lower
  bound and a capacity's upper bound. A hole changes none of its answers. A
  start with domain `{0, 10⁶}` gets the window `[0, 10⁶ + l − 1]`, which is
  sound and costs a million assessment points (#1240).
- **The installed propagator** triggers `on_bounds` and `on_instantiated` only,
  so it declares no hole sensitivity. It neither keeps alive nor suppresses
  anyone else's interior pruning. That is honest: its rules read only window
  bounds and presences. `choose_optional_interior_pruning()` runs after the
  last presolver, so the derived propagator's declaration is counted.

### Robustness and limits

- **Unbounded domains.** The window hull is walked point by point, so a wide
  start domain is time and memory (#1240). At 10¹² the probe ends in
  `bad_alloc`, but the donor alone does that too, from 10⁹. Capacity is capped
  at 10⁶ before any work.
- **Negative values and zero.**
  - Starts near `−(2⁶⁰ − 1)` and near `2⁶⁰ − 1` (spans of 5) are strengthened
    and verify (`range.cc`: `bottom_starts`, `top_starts`, 96 solutions each).
  - A negative height lower bound is rejected by `Cumulative` itself
    ("heights must be non-negative").
  - A zero lower bound sets the task aside.
  - A capacity of zero declines the donor, by reading the code. Any mandatory
    task with a positive height makes it infeasible; otherwise `kappa = 0`.
- **The degenerate shapes** are listed under [Semantics](#semantics).
  - A height above the capacity on a mandatory task gives
    `declined_infeasible_donor` (`huge_height_mandatory`, `2⁶⁰ − 1`).
  - On an optional task that task is set aside, and the rest is strengthened
    and verifies (`huge_height_optional`, 500 solutions).
- **Overflow.** The capacity limit is what keeps the arithmetic in range.
  - Every `Integer` is checked arithmetic.
  - The state prediction is `long long`, summed over the horizon. It could
    only wrap past `9.2 × 10¹⁸ / (n · 10⁶)` time points, which the
    assessment's memory forbids long before.
  - In the raise, `e · weight` is at most `C²`, which is 10¹² at the limit.
  - At the edges: `huge_capacity` (`C = 2⁶⁰ − 1`) and
    `variable_capacity_huge_ub` are both declined as
    `declined_capacity_too_large`.
- **A `Disjunctive2D` donor it would strengthen aborts the solve at an
  assertion level above `Off`.**
  - With no proof, and at `Off`, the presolver test's `bars` instance installs
    one derived constraint and finds 816 solutions. VeriPB verifies the `Off`
    proof.
  - At `Definitions`, `Links`, `Inferences` and `Backtracking`, the recipe
    finds no row for the donor at time 0, and throws from
    `cumulative_strengthening.cc:512`. The message is `unexpected problem:
    cumulative strengthening: the donor has no capacity row at time 0, which
    cannot happen for a constraint derived over all of its tasks`.
  - So the user gets an exception, not a proof. The same happens under the
    time-indexed encoding.
  - It happens only where the presolver would strengthen something. On the
    `strip` instance it posts nothing, and the proof verifies under
    assertions at `Definitions`, `Inferences` and `Backtracking`, under both
    encodings (cross-document re-check, `crossdoc2/d2/runs.txt`).
  - Found by the `disjunctive_2d.md` fact-check (`probe5bars.cc`), and
    reproduced here at `7e1c4178` (`bars-assert/`).
  - It is the same root cause as the parse errors on posted donors: the
    donor's machinery is not set up at these levels. It is folded into
    #1234.
- **Not a presolver problem, but met here.** A `Cumulative` with a variable
  height in `[2, 2⁶⁰ − 1]` and capacity 5 does not finish in 600 s, with or
  without the presolver.
  - The donor never bounds a height by the capacity, so search walks it value
    by value. `vh.cc` takes 96,042 nodes at an upper bound of 10³ and
    9,600,042 at 10⁵.
  - That belongs to [`cumulative.md`](../constraints/cumulative.md), not to
    this presolver.

### Interval efficiency

The pass is a whole-model scan, which is exactly the shape the presolver
variant warns about.

1. **The propagation side (the pass).**
   - **The horizon.** `for (Integer t = global_lo; t <= global_hi; ++t)` walks
     every integer in the window hull. Nothing exits early.
     - It is not bounded by anything but the horizon, and it runs with proofs
       off.
     - The interval structure to exploit is plain: every value it computes at
       `t` depends only on the set of tasks whose windows contain `t`. That
       set changes only at the `2n` window edges.
     - The derived constraint already relies on this (its recipe contract,
       #1130). **#1240.**
   - **The capacity.** `largest_subset_sum_at_most` builds a `C`-bit set
     word-parallel, then scans downward from `C` **one value at a time**
     (`for v = bound; v >= 0; --v`). That scan is per value of the capacity
     range, bounded only by the 10⁶ limit.
2. **The reason side.** None. A presolver gives no reasons.
3. **The proof side.**
   - **Rows** are one per stretch at install, plus one per cited time point,
     never per horizon point (#1130). That was checked: one row at
     `H = 10⁶`, and `cumulative_wide_horizon_test` asserts at most 200 at
     10⁵.
   - **Division path:** two `pol`s per row (one line in the emitted form),
     whatever the widths.
   - **Knapsack path:** three flags per *reachable* partial sum per item. That
     does not change when every number is scaled: in `budget.cc` each
     derivation is about 427 lines at ×1, ×5, ×20 and ×100.
   - **Raise:** up to one `pol` per unit of `kappa` per raised task per row
     (every step is one exactly when the rest of the row totals at least
     twice `kappa`, `T ≥ 2·kappa`; at `T = 1.5·kappa` it is still about
     `0.75·kappa` steps).
     That **is** proportional to the capacity's magnitude.
     `knapsack_raise` ×1/×10/×100 emits 20/200/2,000 raise steps.
     **#1242.**
4. **The audit lane.** No row in `gcs/large_domain_audit_test.cc` posts this
   presolver. `cumulative_wide_horizon_test` checks the *proof* side over a
   horizon of 10⁵ (names and rows), but not the pass's cost. The width of a
   start domain and the magnitude of the capacity are both unvaried.
   [Next steps](#next-steps) has an item.

## Rewrite catalogue

Facts common to every entry:
- Every rewrite is posted in **derived mode**: one `install_derived_cumulative`
  per donor, so no OPB row is written.
- Every rewrite's per-time row starts from the donor's row, reduced by
  `recover_constant_argument_row`. That reduction weakens out set-aside
  tasks, converts variable heights' contribution bits to
  `lb(h) · active`, and buys a variable capacity's current upper bound through
  its order literal. The reduction is `cumulative.md`'s.
- **No pinned root bound.** This presolver pins none: it has no
  `with_makespan` (#702), so the derived constraint's makespan bound is never
  asked for. If #702 is done, the bound gets its own entry here.
- Every rewrite closes with an **`ia` pin** to the declared row
  `Σ derived_h_i · active_{i,t} ≤ kappa`, at `ProofLevel::Top`.
- **No published justification procedure covers any of these.** The
  techniques are ours, built from cutting planes and the redundance rule, so
  each entry owes its argument.
- **Neutrality** below means time-table neutrality: with the energy rules off
  on both constraints, the solution set and the recursion count are the same
  with and without the rewrite. Those two are what the test compares
  (`cumulative_strengthening_test.cc:645–650`), and the design note's
  "node-for-node identical" claims more than that.
  - The design note proves it.
  - `cumulative_strengthening_presolver` asserts it on four fixtures: `searchy`
    for the capacity, `deep_gap` for the knapsack path, and `r1` and
    `knapsack_raise` for raises.
  - Separately, and not as a neutrality check (the default rules include the
    energy rules), the RCPSP sweep below found the recursion count unchanged
    on all 40 seeds. On 39 of them that was within 120 s. Seed 25 timed out in
    both arms here, and the fact-check ran it to completion.

### Rewrite: capacity-by-division

- **Pattern matched** — at time point `t` no full task can run, and the
  non-full heights there share a divisor `d > 1` with `d · ⌊C/d⌋ = kappa_t`.
- **Posted or strengthened** — the derived row at `t` over the donor's tasks,
  with capacity `kappa`.
- **Derived mode** — yes.
- **Soundness argument** — every load at `t` is a sum of multiples of `d`, so
  it is a multiple of `d` at most `C`, hence at most `d · ⌊C/d⌋ = kappa_t`.
  And `kappa_t ≤ kappa`.
- **Proof technique** — `pol` (Chvátal–Gomory rounding: divide by `d`, multiply
  back), then `ia` to `kappa`. If `kappa_t < kappa`, the `ia` relaxes the
  degree.
- **Neutral?** — yes: a load is a sum of heights, so it exceeds `kappa` exactly
  when it exceeds `C`.
- **Proof size** — one `pol` line, one `ia`, one `del`, per row. Independent of
  `n`, `C` and the domains: the `div` family's own contribution is 6 lines per
  row, including the reduced-row `pol` and comments.
- **Tightness** — **`BogusDivisor` is the only lane on this path.** On
  `pack`, the `ia` pin rejects it ("not syntactically implied", line 772),
  which is the only thing that can, since the division itself is sound. The
  control is `pack` verified unmutated (markers check). `ClaimOneBetter` on
  `pack` does *not* exercise this path. It claims 5, and since
  `3 · ⌊8/3⌋ = 6 ≠ 5` the utility takes the knapsack path; see below.

### Rewrite: capacity-by-knapsack

- **Pattern matched** — as above, but the division test fails. For example
  heights `{2, 6, 6}`, `C = 10`: the gcd rule offers 10, but the largest
  reachable sum is 8.
- **Posted or strengthened** — as above.
- **Derived mode** — yes.
- **Soundness argument** — the load at `t` is a subset sum of the heights
  present, at most `C`, hence at most `kappa_t` by definition.
- **Proof technique** — `redundance` (three flags per DP state) plus `pol` and
  `RUP` steps of the layered dynamic programme in
  `derive_subset_sum_strengthening`
  ([`subset-sum-strengthening.md`](../subset-sum-strengthening.md)), then `ia`.
- **Neutral?** — yes, by the same argument.
- **Proof size** — proportional to the reachable partial sums times the items,
  which `budget.cc` shows to be scale-invariant: about 427 lines per row for
  seven tasks. In `own.cc` (`dp` family) the own contribution is 215 lines at `n = 4` and 1,127 at `n = 16`
  for one row. The *budget's* prediction grows with `C` and with the horizon,
  which is #1241.
- **Tightness** — `ClaimOneBetter` on `pack` lands here, as above. VeriPB
  rejects it inside the programme, at `rup 1 ~f[308][sseq_7_6] 1 f[309][ssunder] >= 1;`
  (line 1032). `disjunctive_2d_presolver_test`'s `ClaimOneBetter` on the
  `bars` projection is on this path too. `subset_sum_strengthening_test`
  covers `ClaimOneBetter`, `BogusDivisor` and `SkipALayer` on the utility
  itself.

### Rewrite: row restated

- **Pattern matched** — a time point where `kappa_t = C` (so `kappa = C`)
  because the capacity did not move, only a height did, and no full task runs
  at `t`.
- **Posted or strengthened** — the donor's (reduced) row, restated over the
  derived constraint's flags.
- **Derived mode** — yes.
- **Soundness argument** — it is the donor's row.
- **Proof technique** — `ia` from the reduced row.
  `% presolve cumulative kappa already reached` marks it, and no subset-sum
  counter moves.
- **Neutral?** — trivially: the row says what the donor's says.
- **Proof size** — one line.
- **Tightness** — not shown separately.

### Rewrite: raise-a-full-task

- **Pattern matched** — task `i` is full for the donor: every other usable task
  either cannot overlap it or has `h_i + h_j > C`. The test is per task, not
  per `t`. It applies at every `t` where `i` can run.
- **Posted or strengthened** — in the derived constraint `i`'s height becomes
  `kappa`. That is a raise when `h_i < kappa`, and a **lowering** when
  `h_i > kappa`. For example `{7, 2, 2}` under 8 gives `kappa = 4`, and 7
  comes down to 4. Both directions count in `tasks_raised`
  (`cumulative_strengthening.cc:807`, which also counts a full task already at
  exactly `kappa`) and in the
  summary's "raising R heights". The fact-check's `neutral.cc` verified both
  directions, and found both time-table neutral. At each `t` the row is
  `Σ_{f ∈ F_t} kappa · a_f + Σ_{j ∈ N_t} h_j · a_j ≤ kappa`.
- **Derived mode** — yes.
- **Soundness argument** — if a full task is active at `t`, every other task
  that can be active then is not (pairwise conflict), and the left side is
  exactly `kappa`. If none is, the left side is a subset sum of `N_t`'s
  heights at most `C`, hence at most `kappa_t ≤ kappa`. A full task whose
  real height is below `kappa` is raised too. It need not be a loner: it may
  simply conflict with every task it overlaps. Its rows stay sound by the same
  argument.
- **Proof technique** — four parts:
  1. A pairwise **at-most-one** per pair, off the donor's own row
     (`recover_am1_from_row`: weaken the others, saturate, divide). The
     at-most-ones are cached per row.
  2. The full tasks weakened out of the row, and the rest strengthened as
     above, lazily: only when step 4 needs it.
  3. If `kappa_t < kappa`, an `ia` to `kappa` *before* raising.
  4. Per full task, one of three paths:
     - **`T = 0`**: `RUP` of `kappa · a_i ≤ kappa`.
     - **`T ≤ kappa`**: one `pol` summing the at-most-ones weighted by the
       others' coefficients, then `ia`.
     - **`T > kappa`**: a loop of `pol`s. Each takes `λ` copies of the row,
       plus `e · w_k` times each at-most-one, divided by `λ + e`, raising
       `i`'s coefficient by `k` with `k · (T − R) < T − c`.
   - Then the closing `ia`. The arithmetic is in the design note. This audit
     re-derived the step condition independently: the coefficient
     `(λc + eT)/(λ + e) = c + k` is exact, and the degree lands on `R` iff
     `k(T − R) < T − c`. The code's `ceil((T − c)/(T − kappa)) − 1` is the
     largest such `k`.
- **Neutral?** — yes. The derived profile at a full task's compulsory part is
  `kappa`, which pushes out exactly what the donor's `h_i + h_j > C` pushes
  out (design note). Asserted on `r1` and `knapsack_raise`.
- **Proof size** — at-most-ones `O(|F_t| · |N_t| + |F_t|²)` per row. Raise
  steps run from 1, when `T − kappa = 1`, up to `kappa`, when the rest of the
  row totals at least `2·kappa` (from `for_each_raise_step`,
  `cumulative_strengthening.cc:92–111`). Between those the count is still
  linear in `kappa`: `T = 12` at `kappa = 8` takes six. The design note
  (`cumulative-strengthening.md:235`, "overshoots by half") and the code
  comment above `for_each_raise_step` put the threshold at an overshoot of
  half, which is ambiguous, and wrong as naturally read (an overshoot of
  `kappa/2`); both are outside this stack. Measured: `knapsack_raise` emits 20 steps over
  5 rows, `two_full` 35 over 5, `full_task_pack` 18 over 3. Scaled ×10 and
  ×100, `knapsack_raise` emits 200 and 2,000. A proof by contradiction does
  each raise in three rule steps (six lines of text) whatever `kappa` is
  (#1242).
- **Tightness** — two lanes, both rejected at a row's `ia`:
  - `RaiseTooFast` on `knapsack_raise`, one step past the bound
    (line 326, "not syntactically implied").
  - `RaiseUnentitled` on `r1_control`, which raises a task that misses the
    pairwise test by one.
    - Its at-most-one comes out weaker than claimed, and the row's `ia` pin
      is where VeriPB stops (line 97).
    - The derived constraint is genuinely unsound there: with that mutation
      the solve reports 10 of the 24 solutions.
    - The design note says VeriPB rejects it "only because the conclusion is
      false". That is right about the cause, but the line that fails is the
      pin.
  - The control for `RaiseTooFast` is `knapsack_raise` verified unmutated. For
    `RaiseUnentitled`, the honest run on `r1_control` declines the donor
    (nothing to gain), so there is no honest derivation to compare.

### Rewrite: convert-or-set-aside

- **Pattern matched** — a donor with at least one plain variable height whose
  lower bound is positive.
- **Posted or strengthened** — the task is either in the derived constraint at
  height `lb(h)`, or absent (zero length), whichever gives the smaller `kappa`.
  A tie, or the converted assessment winning, keeps the conversion.
- **Derived mode** — yes.
- **Soundness argument** — `contribution ≥ lb(h) · active` (conversion), or
  weakening (set aside). Either way the derived row is implied.
- **Proof technique** — `recover_constant_argument_row`'s single `pol`
  (`cumulative.md`), then whichever rewrite above applies.
- **Neutral?** — this is a choice between two neutral rewrites. The choice is
  arithmetic and has no proof content.
- **Proof size** — the choice itself emits nothing. A converted task costs its
  share of `recover_constant_argument_row`'s one `pol` per derived row: one
  weakening term per contribution bit for a set-aside task, or one
  bits-to-flag conversion for a converted one. A converted task also costs
  `guaranteed_contribution_row`'s own RUP line per row
  (`guaranteed_contribution.cc:55`), plus at most one unit RUP (`:36`). By
  reading the code, that is one term per bit of the height's contribution,
  plus a constant number of lines, so logarithmic in the height's width per
  row. It was not measured. The rewrite then applied costs what its own entry
  says.
- **Tightness** — not shown by a mutation. The test asserts the choice via
  `donors_better_off_setting_heights_aside` and `converted_heights`.

## Detection and its failure modes

The scan is `problem.each_constraint_of_type<Cumulative>()` plus the published
donors. What it **fails to find, silently** (no counter moves, because the
donor never appears in `donors_seen`):

- a resource posted as anything other than `Cumulative`: linear sums, a
  `Disjunctive`, a hand decomposition;
- a `Disjunctive2D` axis whose projection was not published, because its window
  did not fit in `prepare()`;
- derived constraints installed by the other presolvers. These are not donors
  by construction.

What it **finds but turns away**, counted:

| Counter | Meaning | Note |
|---|---|---|
| `declined_irreducible_capacity` | capacity is a view | General note |
| `declined_capacity_too_large` | `C` above the limit | General note, plus one Important note per run |
| `declined_infeasible_donor` | a mandatory task's guaranteed demand `> C` | General note |
| `declined_over_budget` | predicted DP states over budget (proofs on only) | General note, plus Important |
| `declined_over_raise_budget` | predicted raise steps over budget (proofs on only) | General note, plus Important |
| `declined_nothing_to_gain` | `kappa = C` and no height moves | Detailed note |

A decline that is **mis-reported**, and a comment that is stale:

- **"Every task is full" and "every task is a loner" are counted as
  `declined_nothing_to_gain`.** The note reads "its capacity is already the
  largest load its tasks can reach, and no height moved either", which is
  false for both. Checked on `all_full` (`{7, 7, 7}` under 8) and `loners`.
  The design note calls the first case a disjunctive, but nothing here counts
  it as one.
- **A stale comment, not a decline.** The comment after
  `install_derived_cumulative` (`cumulative_strengthening.cc:789–793`) says
  that above `Off`, a task with both a variable start and a variable length
  makes the install decline. It does not: `cumulative_donor_view` sets such a
  task aside first, and the donor is strengthened over the rest
  (`donors_with_set_aside_tasks`). If the install did return false there, the
  `continue` would skip every counter. That branch is unreachable as far as
  this audit found. The comment is outside this stack. The derived
  constraint's own proofs-on decline is `cumulative.md`'s.

## Evidence that it fired

- **The stats block.** `CumulativeStrengtheningStats` is component
  `cumulative_strengthening`. It is registered unconditionally, so it reaches
  `Stats::components()` even when the caller passed none.
  - Its summary is `"N of M posted Cumulatives strengthened, taking K off their
    capacities and raising R heights"`, against `"nothing strengthened, of M
    posted Cumulative(s) looked at"`.
  - That distinguishes "ran and found nothing" (`donors_seen > 0`,
    `donors_strengthened = 0`) from "never saw a donor" (`donors_seen = 0`).
- **The proof**, with proofs on: one
  `% presolve cumulative: strengthened …` comment per donor, plus the per-row
  markers above.
- **Expected counts on named instances** (`fixtures.cc`, default rules, all
  solutions, proofs on):

| Instance | `donors_strengthened` | `capacity_units_removed` | `tasks_raised` | rows (division / DP / raised) | `raise_lines_emitted` |
|---|---|---|---|---|---|
| `pack` (7 × h3, `C = 8`) | 1 | 2 | 0 | 3 / 0 / 0 | 0 |
| `deep_gap` (`{2, 6, 6}`, `C = 10`) | 1 | 2 | 0 | 0 / 1 / 0 | 0 |
| `r1` (`{5, 4, 2}`, `C = 6`) | 1 | 0 | 1 | 0 / 0 / 1 | 1 |
| `knapsack_raise` (`{1, 3, 4, 6}`, `C = 6`) | 1 | 1 | 1 | 0 / 5 / 5 | 20 |
| `two_full` (`{7, 7, 3, 3}`, `C = 8`) | 1 | 2 | 2 | 0 / 0 / 5 | 35 |
| `r1_control`, `nothing_to_gain` | 0 (`declined_nothing_to_gain` 1) | 0 | 0 | — | — |

  Row counts are rows *cited*, so they depend on the search. The fixtures and
  the search are deterministic, so these are single runs.
- **On the only generated benchmark that can reach it.** That is
  `examples/rcpsp` with a local flag, at size 14, capacity 10, demand ≤ 4,
  seeds 0–39. It strengthened one of the two resources on 2 of the 40 seeds,
  and strengthened nothing on the other 38.

## Can it weaken the model?

- **Lose solutions: no, by argument and by test.**
  - The derived constraint is implied, row by row, and the OPB is unchanged.
  - The test's random corpus (60 instances against brute force, proofs off,
    plus a verified sweep) and the fuzz campaign below found no lost
    solution.
  - The one thing no derivation catches is the *set* of raised tasks. A wrong
    set yields a row the donor does not imply, and VeriPB rejects it at the
    pin (`RaiseUnentitled`). `recover_am1_from_row` also refuses a pair that
    does not overshoot.
- **Lose propagation: no, against running without it.** The donor stays
  posted with all its rules, and the derived constraint only adds.
- **The pin.** Every row closes with an `ia` to the declared
  `Σ derived_h · active ≤ kappa`. That is the step that catches a sound
  derivation of the wrong line: `BogusDivisor`, `RaiseTooFast`, and an
  unentitled raise.
- **Proofs on against proofs off: yes, it can be weaker with proofs on.** Both
  budgets apply only with a logger, so a donor strengthened with proofs off
  can be declined with proofs on.
  - That would be harmless if the budgets measured what they claim. Neither
    does: both sum a prediction over every non-empty time point of the hull,
    and the dynamic-programming one also scales with the capacity's
    magnitude.
  - **Magnitude.** `budget.cc` has seven unit tasks, heights
    `{18, 18, 17, 17, 17, 17, 17} × s`, capacity `50s`, starts in `[0, 2]`.
    - At `s = 20`, proofs off refutes at the root (1 node, `kappa = 720`).
    - Proofs on declines over budget (21,021 predicted states) and searches
      182 nodes, writing 8,405 lines that take 0.24 s to check.
    - With the budget raised, the same solve is 1 node, 3,446 lines and
      0.03 s, of which the three knapsack derivations are about 427 lines
      each, the same at `s = 1`, 5, 20 and 100.
    - Both verify UNSATISFIABLE. The budget made the proof bigger.
  - **Horizon.** These are the fact-check's `budget_h` probes, reproduced
    here.
    - `deep_gap` (`{2, 6, 6}`, `C = 10`, length 2) with starts in `[0, 1000]`
      is strengthened with proofs off and declined over budget with proofs
      on. With the budget raised it has one knapsack row and a 389-line
      proof.
    - `r1` with starts in `[0, 6000]` is declined by the raise budget, though
      the raise it predicts the cost of is one line.
    - In both horizon probes the search is the same either way (4
      recursions), and the declined proof is *smaller* than the strengthened
      one: 173 against 389 lines for `deep_gap`, 197 against 286 for `r1`.
      So over a long horizon the budget costs strength only where an energy
      rule would have used the strengthening. Over a large magnitude it
      costs both strength and proof size.
  - **Assertion levels.** Above `Off`, a task with a variable start and a
    variable length is set aside (see [Variable kinds](#variable-kinds-and-views)).
    In the fact-check's `varlen.cc`, `pack` with task 0's length in `[1, 2]`
    takes 1 node with no proof and at `Off`, and 252 nodes at `Definitions`
    and `Inferences`. Reproduced here. Under the default encoding those
    proofs fail to parse anyway (#1234).
  - The fuzz harness's proofs-on/off comparison would flag a budget-driven
    difference. It found none. Its driver records the derived constraint's
    `% derived cumulative: declined` markers (`driver.py:110`), but not this
    presolver's budget declines, which write nothing to the proof. So it is
    unknown whether any of its instances reached a budget. **#1241.**

## Evidence

### Tests

- **`cumulative_strengthening_presolver`** (`run_test_only.bash`, so VeriPB
  runs inside the binary where `can_run_veripb()`), and
  **`cumulative_strengthening_presolver_recovering`**, the same binary under
  `GCS_CUMULATIVE_ENCODING=both-recovering`. In the second lane every donor row
  is recovered from the start-checkpoints *and* checked against the model's
  row. Its content:
  - arithmetic checks of `kappa` and of the full-task split, before any proof;
  - stats tripwires on every fixture;
  - time-table neutrality on four fixtures;
  - two energy differentials (`pack`, `full_task_pack`) that refute at the
    root only with the presolver;
  - optional, variable-capacity, variable-height, variable-length and
    all-variable-height donors;
  - the view-capacity decline;
  - diagnostics (registration, the levels of notes);
  - both budgets set to zero;
  - an OPB-unchanged check;
  - solution preservation against brute force, proofs off, on 60 random
    instances, extended up to 240 until both halves have fired. Heights are
    drawn against each capacity so that full tasks occur. With `--seed=2` it
    strengthened 18 of 60 and raised 4 heights;
  - a verified sweep of 25 or more instances until some raise happens;
  - four mutation lanes;
  - marker counts with VeriPB;
  - a negative control whose OPB matches a run without the presolver.
  - Seeded (`establish_and_announce_seed`). The random sweeps use
    `get_seed()`, so `--seed=N` reproduces them. One run with `--seed=1`
    takes 2.6 s and 27 MB.
- **`disjunctive_2d_presolver`** runs this presolver on `Disjunctive2D`
  projections (`bars`), and runs `ClaimOneBetter` there.
- **`cumulative_wide_horizon`** checks the *proof* side at a horizon of 10⁵:
  at most 200 rows and flag names.
- **Runtime caps.** The suite-wide caps (`GCS_TEST_MAX_SOLUTIONS`,
  `GCS_TEST_MAX_RECURSIONS`) are set in this lane's environment, but **never
  read**. The test calls `solve_with` directly, not `solve_for_tests`, so no
  cap ever fires and every run is complete in both CI configurations.
- **Mutation lanes:**
  - `ClaimOneBetter` on `pack`, which runs on the knapsack path (it claims 5,
    and `3 · ⌊8/3⌋ ≠ 5`), and `BogusDivisor` on `pack`, on the division path;
  - `RaiseUnentitled` on `r1_control`;
  - `RaiseTooFast` on `knapsack_raise`.
  - Controls verify for `pack` and `knapsack_raise`. `r1_control`'s honest run
    has no derivation to control.
- **Fuzz (this audit).** The scheduling fuzz harness
  (`tmp/optional-donors/fuzz`, copied to
  `tmp/fd-sched/cumulative_strengthening/fuzz` and rebuilt against
  `7e1c4178`) was run with this presolver forced on wherever there is a donor.
  - The other presolvers and rule sets stay random.
  - Each seed is checked by brute force, a reference solve, a proofs-off
    solve, a proofs-on solve, and VeriPB, with a proofs-on/off search
    comparison.
  - 22 workers ran for 1.5 hours, on seeds 500,000 to 503,790: 3,791 seeds,
    **no anomalies**. The proof run of 822 of them carried a strengthening.
  - **What that checked.** VeriPB verified 3,753; 18 timed out, 13 were too
    big to check, and 7 had no proof because the proof run timed out.
    Brute force completed on only 1,171 seeds, 236 of them strengthened, so
    the solution-set check covers those. 224 of the 822 strengthened proof
    runs hit the node cap, so their proofs are partial.

**What the tests do not cover:**
- **Any assertion level above `Off`.** Wherever it installs something, every
  level fails under the default encoding (#1234): a parse error
  over a posted donor, a throw over a `Disjunctive2D` projection.
- **The pass's cost** at any horizon or capacity. No test times it, and no
  audit-lane row posts the presolver.
- **`ClaimOneBetter` on the division path, which cannot be tested.** The
  claim `kappa − 1` is never a multiple of `d` when `d > 1`, since every
  subset sum is, so the corruption always lands on the knapsack path
  (`subset_sum_strengthening.cc:166`). The lanes on `pack` and on
  `bars` in `disjunctive_2d_presolver` both do. Division's tightness rests on
  `BogusDivisor` alone.
- **A budget decline that changes search with proofs on.** The test sets
  budgets to zero, and only checks that the decline happens.
- **The "every task full" or "every task a loner" decline,** which is
  mis-reported, and the set-aside of variable-start, variable-length tasks
  above `Off`.
- **Real instances.** No front end reaches the presolver, so no MiniZinc or
  XCSP3 instance has ever run it.

### Benchmarks and examples

- **None in the repository runs it.** The natural candidate is
  `examples/rcpsp`, which would need a `--strengthen-cumulative` flag beside
  `--infer-cumulative`. With a local patch, generated instances at its
  defaults and nearby rarely give it anything. An unrecorded survey at
  size 12, over capacities 5, 7 and 10 and maximum demands 3, 4, 6 and 8,
  found it firing on at most 3 of 5 seeds per setting. Three of those twelve
  settings (demand above capacity) cannot be built and gave no instances. The
  size-14 sweep (`rcpsp-sweep/size14.tsv`) fired on 2 of 40. Random demands'
  subset sums reach the capacity.
- **For CPU benchmarking:** the pass's own cost is the interesting quantity.
  The `horizon.cc` shape (horizon 10⁶) and the capacity shape (`C ≈ 10⁶`,
  `H = 10⁴`) are the right sizes.
- **For proof verification:** `budget.cc` at scales 1–100 for the knapsack
  path, and `knapsack_raise` scaled for raises. Never uncapped: the `div`
  family at `n = 64` writes a 700 MB proof from the donor alone.

### CPU performance

**The pass.** See [Initialisation](#initialisation-and-global-data): about
1.1 µs and 520 bytes per time point at `n = 3`, and about 0.6 ms per time point
at `C ≈ 10⁶`, `n = 10`.

**The effect on search.** `examples/rcpsp` with a local flag, release build of
`7e1c4178`, fataepyc-08, 2026-10-04, one pinned core, serial, `GLIBC_TUNABLES`
pinned, proofs off, default Cumulative rules (time-tabling, overload, profile
overload). Size 14, capacity 10, max demand 4, seeds 0–39:
- recursions identical on the 39 seeds that finished within 120 s,
  including the 2 where it fired (32 and 57 nodes);
- seed 25 timed out in both arms. The fact-check ran it without a timeout:
  34,927,753 recursions in both arms, 493.8 s and 492.9 s (about 8.2 minutes), nothing
  strengthened;
- wall time within noise on the rest. Most solves are sub-millisecond, and
  the two largest took 8.9 s and 62 s either way.

The energy fixtures show the effect it exists for: on `pack`, 182 → 1 node; on
`full_task_pack`, 39 → 1; on `knapsack_raise` and `two_full`, 5 → 1. That
measures fixtures built to show it, not a benchmark.

**Against other solvers:** not measured. No front end reaches the presolver,
and Gecode, Choco and ACE have no Schulz-style presolve to compare with.

**What this does not exercise.** The generated benchmark reaches the capacity
rewrites only rarely, and the raise never (`tasks_raised` was 0 on both
seeds where it fired).

### Proof performance

**Own against shared.** `own.cc` installs the derived constraint with its rules
off, so it derives its install-time rows and never fires. The search is then
identical to the run without the presolver, and the difference in lines is the
presolver's own. Families of unit tasks with starts in `[0, ⌈n/2⌉ − 1]`, first
solution:

| Family | `n` | lines without | lines with, rules off | own | rows |
|---|---|---|---|---|---|
| `div` (h3, `C = 8`) | 4 | 248 | 254 | 6 | 1 (division) |
| `div` | 16 | 39,228 | 39,234 | 6 | 1 |
| `dp` (h18/17, `C = 50`) | 4 | 248 | 463 | 215 | 1 (knapsack) |
| `dp` | 16 | 39,228 | 40,355 | 1,127 | 1 |
| `raise` (h9 + 4s, `C = 10`) | 4 | 486 | 519 | 33 | 2 (raised, 12 steps) |

The presolver's own share per derived row is 6 lines on the division path,
whatever `n` is. On the knapsack path it grows with the items: 215 lines at
`n = 4` and 1,127 at `n = 16`. Either way it is small against a donor proof
that goes from 248 to 39,228 lines between 4 and 16 tasks. That growth is
`cumulative.md`'s.

`raise` at `n = 16` is the energy differential at scale. Without the presolver,
and with it but its rules off, the solve had not finished after the 120 s
timeout, by which point it had written a 15 GB proof. With its default rules
it refutes at the root: 1 node, 44,522 lines, with 8 raised rows over 64 raise
steps, and VeriPB verifies UNSATISFIABLE.

**With the energy rules on**, the proof is whatever the search becomes. `pack`
goes from 8,405 lines (864 KB) and 0.24 s to check to 2,174 lines (144 KB) and
0.03 s, VeriPB 3.0.2 on the same core.

**At the assertion levels:** not measured. Under the default encoding, every
proof in which it installs something fails to parse (#1234). The
time-indexed arm writes a checkable one, except over a `Disjunctive2D` donor it
would strengthen (`bars`), where it throws under either encoding. The presolver emits no `a` lines of its own and carries
no hint type. A hints-only mode would have to decide what its rows become, and
#1234 leaves that open.

## Status, gaps, and next steps

### Proof-logging gaps

- **Unjustified rewrites:** none. Every row is derived and pinned.
- **Strength changes with proofs on: yes.**
  - Both budgets, `with_dynamic_programming_budget` and `with_raise_budget`,
    apply only with proofs on. A donor strengthened with proofs off can be
    declined with them on (#1241; see
    [Can it weaken the model?](#can-it-weaken-the-model)).
  - Across assertion levels, the variable-length set-aside changes it too:
    252 nodes against 1 on `varlen.cc`.
- **Assertion levels: unparseable wherever it installs something,** under the
  default encoding (#1234, not this presolver's code). Over a
  `Disjunctive2D` projection donor that it would strengthen, the solve throws
  rather than writing a proof at all (also #1234).

### Known limitations

- Not reachable from any front end. A MiniZinc, XCSP3, `.scp` or `gcspy` user
  cannot turn it on.
- A long horizon makes the pass slow and memory-hungry even with proofs off:
  12 s and 5.6 GB at 10⁷ time points. So does a capacity near 10⁶ multiplied
  by a horizon in the thousands.
- With proofs on, a donor whose capacity is large, or whose tasks have wide
  windows, can be passed over ("skipped … because a size limit was
  reached"), and search may then be weaker than without proofs.
- Raised heights cost proof lines in proportion to the capacity.
- "Every task full" (a disjunctive) and "every task a loner" are reported as
  nothing to gain, and loners make it decline outright where plain subset-sum
  would strengthen.
- With a `Disjunctive2D` in the model that it would strengthen, and an
  assertion level above `Off` (for example `GCS_ASSERTION_LEVEL=inferences`),
  the solve aborts with "the donor has no capacity row at time 0"
  (#1234).
- At an assertion level above `Off`, a task with both a variable start and a
  variable length is set aside. The donor is strengthened over the rest, so
  search can be weaker than at `Off`: 252 nodes against 1 on `varlen.cc`.
  Under the default encoding every such proof is unparseable anyway.
- No `with_makespan` (#702).

### Next steps

1. **Assess per stretch, not per time point (#1240).** Collect the `2n`
   window edges, and run the subset sum once per stretch where the set of
   present tasks changes. Store a stretch map rather than a `TimePoint` per `t`,
   and do not build `by_time` with proofs off. Scan the bitset downward a word
   at a time. That is perhaps a day, and it buys the presolver at any horizon:
   10⁶ points become about `2n` assessments. The recipe contract (#1130)
   already guarantees the answers are per stretch.
2. **Budget something closer to what will be derived (#1241).**
   - **The constraint.** A recipe may decline only at install
     (`derived_cumulative.hh:150–166`), and a later decline throws. So a
     budget cannot cost cited points "as they come". Any budget is decided at
     install, over every row search *might* cite.
   - **The current sum is a true bound.** Summing per non-empty time point is
     a true upper bound on that, and a loose one. Summing per stretch bounds
     only the install-time rows, and gives up the bound on rows cited during
     search, which can be up to one per hull point.
   - **Computing the same bound more cheaply:** per stretch, cost one row and
     multiply by the stretch's length. Every row in a stretch has the same
     present set, so they are the same size. That gives exactly today's
     figure without walking the stretch, which belongs with #1240. It
     keeps the bound, and it keeps the looseness.
   - **Tightening the bound** needs a different decision, not a different
     sum, and it is Ciaran's call. One option is a per-stretch budget,
     documented as bounding only install. The other is to keep the
     per-point bound and fix only the magnitude part below. That removes the
     measured case where the budget makes the proof bigger. Over a long
     horizon a decline then still costs strength wherever an energy rule
     would have used the strengthening.
   - The knapsack prediction should count reachable states per layer, not
     `C + 1`.
   - The assessment keeps only the final layer's bitset and then discards it,
     so the count needs either a per-layer popcount while the bitset is built,
     or a separate pass.
   - That is small, and it removes the proofs-on/off divergence on scaled and
     on long-horizon instances.
   - Alternatively apply the budgets with proofs off too, so that proofs never
     change search. Ciaran's standing rule ("never weaken a propagator for
     proof size") argues for the first.
3. **Raise by proof by contradiction (#1242).** One `red … : : subproof`
   per raised task per row:
   - add the row `W ≤ kappa` to the negated goal and saturate, giving
     `a_i ≥ 1`;
   - then `rup >= 1`, because the at-most-ones set every other flag to zero.
   - That is three rule steps (six lines of text) whatever `kappa` is,
     against up to `kappa` `pol`s. It makes the raise budget unnecessary.
   - Checked by hand on VeriPB 3.0.2 (`tmp/fd-sched/cumulative_strengthening/pbc`):
     `kappa = 8`, rest `4 + 4 + 4`. There the loop takes six steps
     (`raise_steps(12, 8)` is `[2, 2, 1, 1, 1, 1]`), and the fixture
     `{5, 4, 4, 4}` under 8 emits 12 over 2 rows. Claiming 9 is rejected.
   - The fact-check confirmed the derivation is valid in general.
4. **Fix #1234 (owned by `cumulative.md`),** then add an
   assertion-level lane to this test.
5. **Report the all-full and all-loner declines truthfully,** and decide
   whether a loner is an ordinary task. Small; the code already flags it.
   Fix the stale comment at `cumulative_strengthening.cc:789–793`.
6. **A `--strengthen-cumulative` flag on `examples/rcpsp`,** and a front-end
   switch per the propagator-or-decomposition convention. Small, and it buys
   real instances. An RCPSP instance set with tight, structured demands would
   be the benchmark that reaches it.
7. **`with_makespan` (#702).**
8. **A large-domain audit row** that posts the presolver with a wide start and
   a capacity near the limit, timing the pass. It would have caught #1240.

## Prior art

- **Propagation side:** Schulz's pre-solving strengthenings of the cumulative
  capacity and of coefficients (gcd rounding, knapsack capacity reduction,
  coefficient raising), as recapped by Cloutier and Quimper (CP 2026, §2.3).
  The pairwise, window-aware form of the full-task test is ours, and slightly
  stronger.
- **Proof side:**
  - Chvátal–Gomory rounding for the division path is textbook cutting planes.
  - The layered subset-sum programme is the solver's own
    ([`subset-sum-strengthening.md`](../subset-sum-strengthening.md)).
  - The raise loop and its step bound are ours (design note).
  - We know of no prior certification of a cumulative *presolve*. What is new
    is posting the strengthening as a derived constraint whose rows are proved
    from the donor's, leaving the model untouched.

## Further reading

- [`cumulative-strengthening.md`](../cumulative-strengthening.md): the design
  note.
  - The rules and why `kappa` is a maximum.
  - The neutrality theorem, and why the derived constraints ship without
    time-tabling.
  - The raise arithmetic and its two degenerate ends.
  - The fixtures, and why `{6, 10, 15}` cannot be one.
  - The restrictions, and the convert-or-set-aside judgement.
  - Still accurate at `7e1c4178` except in three places, all outside this
    stack:
    - the wording noted under raise-a-full-task's Tightness;
    - "node-for-node identical", where the test compares solution sets and
      recursion counts;
    - "a variable length is not set aside at all", which is false above
      `Off`, where a variable-start, variable-length task is set aside. Its
      list of set-aside tasks is incomplete for the same reason.
- [`subset-sum-strengthening.md`](../subset-sum-strengthening.md): the two
  derivations and their tests.
- [`cumulative-proof-logging.md`](../cumulative-proof-logging.md): derived
  Cumulatives, the donor view and lazy rows (#1130).
- [`cumulative.md`](../constraints/cumulative.md): the installed propagator,
  the derived machinery's declines, the makespan rule, and #1234.

## Developer commentary

None.
