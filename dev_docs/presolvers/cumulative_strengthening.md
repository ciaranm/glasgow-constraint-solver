# `cumulative_strengthening`: tighten each `Cumulative` by integrality, as a derived constraint

> **Maturity** experimental: C++ API only, off unless added ·
> **Audited** 2026-10-04 at `7e1c4178`; re-audited 2026-10-08 at `0a5b4ec6`
> for #1240, #1241 and #1242 ·
> **Open issues** filed by this audit: none left open. **Fixed since the
> audit**: #1240 (the pass was `O(horizon)`), #1241 (proof-only budgets) and
> #1242 (raise by contradiction); see [Re-audit,
> 2026-10-08](#re-audit-2026-10-08). Already open and touching this
> presolver: #702 (no `with_makespan`). Shared with the other
> derived-Cumulative presolvers and owned by
> [`cumulative.md`](../constraints/cumulative.md): above `Off`, a proof in
> which it installs something is rejected under the default encoding, and
> over a `Disjunctive2D` donor it would strengthen the solve throws (#1234).
> Tracked under #871 and #976.

### Re-audit, 2026-10-08

All three of the audit's issues were fixed on 2026-10-08. This pass brings the
text into line with them at `0a5b4ec6`.

| Issue | Fixed by | What changed here |
|---|---|---|
| #1240, the pass walks every time point of the hull | #1281 | the assessment runs once per stretch between window edges, at most `2n − 1` of them, and reads the largest reachable sum a word at a time; the recipe looks its stretch up in a shared map. The five things to know, [Semantics](#semantics) step 3, [Proof-time state](#proof-time-state), [Initialisation](#initialisation-and-global-data) and its tables, [Interior values](#interior-values-and-optional-pruning), [Robustness](#robustness-and-limits), [Interval efficiency](#interval-efficiency), [CPU performance](#cpu-performance), next steps 1 and 8 |
| #1242, a raise costs lines linear in `kappa` | #1280 | a raise the rest of the row overshoots is one `red` whose subproof is a `pol` and a `rup >= 1`, per raised task per row. `with_raise_budget`, `declined_over_raise_budget` and the step helpers (`for_each_raise_step`, `raise_steps`, `raise_step_count`) are gone. `RaiseTooFast` now claims `kappa + 1` and is rejected at that closing RUP. The five things to know, [raise-a-full-task](#rewrite-raise-a-full-task), the stats table, [Proof performance](#proof-performance), next step 3 |
| #1241, budgets that apply only with proofs on | #1286, **by removing the budget**, none of the ways next step 2 listed | there is no proof budget, so at `Off` proofs on and off strengthen the same donors and search the same tree. `with_dynamic_programming_budget` and `declined_over_budget` are gone, and `with_subset_sum_capacity_limit` is the one size limit. The price is a derivation of any size: #1286's 767,000-line example. [Options](#options), [Detection](#detection-and-its-failure-modes), [Can it weaken the model?](#can-it-weaken-the-model), [Tests](#tests), [Proof-logging gaps](#proof-logging-gaps), next step 2 |

**Also changed here by a fix elsewhere**: #1290 (#1254) recovers a donor's
capacity row from the row before it by a chain step. Two things here moved
with it. Above `Off`, a proof in which this presolver installs something is
now rejected at `Definitions` and `Links` at a recovery `rup`, where it
failed to parse at `7e1c4178` ([At assertion levels above
`Off`](#proof-time-state)); #1234 is still open and still the cause. And the
recovery of the row a derived constraint cites is now most of the
presolver's own proof cost on the [Proof performance](#proof-performance)
families.

**Fixed after `0a5b4ec6`.** #1265 (docs and comments only, merged at
`86caad24`) rewrote the stale comment at `cumulative_strengthening.cc:686–690`
and the design note's three inaccuracies this document reported. Those
passages describe `0a5b4ec6` and say that #1265 changed them after
`0a5b4ec6`; the audit stays at `0a5b4ec6`.

Nothing about which rows are derived, the division or knapsack derivations or
the neutrality argument changed. Code citations are refreshed to `0a5b4ec6`
where they had moved, including the ones outside the presolver
(`disjunctive_2d.cc`, `difference_graph.cc`, `cumulative.cc`).

**What was measured again**, at `0a5b4ec6` on fataepyc-10, serially on one
pinned core, with `GLIBC_TUNABLES` mmap threshold 32 MiB and trim threshold
4 GiB (the audit used 4 GiB for both): the horizon, task-count and capacity
tables under [Initialisation](#initialisation-and-global-data), the
fixtures' stats table, `budget.cc` at four scales, the two long-horizon
probes, `knapsack_raise` scaled ×1 to ×1,000, the mutation lanes' rejection
points, the energy fixtures and the [Proof performance](#proof-performance)
table, the assertion-level table (all but the time-indexed arm of its
nothing-installed row), the `range.cc` edges (unchanged), and one run of the
test binary with each of `--seed=1` and `--seed=2`. **Not re-run**:
`varlen.cc`, the `rcpsp` sweep and the fuzz campaign. They stay at
`7e1c4178`, labelled as such where they appear. #1286's own price figures are
quoted as its.

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
- **Its own pass is per stretch, not per time point (#1240, fixed by
  #1281).**
  - It assesses each stretch between window edges once: at most `2n − 1`
    stretches, each an `O(n)` scan and a capacity-sized subset sum. Every
    answer depends on the time point only through which tasks can run then,
    which is what the derived constraint's row contract already says.
  - Measured at a horizon of 10⁶: 0.05 s and 51 MB, against 0.04 s and 43 MB
    for the donor alone. At 10⁷ it is 1.5 s and 393 MB, against 0.8 s and
    317 MB. What is left is horizon-sized, but #1281's profile puts it in
    the two `Cumulative` propagators' per-call vectors, the donor's and the
    derived constraint's, not in the presolver.
  - Before #1281 it walked every integer of the window hull, with proofs off
    too: 1.1 s and 567 MB at 10⁶, and 12 s and 5.6 GB at 10⁷, at `7e1c4178`.
- **With proofs on at `Off` it strengthens and searches exactly as with
  proofs off (#1241, fixed by #1286).** There is no proof budget. The subset-sum
  capacity limit is the one size limit, and it is decided without asking
  whether a proof is being written. Above `Off` it can still do less, for a
  reason that is not a budget: a task with a variable start and a variable
  length is set aside (see [Can it weaken the
  model?](#can-it-weaken-the-model)).
  - Before #1286, two budgets declined donors only when a logger was present.
    Each summed a prediction over every non-empty point of the window hull,
    and the dynamic-programming one charged `items × (C + 1)` states per
    point, so it grew with the capacity's magnitude. At `7e1c4178` a
    seven-task fixture scaled ×20 was declined, and the proofs-on search took
    182 nodes and 8,405 lines where the proofs-off one refuted at the root.
  - At `0a5b4ec6` that fixture is strengthened at every scale from ×1 to
    ×100, refutes at the root, and its proof is 2,212 lines however it is
    scaled. Its three knapsack derivations are still about 427 lines each.
  - **The price is that a proof can be large.** #1286's body measured
    sixteen unit tasks with unstructured heights in `[1000, 60000]` under a
    capacity of 213,259: a 767,000-line (155 MB) derivation that took VeriPB
    419 s and 1.1 GB, where the old budget's decline wrote 14,000 lines.
- **A raise is one rule step whatever the capacity (#1242, fixed by
  #1280).** Where the rest of the row overshoots `kappa`, each raised task
  gets one `red` whose subproof is a `pol` and a `rup >= 1` (six lines of
  text), after its at-most-ones. `knapsack_raise` emits one raise line per
  raised row at every scale from ×1 to ×1,000. Before #1280 it was a loop of
  `pol` steps, up to one per unit of `kappa`: 20, 200 and 2,000 steps at ×1,
  ×10 and ×100.
- **Above `AssertionLevel::Off`, a proof in which it installs something is
  rejected, under the default encoding.** At `Inferences` and `Backtracking`
  it fails to parse. At `Definitions` and `Links`, since #1290's chain
  recovery, it parses and is rejected at a recovery `rup`.
  - The cause is owned by [`cumulative.md`](../constraints/cumulative.md)
    (#1234). The donor's start-checkpoint flag
    definitions are emitted only at `Off`, but the recovery of a derived row
    cites them.
  - Confirmed for this presolver on the `r1`, `pack`, `two_full` and
    `knapsack_raise` fixtures at all four levels, at `7e1c4178` and again at
    `0a5b4ec6`. Separately, at `Links` every proof of a satisfiable model is
    rejected at its first `solx` (#1210).
  - **Where it does not happen:**
    - A donor it strengthens nothing on (`nothing_to_gain`, `all_full`) gives a
      proof that verifies under assertions, but for a satisfiable model at
      `Links` (#1210).
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
the neutrality theorem, and the raise, by contradiction since #1242 and in
cutting planes before it. This document is the
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
   - The window edges, `lo` and `hi + 1` of each usable task's window
     `[lo, hi]`, are sorted and deduplicated, and each **stretch** between
     consecutive edges
     is assessed once (`cumulative_strengthening.cc:277–306`). A stretch
     where no task can run is skipped. `kappa_t` is the largest subset sum
     at most `C` of the non-full heights whose windows contain the stretch,
     so it is the same for every `t` in it. Before #1281 this was done for
     every integer `t` in the hull.
   - `kappa` is the maximum of the `kappa_t`. A donor where every task is
     full gets `kappa = 0`, and is declined.
   - A donor whose `kappa` equals `C` and which raises no height is declined
     as "nothing to gain".
4. **Choose between converting and setting aside.** If any height was
   converted, the donor is assessed again with those tasks set aside. The
   set-aside version wins when it gives a strictly smaller `kappa`, or when
   the converted one had nothing to gain.
5. **No budget step.** This was a proofs-on-only budget on the predicted
   dynamic-programming states (20,000) and raise steps (5,000). #1280 removed
   the raise budget and #1286 the other, so the step is deleted, not
   renumbered. Since #1286 nothing between assessment and install asks about
   the logger at all, as the comment at `cumulative_strengthening.cc:159–168`
   records. The pass does still consult it in two places, and both change
   what is strengthened only above `Off`: the donor view (`:139`) sets a
   variable-start, variable-length task aside (`donor_view.cc:215`), and an
   install decline is passed over rather than thrown (`:691–692`). The view
   also consults it at `Off`, with no effect on the strengthening: an encoded
   task that can never run (length or height fallen to zero, or never
   present) is put in `set_aside` when a logger is present and skipped
   without one (`donor_view.cc:185–188`). It is unusable either way, so
   `kappa` and the search are the same, and only
   `donors_with_set_aside_tasks` can differ.
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

[^fe]: Checked by grep at `7e1c4178`, and again at `0a5b4ec6`. The only
callers are its own test, `disjunctive_2d_presolver_test.cc` and
`cumulative_wide_horizon_test.cc`.
`fzn-glasgow` and the XCSP3 solver add `DifferenceLogic` only.
`examples/rcpsp` adds `DifferenceLogic`, `InferredDisjunctive` and
`InferredCumulative`. The audit's measurements on `rcpsp` used a local
one-flag patch (`tmp/fd-sched/cumulative_strengthening/src-rcpsp`, never
committed).

The donors it reads:

| Donor | Read as |
|---|---|
| `Cumulative` (any of its three constructors) | `cumulative_donor_view`: per-task reduction, as above |
| `Disjunctive2D`, each axis | the projection `Disjunctive2D` resolves in `prepare()` and publishes from `install_propagators` (`disjunctive_2d.cc:656`, `:705`): every length, height and the capacity already constants (`PublishedCumulativeDonor`); variable sizes enter at their declared floors |
| `Disjunctive` | not read. A unary resource has nothing to subset-sum |
| a resource written as linear inequalities | not read |

### Options

None of them changes the OPB, and none of them changes what the derived
constraint *says*. Each one decides only whether a donor is strengthened, and
which rules the result runs.

- **`with_subset_sum_capacity_limit(capacity)`**, default 10⁶. A donor whose
  capacity exceeds it is declined before assessment, with proofs on or off.
  It is the only size limit. It bounds the assessment of each stretch, since
  the bitset has `C` bits, and since #1281 there are at most `2n − 1`
  stretches, so it bounds the whole pass too. It does not bound the proof: a
  knapsack derivation is three flags per reachable partial sum per item, at
  every row a firing cites.
- **Removed:** `with_dynamic_programming_budget(states)` (default 20,000) and
  `with_raise_budget(lines)` (default 5,000). Both applied only with proofs
  on. #1280 removed the raise budget and #1286 the other (#1241); see [Can it
  weaken the model?](#can-it-weaken-the-model).
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
    knapsack overload (KAOC, `cumulative.cc:3105`). #1281 changed how
    `largest_subset_sum_at_most` reads its answer off the bitset, a word at a
    time from the top (`subset_sum_strengthening.cc:116–119`), not what it
    returns, so KAOC's derivations are as before.
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
      (`difference_graph.cc:1261–1283`, with root simplification at `:361`)
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
  - the raises: one line per raised task per row, a `red` with a two-step
    subproof where the rest of the row overshoots `kappa` (#1280).
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
  The recipe holds a `shared_ptr` to the assessment's stretches, `by_start`,
  a map keyed by where each stretch starts, and finds the stretch holding the
  `t` it is asked for with `upper_bound` (`cumulative_strengthening.cc:379–382`,
  `:409–411`). Before #1281 it captured a copy of a map with one entry per
  time point (`by_time`).

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
  the proof is nevertheless rejected at every level above `Off`. The recovery
  of the donor's row cites flag definitions the donor emits only at `Off`.
  That defect is owned by [`cumulative.md`](../constraints/cumulative.md)
  (#1234).
  - At `Inferences` and `Backtracking` the proof fails to parse.
  - At `Definitions` and `Links` it parses, and is rejected at the row
    recovery's first `rup`, `~cact ∨ cb` (`r1`, line 23 at `Definitions`),
    which the omitted definitions leave unimplied. That is #1290's chain
    recovery; at `7e1c4178` these two levels failed to parse too.
- **At `Links`**, without the presolver or with nothing installed, a
  satisfiable model is rejected at its first `solx` (#1210; `r1`,
  `nothing_to_gain`), while the unsatisfiable `pack` verifies.

Evidence from this audit (`fixtures.cc`) and the cross-document re-check
(`tmp/fd-sched/factcheck/crossdoc2/fx`, `d2`, and `crossdoc3/fx` for the
`Links` and nothing-installed rows), re-run at `0a5b4ec6` for every row but
the time-indexed arm of the nothing-installed one:

| Fixture | `Off` | `Definitions` | `Links` | `Inferences` | `Backtracking` |
|---|---|---|---|---|---|
| `r1`, without the presolver | verified | under assertions | rejected (#1210) | under assertions | under assertions |
| `r1`, `pack`, `two_full`, `knapsack_raise`, with it | verified | rejected at a recovery `rup` (parse error at `7e1c4178`) | rejected at a recovery `rup` (parse error at `7e1c4178`) | parse error | parse error |
| the same four, with it, `GCS_CUMULATIVE_ENCODING=time-indexed` | verified | under assertions | `r1` rejected (#1210); the other three under assertions | under assertions | under assertions |
| `nothing_to_gain`, `all_full`, with it (nothing installed), either encoding | verified | verified (`nothing_to_gain`: nothing asserted) / under assertions (`all_full`) | `nothing_to_gain` rejected (#1210); `all_full` under assertions | under assertions | under assertions |
| `bars` (a `Disjunctive2D` projection donor, strengthened), either encoding | verified (816 solutions) | **throws** | **throws** | **throws** | **throws** |
| `strip` (a `Disjunctive2D` projection donor, nothing posted), either encoding | verified (48 solutions) | under assertions | rejected (#1210) | under assertions | under assertions |

The parse error is `The label @v[_1][0_0][ca][r] is not assigned to a
constraint ID`. `InferredCumulative` gives the same errors on all four
fixtures. `InferredDisjunctive` gives them on `two_full` and
`knapsack_raise`. On `r1` and `pack` its proofs are accepted, because it
installs nothing there: at `Off` it writes no presolve comment on either,
against 8 on `two_full` and 6 on `knapsack_raise`.

The `bars` row comes from the fact-check's corrected probe, which maps `Links`
correctly. The copy in this audit's `bars-assert/` ran its `links` case at
`Backtracking`.

## The implementation

### Initialisation and global data

The pass itself is the whole of the root cost. There is no initialiser of its
own.
- **Per donor:** the view; then an `O(n²)` pairwise full-task test; then
  the `2n` window edges, sorted (`cumulative_strengthening.cc:277–283`); then,
  for each of the at most `2n − 1` stretches between them (`:285–306`):
  - an `O(n)` scan to collect the tasks;
  - `largest_subset_sum_at_most` over a fresh `C`-bit bitset,
    `O(|items| · C / 64)` words;
  - a downward scan **a word at a time** from the top word for the highest
    set bit, `O(C / 64)` at worst (`subset_sum_strengthening.cc:116–119`).
    Before #1281 this scan was per value, `O(C − kappa_t)`, and it ran at
    every time point.
- **Retained:** a `TimePoint` per non-empty stretch, holding its bounds and
  three vectors. They are moved into a `std::map` keyed by each stretch's
  start, which the recipe shares through a `shared_ptr` rather than copying
  (`:379–382`). It is built with proofs off too, where nothing reads it, but
  it has at most `2n − 1` entries. Before #1281 there was an entry per time
  point, and the recipe copied the map, so the peak held two maps.
- **Repeated work:** with a converted height the assessment runs twice.

Measured, with proofs off. The probe is `horizon.cc`: three tasks, length 2,
height 2, capacity 5 → `kappa = 4`, starts in `[0, H]`, stopped at the first
solution. Release build at `0a5b4ec6`, fataepyc-10, 2026-10-08, one pinned
core, serial, `GLIBC_TUNABLES` mmap threshold 32 MiB and trim threshold
4 GiB:

| `H` | donor alone: `instructions:u` / s / peak RSS | with presolver: `instructions:u` / s / peak RSS | with presolver at `7e1c4178`: s / peak RSS |
|---|---|---|---|
| 10⁴ | 2.9 M / < 0.01 / 4.7 MB | 3.6 M / < 0.01 / 4.7 MB | 0.010 / 9.3 MB |
| 10⁵ | 8.6 M / < 0.01 / 7.8 MB | 14.9 M / < 0.01 / 9.3 MB | 0.10 / 60 MB |
| 10⁶ | 65 M / 0.04 / 43 MB | 128 M / 0.05 / 51 MB | 1.10 / 567 MB |
| 10⁷ | 635 M / 0.81 / 317 MB | 1,259 M / 1.5 / 393 MB | 12.1 / 5.6 GB |
| 10⁸ | not counted / 8.2 / 3.1 GB | not counted / 15.6 / 3.9 GB | not run |

The windows here all coincide, so there is one stretch, and what the
presolver adds is no longer the pass. It still roughly doubles the
horizon-sized cost, and #1281's profile at 10⁷ attributes that to the two
`Cumulative` propagators' per-call horizon-sized vectors, the donor's and the
derived constraint's. The `7e1c4178` column was taken with both
`GLIBC_TUNABLES` thresholds at 4 GiB, and its donor column read 0.34 s and
395 MB at 10⁷, so compare wall times within a column, not across.

With proofs on at 10⁶ it is the same (0.06 s, 51 MB), and one capacity row is
derived (a 133-line proof). The proof side is lazy (#1130), and since #1281
the assessment is too.

**The donor's own horizon cost is `cumulative.md`'s.** At 10⁸ the donor alone
peaks at 3,129,716 KiB here, about 32 bytes per time point (3,129,716 ×
1,024 / 10⁸). The table writes it as 3.1 GB, counting 1,000 KiB to the MB as
the audit did; the audit's 39 bytes per point at `7e1c4178` was read off its
table that way (3.9 GB / 10⁸), and is about 40 in bytes. At `7e1c4178` it hit
`bad_alloc` at 10⁹ under a 16 GB `ulimit -v`; that was not re-run.

**The task-count and capacity axes**, same build and machine, `instructions:u`
donor alone → with presolver:
- **Task count:** at `H = 10⁵`, `n = 3 / 10 / 30` go 8.6 → 14.9 M, 21 → 40 M
  and 62 → 120 M (under 0.02 s each). At `7e1c4178` they took
  0.10 / 0.14 / 0.22 s with the presolver.
- **Capacity:** `n = 10`, `C = 999,999`, heights 2, so `kappa = 20`.
  - `H = 10³`: 2.6 → 4.9 M, under a millisecond. `H = 10⁴`: 3.9 → 7.3 M.
    At `7e1c4178` these took 0.59 s and 5.9 s, about 0.6 ms per time point,
    most of it the per-value scan.
  - That is one stretch. With the starts staggered (`STAGGER=1`, start `i`
    in `[3i, H + 3i]`), there are 19 stretches, and `H = 10³` goes 2.8 →
    23.9 M: about a million instructions per stretch at this capacity,
    whatever the horizon (`H = 10⁶`: 140 → 298 M, against 140 → 279 M
    unstaggered).

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

**The recipe:** it holds immutable captures (`by_start`, the stretch map
shared through a `shared_ptr`, `cumulative_strengthening.cc:379–382` and
`:406`; the view; the heights; `kappa`), plus a `shared_ptr` to the stats
block. Before #1281 it captured a copy of the per-time-point map `by_time`.
During search it bumps `rows_by_division`, `rows_by_dynamic_programming`,
`rows_with_a_raise` and `raise_lines_emitted` as rows are cited, so those
counters grow during the solve. That is by design (#1130), but a reader comparing two runs' stats must
compare at the end of the solve.

The installed propagator's state is `cumulative.md`'s.

### Interior values and optional pruning

**What this presolver offers.** None. It installs no optional-interior-pruning
pair.

**What it observes.** Its whole vocabulary is bounds.
- **The pass** reads a start's bounds, a length's upper bound, a height's lower
  bound and a capacity's upper bound. A hole changes none of its answers. A
  start with domain `{0, 10⁶}` gets the window `[0, 10⁶ + l − 1]`, which is
  sound. Since #1281 a wide window costs the pass nothing extra, since it adds
  two edges whatever its width; before it, that window cost a million
  assessment points (#1240).
- **The installed propagator** triggers `on_bounds` and `on_instantiated` only,
  so it declares no hole sensitivity. It neither keeps alive nor suppresses
  anyone else's interior pruning. That is honest: its rules read only window
  bounds and presences. `choose_optional_interior_pruning()` runs after the
  last presolver, so the derived propagator's declaration is counted.

### Robustness and limits

- **Unbounded domains.** Since #1281 the pass costs a wide start domain two
  window edges, whatever its width. What stays horizon-sized is the donor's
  and the derived constraint's propagators (see
  [Initialisation](#initialisation-and-global-data)); at `7e1c4178` the donor
  alone hit `bad_alloc` from 10⁹, which was not re-run. Before #1281 the pass
  walked the hull point by point (#1240). Capacity is capped at 10⁶ before
  any work.
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
  - There is no budget prediction to overflow any more (#1286). Before #1281
    it was a `long long` summed over every time point.
  - The raise multiplies nothing since #1280. Its arithmetic is the running
    total of a row's coefficients (`cumulative_strengthening.cc:597–598`),
    each at most `C`, so at most `n · 10⁶` at the limit. The cutting-planes
    loop it replaced reached `e · weight ≤ C²`.
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
    `cumulative_strengthening.cc:417`. The message is `unexpected problem:
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
  - It is the same root cause as the rejected proofs on posted donors: the
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

The pass is a whole-model scan, which is the shape the presolver variant warns
about. Since #1281 it is a scan over the tasks' window edges, not over the
horizon.

1. **The propagation side (the pass).**
   - **The horizon.** The assessment sorts the `2n` window edges and visits
     each stretch between consecutive edges once
     (`cumulative_strengthening.cc:277–306`). Every value it computes at `t`
     depends only on the set of tasks whose windows contain `t`, and that set
     changes only at an edge, so this is exact, not an approximation. It is
     the same structure the derived constraint's recipe contract relies on
     (#1130). Before #1281 the loop was
     `for (Integer t = global_lo; t <= global_hi; ++t)` over every integer
     in the hull (#1240).
   - **The capacity.** `largest_subset_sum_at_most` builds a `C`-bit set
     word-parallel, then finds the highest set bit a word at a time from the
     top (`subset_sum_strengthening.cc:116–119`). Building the set is
     `O(|items| · C / 64)` per stretch, bounded by the 10⁶ limit; there is no
     per-value scan left. Before #1281 the read-off scanned downward from `C`
     one value at a time.
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
   - **Raise:** one line per raised task per row, whatever `kappa` is
     (#1280), plus the pairwise at-most-ones, which are bounded by the tasks
     present. `knapsack_raise` ×1/×10/×100/×1,000 emits 5 raise lines over
     5 rows each time, and a 1,492-line proof. Before #1280 it was up to one
     `pol` per unit of `kappa` per raised task per row: 20/200/2,000 steps at
     ×1/×10/×100 (#1242).
4. **The audit lane.** No row in `gcs/large_domain_audit_test.cc` posts this
   presolver. `cumulative_wide_horizon_test` checks the *proof* side over a
   horizon of 10⁵ (names and rows), but not the pass's cost. The width of a
   start domain and the magnitude of the capacity are both unvaried. #1281
   added no row: its body notes that one would not reach the presolver,
   because `Cumulative` is a `KnownTrip` there
   (`large_domain_audit_test.cc:761`) and trips in its own `prepare` first.
   [Next steps](#next-steps) item 8 records that.

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
  (`cumulative_strengthening_test.cc:654–663`), and the design note's
  "node-for-node identical" claimed more than that at `0a5b4ec6`. #1265,
  merged after `0a5b4ec6`, changed it to "the same solutions in the same
  number of recursions".
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
  `pack`, the `ia` pin rejects it ("not syntactically implied", line 235 at
  `0a5b4ec6`),
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
  seven tasks, at ×1, ×5, ×20 and ×100, re-measured at `0a5b4ec6`. In
  `own.cc` (`dp` family) the derivation is 215 lines at `n = 4` and 1,127 at
  `n = 16` for one row. Nothing caps it since #1286 (#1241): the old budget's
  prediction grew with `C` and with the horizon, not with this.
- **Tightness** — `ClaimOneBetter` on `pack` lands here, as above. VeriPB
  rejects it inside the programme, at `rup 1 ~f[231][sseq_7_6] 1 f[232][ssunder] >= 1;`
  (line 495 at `0a5b4ec6`). `disjunctive_2d_presolver_test`'s `ClaimOneBetter` on the
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
  (`cumulative_strengthening.cc:704`, which also counts a full task already at
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
     - **`T > kappa`**: since #1280, one `red` of the goal
       `kappa · a_i + Σ w_k · a_k ≤ kappa` with an empty witness, after the
       task's at-most-ones (`cumulative_strengthening.cc:628–661`). Its
       subproof adds the row so far to the negated goal and saturates, which
       leaves `a_i ≥ 1`, then closes with `rup >= 1`: `a_i = 1` sets every
       `a_k` to zero through the at-most-ones, and the negation reads
       `kappa ≥ kappa + 1`. #1280's body records a Fable consult that
       checked it against VeriPB 3.0.2's source, including that the `pol` is
       load-bearing.
   - Then the closing `ia`. The arithmetic is in the design note.
   - **Before #1280** the `T > kappa` path was a loop of `pol`s, each taking
     `λ` copies of the row plus `e · w_k` times each at-most-one, divided by
     `λ + e`, raising `i`'s coefficient by `k` with `k · (T − R) < T − c`.
     The audit re-derived that step condition independently, and found the
     code's `ceil((T − c)/(T − kappa)) − 1` to be the largest such `k`.
- **Neutral?** — yes. The derived profile at a full task's compulsory part is
  `kappa`, which pushes out exactly what the donor's `h_i + h_j > C` pushes
  out (design note). Asserted on `r1` and `knapsack_raise`.
- **Proof size** — at-most-ones `O(|F_t| · |N_t| + |F_t|²)` per row, and one
  raise line per full task per row whatever `kappa` is (#1280): a `red` with
  a `pol` and a `rup` inside, six lines of text, where the rest overshoots.
  `raise_lines_emitted` counts that line on all three paths
  (`cumulative_strengthening.cc:607`, `:618`, `:660`). Measured at
  `0a5b4ec6`: `knapsack_raise` emits 5 over 5 rows, `two_full` 10 over 5,
  `full_task_pack` 3 over 3, and `knapsack_raise` scaled ×10, ×100 and
  ×1,000 still 5. **Before #1280** the loop took from 1 step, when
  `T − kappa = 1`, up to `kappa`, when the rest of the row totals at least
  `2·kappa`, and was linear in `kappa` between: 20, 35 and 18 steps on those
  three fixtures at `7e1c4178`, and 200 and 2,000 for `knapsack_raise` at ×10
  and ×100 (#1242). At `0a5b4ec6` the design note's "overshoots by half",
  which the audit found ambiguous, described only that loop. #1265, merged
  after `0a5b4ec6`, replaced it there with "overshoots by at least the right
  hand side itself — `T ≥ 2·R`". The matching code comment at
  `cumulative_strengthening.cc:629–633` still says "once the rest overshoots
  by half", after #1265 too.
- **Tightness** — two lanes:
  - `RaiseTooFast` on `knapsack_raise`. Since #1280 it claims the raised
    coefficient at `kappa + 1` inside the `red`. With the task on and every
    other task off the negated claim still holds, so VeriPB rejects the
    subproof's closing `rup >= 1` (line 727 at `0a5b4ec6`). Before #1280 it
    took one loop step past the bound and was rejected at the row's `ia`.
  - `RaiseUnentitled` on `r1_control`, which raises a task that misses the
    pairwise test by one.
    - Its at-most-one comes out weaker than claimed, and the row's `ia` pin
      is where VeriPB stops (line 72 at `0a5b4ec6`).
    - The derived constraint is genuinely unsound there: with that mutation
      the solve reports 10 of the 24 solutions.
    - At `0a5b4ec6` the design note says VeriPB rejects it "only because the
      conclusion is false". That is right about the cause, but the line that
      fails is the pin. #1265, merged after `0a5b4ec6`, rewrote that
      paragraph to name the failing step.
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
| `declined_nothing_to_gain` | `kappa = C` and no height moves | Detailed note |

None of these depends on whether a proof is being written. The capacity limit
is the only decline that raises the `Important` note
(`cumulative_strengthening.cc:713–717`). Two rows are **deleted**:
`declined_over_budget` (#1286) and `declined_over_raise_budget` (#1280), the
proofs-on-only budget declines, which each also raised the `Important` note.

A decline that is **mis-reported**, and a comment that is stale:

- **"Every task is full" and "every task is a loner" are counted as
  `declined_nothing_to_gain`.** The note reads "its capacity is already the
  largest load its tasks can reach, and no height moved either", which is
  false for both. Checked on `all_full` (`{7, 7, 7}` under 8) and `loners`.
  The design note calls the first case a disjunctive, but nothing here counts
  it as one.
- **A stale comment, not a decline** (at `0a5b4ec6`; fixed by #1265 after
  `0a5b4ec6`). The comment after `install_derived_cumulative`
  (`cumulative_strengthening.cc:686–690`) says that above `Off`, a task with
  both a variable start and a variable length makes the install decline. It
  does not: `cumulative_donor_view` sets such a task aside first, and the
  donor is strengthened over the rest (`donors_with_set_aside_tasks`).
  #1265 rewrote the comment: a decline above `Off` is passed over rather
  than thrown, and the end-of-task case no longer reaches it because
  `cumulative_donor_view` sets such a task aside. If the install did return
  false there, the `continue` would skip every counter. That branch is
  unreachable as far as this audit found. The derived constraint's own
  proofs-on decline is `cumulative.md`'s.

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
  solutions, proofs on; re-measured at `0a5b4ec6`, where only the raise
  column moved, by #1280):

| Instance | `donors_strengthened` | `capacity_units_removed` | `tasks_raised` | rows (division / DP / raised) | `raise_lines_emitted` |
|---|---|---|---|---|---|
| `pack` (7 × h3, `C = 8`) | 1 | 2 | 0 | 3 / 0 / 0 | 0 |
| `deep_gap` (`{2, 6, 6}`, `C = 10`) | 1 | 2 | 0 | 0 / 1 / 0 | 0 |
| `r1` (`{5, 4, 2}`, `C = 6`) | 1 | 0 | 1 | 0 / 0 / 1 | 1 |
| `knapsack_raise` (`{1, 3, 4, 6}`, `C = 6`) | 1 | 1 | 1 | 0 / 5 / 5 | 5 (20 before #1280) |
| `two_full` (`{7, 7, 3, 3}`, `C = 8`) | 1 | 2 | 2 | 0 / 0 / 5 | 10 (35 before #1280) |
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
  derivation of the wrong line: `BogusDivisor` and an unentitled raise. A
  raise claimed too high (`RaiseTooFast`) is caught earlier since #1280, at
  the raise's own closing RUP.
- **Proofs on at `Off` against proofs off: the same, since #1286.** No
  decline asks whether a proof is being written, so a donor strengthened
  with proofs off is strengthened with them on at `Off`, and the search is
  the same. Only `donors_with_set_aside_tasks` can differ, by the
  zero-length corner under [Semantics](#semantics) step 5.
  - The test asserts it on #1241's five fixtures: each is strengthened both
    ways with the same recursions, and its proof verifies
    (`cumulative_strengthening_test.cc:1282–1319`).
  - **Magnitude**, re-measured. `budget.cc` has seven unit tasks, heights
    `{18, 18, 17, 17, 17, 17, 17} × s`, capacity `50s`, starts in `[0, 2]`.
    At `s = 1`, 5, 20 and 100 it is strengthened with proofs on and off and
    refutes at the root (1 node). The proof is 2,212 lines at every scale,
    of which the three knapsack derivations are about 427 lines each, and
    VeriPB verifies it UNSATISFIABLE in 0.01 s.
  - **Horizon**, re-measured with the fact-check's `budget_h` probes, first
    solution. `deep_gap` (`{2, 6, 6}`, `C = 10`, length 2) with starts in
    `[0, 1000]` is strengthened both ways, 4 recursions, one knapsack row,
    and a 261-line proof that verifies. `r1` with starts in `[0, 6000]` is
    strengthened both ways, 4 recursions, one raise line, 155 lines.
  - **Before #1286 and #1280**, at `7e1c4178`, two budgets applied only with
    a logger. Each summed a prediction over every non-empty point of the
    window hull, and the dynamic-programming one charged `items × (C + 1)`
    states per point. At `s = 20` it declined (21,021 predicted states), and
    the proofs-on search took 182 nodes and 8,405 lines (0.24 s to check)
    against 1 node, 3,446 lines and 0.03 s with the budget raised: the
    budget made the proof bigger. Both horizon probes were declined with
    proofs on, `r1` by the raise budget, with the same 4 recursions, and the
    declined proofs were smaller (173 against 389 lines, 197 against 286).
  - The fuzz campaign's proofs-on/off comparison, at `7e1c4178`, found no
    difference. Its driver recorded the derived constraint's
    `% derived cumulative: declined` markers (`driver.py:110`), but not this
    presolver's budget declines, which wrote nothing to the proof, so it
    could not say whether any instance reached a budget (#1241). There is no
    budget left to reach.
  - **The price of no budget** is proof size. #1286's body measured sixteen
    unit tasks with unstructured heights in `[1000, 60000]` under a capacity
    of 213,259, strengthened by 6: a 767,000-line (155 MB) proof that took
    VeriPB 419 s and 1.1 GB, where the budget's decline at #1280's head wrote
    14,000 lines. With proofs off it takes under 1 ms either way.
- **Across assertion levels: yes, it can be weaker above `Off`.** That is
  unchanged by the fixes.
  - Above `Off`, a task with a variable start and a
    variable length is set aside (see [Variable kinds](#variable-kinds-and-views)).
    In the fact-check's `varlen.cc`, `pack` with task 0's length in `[1, 2]`
    takes 1 node with no proof and at `Off`, and 252 nodes at `Definitions`
    and `Inferences`. Reproduced at `7e1c4178`, not re-run. Under the
    default encoding those proofs are rejected anyway (#1234).

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
  - #1241's five fixtures (`scaled_1`, `scaled_20`, `scaled_100`,
    `deep_gap_long`, `raise_long`), each solved to its first solution with
    proofs off and on, which must strengthen both ways with the same
    recursions and verify. The two long-horizon ones are skipped under the
    recovering arm, which writes a row at every time point
    (`cumulative_strengthening_test.cc:1300–1307`). Added by #1286, which
    removed the two fixtures that set a budget to zero; #1280 removed the
    zero-raise-budget checks;
  - an OPB-unchanged check;
  - solution preservation against brute force, proofs off, on 60 random
    instances, extended up to 240 until both halves have fired. Heights are
    drawn against each capacity so that full tasks occur. With `--seed=2` it
    strengthened 18 of 60 and raised 4 heights, at `7e1c4178` and again at
    `0a5b4ec6`;
  - a verified sweep of 25 or more instances until some raise happens;
  - four mutation lanes;
  - marker counts with VeriPB;
  - a negative control whose OPB matches a run without the presolver.
  - Seeded (`establish_and_announce_seed`). The random sweeps use
    `get_seed()`, so `--seed=N` reproduces them. One run with `--seed=1`
    takes 2.3 s and 15 MB at `0a5b4ec6` (2.6 s and 27 MB at `7e1c4178`).
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
  - `RaiseTooFast` on `knapsack_raise`, which since #1280 claims `kappa + 1`
    inside the raise's `red` and is rejected at its closing RUP.
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
  level fails under the default encoding (#1234): a rejected proof over a
  posted donor, a throw over a `Disjunctive2D` projection.
- **The pass's cost** at any horizon or capacity. No test times it, and no
  audit-lane row posts the presolver.
- **`ClaimOneBetter` on the division path, which cannot be tested.** The
  claim `kappa − 1` is never a multiple of `d` when `d > 1`, since every
  subset sum is, so the corruption always lands on the knapsack path
  (`subset_sum_strengthening.cc:166`). The lanes on `pack` and on
  `bars` in `disjunctive_2d_presolver` both do. Division's tightness rests on
  `BogusDivisor` alone.
- **Deleted:** "a budget decline that changes search with proofs on". There
  is no budget since #1286, and the test now asserts the opposite on five
  fixtures.
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
- **For CPU benchmarking:** since #1281 the pass's own cost is small, and it
  scales with the stretches, not the horizon. The capacity shape with
  staggered starts (`C ≈ 10⁶`, 19 stretches) is the one where it still shows;
  the `horizon.cc` shape now measures the two `Cumulative` propagators.
- **For proof verification:** `budget.cc` at scales 1–100 for the knapsack
  path, and #1286's sixteen-task example for a derivation of any size. A
  scaled `knapsack_raise` is no longer interesting: its raise is one line at
  any scale. Never uncapped: at `7e1c4178` the `div` family at `n = 64`
  wrote a 700 MB proof from the donor alone (not re-run).

### CPU performance

**The pass.** See [Initialisation](#initialisation-and-global-data). Since
#1281 it is per stretch. On `horizon.cc` a run with it still costs about
twice the donor's horizon-sized cost, which #1281's profile attributes to the
two `Cumulative` propagators, the derived constraint's as well as the
donor's, and at `C ≈ 10⁶`, `n = 10` it costs about a million
instructions per stretch. At `7e1c4178` it was about 1.1 µs and 520 bytes per
time point at `n = 3`, and about 0.6 ms per time point at `C ≈ 10⁶`.

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
`full_task_pack`, 39 → 1; on `knapsack_raise` and `two_full`, 5 → 1, at
`7e1c4178` and again at `0a5b4ec6`. That measures fixtures built to show it,
not a benchmark.

**Against other solvers:** not measured. No front end reaches the presolver,
and Gecode, Choco and ACE have no Schulz-style presolve to compare with.

**What this does not exercise.** The generated benchmark reaches the capacity
rewrites only rarely, and the raise never (`tasks_raised` was 0 on both
seeds where it fired).

### Proof performance

**Own against shared.** `own.cc` installs the derived constraint with its rules
off, so it derives its install-time rows and never fires. The search is then
identical to the run without the presolver (the same recursions), and the
difference in lines is what the presolver costs. Families of unit tasks with
starts in `[0, ⌈n/2⌉ − 1]`, first solution, re-measured at `0a5b4ec6`, every
proof verified:

| Family | `n` | lines without | lines with, rules off | difference | of which the derivation | rows |
|---|---|---|---|---|---|---|
| `div` (h3, `C = 8`) | 4 | 91 | 169 | 78 | 6 | 1 (division) |
| `div` | 16 | 1,289 | 2,147 | 858 | 6 | 1 |
| `dp` (h18/17, `C = 50`) | 4 | 91 | 378 | 287 | 215 | 1 (knapsack) |
| `dp` | 16 | 1,289 | 3,268 | 1,979 | 1,127 | 1 |
| `raise` (h9 + 4s, `C = 10`) | 4 | 327 | 361 | 34 | 34 | 2 (raised, 2 raise lines) |

"The derivation" counts from the subset-sum comment to the presolver's
summary comment. The derivations are the same size as at `7e1c4178`: 6 lines
on the division path whatever `n` is, and on the knapsack path 215 at
`n = 4` and 1,127 at `n = 16`. What changed is the rest of the difference.
At `0a5b4ec6` the donor's own search on `div` and `dp` recovers no capacity
row (its proof has no `% checkpoint recovery` marker), so the recovery of the
row the derived constraint cites is charged to the presolver: 74 lines at
`n = 4` and 854 at `n = 16`, as a chain base (#1290), two of which define
flags the donor's search would otherwise define itself. At `7e1c4178` the
difference was the derivation alone (6, 6, 215 and 1,127), against donor
proofs of 248 and 39,228 lines. On `raise` the donor recovers the rows itself,
so the difference is the derivation, 34 lines for two raised rows where it
was 33 over 12 raise steps.

`raise` at `n = 16` is the energy differential at scale. At `7e1c4178`,
without the presolver, and with it but its rules off, the solve had not
finished after the 120 s timeout, by which point it had written a 15 GB
proof; that was not re-run. With its default rules it refutes at the root:
1 node, 9,065 lines, with 8 raised rows and 8 raise lines, and VeriPB
verifies UNSATISFIABLE. At `7e1c4178` that proof was 44,522 lines with 64
raise steps.

**With the energy rules on**, the proof is whatever the search becomes. `pack`
goes from 5,811 lines (381 KB) and 0.09 s to check to 940 lines (47 KB) and
0.01 s, VeriPB 3.0.2 on the same core, at `0a5b4ec6`. At `7e1c4178` it was
8,405 lines (864 KB) and 0.24 s against 2,174 lines (144 KB) and 0.03 s.

**At the assertion levels:** not measured. Under the default encoding, every
proof in which it installs something is rejected (#1234). The
time-indexed arm writes a checkable one, except over a `Disjunctive2D` donor it
would strengthen (`bars`), where it throws under either encoding. The presolver emits no `a` lines of its own and carries
no hint type. A hints-only mode would have to decide what its rows become, and
#1234 leaves that open.

## Status, gaps, and next steps

### Proof-logging gaps

- **Unjustified rewrites:** none. Every row is derived and pinned.
- **Strength changes with proofs on: no, since #1286.** There is no proof
  budget, so proofs on and off strengthen the same donors (see [Can it weaken
  the model?](#can-it-weaken-the-model)). Before it, two budgets applied only
  with proofs on (#1241).
- **Strength changes across assertion levels: yes.** The variable-length
  set-aside above `Off` costs 252 nodes against 1 on `varlen.cc` (at
  `7e1c4178`).
- **Assertion levels: rejected wherever it installs something,** under the
  default encoding (#1234, not this presolver's code): a parse error at
  `Inferences` and `Backtracking`, a rejected recovery `rup` at `Definitions`
  and `Links`. Over a
  `Disjunctive2D` projection donor that it would strengthen, the solve throws
  rather than writing a proof at all (also #1234).

### Known limitations

- Not reachable from any front end. A MiniZinc, XCSP3, `.scp` or `gcspy` user
  cannot turn it on.
- A derivation can be large, and nothing caps it. The knapsack path costs
  three flags per reachable partial sum per item, at every row a firing
  cites: #1286's sixteen-task example is 767,000 lines and 419 s to check.
  That is the price of proofs on and off searching identically.
- A capacity above 10⁶ is declined, with proofs on or off ("skipped … because
  a size limit was reached").
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
  Under the default encoding every such proof is rejected anyway.
- No `with_makespan` (#702).

### Next steps

1. **Assess per stretch, not per time point (#1240).** Done by #1281, as
   proposed: the assessment runs once per stretch between the `2n` window
   edges, the recipe looks its stretch up in a shared map rather than a
   copied per-point one, and the bitset is read a word at a time. The map
   is still built with proofs off, but it has at most `2n − 1` entries.
2. **Budget something closer to what will be derived (#1241).** Done by
   #1286, **a different way from any this item listed**. It weighed
   re-predicting the budget per stretch, fixing only its magnitude part, or
   applying it with proofs off too. Ciaran's call on #1241 was that proofs on
   and off must search identically even where that makes a proof expensive,
   and applying the budget with proofs off would weaken propagation, so the
   budget was removed instead. Its cost is under [Can it weaken the
   model?](#can-it-weaken-the-model).
3. **Raise by proof by contradiction (#1242).** Done by #1280, as proposed:
   one `red` per raised task per row whose subproof is a saturating `pol` and
   a `rup >= 1`, which made the raise budget unnecessary, and it was removed
   with the step helpers. The audit's hand check (`kappa = 8`, rest
   `4 + 4 + 4`, `tmp/fd-sched/cumulative_strengthening/pbc`) took the loop's
   six steps to one; #1280's body records a Fable consult against VeriPB
   3.0.2's source.
4. **Fix #1234 (owned by `cumulative.md`),** then add an
   assertion-level lane to this test.
5. **Report the all-full and all-loner declines truthfully,** and decide
   whether a loner is an ordinary task. Small; the code already flags it.
   The stale comment at `cumulative_strengthening.cc:686–690` that this item
   also listed was fixed by #1265, after `0a5b4ec6`.
6. **A `--strengthen-cumulative` flag on `examples/rcpsp`,** and a front-end
   switch per the propagator-or-decomposition convention. Small, and it buys
   real instances. An RCPSP instance set with tight, structured demands would
   be the benchmark that reaches it.
7. **`with_makespan` (#702).**
8. **A large-domain audit row** that posts the presolver with a wide start and
   a capacity near the limit, timing the pass. Not done, and not as simple as
   it looked: #1281's body notes that such a row would not reach the
   presolver, because `Cumulative` is a `KnownTrip` in that test
   (`large_domain_audit_test.cc:761`) and trips in its own `prepare` first.
   A row would have to wait for the donor, or the timing go elsewhere.

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
  - The raise by contradiction (#1280) is ours, as were the cutting-planes
    loop it replaced and that loop's step bound (design note).
  - We know of no prior certification of a cumulative *presolve*. What is new
    is posting the strengthening as a derived constraint whose rows are proved
    from the donor's, leaving the model untouched.

## Further reading

- [`cumulative-strengthening.md`](../cumulative-strengthening.md): the design
  note.
  - The rules and why `kappa` is a maximum.
  - The neutrality theorem, and why the derived constraints ship without
    time-tabling.
  - The raise by contradiction, the cutting-planes loop it replaced, and its
    two degenerate ends.
  - The fixtures, and why `{6, 10, 15}` cannot be one.
  - The restrictions, and the convert-or-set-aside judgement.
  - #1280, #1281 and #1286 each updated it for their change. At `0a5b4ec6`
    it was still accurate except in three places, all outside this stack,
    and **#1265 fixed all three after `0a5b4ec6`**:
    - the wording noted under raise-a-full-task's Tightness (the
      `RaiseUnentitled` paragraph now names the failing step);
    - "node-for-node identical", where the test compares solution sets and
      recursion counts (now "the same solutions in the same number of
      recursions");
    - "a variable length is not set aside at all", which is false above
      `Off`, where a variable-start, variable-length task is set aside (now
      "not set aside merely for varying", with the above-`Off` exception and
      a fuller set-aside list).
- [`subset-sum-strengthening.md`](../subset-sum-strengthening.md): the two
  derivations and their tests.
- [`cumulative-proof-logging.md`](../cumulative-proof-logging.md): derived
  Cumulatives, the donor view and lazy rows (#1130).
- [`cumulative.md`](../constraints/cumulative.md): the installed propagator,
  the derived machinery's declines, the makespan rule, and #1234.

## Developer commentary

None.
