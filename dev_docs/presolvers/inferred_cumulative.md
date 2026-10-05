# `inferred_cumulative`: lifted cover cuts over the posted resources, posted as derived `Cumulative`s

> **Maturity** experimental ·
> **Audited** 2026-10-04 at `7e1c4178` ·
> **Open issues** filed by this audit: #1254 (certificate cost under
> start-checkpoint), #1255 (the lifting programme's cost and its state
> budget), #1256 (the "cut short" note), #1257 (silent detection losses); see
> [Next steps](#next-steps). Already open and touching this presolver: #703
> (Sidorov's early stop, correctly gated), #868 (cross-solver comparisons),
> #976 (the scheduling tracker), #983 (no front end reaches the scheduling
> presolvers). Owned by `cumulative.md`: #1234, and #1267 (the installed
> makespan initialiser scans the whole candidate horizon; filed from the
> Codex review). At
> `AssertionLevel::Definitions` and above, a derived `Cumulative`
> over posted donors makes VeriPB reject the proof under the default
> start-checkpoint encoding. Over a `Disjunctive2D` projection donor the
> install declines instead.
> Tracked under #871.

`InferredCumulative` reads the posted `Cumulative`s, and the projections a
`Disjunctive2D` publishes, as one matrix of demands. It runs the second stage
of Sidorov's CP 2026 procedure over that matrix:
- enumerate *covers* (sets of tasks that cannot all run at once on some
  resource);
- *lift* each into an inequality `Σ πᵢ aᵢ ≤ π₀` over activity indicators,
  with the largest coefficients that stay valid over every resource at once;
- post the best five as derived `Cumulative`s, whose heights are the
  coefficients and whose capacity is the right-hand side.

Nothing reaches the OPB. Each posted cut's per-time capacity rows are derived
in the proof wherever something cites them, by replaying the knapsack dynamic
programme that says the cut holds. Given a makespan variable, each cut also derives a lower bound
on it from the cut's energy.

Its sibling for capacity one and unit coefficients is
[`inferred_disjunctive.md`](inferred_disjunctive.md); the derived constraint it
installs, and that constraint's runtime rules, are
[`cumulative.md`](../constraints/cumulative.md)'s.

Five things to know before touching it.

- **No front end can run it.** `fzn-glasgow`, the XCSP3 solver,
  `glasgow_scp_solver` and `gcspy` have no flag for it. It is reachable from
  the C++ API and from `examples/rcpsp` (`--infer-cumulative`) only. So the
  MiniZinc and XCSP3 encodings of an RCPSP never meet it, and the question of
  whether it would detect them is answered below by building those shapes by
  hand.
- **Every cut it validates is certified.** Not one cut was found that
  failed to hold (`cuts_uncertifiable` is zero by construction). It was zero
  on every run made for this audit: the audit's own sweep of 710 MiniZinc RCPSP
  instances, the fact-check's 1,999 finished PSPLib instances, and the test
  binary's sweeps on two seeds.
  - **What is not complete.** The state budget does bind on PSPLib J90 and
    J120, on at least 102 instances (the fact-check's finished runs; runs the
    fact-check's sweep killed, `J120_59_6` and `J120_19_1`, hit it too).
    - It leaves a task out of a cut, or drops a cut whose validating
      programme ran out of states.
    - A dropped cut should hold, since its lifting subproblems were exact,
      but it was never checked and has no certificate.
    - So there the posted set is not the published procedure's.
  - **Proofs on against off.** Posting cuts never changed a solution set or a
    node count.
- **Its certificates got much dearer to check when `Cumulative` went to one
  encoding.** #943 (2026-09-19) made start-checkpoint the only `Cumulative`
  encoding, so every donor row a cut cites is now recovered from the
  checkpoint block. On the certificate the August artefact measured
  (`pack001`, deadline 20):
  - the proof grew from 172,386 lines to 568,680;
  - VeriPB's time went from 0.77 s to 35.5 s.
  - On `main` today, the time-indexed test arm writes the same certificate in
    83,982 lines that check in 0.38 s.

  On Pack_d the root proof alone is now 1.4 to 5 GB, and the two tried did
  not verify in 30 minutes. See [Proof performance](#proof-performance).
- **With a makespan named, the root proof is linear in the makespan bound,
  and its check is worse than linear.** It does not depend on the horizon's
  slack: it grows with the window the bound argues over, which grows with the
  task lengths.
  - With lengths scaled tenfold (bound 105 to 1,050), the fixture goes from
    37,641 lines and 0.41 s of checking to 374,871 lines and 37.3 s.
  - With lengths fixed and the horizon multiplied by a hundred, it stays at
    37,641 to 37,812 lines.
  - Without a makespan the root proof is 798 lines at every scale.
- **The presolver's own CPU time is not small on PSPLib J90 and J120.**
  - One instance spends 57 s in it, with proofs off and serially.
  - 94% of that is `build_programme`, nearly all of it the all-pairs frontier
    sweep in the lifting subproblems' dynamic programme (#1255).

## What it is

### Semantics

`InferredCumulative{stats}` is a `Presolver`. `run()` is called once, after
every constraint's propagators are installed (`Problem::create_propagators`)
and before search. It:

1. collects every donor: each posted `Cumulative`, in posting order, then
   every `PublishedCumulativeDonor` (today only `Disjunctive2D`'s two axis
   projections, #973);
2. builds one column per task, matched across donors by
   `(start, length, presence)`, and one row per donor;
3. enumerates covers per row (Algorithm 1), pools them, and keeps every cover
   of more than three tasks plus the best `max_covers` of the whole pooled
   list, by rank (which may include some of those already kept);
4. lifts each cover (Algorithm 2), longest task first, solving each
   coefficient's subproblem over **every** row (Sidorov's Equation 4);
5. drops a cut some single row already implies term by term, ranks the rest by
   `energy / π₀`, keeps the best `max_posted`, validates each by building its
   dynamic programme, and installs each as a derived `Cumulative` with the
   rules `{time_table = false, overload = true, profile_overload = true}`.

It returns `true` always: it never proves the model infeasible on its own and
never removes a value. Everything it does to the search happens through the
propagators it installs.

**Degenerate cases.**
- No donor, or fewer than two usable tasks across all donors: nothing happens,
  and the stats block still appears with `donors_seen` and `tasks`.
- A task whose demand on a donor exceeds that donor's capacity gets no entry on
  that row (a mandatory such task makes the donor infeasible on its own; an
  optional one is set aside by `cumulative_donor_view`).
- A donor whose capacity is a view is passed over and counted
  (`declined_irreducible_capacity`).
- A zero-demand member of a cover is admitted, as Definition 6 admits it.

### Concrete constraints and frontend coverage

A presolver posts no constraint of its own, so this table is about entry
points rather than classes: the places a user can switch it on.

| Entry point | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `InferredCumulative` | `frontend gap (#983)`¹ | `frontend gap (#983)`¹ | `frontend gap (#983)`² | `frontend gap (#983)`³ | C++ API, and `examples/rcpsp --infer-cumulative` |

1. #983 tabulates all three scheduling presolvers as reachable from no front
   end. Neither `fzn-glasgow` nor the XCSP3 solver adds the presolver;
   both add `DifferenceLogic` only, behind a flag. A flag would be a few
   lines; what it would reach is under [Detection and its failure
   modes](#detection-and-its-failure-modes), including the MiniZinc library
   rewriting some resources into `disjunctive` before this presolver could see
   them.
2. `gcspy` binds no presolver at all.
3. The `.scp` solver, `glasgow_scp_solver`, adds no presolver. The `.scp`
   file format has nothing to say either way, since it describes the model
   only. A presolver adds nothing to the `.scp` a solve writes, nor to the
   `.opb`, so that `.scp` is still the right input for the verified chain;
   see [Cake conformity](#cake-conformity).

### Options

Every option changes what is inferred or how it is proved, never the OPB
model: nothing this presolver does reaches the `.opb`, which the test asserts
byte for byte.

| Option | Default | What it is |
|---|---|---|
| `with_budgets(max_covers, max_posted)` | 100, 5 | Sidorov's `N_cover` and `N_out`. `max_covers` bites twice: on each row's short covers, then on the pooled list. Covers of more than three tasks are exempt from both. |
| `with_maximum_capacity(c)` | 1000 | Sidorov's `-b`. Implemented as a cover-size limit, `c + 1`, which bounds `π₀` because lifting never moves it. Pair covers are always enumerated, so `c = 0` still posts cuts with `π₀ = 1`. |
| `with_lifting_call_budget(n)` | 20,000 | Sidorov's `N_calls`, from his Appendix C. Shared over all covers. A cover whose budget runs out mid-lift is posted with the coefficients it has. |
| `with_programme_state_budget(s)` | 100,000 | States *built* per dynamic programme. Over it, a lifting subproblem leaves its task out (`lifting_subproblems_over_budget`), and a cut is dropped (`dropped_over_state_budget`). |
| `with_rules(r)` | energy rules only | The `CumulativeRules` the derived constraints run. Time-tabling is off because a valid cut cannot change a single-time-point verdict; see [Can it weaken the model?](#can-it-weaken-the-model). |
| `with_makespan(m)` | none | Name the makespan, so that each cut also derives `m ≥ L`. See [Rewrite: makespan-bound](#rewrite-makespan-bound). |
| `with_proof_mutation(…)` | `None` | Tests only; see [Tests](#tests). |

The defaults are the main experiments' `N_cover` and `N_out` under Appendix C's
call budget, a combination Sidorov's experiments did not run;
[`inferred-cumulative.md`](../inferred-cumulative.md) says why that matters
for #703.

Measured here, with the default budget of 20,000 lifting calls:
- **PSPLib:** of the instances that finished inside the 120 s cap of the
  audit's own sweep, the most any used was 18,294 (`J120_58_4`).
  - **Killed runs.** That sweep killed 37 (the fact-check's 14-way re-sweep
    killed 41), and their counts are unknown.
  - **`J120_19_1`.** One killed instance, it finishes outside a batch in about
    3 to 4 minutes (248.8 s and 176.2 s in two runs, both partly beside other
    jobs) with 4,683 calls. So the call
    budget is not what makes those slow.
- **The 710 MiniZinc-set instances:** 25 of the la_x instances exhausted it.
  They have 300, 400, 450, 600 and 675 tasks, five of each. It cost them
  nothing, since every la_x cut is dominated anyway.
  - **Against the August note.** So the budget does bind on some collections.
    `certified-makespan-bounds.md`'s "the lifting-call budget never binds" was
    measured on Pack and Pack_d only.

The **state budget** (100,000 states per programme) does bind, on PSPLib J90
and J120; see [Can it weaken the model?](#can-it-weaken-the-model).

`with_consistency()` does not exist. `consistency::Auto` and
`consistency::Dynamic` do not apply.

### Variable kinds and views

What the presolver reads from a donor, per task, through
`cumulative_donor_view` (shared with the other two presolvers):

| Argument | Accepted | What happens |
|---|---|---|
| start | any `IntegerVariableID` | Part of the column key, compared as an `IntegerVariableID`. |
| length | constant or variable | Part of the column key, **as the variable**: two donors naming different variables of the same value make two columns. Ranked and counted by `lb(length)`. |
| height | constant; plain variable with a positive lower bound | A variable height is converted to `lb(height)` (`converted_heights`). A view, or a lower bound of zero, sets the task aside on that donor (`donors_with_set_aside_tasks`). |
| capacity | constant; plain variable | A variable capacity is argued at its current upper bound. A view declines the donor. |
| presence | any, through `task_presence` | Part of the column key (#1136). An optional task's guaranteed length is zero. |

**On the proof side:**
- A set-aside task, and a variable capacity, are handled by
  `recover_constant_argument_row` before the cut is derived.
- A variable height is converted there too, through the row saying the
  contribution is at least the height.
- A variable length costs nothing in the rows.
  - **Proofs-on caveat.** With proofs on, a variable-length task whose start
    is not a constant is set aside if its donor published no
    `end ≥ start + length` line to pin through (`cumulative_donor_view`).
  - **The makespan argument.** A variable length keeps the task out of it,
    even when the variable has a single value; see
  [Rewrite: makespan-bound](#rewrite-makespan-bound).

### Reification

None, and none would be wanted: a presolver's output is unconditional.

### Relation to other families

- **Reads (donors).** `Cumulative`, exactly that class
  (`Problem::each_constraint_of_type<Cumulative>`), and the per-axis
  projections `Disjunctive2D` publishes (`publish_cumulative_donor`, #973).
  **`Disjunctive` is not a donor**, nor is any decomposition, nor a derived
  `Cumulative` another presolver installed.
- **Installs.** A derived `Cumulative` per cut (`install_derived_cumulative`),
  whose propagator, declines, makespan initialiser and hole sensitivity are
  documented in [`cumulative.md`](../constraints/cumulative.md).
- **Shares code.**
  - `cumulative_donors` and `cumulative_donor_view`, with
    `InferredDisjunctive` and `CumulativeStrengthening`;
  - `find_makespan_links` and `makespan_energy`, with `InferredDisjunctive`;
  - `recover_conjunction_flag_bridge` and `recover_bridged_row`
    (`flag_bridge.hh`), with `InferredDisjunctive`;
  - `lifted_cover_cut.{hh,cc}`, its own.
- **Other presolvers.** It is the second stage of the procedure whose first
  is `InferredDisjunctive`. The two do not see each other's output, and
  posting both posts both sets of cuts with no deduplication.
  `CumulativeStrengthening`'s strengthened capacities are not visible here
  either, since they live in a derived constraint. So the **donor set** does
  not depend on presolver order.
  - **The cuts found can.** The pass reads live bounds: through the donor
    views (a capacity's upper bound at `donor_view.cc:123`, height lower
    bounds, length upper bounds at `:169`) and directly (start windows,
    `cumulative_task_window` at `inferred_cumulative.cc:601`, and length
    lower bounds at `:602`). `solve_with` runs each presolver's
    initialisers before the next presolver runs, so an earlier presolver's
    initialiser can change what this one discovers.
  - **Checked** (`tmp/fd-codex-1005/sched/probes/ord.cc`, `7e1c4178`, no
    makespan named). Three starts in `[0, 5]`, lengths and heights 2, one
    `Cumulative` with capacity in `[3, 4]`; auxiliaries `a, b ∈ [0, 5]` with
    `a − b ≤ 2`, and `capacity ≥ 4 ⇒ b − a ≤ −3`. `DifferenceLogic`'s
    initialiser refutes that guarded negative cycle and sets the capacity to
    3. With `DifferenceLogic` first this presolver posts 3 cuts; alone, or
    with `DifferenceLogic` after it, 1. Proofs on and off agree, and the root
    proofs verify with VeriPB 3.0.2 (`--force-checked-deletion`,
    `VERIFIED NO CONCLUSION`).
  - **It also matters to the certified bound**, separately. `solve_with`
    runs each presolver's initialisers before the next presolver runs
    (`solve.cc`, after each `run`). So an earlier `InferredDisjunctive` with
    the same makespan raises the makespan's lower bound first, and this
    presolver's bound then has nothing to beat.
  - **Measured.** On KSD15_D `j3033_9`, `examples/rcpsp --infer-cumulative`
    certifies 361. `--infer-disjunctive --infer-cumulative` certifies 361 in
    `InferredDisjunctive`'s block and 0 in this one's.
- **Reachability.** Only directly, from C++. No front end decomposes into it.

## The proof model

### OPB encoding

None. The presolver writes nothing to the `.opb`, and the `"the OPB is
untouched"` lane in `inferred_cumulative_test.cc` compares the `.opb` with and
without it byte for byte. What the derived constraints cite are the donors'
own rows and flags; their encoding is `cumulative.md`'s (the start-checkpoint
encoding, with per-(task, time) `before`, `after` and `active` flags defined
in the proof when first cited).

### Labels

The presolver names no OPB row. It reaches donor rows by
`CumulativeDonorKey{constraint id, row family}`, through the derived
constraint's row lookup, and makespan rows through the labels
`find_makespan_links` reads with each row (`MakespanLink::row`). With proofs
on, a makespan row with no label is skipped, which costs that task its link
(the deadline's confinement); the overlap its own start bounds force still
counts.

### Cake conformity

`cake_pb_cp` never sees the presolver: it re-derives the OPB from the `.scp`,
which describes the model only. The question is whether the proof checks
against cake's OPB rather than ours, and it does. By hand, on
`examples/rcpsp --dzn pack001.dzn --infer-cumulative --deadline 20 --prove` at
`7e1c4178`:
1. `cake_pb_cp` re-derives the OPB from the `.scp`;
2. `veripb --elaborate` turns the proof into a core (41.8 s,
   `s VERIFIED UNSATISFIABLE`);
3. `cake_pb_cp` checks that core: `s VERIFIED UNSATISFIABLE`.

No ctest lane runs this: the SCP chain cases go through
`glasgow_scp_solver`, which cannot add a presolver.

### Proof-time state

What a derived cut leaves in the proof, per cut and per time point `t` that
something cites (or that starts a stretch between window edges, at install):

- **At `Top`, surviving:** one pinned line,
  `Σ_{present k} π_k · active[k, t] ≤ π₀`, over the members' own donors'
  `active` flags. It is the `ia` at the end of `derive_lifted_cover_cut`, or,
  when the present members' coefficients cannot reach `π₀`, a plain RUP of
  the same line.
- **Also at `Top`, surviving: the donor rows the cut cites.** Each one is
  recovered from its donor's start-checkpoint block once per (donor, time
  point), and memoised (`find_or_derive_line_in_family`).
  - **Where it is written.** `checkpoint_recovery.cc` emits every line at
    `ProofLevel::Top`, so the recovered rows and the `ckp*` flags they
    introduce survive.
  - **How much.** On the `pack001` deadline-20 certificate, 432,684 of the
    568,680 lines (76%) name `ckp*` flags. That comes from 60 recoveries
    (3 donors × 20 time points), about 7,200 lines each.
  - **Whose.** This is `cumulative.md`'s machinery, but it dominates what this
    presolver's proofs cost.
- **One level deeper, deleted on the way out** (`ProofScaffoldingScope`):
  - the reduced donor rows (`recover_constant_argument_row`);
  - the bridges, three `pol`s per member per crossed row, and each crossed
    row's `ia`;
  - the dynamic programme. Over `r` rows, a state is `r + 2` extension
    variables (`lifted_cover_cut.cc`), though halves are shared between
    states of a layer that agree on a coordinate:
    - `lccw{row}_{layer}_{weight}`, the "at least this weight" half, one per
      row;
    - `lccp{layer}_{profit}`, the "at most this profit" half;
    - `lccs{layer}_{profit}_{weights…}`, the state;
    - and one `lcccut` for the cut;
  - every transition, at-least-one and conclusion line.

  Deleting a variable's two defining lines deletes the variable, so nothing of
  the programme survives. A justifier rebuilding a row has to rebuild its
  programme. That is cheap and deterministic from the row's members, their
  demands and the capacities (`validate_lifted_cover_cut`).
- **A marker.** For each posted cut the presolver writes the proof comment
  `presolve lifted cover: inferred a cut over N tasks on R resources with
  capacity π₀, makespan bound L`. It names no line or flag.
- **Proof-only auxiliaries.** Every one of the above is introduced in the
  proof and is determined by unit propagation on a solution: each is a
  reification of a linear inequality over the flags. None is in the OPB.
- **When proofs are off,** the recipe never runs, so no programme over fewer
  than all members is built (`restricted_rows_rebuilt` stays zero, which the
  test asserts). The programme cache is a `map<vector<size_t>, …>` held by the
  recipe and is never indexed by anything that dangles.

**Hints-only content.** The installed constraint runs under
`CurrentlyUnnamedConstraint`, so at an assertion level its `a` lines carry
`constraint_id unnamed`. For example, at `Inferences` the makespan bound's
assertion ends `::cumulative:((constraint_id unnamed) (subhint makespan));`.
- **What the hint does not say.** Which cut, which presolver, or which donor
  rows an assertion came from.
- **What a justifier has instead.** It has to recover the cut from the
  marker comment and the members' flags. How that affects each rule's
  reconstructibility verdict is `cumulative.md`'s to say.
- **Where it is listed.** This is a Next steps item.

How the derived propagator cites these rows, and what else the derived
row carries at an assertion level, is `cumulative.md`'s.

**At `AssertionLevel::Definitions` and above** (#1234):
- **Over posted donors,** a derived `Cumulative` makes VeriPB reject the
  proof, under the default start-checkpoint encoding.
- **Over a `Disjunctive2D` projection donor,** the install declines instead,
  and this presolver posts nothing.
  - **At `Definitions`, `Inferences` and `Backtracking`** the proof then
    verifies.
  - **At `Links`** it is still rejected, not because of this presolver: at
    `Links` every proof of a satisfiable model is rejected at its first `solx` (#1210), and the projection fixtures
    are satisfiable.
  `disjunctive_2d_presolver_test`'s strip instance at `Inferences` reports
  `declined_by_install = 5`, one per cut (`disjunctive_2d.md`; probe
  `tmp/fd-sched/factcheck2/disjunctive_2d/bars/probe5.cc`).

## The implementation

### Initialisation and global data

The whole pass is initialisation. Its cost, in terms of `n` tasks (columns),
`r` donors and the budgets:

- **Donor scan:** `O(r · n)`, plus a `map` lookup per task appearance.
- **Algorithm 1:** per row, `O(n²)` pair covers, then `O(n² · |distinct
  demands|)` ternary candidates, each inserted into a `set<vector<size_t>>`.
  These are sorted before the budget cuts them down, so the memory and the
  sort are over every pair that overshoots, not over `max_covers`.
- **Algorithm 2:** at most `max_lifting_calls` subproblems. Each one is a
  dynamic programme over the current support, with all `r` binding rows. Each
  layer is reduced to its frontier by an all-pairs sweep, so a layer of `L`
  states costs `O(L² · r)`. This is where the time goes; see [CPU
  performance](#cpu-performance).
- **Validation:** one more programme per surviving cut (at most `max_posted`).
- **Install:** with proofs on, one row per stretch between the cut's window
  edges, each a programme replay (see
  [Proof performance](#proof-performance)).

None of the pass is proportional to the horizon or to a domain's width (see
[Interval efficiency](#interval-efficiency)). The install-time rows are one
per stretch, whatever the horizon. What the pass installs is another matter
when a makespan is named, in two ways:
- **The makespan bound's rows**, with proofs on, are linear in the bound.
- **The installed makespan initialisers**, one per posted cut, run once at
  the root with proofs on or off. Each scans every candidate bound up to
  `min(ub(m), last window end)` and sums every counted task at each, so it is
  `O(n · H)` on a loose `ub(m)` (`cumulative.md`'s `makespan-bound`, #1267).
  That grows with unused horizon even where the bound, and its certificate's
  window, stay small. It is not part of the pass's own cost above.

### Propagator inventory

The presolver installs, per posted cut, one derived `Cumulative` propagator
and, with a makespan, one initialiser. Both are documented in `cumulative.md`.
The row here says only how this presolver configures them.

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| derived `Cumulative` (one per cut) | as `cumulative.md` | as `cumulative.md` | `cumulative.md`'s energy rules | a posted cut | as `cumulative.md` | as `cumulative.md` |
| makespan initialiser (one per cut) | n/a | n/a | [makespan-bound](#rewrite-makespan-bound) | `with_makespan` | runs once | n/a |

The presolver's own pass has no propagator.

### Mutable state and incrementality

None in the pass: it runs once and keeps nothing but the stats block. Each
cut's recipe owns a copy of the donors and members, and a shared cache of
programmes keyed by the set of present members. The full set is seeded at
install; a time point with fewer members present builds and caches its own
(`restricted_rows_rebuilt`). That cache lives as long as the propagator. It
is not backtrackable and needs no restore: a programme depends only on which
members are present.

`InferredCumulativeStats` accumulates across solves when one block is shared
(`clone()` shares it), so `donors_seen` and the rest are totals over every
solve of the `Problem`. The `Important` note is computed per run.

### Interior values and optional pruning

**What this presolver offers.** None. It installs no
optional-interior-pruning pair, and its own pass prunes nothing.

**What it observes.** Its own pass reads bounds only: `lb(length)`,
`lb(height)`, `ub(capacity)`, and each task's window from its start's bounds.
It runs before `choose_optional_interior_pruning()`, so what it *installs* is
counted in someone else's `consistency::Auto`. The derived `Cumulative`'s hole
sensitivity is `cumulative.md`'s.

### Robustness and limits

- **Unbounded or huge domains.** Every input is read through bounds. A
  `Cumulative` whose horizon is near `2⁶⁰` cannot get as far as this presolver:
  `Cumulative::prepare` throws `std::length_error` allocating a horizon-sized
  vector (`prepare_cumulative_overload_check`, `cumulative.cc:501`), and
  presolvers run after `prepare`. That is `cumulative.md`'s. At a horizon of
  10⁶ with lengths of 2.5 · 10⁵, this presolver posts its cuts and reports a
  bound of 750,000.
- **Overflow.** All arithmetic is checked `Integer`.
  - The largest intermediates are a cover's total length times `|C| − 1`,
    when covers are ranked, and a cut's energy times `π₀`, when cuts are
    ranked. They are bounded by about `n² · H` and `n³ · H`.
  - A `Cumulative` that `prepare` can allocate keeps `H` far below the
    overflow line. Past it, the presolver would throw `IntegerOverflow` and
    abort the solve, rather than wrap.
  - Not reachable today. Recorded because #1223 is the same shape in
    `Cumulative` itself.
- **Negative values and zero.** A demand of zero or below is not a column
  entry. A length whose lower bound is zero ranks and counts as zero. A
  capacity of zero leaves no usable task, so nothing is a cover.
- **Degenerate shapes.**
  - **Duplicate tasks in one donor** (same key) stay separate columns, so a
    later donor's copy of the second one matches nothing. That is weaker,
    never wrong.
  - **The same task spelled differently on two donors** (a different length
    variable, a view on the start) makes two columns; see
    [Detection](#detection-and-its-failure-modes).
  - **Aliased starts within a cut** reach the derived constraint unchanged.
- **Option edge.** `with_maximum_capacity(SIZE_MAX)` wraps `c + 1` to zero,
  which silently turns off the ternary and long covers. It is harmless,
  and worth a `std::min`.

### Interval efficiency

1. **The propagation side (the pass).** It walks no value of any domain:
   every read is a bound, and `cumulative_task_window` is two bound reads. Its
   work is in tasks, donors, covers, subproblems and programme states. It is
   **fine at any width**, and at any horizon, for the pass itself. What it
   installs is not, with a makespan named: each cut's makespan initialiser
   scans the candidate horizon, proofs on or off (see
   [Initialisation](#initialisation-and-global-data), #1267).
2. **The reason side.** The pass gives no reasons. The makespan bound's reason
   (`bounds_reason(scope)` over the counted starts, plus presence literals) is
   per task, not per value.
3. **The proof side.** This is where time comes in, which is this family's
   analogue of width:
   - At install, one row per stretch between window edges: at most about
     `2 · members + 1` rows per cut, whatever the horizon (#1130).
   - During search, one row per time point that something cites.
   - **With a makespan named, every row from the earliest window start up to
     the bound's window end,** at the root.
     - That is linear in the makespan bound, about 357 lines per time unit on
       the fixture below, and not in the horizon: multiplying the horizon by
       100 with the lengths fixed moves the proof from 37,641 to 37,812
       lines.
     - It is the derived constraint's makespan initialiser that sums them
       (`cumulative.md`).
     - With no makespan named, the fixture's root proof is 798 lines at every
       scale.
4. **The audit lane.** No row in `gcs/large_domain_audit_test.cc`. The
   horizon axis is exercised by `cumulative_wide_horizon_test` (horizon
   10⁵, no makespan named), which asserts the number of per-time names stays
   under 200. No lane names a makespan over long tasks, where the bound and
   hence the root proof are large; [Next steps](#next-steps) has an item.

## Rewrite catalogue

One entry per rewrite. Facts common to all three:
- every row is derived at `ProofLevel::Top`, and its working is one level
  deeper and deleted;
- each rewrite installs through `install_derived_cumulative`, which with
  proofs on can decline (`declined_by_install`).
  - It declined nothing in any run made against posted donors.
  - It does decline over a `Disjunctive2D` projection donor at
    `AssertionLevel::Definitions` and above: every cut, on the
    `disjunctive_2d_presolver_test` strip.

How often the pieces of each rewrite fire, over the 710 instances of the
MiniZinc RCPSP collections (Pack, Pack_d, BL, KSD15_D, la_x), proofs off, at
`7e1c4178`:
- some cut posted on 588;
- a multi-resource cut on 389;
- a non-zero certified makespan bound on 281 (with the `examples/rcpsp`
  windows; see [Benchmarks](#benchmarks-and-examples)).

### Rewrite: lifted-cover-cut

- **Matches** — a cover on some donor row: a set `C` of usable tasks, of
  demand at most the capacity each, whose demands on that row sum to more than
  the capacity. The families are Sidorov's Algorithm 1: every overshooting
  pair; each non-overshooting pair plus the longest task of each demand that
  overshoots the room left; and, for each demand `v` with `k = ⌈(C + 1)/v⌉`
  between 3 and the cover-size limit, the `k` longest and `k` shortest tasks of
  that demand.
- **Posts** — `Σ πᵢ aᵢ ≤ π₀`, starting from `Σ_C aᵢ ≤ |C| − 1` and lifting
  every other column in, longest guaranteed length first. Each gets
  `π₀ − v*`, where `v*` is the most the current left-hand side can reach once
  that task runs, subject to **every** row (Equation 4). It is posted as a
  derived `Cumulative`: heights `π`, capacity `π₀`, each member's flags taken
  from the first donor that gives it a term. This entry is the case where the
  programme keeps a single row; see
  [multi-resource-cut](#rewrite-multi-resource-cut) for more than one.
- **Posted in derived mode** — yes. No OPB row. The per-time rows are derived
  by the recipe; a row asked for at a time `t` is the cut restricted to the
  members whose window contains `t`, with the same coefficients.
- **Why it is sound** — at a time `t`, the donor row says
  `Σ cᵢ aᵢ ≤ C` over the 0/1 activity indicators. `Σ πᵢ aᵢ ≤ π₀` holds at
  every 0/1 point that row allows exactly when
  `max{Σ πᵢ xᵢ : Σ cᵢ xᵢ ≤ C, x ∈ {0,1}}` is at most `π₀`.
  - The knapsack dynamic programme computes that maximum exactly: layers of
    reachable (weight, profit) pairs, a successor that overruns `C` never
    created, dominated states dropped.
  - `validate_lifted_cover_cut` builds it, and the cut is posted only if no
    final state's profit exceeds `π₀`. So nothing false is posted, however the
    coefficients were chosen.
  - A restriction to the members present at `t` is valid too: setting an
    absent member's indicator to zero is a point the full cut already covers.
  - Set-aside tasks and other non-members only add non-negative terms to the
    donor row, so dropping them weakens it.
- **Proof technique** — per row, `pol` + `redundance` + `hinted RUP` + `ia`:
  - **`pol`**, when there is anything to reduce
    (`recover_constant_argument_row`): weakens set-aside tasks out, converts
    variable heights to `lb(h) · active`, and replaces a variable capacity by
    its current upper bound through the order literal. Otherwise the row is
    used as it stands, with no line.
  - **`redundance`**: the dynamic programme's states, `r + 2` extension
    variables per state over `r` rows, as above.
  - **`hinted RUP`**: the start state, each transition clause, each source's
    and each layer's at-least-one, and the conclusion. Each cites exactly what
    it resolves (#676, #681).
  - **`pol`**: each transition half, and the step that rules a member out
    (weakened, saturated, divided), which lands on a two-literal clause.
  - **`ia`**: the pin onto the literal-exact cut.

  The procedure is Demirović et al. (CP 2024)'s certified knapsack dynamic
  programme, in its one-sided form. Its use to certify a *lifted cover cut*
  is ours: no published justification procedure covers it.
  - **Precondition:** every row the programme keeps is expressed over the same
    flags as the members, so a single row is used as is.
  - **Reconstructibility:** `hinted`, by Appendix C's rules. The marker
    comment and the derived constraint's tasks name the members and
    coefficients, the donor rows are in the baseline context, and the
    programme is a deterministic function of those.
  - **Vocabulary.** Appendix A has no row for a dynamic-programme replay.
    `chain scaffolding` is the nearest and is wrong (it is root-level and per
    value), so the four names above are listed instead.
- **Neutral with respect to its consumers?** Yes, for time-tabling: a valid
  cut cannot change a verdict about one time point. That is why the derived
  constraint ships with time-tabling off, and why the test can assert
  node-for-node equality with it back on (181 nodes either way, seeds 1
  and 2). The energy rules are where it is meant to be stronger.
- **Proof size** — the programme replay costs about 12.5 lines per state,
  and over one row the states number `members × (π₀ + 1)` or fewer. That is
  the design note's figure, taken before #943; the replay itself did not
  change at #943. On top of it, every donor row the cut cites is now
  recovered from the checkpoint block, which is what dominates today (see
  [Proof performance](#proof-performance)). Rows are derived per stretch at
  install, and then per cited time point.
- **Tightness** — in `inferred_cumulative_test.cc`, all rejected by VeriPB,
  each against an honest control on the same fixture:
  - `ClaimTighterCapacity` (pin `π₀ − 1`) and `ClaimTallerTask` (one member's
    coefficient + 1): refused at the pin.
  - `ClaimTighterRow` (programme built against capacities one lower): refused
    inside the replay.
  - The fixture carries a spare task (`lifted_instance_with_spare(13)`) so the
    row has a term the cut is not about.
  - `ForgetPresence` (an optional cut posted as mandatory) is refused on the
    optional-task fixture.
  - One more in `disjunctive_2d_presolver_test` ("inferred cumulative tighter
    capacity") over a `Disjunctive2D` projection's rows.

### Rewrite: multi-resource-cut

- **Matches** — as [lifted-cover-cut](#rewrite-lifted-cover-cut), when the
  programme keeps more than one binding row. That is, the members' demands
  overshoot more than one capacity, so the cut is a consequence of several
  rows together and possibly of none alone.
  - Counted as `multi_resource_cuts_posted`.
  - Posted on 5 of 5 cuts on every Pack and Pack_d instance, and on 389 of
    the 710 MiniZinc-set instances.
- **Posts** — the same derived `Cumulative`. Members' flags come from their
  canonical donors, and each other row's terms are carried onto them.
- **Posted in derived mode** — yes.
- **Why it is sound** — the programme carries one weight per binding row, and
  forbids any successor that overruns any of them. Each row is used only to say
  one transition cannot happen, exactly as over one row; nothing scales or adds
  rows together.
  - **The flags must mean the same thing.** Row `r` speaks about the members'
    `active` flags on donor `r`, and the cut about their flags on their
    canonical donors.
  - **What makes them agree.** Both are reified as `before ∧ after` over the
    same start, length and presence, by the column key. So
    `a_canonical ⇒ a_r`, which is the direction needed for `Σ c_j a_r ≤ C` to
    imply `Σ c_j a_canonical ≤ C`.
- **Proof technique** — as [lifted-cover-cut](#rewrite-lifted-cover-cut),
  preceded per crossed row by `pol`. Each member gets a
  `recover_conjunction_flag_bridge`: three `pol`s, crossing the conjuncts.
  `recover_bridged_row` then weakens the row to the members and adds `c_j`
  copies of each bridge, so every flag appears with both signs and cancels.
  It pins the result with an `ia`.
  - The bridge needs both donors' `before` / `after` flags defined at `t`.
    `active_conjuncts_for` asks for them first.
  - A presence conjunct cancels only when both flags carry the same literal,
    which the column key guarantees (#1136).
  - Reconstructibility: `hinted`, as above, plus the donors' flag keys.
- **Neutral?** As above.
- **Proof size** — the programme over several rows is a Pareto frontier rather
  than a staircase. The design note measured the widest layer going from 4 to
  14 states on Sidorov's published Pack cuts. Plus three `pol`s per member per
  crossed row.
- **Tightness** — `BridgeWrongTask` (a row carried onto the previous member's
  flags) is refused on `two_resource_instance(8)`, alongside the three
  single-row mutations on the same fixture. The random verified sweep checks
  66 and 55 multi-row cuts (seeds 2 and 1) uncorrupted.

### Rewrite: makespan-bound

- **Matches** — `with_makespan(m)` was called and a cut was posted. What
  makes the bound worth anything is the links: for each member,
  `find_makespan_links` (this presolver's, shared with `InferredDisjunctive`)
  looks for an unconditional model row saying the task finishes by `m`. A
  member with no link keeps only what its own domain gives: the overlap its
  start bounds force into the window, which can be its whole duration. It
  finds:
  - **linear:** two-term `ReifiedLinearInequality` under `MustHold`, of the
    shape `m − s ≥ b` with coefficients exactly `+1` and `−1` and `s` a plain
    variable;
  - **comparison:** `LessThanEqual`-family rows `s + b ≤ m` or `s ≤ m − b`
    over offset views, cited in deview mode;
  - with proofs on, only rows that have a label.
- **Posts** — `m ≥ B`, inferred once at the root by the derived constraint's
  initialiser, where `B` is the energy bound over the cut's members. That
  runtime rule, its search for the window, its reason and its derivation are
  `cumulative.md`'s; [`certified-makespan-bounds.md`](../certified-makespan-bounds.md)
  is the long note. Until #1265 its argument confined every task to
  `[lo, μ)`, which is the special case of the one under *Why it is sound*
  below.
- **Posted in derived mode** — it is an inference, not a row.
- **Why it is sound** — the cut says its members occupy at most `π₀` per time
  step. Suppose `m ≤ μ`. Each counted member (known present, with a constant
  length) is confined to its own start bounds and, where a link
  `m − s ≥ b` exists, to `s ≤ μ − b`. From that range the window-energy lemma
  gives the least it must run inside the window `[lo, μ)`, and `πᵢ` times
  that is its guaranteed energy there. If those energies add up to more than
  `π₀` times the window's rows, `μ` is refuted (`cumulative.md`'s
  `makespan-bound`). Every member finishing inside the window, at its full
  `dᵢ πᵢ`, is the special case.
- **Proof technique** — `cumulative.md`'s; it sums the cut's derived rows for
  every time point from the earliest window start to the bound's window end,
  which is why [Interval efficiency](#interval-efficiency) item 3 is linear
  in the bound.
- **Neutral?** No, by design: it moves the makespan's lower bound.
- **Proof size** — the cut's derived row for every time point from the
  earliest window start to the bound's window end, plus the summing
  derivation. That is linear in the bound, not the horizon: about 357 lines
  per unit of the bound on the headline fixture (see [Proof
  performance](#proof-performance)).
  - Each of those rows also needs its donor rows recovered at that time
    point, unless something has already recovered them (recovery is
    memoised). That is about 7,200 lines per donor row on `pack001`.
  - On the `pack001` root proof, naming the makespan adds 411,205 lines
    (279,766 to 690,971) and 51 s of checking (9.3 s to 60.6 s).
- **What makes it silently weaker (this presolver's half).**
  - A member with no link loses the deadline's confinement, and so whatever
    energy only the deadline forced into the window. It keeps what its own
    start bounds force there. So a missing link can weaken the bound, and
    need not: with three pairwise-disjoint length-2 tasks, starts
    `x ∈ [0, 2]` and `y, z ∈ [0, 8]`, `m ∈ [0, 10]` and only `y` and `z`
    linked, the bound is `m ≥ 6`, the same as with `x` linked, while widening
    the unlinked `x` to `[0, 8]` lowers it to `m ≥ 4`. Proofs on and off
    agree, and the root proofs verify
    (`tmp/fd-codex-1005/sched/probes/mk.cc`; the tasks are made disjoint by
    one unit-capacity `Cumulative` per pair).
  - **With no linked member, nothing is certified on a feasible model.** The
    energies then do not depend on `m`, so a refuted `μ` would refute the
    root itself. The same probe with no links certifies nothing. That is why
    the end-variable spelling, which loses every link, certifies no bound on
    any of the 710 instances (see
    [Detection](#detection-and-its-failure-modes)).
  - A member whose length is any variable, even one with a single value,
    is left out by the runtime rule.
  - With proofs on, a makespan row with no label is skipped.
  - `certified_makespan_bound` reports the best `B` reached, and stays zero
    when no `B` beats the makespan's lower bound as it stands, which includes
    what the links imply and what an earlier presolver's initialiser has
    already raised it to. See [Relation to other
    families](#relation-to-other-families).
  - No note says which members went uncounted. See
    [Detection](#detection-and-its-failure-modes) for measured cases.
- **Tightness** — `ClaimHigherMakespanBound` is forwarded by this presolver.
  It is refused end to end by `rcpsp_dzn_inferred_cumulative_mutated`, and the
  derivation itself by `derived_cumulative_test`'s fixtures.

## Detection and its failure modes

What the scan looks for: posted `Cumulative`s of exactly that class, and
published projections. Then, within them, tasks matched by
`(start, length, presence)` as `IntegerVariableID`s. Every failure below is
silent in the sense that matters: the presolver posts something smaller or
nothing, every proof verifies, and every solution set is right. Each was
measured at `7e1c4178` with a probe that builds the same MiniZinc RCPSP
instance several ways (`tmp/fd-sched/inferred_cumulative/variants/`).

| Model built as | What the scan does | Measured effect |
|---|---|---|
| A capacity-one resource as `Disjunctive` (`examples/rcpsp`'s default `--machine disjunctive`, or `--unary disjunctive`) | Not a donor | 30 generated instances (`--size 14 --seed 1` to `30`): with the machine as a `Cumulative`, `L` higher on 13 and lower on none; certified bound higher on 5, lower on 1 |
| The MiniZinc library's own `cumulative`, which rewrites a resource where every pair (but the lightest) overloads into `disjunctive` before `fzn_cumulative` | Those resources are not donors | 41 of 480 KSD15_D instances have such a resource; `L` falls on 8 of them (`j3033_9`: 361 → 89) |
| Each donor given its own length variables of the same values | Columns do not match across donors, so no cross-resource lifting; and the lengths are variables, so the makespan rule counts none of them | `L` lower on 87 of 710 instances; multi-resource cuts on 57 instances against 389; **certified bound zero on all 710** (281 non-zero canonically) |
| Lengths as single-value variables, shared across donors | Columns match | Same cuts and `L`; **certified bound zero on all 710** (281 non-zero canonically; `pack007`: 41 → 0), since the makespan rule takes constant lengths only |
| End variables: `e = s + d` (`LinearEquality`), `m − e ≥ 0` | No link found (two hops, and a bound of 0) | Same cuts and `L`; **certified bound zero on all 710** (281 non-zero canonically; `pack007`: 41 → 0) |
| Makespan rows as `LessThanEqual{s + d, m}` | Found (comparison family) | Unchanged |
| A capacity as a view (`x + 1`) | Donor declined, counted | Nothing posted on `pack007` (`declined_irreducible_capacity = 3`) |
| A capacity as a plain variable, every task in every donor (zero heights included), heights as single-value variables | Handled | Unchanged (`converted_heights` counts the last) |
| Multi-mode (variable lengths and heights) | Columns kept at their guaranteed values | PSPLib j20 multi-mode, first 60 in lexicographic filename order: cuts on 28 (12 with a coefficient above one), certified bound on none |

**The front ends do not reach it at all**, which is the first failure mode.
Of the rest, the three that zero the certified bound on every instance
without any note are the ones a user is least likely to notice: per-donor
length variables, shared single-value length variables, and end variables.
`largest_capacity_bound` still reports `L`, so a reader comparing the two
sees a certification gap that is really a modelling spelling.

The probe's corpus counts above use the naive `[0, Σd − d]` windows for the
`L` rows (`L` does not depend on windows) and the `examples/rcpsp` windows
for the certified-bound rows.

**One more silent loss, from presolver order:** an `InferredDisjunctive`
added before this presolver, with the same makespan, can leave this one's
certified bound at zero; see [Relation to other
families](#relation-to-other-families).

## Evidence that it fired

The stats block is allocated whether or not the caller passes one, so it
reaches `Stats::components()` and `%%%mzn-stat` for any caller that prints
components. `examples/rcpsp --stats` prints nine of its fields by hand. The
fields that distinguish "ran and found nothing" from "did nothing":

| Field | Says |
|---|---|
| `donors_seen`, `tasks` | The scan found donors and columns. Zero `donors_seen` is the summary "no posted Cumulative to look at" |
| `covers_considered`, `lifting_subproblems`, `cuts_found` | Algorithms 1 and 2 ran |
| `cuts_posted`, `non_unit_cuts_posted` | Something was installed, and something InferredDisjunctive could not have found |
| `multi_resource_cuts_posted` | The bridging path ran |
| `restricted_rows_rebuilt` | A programme over fewer members was built. **Proofs on only**: zero with proofs off by construction |
| `largest_capacity_bound`, `certified_makespan_bound` | `L`, reported, and the bound derived. The second is zero when: no makespan was named; no member was linked or every member has a variable length; or the bound did not beat the makespan's lower bound as it stood, which an earlier presolver may already have raised |
| `dropped_*`, `declined_*`, `lifting_subproblems_over_budget` | Every way a candidate was lost |

The test's verified sweep asserts the accounting
`posted + uncertifiable + over_budget + declined + over_state_budget ==
found`. In the presolver's own fixtures, a cut posted is also recorded in the
proof (the marker comment; the `markers` lane asserts it).

**Expected counts on named instances**, at `7e1c4178`, defaults, proofs off:
- `pack007`: `donors_seen = 3`, `tasks = 15`, `covers_considered = 102`,
  `lifting_subproblems = 1258`, `cuts_found = 102`, `cuts_posted = 5`, all
  five non-unit and multi-resource, `L = 41`, certified 41 (with the
  `examples/rcpsp` model, whose optimum is 41).
- `examples/rcpsp/sample.dzn`: `L = 6`, the optimum.
  - `rcpsp_dzn_inferred`'s comment records it.
  - `rcpsp_dzn_inferred_cumulative_mutated` relies on it: its `+1` must
    exceed a schedule that exists.

**A note that fires on almost every default run.** When more than
`max_posted` cuts are found, the presolver adds an `Important` note: "Inferring
lifted cover cuts was cut short because a size limit was reached: N inferred
constraints were never posted; answers are still correct, but search may be
slower".
- **How often.** On 556 of the 710 MiniZinc-set instances, and in nearly every
  fixture of its own test.
- **Why it misleads.** The output budget is step L5 of the published
  procedure, not a limit the solver ran into, so the note reports the
  configuration working as designed.
- **What to do.** Demote it, or count against a budget the caller set
  (#1256).

## Can it weaken the model?

- **Solutions.** No cut is posted unless its own programme shows it holds at
  every 0/1 point the rows allow, so no solution is removed. Checked:
  - against brute force in the test (60 to 240 random single-row instances
    with proofs off; 25 one-to-three-row instances with proofs on; the
    optional-task, variable-argument, window-edge and two-resource fixtures);
  - by identical node counts with proofs on and off on Pack 1, 3, 5 and 7
    (168, 171, 388 and 119 recursions);
  - by every proof this audit ran verifying, apart from those that timed out.
- **Strength.**
  - **The pass.** It disables no donor and removes nothing from one. Each cut
    only adds a propagator, so it cannot lose strength.
  - **Proofs on against off.** Three paths let proofs-on infer less than
    proofs-off. At `AssertionLevel::Off`, none fired in any run here. The
    first does fire over a `Disjunctive2D` projection donor at assertion
    levels above `Off` (see [Proof-time state](#proof-time-state)).
    - **A decline at install,** which drops a cut that proofs off would keep.
      It happens when a member's flag is missing, a restricted programme is
      over the state budget, or a row donor has no row (`declined_by_install`,
      counted by the sweep). The decline itself is `cumulative.md`'s.
    - **A variable-length task with a non-constant start set aside** when
      its donor published no `end ≥ start + length` line
      (`cumulative_donor_view`). It then takes no
      part in any cover with proofs on, and it would with proofs off.
    - **A makespan row with no label,** skipped by `find_makespan_links` with
      proofs on, which costs that task its link (the deadline's
      confinement); the overlap its own start bounds force still counts.
- **The state budget binds on PSPLib J90 and J120.** In the fact-check's
  re-sweep, 102 of the 1,999 instances that finished inside the cap hit the
  budget. That is a lower bound, since killed runs hit it too: `J120_59_6`
  has 7 subproblems over, and `J120_19_1` has 38 over, 3 cuts dropped and 2
  posted. Either way the posted result is not the published procedure's.
  - **Subproblems over budget.** 57 instances had lifting subproblems over it,
    511 in all. Each over-budget subproblem leaves its task out of the cut. The
    later tasks then meet a smaller support, so they can lift *higher*: a
    different cut, not only a weaker one, and still valid.
  - **Cuts dropped unvalidated.** 81 instances had cuts dropped because the
    programme that would validate and certify them ran out of states
    (`dropped_over_state_budget`), 121 in all, so fewer than five were
    posted.
    - Such a cut should hold, since the lifting subproblems are exact.
    - But it was never checked, and it has no certificate.
    - For example `J120_14_3` drops 2 and posts 3, and `J120_58_4` posts 4
      of 5.
  - None of this happens on the 710 MiniZinc-set instances or in the suite.
    The verified sweep asserts that it does not.
- **The call budget.** When it runs out mid-lift, the cut is posted with the
  coefficients it has so far. That is weaker than the published procedure's,
  and visible only as `lifting_subproblems` reaching the budget.
- **The pin.** The `ia` at the end of each row's derivation pins the derived
  line to the intended inequality, coefficient for coefficient. A derivation
  that landed on a weaker true line would be refused there, which
  `ClaimTighterCapacity` and `ClaimTallerTask` show.

## Evidence

### Tests

- **`inferred_cumulative_presolver`** (`inferred_cumulative_test.cc`, plus the
  `_recovering` arm, which reruns it under `GCS_CUMULATIVE_ENCODING=both-recovering`
  so every recovered row is checked against the row the time-indexed encoding
  carries). One binary, seeded (`--seed=N`), 7 to 9 s. It covers:
  - the headline fixture refuted at the root, against 7 nodes without;
  - the differential pair against `InferredDisjunctive`;
  - a certified makespan bound (11 against an optimum of 13), and the same
    with comparison-family makespan rows;
  - a satisfiable twin;
  - solution preservation on three shapes;
  - the cardinality cut;
  - a variable capacity and a variable height, all heights variable, and a
    variable length;
  - the window edges (13 restricted rows);
  - time-table neutrality;
  - both budgets;
  - a random corpus against brute force with proofs off;
  - optional tasks (one resource, two, mixed) against brute force with proofs
    on and off, plus `ForgetPresence`;
  - the notes channel;
  - the verified sweep: 25 random one-to-three-row instances, with
    `restricted_rows_rebuilt`, multi-row and accounting assertions;
  - the OPB untouched;
  - the three mutations, on one row and on two rows, plus `BridgeWrongTask`;
  - the capacity-top lane (#1040) over 3/4, 7/8 and 15/16, through both
    `InferredCumulative` and `InferredDisjunctive`;
  - the markers.

  It does not use `solve_for_tests`, so the suite's default solution and node
  caps never apply to it. Every enumeration runs to completion.
- **`disjunctive_2d_presolver`**: the presolver over `Disjunctive2D`
  projections, against brute force, plus a mutation.
- **`cumulative_wide_horizon`**: horizon 10⁵, at most 200 per-time names.
- **`rcpsp_dzn_inferred`** (with `InferredDisjunctive`) and
  **`rcpsp_dzn_inferred_cumulative_mutated`**: end to end from a `.dzn` file.
- **VeriPB runs** in all of these. Honest proofs in the main harness are
  checked with `--force-checked-deletion`.
  - **Two lanes skip that flag.** The capacity-top lane and the markers lane
    check through `run_veripb`, without it. This audit re-ran the twelve
    capacity-top `InferredCumulative` cases with the flag: all twelve verify.
  - The mutation lanes also use `run_veripb`, which is the safe direction for
    a rejection.

**What the tests do not cover.**
- **Assertion levels.** No lane runs a derived `Cumulative` above
  `AssertionLevel::Off`, which is how #1234 went unseen.
- **Front ends.** None, since none can add the presolver.
- **The verified chain.** No lane runs `cake_pb_cp` on a proof with a derived
  cut. This audit ran it once by hand (above).
- **Long tasks with a makespan.** No lane names a makespan over tasks long
  enough for the bound to be large, where the root proof is linear in the
  bound and its check worse than linear.
- **Size.** No lane has more than five tasks or three rows with proofs, so
  multi-row frontiers stay tiny. The J120 CPU pathology is invisible to the
  suite.
- **Checking time.** No lane checks proof size or VeriPB time. That is how
  #943 made the reference certificate 36 times slower to check (0.79 s to
  28.4 s), and later merges took it to 35.5 s, without a red lane.
- **Detection spellings.** Separate length variables per donor, end-variable
  makespan links, and the MiniZinc library's rewrite into `disjunctive`.
  - Correctness is not at stake in any of them.
  - The effect is the measured weakening above.

### Benchmarks and examples

- **In-repo:** `examples/rcpsp` (`--dzn`, `--mm`, `--file`, `--jss`, or
  generated). `sample.dzn` is the end-to-end fixture.
- **Instance sets:** the MiniZinc RCPSP collections under
  `/cluster/ciaran/claude/scheduling-instances/rcpsp/` (Pack, Pack_d, BL,
  KSD15_D, la_x, PSPLib j30 to j120). The multi-mode PSPLib sets are under
  `multimode/`.
- **For CPU benchmarking of the presolver itself:** PSPLib J120 with proofs
  off, run serially (the times move several-fold under load). `J120_59_6`
  spends 57 s in the pass. Pack, BL and KSD15_D take
  milliseconds. la_x posts nothing: unit demands under capacities 2 and 3 make
  every cut dominated by its own row.
- **For proof verification:** Pack, deadline one below the certified bound,
  which is the August artefact's shape. At `7e1c4178`, `pack001`'s checks in
  35.5 s serially. The batch below, run 24 at a time, took up to half an hour
  per proof, so take a handful. **Never** run Pack_d with proofs and a
  makespan uncapped: its root proofs are 1.4 to 5 GB and did not verify in
  30 minutes, and a search run writes 20 to 40 GB in five minutes.

Collection-level counts for the 710 MiniZinc-set instances, proofs off,
defaults, at `7e1c4178`. The probe uses the same model and windows as
`examples/rcpsp`: horizon from the greedy schedule, starts in
`[head, horizon − d − tail]`.
- **Domain-independent counts.** Cuts and `L` depend only on lengths and
  demands.
- **The certified bound.** It counts only when it beats what the makespan rows
  already imply, so tighter windows give fewer non-zero ones. With the naive
  `[0, Σd − d]` windows it was non-zero on 475 instances.

| Set | Instances | With a cut | With a multi-row cut | Certified bound > 0 | Certified < `L` | Certified > `L` |
|---|---:|---:|---:|---:|---:|---:|
| Pack | 55 | 55 | 55 | 55 | 0 | 0 |
| Pack_d | 55 | 55 | 55 | 51 | 0 | 0 |
| BL | 40 | 40 | 40 | 26 | 1 | 0 |
| KSD15_D | 480 | 438 | 239 | 149 | 11 | 70 |
| la_x | 80 | 0 | 0 | 0 | 0 | 0 |

PSPLib single-mode, 2,040 instances, same probe.
- **Concurrency.** Eight jobs at a time on eight cores, each pinned, with a
  120 s cap per instance. 37 instances hit the cap (3 J90, 34 J120) and are
  left out of every column, so the Max column understates the tail.
- **Load-sensitivity.** These times move a lot with load. `J120_58_4` is
  16.9 s here and 15.9 s serially, but the fact-check's 14-way re-sweep timed
  it at 74.6 s. Read the distribution's shape, not its values.

| Set | Instances | With a cut | Multi-row | Median wall | 90th percentile | Max | Over 10 s |
|---|---:|---:|---:|---:|---:|---:|---:|
| J30 | 480 | 476 | 351 | 0.014 s | 0.032 s | 0.17 s | 0 |
| J60 | 480 | 478 | 351 | 0.045 s | 0.91 s | 11.1 s | 1 |
| J90 | 477 | 476 | 345 | 0.21 s | 21.5 s | 117.6 s | 80 |
| J120 | 566 | 566 | 416 | 0.58 s | 32.5 s | 111.7 s | 142 |

### CPU performance

Measured at `7e1c4178`, 2026-10-04, fataepyc-08 (AMD EPYC, Release build),
pinned single core, `GLIBC_TUNABLES` pinned, proofs off. The probe stops at
the root, so `wall` is presolve plus root propagation.

| Instance | Tasks | Covers | Subproblems | Cuts | Wall with | Wall without |
|---|---:|---:|---:|---:|---:|---:|
| `pack007` | 15 | 102 | 1258 | 5 | 0.016 s | — |
| PSPLib `J30_10_1` | 30 | 103 | 2777 | 5 | 0.0069 s | 0.0004 s |
| PSPLib `J120_10_1` | 120 | 31 | 3549 | 5 | 0.354 s | 0.0012 s |
| PSPLib `J120_59_6` | 120 | 57 | 6441 | 5 | 57 s | — |

`J120_59_6` measured 56.7 s and 57.2 s in two serial runs (the fact-check got
58.2 s). The PSPLib table under [Benchmarks](#benchmarks-and-examples) gives
the distribution under load: 222 of the J90 and J120 instances took over
10 s, and 37 more over 120 s.

**Where the time goes.** On `J120_59_6`, `perf` puts about 94% of the time in
`build_programme`, the lifting subproblems' dynamic programme. Nearly all of
that is `reduce_to_frontier`: the frontier sweep is all-pairs per layer, and
over four resources the layers are wide Pareto sets.
- **The state budget does not stop it.** The budget (100,000 states per
  programme) counts states built, not comparisons. On this instance it cut
  off only 7 of 6,441 subproblems, so nothing stops a programme that is merely
  slow.
- **A cheap piece of the cost.** In the worst case, every pair in the sweep
  is first compared for equality (`other != state`, the defaulted `==` over
  the whole state: weights, then profit) before the cover test. `any_of` stops
  at the first covering state, so typical pairs are fewer. `perf`'s sample
  attribution put 41% of cycles there in one reading, and about 62% in
  another.
  - **Measured.** In a scratch build, replacing that comparison with an index
    comparison took `J120_59_6` from 57.2 s to 48.2 s serially, a 16% saving.
    The output was the same.
  - **The fact-check's measurement.** It got 415.30 G to 261.27 G
    `instructions:u` (−37%) and −15.7% in cycles and time, with identical
    counters and note (only the wall time differs; the cut coefficients were
    not printed, so they were not compared).
  - **Sample share is not a saving.** The sample share, the instructions
    saved and the time saved are three different numbers, and only the last
    is the saving. Why the instructions removed are cheaper than average was
    not investigated.
  - **The rest.** It is the quadratic sweep itself (#1255).

**What the corpus does not exercise.** No instance here has a `Disjunctive2D`
donor or optional tasks. The time is all in Algorithm 2, not detection.

**Search effect.** On the Pack instances the certified bound is usually the
optimum, so with the presolver the search only has to find a schedule:
`pack007` solves to optimality in 119 recursions. Without the presolver, the
same probe model times out at 300 s (the probe's horizon is the greedy
schedule's, and the model has no other lower-bounding argument). That is a
statement about the bound, not about the derived propagator. Not compared
against Gecode, Choco or ACE (#868): none of them has this inference, so an
identical-search-tree comparison does not exist.

### Proof performance

All at `7e1c4178`, 2026-10-04, fataepyc-08, VeriPB 3.0.2 with
`--force-checked-deletion`. "Root" proofs stop at the first search node, so
they contain the presolver's install-time rows, the makespan bound and root
propagation. Metric: lines and bytes of `.pbp`, and VeriPB wall time.
Batch figures were taken 24 jobs at a time on 24 cores and are rough; the
serial ones are marked.

**What the presolver adds, at the root.** The probe's `pack001` and `pack007`
models (no deadline), serial, pinned:

| Instance | Configuration | Lines | VeriPB |
|---|---|---:|---:|
| `pack001` | no presolver | 39 | 0.11 s |
| `pack001` | presolver, no makespan | 279,766 | 9.3 s |
| `pack001` | presolver and makespan | 690,971 | 60.6 s |
| `pack007` | no presolver | 61 | 0.17 s |
| `pack007` | presolver, no makespan | 102,018 | 2.0 s |
| `pack007` | presolver and makespan | 467,952 | 44.1 s |

So on these two, the makespan bound is 60 to 78% of the lines and 85 to 95%
of the checking. Without the presolver the root proof is just the
definitions.

**What #943 cost these certificates.** The certificate the August artefact used
(`examples/rcpsp --dzn pack001.dzn --infer-cumulative --deadline 20 --prove`,
`s VERIFIED UNSATISFIABLE` throughout):

| Commit | Commit date | Lines | MB | VeriPB |
|---|---|---:|---:|---:|
| `72861aa5` | 2026-08-11 | 172,386 | 20 | 0.77 s |
| `68332306` (before #781) | 2026-09-19 | 173,779 | — | 0.79 s |
| `3f499623` (#781 merged) | 2026-09-19 | 173,779 | — | 0.78 s |
| `b4eeda20` (#839 merged) | 2026-09-19 | 173,779 | — | 0.79 s |
| `5f2ca305` (#943 merged) | 2026-09-19 | 658,477 | — | 28.4 s |
| `42aa8598^` | 2026-09-30 | 658,477 | — | 28.7 s |
| `42aa8598` (#1129 merged) | 2026-09-30 | 658,477 | — | 34.0 s |
| `736d529c` (#1134 merged) | 2026-09-30 | 568,680 | — | 38.4 s |
| `7e1c4178` | 2026-10-03 | 568,680 | 48 | 35.5 s |
| `7e1c4178`, `GCS_CUMULATIVE_ENCODING=time-indexed` | 2026-10-03 | 83,982 | — | 0.38 s |

Each commit was built and run on fataepyc-08, serially, on one pinned core.
- **The jump is #943.** `5f2ca305` is that merge, and its first parent
  `b4eeda20` is the last cheap row: 0.79 s to 28.4 s, 36 times (the
  fact-check's re-run of `5f2ca305` gave 29.0 s). Later merges added the rest,
  to 34.0 s at #1129 and 38.4 s at #1134.
- **The encoding is the cause, not anything this presolver does.** The last
  row selects the time-indexed encoding the test arms still compile, on
  today's code. It has about a seventh of the lines (83,982 against 568,680)
  and a ninety-third of the checking time.
- **What the cost is, exactly.** It is the per-recovery cost of the donor
  rows, not repetition, since recovery is already memoised per (donor, time
  point).
  - This proof makes exactly 60 recoveries (3 donors × 20 time points).
  - 432,684 of its lines name `ckp*` flags, about 7,200 lines per recovered
    row.
- **The makespan bound is part of it, not most of it.** With
  `--infer-makespan-bound=false` the proof is still 371,497 lines, against
  61,545 under the time-indexed arm (6.0 times).
- **What was known at the flip.** #780's own measurement put the recovery's
  cost at 1.3 to 2.4 times the proof on search-heavy instances, for posted
  constraints. It did not measure checking time, or derived cuts.
- **What the fix cannot be.** Ciaran's rule is one OPB encoding per
  constraint, so the time-indexed arm is a diagnostic, not a way out. The fix
  belongs in the recovery's proof, which is `cumulative.md`'s (#1254
  has the measurement).

The search proofs of this audit's batch, with the presolver: 10 Pack, 5 BL
and 5 KSD15_D instances, with a 300 s solve cap.
- **Pack:** 5 of 10 solved to optimality, with 470,227 to 2,605,010 lines and
  131 to 1,698 s to check. The other five hit the cap having written 54 to
  141 M lines, which were not checked.
- **BL:** 4 of 5 solved, 68,450 to 1,304,900 lines, 3 to 415 s to check. The
  fifth wrote 98 M lines unchecked.
- **KSD15_D:** all 5 solved, 36,799 to 1,107,375 lines, 1 to 944 s to
  check.
- **Pack_d:** the root proof alone was 16 to 59 M lines (1.4 to 5.0 GB), and
  took 0.5 to 5 minutes to write.
  - The two under 3 GB (`pack001` and `pack003`) did not verify in
    30 minutes.
  - The other three were not tried.

These cannot be set beside `certified-makespan-bounds.md`'s August figures.
There the median `.pbp` was 77 MB, and the largest, 4.7 GB on Pack_d, checked
in 146 s. That was a different commit and a different solve shape, and the
table above is why the two disagree.

**Scaling with the bound, not the horizon.** The headline fixture: one task
of demand 5 and three of demand 2, capacity 5, lengths `3k, 5k, 5k, 5k`, so
`L = 10.5k`. It is stopped at the root.
- **First table.** The horizon is `13k`, so the lengths and the horizon
  scale together.
- **Second.** The lengths are fixed and the horizon alone is multiplied.

| `k` | Horizon | Lines, no makespan | Lines, with makespan | VeriPB, with makespan |
|---:|---:|---:|---:|---:|
| 1 | 13 | 798 | 4,091 | 0.02 s |
| 10 | 130 | 798 | 37,641 | 0.41 s |
| 100 | 1,300 | 798 | 374,871 | 37.3 s |
| 1000 | 13,000 | 798 | 3,747,171 | killed after 53 min (and after 20 min in the fact-check) |

| `k` | Horizon | Lines, with makespan | VeriPB |
|---:|---:|---:|---:|
| 1 | 13 | 4,091 | 0.02 s |
| 1 | 1,300 | 4,124 | 0.03 s |
| 10 | 130 | 37,641 | 0.41 s |
| 10 | 13,000 | 37,812 | 0.52 s |

All serial on one pinned core, except the `k = 1000` check, which ran beside
other jobs.
- **Lines.** About 357 lines per unit of the bound. They grow with the bound
  and hardly at all with the horizon. The derived constraint's makespan
  initialiser sums every row from the earliest window start to the bound's
  window end (`derived_cumulative.cc`), so the count follows the bound, which
  follows the task lengths.
- **Checking.** It grows faster than the lines: 91 times the time for ten
  times the lines, from `k = 10` to `k = 100` (the fact-check measured 74 to
  106 times).
- **Whose.** That is the makespan rule's derivation (`cumulative.md`'s),
  paid here because this presolver is what names the makespan.

**Assertion levels.** Not measured:
- over posted donors, under the default start-checkpoint encoding, the proof
  is currently rejected above `Off` (#1234);
- over a projection donor, every cut is declined, so there is nothing of this
  presolver's to measure.

## Status, gaps, and next steps

### Proof-logging gaps

- Nothing the presolver infers is unjustified: every row is derived, the
  makespan bound is derived, and nothing is asserted at `Off`.
- Propagation strength does not change with proof logging, except through
  the three proofs-on paths under [Can it weaken the
  model?](#can-it-weaken-the-model): an install decline, a variable-length
  task with no published end line, and an unlabelled makespan row.
  - At `Off`, none was seen in any run here.
  - Above `Off`, the install declines every cut over a `Disjunctive2D`
    projection donor.
- Above `AssertionLevel::Off`, over posted donors, every proof with a
  derived cut is rejected under the default start-checkpoint encoding
  (#1234).

### Known limitations

- You cannot use it from MiniZinc, XCSP3, `.scp` or Python; only from C++
  and `examples/rcpsp`.
- A capacity-one resource posted as `Disjunctive` is invisible to it.
- The same task must be spelled the same way on every resource (same start
  variable, same length variable or constant, same presence) for a cut to
  span resources.
- With a makespan named, a task with any variable length contributes no
  energy to the makespan bound. A makespan reached through end variables
  leaves every member unlinked, so on a feasible model nothing is certified.
  Either way the reported `certified_makespan_bound` can be zero while
  `largest_capacity_bound` is not.
- On instances with 100+ tasks and several resources, the pass can take
  minutes with proofs off.
- With a makespan, the root proof grows linearly with the makespan bound (so
  with the task lengths), and checking it grows faster. Pack_d proofs do not
  check in reasonable time at the moment.
- With a makespan, adding `InferredDisjunctive` before this presolver can
  leave this one's certified bound at zero, since the earlier one has already
  raised the makespan.
- On PSPLib J90 and J120 the state budget sometimes leaves a task out of a
  cut, or drops a cut it could not afford to validate. So fewer or different
  cuts are posted than the published procedure would post.
- Root-level only: nothing is lifted during search.
- It prints an `Important` "cut short" note on most runs, when nothing was cut
  short in any sense a user should act on.

### Next steps

1. **Make a derived cut's rows cheap to check under start-checkpoint**
   (#1254). Since #943 the reference certificate is 6.8 times the
   lines and 93 times the checking time it is under the time-indexed arm.
   - **Why it comes first.** Any proof-size or checking-time claim for the
     paper about these presolvers has to be re-measured after it.
   - **Where the fix lives.** The recovery's proof, which is `cumulative.md`'s.
   - **What to attack.** Recovery is already memoised per (donor, time
     point), so the target is the cost of one recovery: about 7,200 lines
     each on `pack001`, all left at `Top`. Two things to try:
     - hinting its RUPs, by analogy with the programme replay's own
       sixfold-to-fourteenfold gain from hints (#681);
     - deleting the `ckp*` scaffolding once the row is pinned.
   - **Cost.** Unknown until one recovery is profiled.
2. **Bound the lifting programme's cost** (#1255). In order of
   effort:
   - drop the vector equality test from the sweep's inner loop, which saves
     16% on `J120_59_6`, measured;
   - make the state budget count pair comparisons;
   - replace the all-pairs frontier sweep with a sort-based one.
     - It builds the same states, so it does not change where the budget
       binds (states are counted before the sweep).
     - It is a day's work.
     - What it would buy on J120 is not measured; the target is the J30 to
       J60 regime of well under a second.

   Reusing layers across lifting subproblems does not work as things stand:
   each runs on capacities minus the member's demand, with its own binding
   rows and profit ceiling. It would need a capacity-independent
   formulation.
3. **Name a makespan over long tasks in a lane,** so the bound and the root
   proof are large. Then decide what the makespan derivation's superlinear
   checking should cost. That is the runtime rule's, in `cumulative.md`; the
   lane is cheap.
4. **Front-end flags** for `fzn-glasgow` and the XCSP3 solver. Small, but
   only worth doing with item 5. And note that the MiniZinc library will hide
   resources it rewrites into `disjunctive` unless `glasgow`'s `mznlib`
   overrides `cumulative.mzn`, which under #1006's rules is a shape lane, not
   a clever front end.
5. **Say when detection degrades** (#1257):
   - a `General` note when a makespan is named and some cut members have no
     link, or are left out for a variable length;
   - a count of tasks that look the same but did not match across donors.

   It turns the silent rows of the detection table into visible ones. Cost:
   hours.
6. **Demote the "cut short" note** (#1256) to `General` when only
   the output budget bit, or rephrase it. Cost: minutes.
7. **Small:** clamp `with_maximum_capacity`'s `c + 1`, and update the class
   comment in `inferred_cumulative.hh` that still says donors with optional
   tasks are excluded (#1152 lifted that).
8. **Name the cut in the installed constraint's hints.** Today its `a` lines
   say `constraint_id unnamed`, so a hints-only justifier cannot tell one
   derived cut from another, or from another presolver's, without the marker
   comment. Cost: small, once a naming scheme for installed constraints is
   agreed for all presolvers.
9. **#703** (Sidorov's early stop, correctly gated) stays open and unchanged
   by this audit.

## Prior art

- **Inference.** Sidorov (CP 2026) proposed inferring implied cumulative
  constraints by cover enumeration and lifting, and this presolver is a
  reproduction of his Algorithms 1 and 2. The deliberate departures are:
  - the corrected `inv_A_longest` line;
  - every cover lifted, with no visited-cover rule (#726);
  - no early stop (#703).

  Lifting is classical: Zemel (1978) for sequence dependence, Balas (1975)
  and Wolsey (1975) for lifted cover inequalities.
- **Certification.** Demirović et al. (CP 2024) certified knapsack dynamic
  programmes in VeriPB, and the replay here is their one-sided form. As far
  as this audit knows, nobody has certified a *lifted cover cut*, or an
  implied cumulative constraint, in any proof system before. What is new:
  - using the lifting procedure's own programme as the certificate, so that
    no validated cut can fail to be derived: validation and certificate are
    the same programme. (That `cuts_uncertifiable`, the count of cuts the
    programme refuted, is zero rests on the lifting being exact, which is a
    separate point.) Cuts the state budget stops from being validated are
    dropped instead, so the certified set is not always the whole of what
    the procedure infers;
  - carrying several resources' rows onto one set of flags;
  - deriving the per-time rows lazily (#1130).

## Further reading

- [`inferred-cumulative.md`](../inferred-cumulative.md): the long design note.
  It covers:
  - Algorithms 1 and 2 and where the paper and its code disagree;
  - the visited-cover rule and why it went;
  - Equation 4 over every resource;
  - the dynamic-programme certificate, the bridges and dominated states;
  - window-edge restriction;
  - proof size and hinting, with the August measurements, which no longer
    describe `main` (see [Proof performance](#proof-performance)).
- [`certified-makespan-bounds.md`](../certified-makespan-bounds.md): the
  makespan bound's derivation and the August Pack / Pack_d sweep.
  - Until #1265 its argument confined every task to `[lo, μ)`. That is the
    special case: an unlinked task counts the overlap its start bounds force
    (see the makespan rewrite).
  - Its claim that a comparison-family makespan row "is not matched" is out of
    date: `find_makespan_links` has matched the comparison family since
    `bd966a2b`.
- [`inferred-disjunctive.md`](../inferred-disjunctive.md): the capacity-one
  stage.
- [`cumulative-proof-logging.md`](../cumulative-proof-logging.md): the
  encoding the derived rows are recovered from.
- [`../constraints/cumulative.md`](../constraints/cumulative.md): the derived
  constraint's runtime rules.

## Developer commentary

None beyond the design note.
