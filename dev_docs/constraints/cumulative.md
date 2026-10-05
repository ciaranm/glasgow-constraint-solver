# `Cumulative`: tasks sharing a renewable resource of bounded capacity

> **Maturity** production ·
> **Audited** 2026-10-04 at `7e1c4178` ·
> **Open issues** #1223 (an overflow in the overload check's profile sum),
> #705 (four propagation and proof-size costs, among them the time-table scans
> being `O(domain × length)`), #742 (edge-finding's `O(n³)` scan), #1126
> (Cloutier and Quimper's Profile for the elastic rungs), #755 (energetic
> edge-finding's cache key), #550 (the optional-task interaction of the
> elastic rungs, parked), #833 (the horizon-sized arrays), #700 and #829 (the
> makespan bound's window and its `deview` fixture), #868 (cross-solver
> comparison), #364 (an incremental profile). Filed by this audit: #1234
> (derived Cumulatives above `AssertionLevel::Off`), #1235 (three more
> overflow sites), #1236 (the elastic conflicts are not counted), #1237 (a
> time-table push's certificate is linear in the distance), #1238 (the
> test-only encodings are reachable), #1239 (a variable height's upper bound
> is never lowered). Filed from the Codex review: #1267 (the makespan
> initialiser scans the whole candidate horizon). Tracked under #871 and #976.

`Cumulative(s, d, r, b)` says that at every time point the summed demand of
the tasks running then is at most the capacity, where task `i` runs over
`[s_i, s_i + d_i)` with demand `r_i`. It is the largest family in the solver
and the most heavily certified: one propagator carries the whole standard rule
ladder — time-tabling, the overload check and its three strengthenings,
edge-finding and its two strengthenings, and not-first / not-last in two
detections — and **every inference it makes is proved**, over optional tasks
and over variable lengths, heights and capacity. The same propagator also runs
over constraints that are not in the model at all: the *derived* Cumulatives
that three presolvers install, and each axis of a `Disjunctive2D`. This
document covers both, because the runtime machinery is the same.

Five things to know before touching it.

- **There is exactly one OPB encoding, and it is the start-checkpoint one**
  (#780). Per ordered pair of tasks there are three flags saying whether `i` is
  running when `j` starts, and per task there is one row capping the load at
  that start. That is `6n(n − 1) + n` rows, and no row mentions a time point.
  Every rule still argues over per-time capacity rows `C_t`, which are
  **recovered inside the proof** from the checkpoint rows, the first time
  something cites them, at about `2m³` lines for `m` tasks that can run at `t`.
  The per-(task, time) flags those rows mention are named and defined lazily
  too (#1111). Nothing about a time point is written up front.
- **Only time-tabling and the overload check (with its profile term) are on
  by default.** Everything else is behind `CumulativeRules`, and no frontend
  turns any of it on. What a MiniZinc or XCSP3 model gets is time-tabling plus
  (TTOC).
- **The reason is the whole scope, every time.** Every inference gives the
  bounds of every start, plus every variable length's, height's and the
  capacity's, plus a `p = 1` literal per task known to be present. The reason
  is materialised lazily, so proofs-off pays nothing. But it is not minimal,
  and an external justifier has to trim it.
- **The cost is horizon-shaped, not domain-shaped.** The propagator builds an
  array over the current span of the tasks' windows on every call. The
  time-table bound scans walk start values one at a time, testing each over
  the task's length (#705). One time-table push's certificate is a chain whose
  length is the push distance over the task's length. At length 1 and a push
  of 5,000 that is one inference with 295,048 lines, 24.6 MB and 10.3 s of
  VeriPB, measured below. None of this shows on scheduling benchmarks, whose
  horizons are short.
- **At `Definitions`, `Inferences` and `Backtracking`, a derived Cumulative
  over a posted `Cumulative` makes the proof unreadable**, under the shipped
  start-checkpoint encoding, whenever a presolver actually installs one. The
  donor publishes its row deriver at every level but its flag definer only at
  `Off`. So a recovered row cites flags that were never defined, and VeriPB
  stops with a syntax error.
  - Under the test-only `time-indexed` encoding the derived rows build on the
    donor's model rows instead, and the same runs verify `UNDER ASSERTIONS`.
  - A presolver that strengthens nothing installs nothing, and its proof
    verifies.
  - **Over a `Disjunctive2D` projection donor** the symptom is different, and
    does not depend on the encoding. `Disjunctive2D` gates both its definer
    and its row family at `Off`. `InferredDisjunctive` and
    `InferredCumulative` then decline at install, so nothing is posted. The
    proof verifies, and the presolver contributes less than it does at `Off`
    or with proofs off. On the presolver test's `bars` instance,
    where it finds something to strengthen, `CumulativeStrengthening` instead
    **throws a `ProofError`**, printed as "unexpected problem: cumulative
    strengthening: the donor has no capacity row at time 0, which cannot
    happen…" (`cumulative_strengthening.cc:512`), so the solve aborts.
    On that test's `strip` instance it posts nothing and does not throw.
  - Lifting the one gate is not enough. A variable height's order literal is
    then cited and never defined at `Inferences` (#1210's class).
  - Nothing in the suite runs at those levels. This is #1234, and the
    one finding here that bites a supported configuration.

The design and every derivation are in
[`cumulative-proof-logging.md`](../cumulative-proof-logging.md), which stays as
this family's long note. This document audits the implementation
against it, and it is where the rule catalogue, the measurements and the
triage live.

## What it is

### Semantics

`Cumulative(starts, lengths, heights, capacity)` and the optional-task form
`Cumulative(starts, lengths, heights, presences, capacity)`. Task `i` is
*active* at time `t` iff `starts[i] ≤ t < starts[i] + lengths[i]` (and, in the
optional form, `presences[i] = 1`). The constraint holds iff, at every integer
`t`,

```
Σ_{i active at t} heights[i]  ≤  capacity .
```

- **Arguments.** Starts, lengths, heights and the capacity may each be a
  variable or a constant (`ConstantIntegerVariableID`). The convenience
  constructor takes `vector<Integer>` lengths and heights and an `Integer`
  capacity. A presence must be a variable whose domain lies within `{0, 1}`, or
  the constant 0 or 1. The constant 1 is the same constraint as the
  non-optional form and encodes identically. The constant 0 drops the task.
- **Sign.** A negative constant length, height or capacity throws
  `InvalidProblemDefinitionException` at construction. A variable one whose
  initial lower bound is negative throws in `prepare()`. Starts may be
  negative.
- **Degenerate cases.** A task whose length or height can only be zero, or
  which is constantly absent, never loads the resource and is dropped
  (`_active_tasks`). If none is left, `prepare()` returns false and nothing is
  installed, which is correct, since the constraint is then vacuous. An empty
  array is that case. A zero capacity with a positive-height task is enforced
  like any other overload. Aliased starts (`x, x`), offset views (`x, x + 1`)
  and negated views (`x, −x + 4`) all give the brute-force answer with
  verifying proofs (`tmp/fd-sched/cumulative/alias/`). That holds under the
  default rules, and with elastic, knapsack, edge-finding, energetic
  edge-finding and not-first / not-last on.
- **What it is not.** There is no `end` argument. MiniZinc's `cumulative` has
  none either, and a model that wants `e = s + d` posts it separately, which is
  where the presolvers' makespan links come from.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Cumulative` (four arguments) | `fzn_cumulative` ✓ | `cumulative` ✓ | `frontend gap` (no issue)[^cpmpy] | `cumulative` ✓ | variable `s`, `d`, `r`, `b` in both frontends[^fe] |
| `Cumulative` (with presences) | `fzn_cumulative_opt` ✓[^opt] | `n/a` | `frontend gap` (no issue)[^cpmpy] | `cumulative_optional` ✓ | outside the `cake_pb_cp` chain[^optcake] |

[^fe]: MiniZinc's `mznlib/fzn_cumulative.mzn` forwards straight to
    `glasgow_cumulative`, which `fzn-glasgow` posts as
    `Cumulative{starts, lengths, heights, capacity}`. Constants pass through as
    constant variables. XCSP3's `post_cumulative` handles all four
    constant/variable length × height overloads, and a capacity that is an
    integer or a variable under the `le` condition. Any other condition reports
    `s UNSUPPORTED`, with a message citing #147, which is closed. Neither frontend sets a `CumulativeRules` flag, and
    neither installs a scheduling presolver: `fzn-glasgow` installs only
    `DifferenceLogic`. So a frontend model gets time-tabling and (TTOC), as
    the matrix's footnote already says.
[^opt]: `fzn_cumulative_opt` splits each `var opt int` start into a deopted
    start and an `occurs` Boolean. An absent constant start becomes `0`.
    XCSP3 has no optional-task cumulative.
[^optcake]: `constraint_type()` is `cumulative_optional` for the optional form,
    so that the verified-encoding chain names the gap rather than silently
    mismatching: `cake_pb_cp` has no encoder for it (see
    [Cake conformity](#cake-conformity)).
[^cpmpy]: `gcspy` (`python/gcspy.cc`) has no Cumulative binding at all, so
    CPMpy's GCS interface cannot post one natively. Whether CPMpy decomposes
    `Cumulative` before it reaches GCS was not checked. No issue is filed.

### Options

**`with_rules(CumulativeRules)`** chooses the propagation rules. It never
changes the OPB, and never changes the solutions. A test can use it to
attribute an inference to the rule that made it, and a fixture can show a rule
is load-bearing by watching the search get worse without it. The ten flags
and their defaults:

| Flag | Default | Rule(s) it enables | Why that default |
|---|---|---|---|
| `time_table` | on | `time-table-lower`, `time-table-upper`, `presence-falsification` | the standard |
| `overload` | on | `overload`; **and the window sweep every rule below runs in** | cheap, quadratic sweep |
| `profile_overload` | on | `overload-profile` | (TTOC); needs `overload` |
| `elastic_overload` | **off** | `overload-elastic` | (TTHE-OC); `O(n²·horizon)` sweep (#1126); needs `overload` |
| `knapsack_overload` | **off** | `overload-knapsack` | (KAOC); turns the elastic machinery on itself; per-time bitset; needs `overload` |
| `edge_finding` | **off** | `edge-finding-lower`, `edge-finding-upper` | `O(n³)` scan (#742); needs `overload` |
| `time_table_edge_finding` | **off** | `time-table-edge-finding` | (TTEF); strengthens what edge-finding (and not-first / not-last) charge, so it needs one of them |
| `energetic_edge_finding` | **off** | `energetic-edge-finding` | subsumes TTEF and takes precedence; likewise needs edge-finding or not-first / not-last |
| `not_first_not_last` | **off** | `not-first`, `not-last` | "fires in the millions, buys 0.3%" (header); needs `overload`, **not** `edge_finding` |
| `not_first_not_last_published` | **off** | `published-not-first`, `published-not-last` | switches `not_first_not_last`'s detection to the published one; does nothing on its own |

**Every rule below `profile_overload` runs inside the overload sweep**, which
is gated on `overload`, a constant capacity, and at least one eligible task
(`cumulative.cc:2093`). With `overload` off, edge-finding, not-first / not-last
and the elastic rungs never run whatever their own flags say. On a
library-level replica of `Bl2019`
(`tmp/fd-sched/factcheck/cumulative/rules/bl.cc`, re-run), `overload` off with
edge-finding, not-first / not-last and the elastic rung requested shows all
their calls at 0. The search is 59,452 recursions against the default's 985,
since the overload check itself is gone too. The implications "not-first /
not-last implies edge-finding" and "published implies not-first / not-last" are
the `examples/rcpsp` driver's (`rcpsp.cc:855-857`), not the library's. In the
library, `not_first_not_last` alone fires with edge-finding's calls at 0, and
`not_first_not_last_published` alone does nothing.

`time-table-overflow` is not switched off by `time_table`. That scan is what
makes the propagator a checker at a fully assigned state, and gating it
accepted an overloaded assignment once (#1037).

The doc comment on `CumulativeRules` still says "All three are on by default",
from when there were three. It is stale. Which defaults are *right* is out of
this arc's scope (Ciaran, 2026-09-20: what matters is that every technique is
certified, not which are worth having), but the ladder below measures them.

**`with_encoding(CumulativeEncoding)`**, and the `GCS_CUMULATIVE_ENCODING`
environment variable it overrides, **do** change the OPB. There are three
arms:

- `StartCheckpoint`, the default and the only one that ships.
- `TimeIndexed`, the old per-time block.
- `BothRecovering`, both blocks plus an eager recovery of every per-time row,
  checked against the row the model still carries.

The rule is one encoding per constraint, because `cake_pb_cp` re-derives the
OPB from the `.scp` and cannot follow a per-constraint choice. The other two
arms exist only as test fixtures, and the `BothRecovering` arm is the only
thing that catches a recovery which derives a valid but wrong row. The header,
`gcs/CMakeLists.txt` and the arm's ctest comment all say no solve can select
them. **That is not quite true.** Both are public API, and the environment
variable is read by every binary.
`GCS_CUMULATIVE_ENCODING=time-indexed ./build/rcpsp --prove` writes the per-time
block (18 `cap_` rows on `examples/rcpsp/sample.dzn`, against 8 checkpoint rows
by default), and the proof verifies against its own OPB. Nothing is unsound.
But a user can produce a model that cake would not reproduce, and
`with_encoding` belongs in `innards` beside the mutations
([Next steps](#next-steps)).

**`with_proof_mutation` and `with_presence_mutation`** corrupt one step of a
derivation. They are for tests only, and their types live in `innards` (#669).

There is no `with_consistency()`, and no `consistency::` tag applies.

### Variable kinds and views

- **Starts** may be any `IntegerVariableID`, views included. Time-tabling
  takes them as they are: the flags are reified on the view's own order
  literals. Only a task whose start is a plain `SimpleIntegerVariableID` with
  an order encoding (not `{0, 1}`) is *eligible* for the energy rules (the
  overload family, edge-finding and not-first / not-last), because the
  window-energy lemma bridges the flags to the start's order literals
  (`prepare_cumulative_overload_check`). An ineligible task still counts
  through the profile term. That is a weakening, not a gap.
- **Lengths** may be views for time-tabling. The energy rules take a plain
  variable or a constant, and count a variable length at its live lower bound
  (#689). A task whose start and length both vary has `after` reified on
  `s + l`, which no RUP reaches from the operands' bounds. So the proof
  introduces an `end = s + l` proxy, inside the proof only, and pins through it.
- **Heights.** A view height **throws `UnimplementedException` with proofs
  on** (`cumulative.cc:370`): a view has no bits of its own for the
  checkpoint encoding's contribution conjunctions. With proofs off a view
  height works. Neither frontend produces one. A variable height is counted at
  its lower bound throughout.
- **Capacity** may be a variable or a view. The overload family and
  edge-finding run only when it is a **constant**. With a variable capacity
  the conflict `pol` would be left with a `(b − a)·capacity` term over the
  capacity's bits, which the wrapping RUP cannot dispose of in general. The
  time-table rules read `ub(capacity)`, and put its bounds in the reason.
- **Presences** are plain `{0, 1}` variables. The proof uses their single
  equality atom, `p = 1`.
- **Checked.** A view length (`a + 1`) and a view capacity (`c + 1`) give the
  brute-force answer (112 solutions) with verifying proofs, under the default
  rules and with edge-finding, energetic edge-finding and not-first / not-last
  on (`tmp/fd-sched/cumulative/alias/lview.cc`). The suite's view-wrap lanes
  wrap starts only.

### Reification

None. No reified or half-reified `Cumulative` exists, and nothing asks for one.
The optional-task form is not a reification: an absent task drops out of the
load, but the constraint itself always holds.

### Relation to other families

- **Into this family.** No frontend decomposes anything into `Cumulative`.
  `fzn_disjunctive*` used to ride an optional Cumulative and no longer does
  (#735). `Disjunctive`'s own tests post a capacity-one Cumulative as a
  differential oracle (`disjunctive_optional_constraint_cumulative`).
- **Child constraints.** None. Everything is one propagator plus
  initialisers.
- **Shared code.** This is the coupling a reader will not otherwise see.
  - `propagate_cumulative` and `CumulativeInputs` (`propagate.hh`) run under
    three owners: a posted `Cumulative`, a derived Cumulative
    (`install_derived_cumulative`), and **each axis of a `Disjunctive2D`**, which
    projects itself onto a Cumulative and runs this propagator over the
    projection (#1027, #973). See [`disjunctive_2d.md`](disjunctive_2d.md).
  - `per_time_{before,after,active}_says` state what the per-time flags mean,
    once, and `Disjunctive2D` defines its projection's flags with them.
  - `cumulative_task_window` is called by `Disjunctive2D` and by all three
    presolvers, so that their windows agree with a donor's. A disagreement of
    one makes a presolver decline, silently.
    `prepare_cumulative_overload_check` is called by `Disjunctive2D` and by
    `install_derived_cumulative`, not by the presolvers directly.
  - `gcs/constraints/innards/window_energy.{hh,cc}` (the window-energy lemma)
    is shared with `Disjunctive`, `Disjunctive2D` and `makespan_energy`.
  - `guaranteed_contribution` (a variable height's bits back to
    `lb(h)·active`) is shared with `donor_view.cc`.
  - `task_presence` is shared with `Disjunctive`, `Disjunctive2D` and two
    presolvers.
  - `flag_bridge` is shared with the window-energy lemma, the checkpoint
    recovery, `Disjunctive2D` and two presolvers.
  - `innards/proofs/subset_sum_strengthening` (the KAOC availability lines) is
    shared with `CumulativeStrengthening`.
  - `ComparatorNetwork` is **not** used here. It is `Disjunctive`'s and
    `Disjunctive2D`'s ([`disjunctive.md`](disjunctive.md)).
- **Presolvers.** `CumulativeStrengthening`, `InferredCumulative` and
  `InferredDisjunctive` read posted Cumulatives (and the projections
  `Disjunctive2D` publishes) as donors and install derived Cumulatives, which
  run this propagator over the donors' flags. Their detection, rewrites and
  evidence of firing are in
  [`cumulative_strengthening.md`](../presolvers/cumulative_strengthening.md),
  [`inferred_cumulative.md`](../presolvers/inferred_cumulative.md) and
  [`inferred_disjunctive.md`](../presolvers/inferred_disjunctive.md). The
  runtime half is here, under
  [The derived constraint](#the-derived-constraint) and the `makespan-bound`
  rule. No presolver rewrites a `Cumulative` *into* something else.
- **Reachability.** Directly reachable from MiniZinc, XCSP3, the `.scp`
  reader and the C++ API, so nothing about it depends on a decomposition
  reaching it.

## The proof model

### OPB encoding

The shipped encoding (`CumulativeEncoding::StartCheckpoint`, #780). Let `A` be
the active tasks (length and height can be positive, and not constantly
absent). For each ordered pair `i ≠ j` in `A`:

```
sb_{i,j}   ⇔  s_i − s_j ≤ 0                                   (i has started by s_j)
sa_{i,j}   ⇔  s_i − s_j ≥ 1 − d_i         (constant d_i)
           ⇔  s_i + d_i − s_j ≥ 1         (variable d_i)       (i is still running at s_j)
sact_{i,j} ⇔  sb_{i,j} ∧ sa_{i,j} [∧ p_i = 1]
```

and on the diagonal, `sact_{j,j} ⇔ [d_j ≥ 1] [∧ p_j = 1]`, minted only when
it says something: a variable length, or a presence. For each `j ∈ A`, one
checkpoint row:

```
scap_j :   Σ_{i ∈ A} c_{i,j}  ≤  capacity
```

where `c_{i,j}` is `r_i · sact_{i,j}` for a constant height. A variable height
contributes `Σ_k 2^k · scc_{i,j,k}`, with `scc_{i,j,k} ⇔ sact_{i,j} ∧
bit_k(r_i)`, two reification halves per bit. An unminted diagonal contributes
`r_j` unconditionally, and that goes to the right-hand side. A variable
capacity moves to the left as `−capacity`.

- **Definitional.** It is "the load profile only rises at a task's start, so
  checking at every start checks every peak". That is the constraint's
  meaning, stated at the finitely many points where a violation can first
  appear. Nothing is derived into the model.
- **Size.** By construction it is `6n(n − 1) + n` rows over `n = |A|`, plus 2
  per minted diagonal flag and 2 per bit per pair for a variable height
  (`⌈log₂(ub(r_i) + 1)⌉` bits). It is **independent of the horizon**. Each
  pairwise row mentions both starts' bits, so the OPB is `Θ(n² log H)` terms.
  The block is not windowed: every ordered pair gets flags, including pairs
  that can never overlap.
- **What it does not contain.** There are no per-time rows and no per-(task,
  time) flags. Under the test-only `TimeIndexed` and `BothRecovering` arms, the
  model also carries three reified flags per (task, time point) in the task's
  window (`cb`, `ca`, `cact`), one `cap_t` row per time point, and three
  contribution rows per (task, time) for a variable height. That is
  `O(n × horizon)`, which is what #780 removed.

### Labels

Labels other code actually cites:

| Label / key | Rows | Cited by |
|---|---|---|
| `scap_<j>` (`checkpoint_row_role`) | the checkpoint rows | the checkpoint recovery; and `cake_pb_cp`'s chain, which resolves our citations against its OPB by these labels |
| `sb` / `sa` / `sact` keys `(i, j)`, `scc` keys `(i, j, k)` | the pairwise flags | the recovery; cake (same names) |
| `cb` / `ca` / `cact` keys `(i, t)`, `cc` keys `(i, t, k)` | per-time flags, **proof-only** under the shipped encoding | every rule; derived Cumulatives and `Disjunctive2D` by key |
| `cap` (`capacity_row_family`) | the deriver of recovered `C_t` | derived Cumulatives (`find_or_derive_line_in_family`) |
| `<i>_<t>_cge` (`contribution_ge_row_role`) | a variable height's "contribution ≥ height" row, published as a **derived** line under the shipped encoding | the energy rules; `recover_constant_argument_row` |
| `end_ge_<i>` (`end_lower_bound_role`) | the `end ≥ s + l` line of the proof-only end proxy | the propagator; derived Cumulatives (which decline without it) |

`cap_<t>`, `_cle`, `_cz` and the pairwise `_scge` / `_scle` / `_scz` rows exist
only under the test-only arms, or (for the pairwise ones) when a height has no
citable bits, which the shipped encoding refuses with proofs on. Nobody cites
them under the shipped encoding. Renaming a pairwise label is a **cross-tool
break**: cake writes the same names.

### Cake conformity

`cake_pb_cp` (CakePB-dev `a402078`, 2026-09-19) derives the start-checkpoint
block under the same labels, and the six `scp_chain_cumulative*` cases pass the
full workflow-2 chain: `sat`, `var_sat`, `var_height_sat`, `var_duration_sat`,
`mixed_sat` and `unsat`. Re-run for this audit, each printed `OK: full
workflow-2 chain passed`. Between them they cover constant and variable
lengths, heights and capacity, a negative start, and tasks dropped for zero
length and for zero height. All six run with opbdiff mode **`none`**, which
skips the label oracle, for documented reasons
(`verified_encodings/scp_cases/CMakeLists.txt`):

- where a reification half is implied by the start domains, cake writes a 0
  coefficient on the flag and we write 1. Both are tautologies.
- cake also writes `@c[id][cap_ge0]` and `@c[id][h_<i>_ge0]` rows. We have no
  counterpart for those, because we reject a negative capacity or height at
  posting.
- `{0, 1}` starts differ in their bit encodings, according to the comment,
  which cites #358. #358 is closed, and whether the divergence is still there
  was not re-checked.

**`cumulative_optional` has no cake encoder.** It is named apart by
`constraint_type()`, so the gap is visible rather than silent. The rules say a
request waits for the next batch of cake requests rather than going alone
(scheduling-front scope note).

### Proof-time state

What the proof contains, and how an external tool finds it.

- **At the root, in the OPB:** the checkpoint block above. Nothing else.
- **At the root, in the proof** (install initialisers; the first two items
  only at `AssertionLevel::Off`, the third at every level):
  - for each task whose start and length both vary, `end = s + l` is bit-defined
    by `introduce_bits_of` (a conservative extension; cake has no such
    variable). Its `end ≥ s + l` line is published as `end_ge_<i>`;
  - a **flag definer** is published with the tracker
    (`publish_flag_definer`);
  - the **capacity-row family deriver** is published (`publish_derived_line_family`,
    family `cap`). This one is published at **every** assertion level, which is
    #1234's defect.
- **Lazily, during search:**
  - **Per-time flags.** A `cb` / `ca` / `cact` flag at `(i, t)` is *named* the
    first time anything looks it up (#1111), under key `(i, t)` and annotation
    `cb` / `ca` / `cact`. It is *defined* the first time anything cites one of
    the point's flags (the definer, keyed on `cact`), as two `red` steps per
    flag at `Top`, registered so that `reification_half` hands citers the
    lines. A variable height's `cc` bits come with it, as conjunctions
    `cc_k ⇔ cact ∧ bit_k(h)`, plus the derived `cge` row. So does the bridge
    `end ≥ t + 1 → after` for an end-proxy task.
  - **Recovered rows.** `C_t` is derived from the checkpoint rows the first
    time any citer asks for `t`, reason-free at `Top`, and cached per
    constraint (`CheckpointRecoveryCache`). The time-free order facts
    (totality `sb_{i,j} ∨ sb_{j,i}`, and transitivity) are derived once and
    shared by every `t`. Each recovery introduces its own proof flags, labelled
    `ckpe`, `ckpw`, `ckpn` and `ckpf`. On `Bl2004` these were 15,650 of the
    proof's 19,668 `red` steps.
  - **Guarded window-energy rows** for the edge-finding family are derived at
    `Top` the first time a `(task, window, guards, length)` key is needed, and
    cited from then on. The cache is per constraint and never pruned.
- **Deletion.** Everything per-firing goes at `ProofLevel::Temporary` and is
  deleted with the firing. Nothing at `Top` is ever deleted, except when a
  derived Cumulative declines at install after deriving some rows: it deletes
  those orphans explicitly (`derived_cumulative.cc:266-273`). No deletion makes
  a later reconstruction impossible.
- **In the OPB or in the proof.** The pairwise flags are in the OPB. The
  per-time flags, the end proxies and the recovery flags are all in the proof.
  On a solution: `cb`/`ca`/`cact` are functions of the starts, lengths and
  presences; `cc` of those and the heights; `end` of `s + l`; and `ckp*` of
  the per-time and pairwise flags they are reified over. So every proof-only auxiliary is determined by unit
  propagation on a solution, as `solx` needs. The enumeration tests' verifying
  `solx` lines are the evidence that this holds.
- **Proofs off.** The flag vectors in `CumulativeInputs` are left empty, and
  every arithmetic decision reads the windows (`per_task_t_lo/hi`) rather than
  the vectors. That is deliberate, so that propagation cannot differ with
  proofs on (`active_flag_count`'s comment).

## The implementation

### Initialisation and global data

- **`prepare()`** resolves presences, lengths, heights and the capacity
  against the initial state. It drops inactive tasks, computes each task's
  flag window `[lb(s), ub(s) + ub(d) − 1]` (`cumulative_task_window`) and,
  with `overload` on, `prepare_cumulative_overload_check`. That picks the
  eligible tasks, and builds `time_slot_prefix`, a difference array prefix-summed
  over the **whole initial horizon**: `O(n + H)` time and memory, guarded by
  `GCS_CHECK_LARGE_DOMAIN`. This is #833's H3 site and the large-domain audit's
  `KnownTrip`. It also throws the view-height `UnimplementedException` with
  proofs on.
- **`define_proof_model()`** writes the `6n(n − 1) + n`-row block and
  publishes the per-time flag family (which keys exist), at `O(n²)` names.
  Under the test-only arms it also writes the `O(n × H)` per-time block.
- **Initialisers.** Two at the default priority, three under
  `BothRecovering`. They are the end-proxy definitions and flag definer, and
  the capacity-row family. They cost `O(n)` plus one `introduce_bits_of` per
  end-proxy task. Nothing is horizon-sized: the definer is lazy. A derived
  `Cumulative` installs none of these. If it names a makespan it installs
  one, the makespan initialiser (`InitialiserPriority::Expensive`), whose
  candidate scan is horizon-shaped (see
  [`makespan-bound`](#rule-makespan-bound), #1267).

No root cost dominates on a scheduling-shaped instance. On a `0..10⁹` horizon
the root's and each call's horizon-sized arrays (`8 × 10⁹` bytes each) cost
time and memory. Three free tasks reach a first solution in 77.5 s, at a
29.8 GiB peak, on this 2 TB machine (`hz.cc free`). How the arrays fail
depends on the span and on whether the process runs under a memory limit:
- **One array exceeds what the kernel will commit** (roughly RAM plus swap,
  under default overcommit). The allocation throws `std::bad_alloc`, as at
  `0..10¹²`, which throws at once. Spans near `2⁶⁰` elements, from starts or
  lengths near `±2⁶⁰`, throw `std::length_error` (the overflow ledger's
  lane, #833). Both happen with or without a memory limit: a cgroup limit
  acts only on memory actually used, not on an allocation the kernel
  refuses.
- **The kernel commits the arrays but the memory runs out** as they are
  zero-filled. The process is OOM-killed, with no exception. Under a memory
  limit (a cgroup, as a Slurm allocation sets) that is any span whose arrays
  exceed the limit, short of the first case: `hz free 10⁸` and `hz free 10⁹` under a 1 GiB limit
  (`systemd-run -p MemoryMax=1G -p MemorySwapMax=0`) were both killed, rc
  137, the second with a single array of `8 × 10⁹` bytes. With no limit it
  is the spans whose arrays fit one at a time but not together: on this
  machine about `6 × 10¹⁰` to `2.5 × 10¹¹`, estimated, not run.

See [Interval efficiency](#interval-efficiency).

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| `propagate_cumulative` (posted) | `on_bounds`: every active start, a variable capacity, every variable height, every variable length; `on_instantiated`: every variable presence | derived | all except `makespan-bound` | always | not claimed | yes, until backtrack |
| `propagate_cumulative` (derived) | `on_bounds`: starts, variable lengths; `on_instantiated`: variable presences | derived | as above, over the derived task set | `install_derived_cumulative` | not claimed | yes, until backtrack |
| derived makespan initialiser | — (runs once) | — | `makespan-bound` | a derived spec with `makespan` set; priority `InitialiserPriority::Expensive` | n/a | n/a |
| end-proxy / flag-definer initialiser | — | — | none (definitions) | proofs on, `AssertionLevel::Off` | n/a | n/a |
| capacity-row family initialiser | — | — | none (derivations on demand) | proofs on, every level | n/a | n/a |
| `BothRecovering` differential initialiser | — | — | none (test-only check) | `CumulativeEncoding::BothRecovering` | n/a | n/a |

- **Self-disabling.** The propagator returns `DisableUntilBacktrack` when
  every active task is known absent, and after any contradiction. Otherwise it
  returns `Enable`. It never disables permanently.
- **Idempotence.** Not claimed (`Enable`, never the idempotent state). That is
  "not claimed", which is not the same as "not idempotent", but here the code
  *relies* on being re-run. A sweep that has pushed a bound does not try the
  elastic rungs again (`pushed_in_sweep`), and says the next run will.
- **Holes affect.** *Derived*, and true. Every trigger is `on_bounds` or
  `on_instantiated`, and the propagator reads only `lower_bound`,
  `upper_bound` and `bounds` of everything it touches. **This family's whole
  vocabulary is bounds.** Holes in a start's domain are never read, never
  pruned and never woken on.

### Mutable state and incrementality

There is no backtrackable state. Every call rebuilds everything from the
current bounds:

- the mandatory-load profile over the current span of the tasks' windows,
  `O(Σ mandatory lengths + span)`;
- the candidate list, sorted, `O(n log n)`;
- the overload sweep's prefix sums, `O(span)`;
- for the elastic rungs, a per-time-point height array (and a bitset for
  KAOC), reset per window, `O(n² · span)`;
- the time-table scans, `O(n · width · length)`.

#364 (the incrementality survey) lists the profile as the highest-payoff
algorithmic target. It would be maintained across calls with an
`on_backtrack` delta.

What persists without restore, because it is monotone and backtracking cannot
invalidate it:

- the `CumulativeFlagCache` (flags looked up, points defined);
- the `CheckpointRecoveryCache` (order facts and recovered rows);
- the guarded window-energy map;
- for a derived constraint, `LazyCapacityRows`.

All of them are about lines at `Top`. **None is ever pruned**, so on a long
solve they grow with the number of distinct points, windows and guards ever
cited. The guarded-energy map in particular is keyed on six integers, two of
which move with the search for an energetic contributor (#755). Their memory
was not measured.

### Interior values and optional pruning

**What this family offers.** `None.` It installs no optional-interior-pruning
pair, and has no `consistency::Auto`.

**What this family observes.** Nothing. The family's whole vocabulary is
bounds: no propagator reads a hole in any variable, and none is woken by one.
So a `Cumulative` keeps nobody's interior pruning alive, and a model whose
only other constraint on the starts is this one lets that constraint drop its
interior pruning. The declarations are the triggers' own, and they tell the
truth.

### Robustness and limits

- **Unbounded domains.** Not supported in practice. Both the root and every
  call allocate arrays sized by the horizon (see
  [Interval efficiency](#interval-efficiency)). Three free tasks, proofs off,
  to a first solution:

  | horizon | time | peak memory |
  |---|---|---|
  | `10⁶` | 56 ms | 42.5 MiB |
  | `10⁷` | 1.0 s | 308.9 MiB |
  | `10⁹` | 77.5 s | 29.8 GiB |
  | `10¹²` | `std::bad_alloc` at once | — |

  The arrays fail when one of them exceeds what the kernel will commit:
  `std::bad_alloc`, as at `10¹²`, or `std::length_error` for spans near `2⁶⁰`
  elements, from starts or lengths near `±2⁶⁰`. Neither is a `gcs`
  exception (#833, H3, the overflow ledger's F3). Short of that, exhausting
  memory gets the process OOM-killed, with no exception at all.
- **Negative values and zero.** Negative starts are fine (`mixed_sat` covers
  one in the cake chain). An end proxy whose lower bound is negative gets a
  sign bit (#553). Zero lengths and heights drop the task. A zero capacity is
  ordinary.
- **Degenerate shapes.** These were checked against brute force with verifying
  proofs, under the default rules and with elastic, knapsack, edge-finding,
  energetic edge-finding and not-first / not-last on:
  - aliased starts `{x, x}` at capacity 1 (UNSAT) and at capacity 2;
  - offset views `{x, x + 1, y}`, negated views `{x, −x + 4, y}`;
  - zero length beside a tall task, zero heights at capacity 0.

  A view **height** throws with proofs on. The energy rules exclude any task
  whose start is not a plain variable with an order encoding (a constant
  start, a view start, a `{0, 1}` start), whose length is a view or a
  `{0, 1}` variable, or whose height is a view (`cumulative.cc:481`; reachable
  only with proofs off, since a view height throws with them). That is weaker,
  not wrong.
- **Overflow.** The integer range policy (inputs within `±(2⁶⁰ − 1)`) does not
  hold here: in-range inputs reach `IntegerOverflow`. Four sites are known,
  all checked arithmetic, so each throws rather than wrapping. Write
  `B = 2⁶⁰ − 1`. Three of the four throw on **feasible** single-task
  instances:
  - `mand_prefix` (#1223, `cumulative.cc:2097`): one task of length 9, height
    `B`, capacity `B`, start a *variable* with domain `{0}` throws `9223372036854775800 +
    1152921504606846975`. With `constant_variable(0_i)` as the start, it
    solves, as #1223 notes. #1223's own repro uses nine unit tasks;
  - the candidate energy `p × h` (`cumulative.cc:2142`): one task of length 9,
    height `B`, capacity `B`, start in `[0, 100]` throws `9 *
    1152921504606846975`;
  - the overload sweep's `supply = capacity × width` (`cumulative.cc:2338`),
    which depends only on the capacity and the window's slot count. One
    height-1 task with capacity `2⁴⁰` and start in `[0, 2²³]` throws
    `1099511627776 * 8388609`, and at `[0, 2²²]` it solves. With heights and
    capacity `B`, a window of 9 slots is enough: two unit tasks with starts
    in `[0, 8]` throw `* 9`, and in `[0, 7]` they solve;
  - the profile `mand_load[t] += lb(h)` (`cumulative.cc:2013`): nine
    overlapping height-`B` tasks at capacity `B` throw instead of reporting
    UNSAT. Eight report UNSAT, and the proof verifies.

  The last three, and the single-task `mand_prefix` repro, are #1235, filed
  beside #1223 (repros in
  `tmp/fd-sched/cumulative/overflow/`, plus `supply2.cc` in
  `tmp/fd-sched/factcheck/cumulative/overflow/`, whose copies of
  `energy2.cc` and `energy3.cc` carry an outdated "(UNSAT)" comment). Lengths near `2⁶⁰` fail
  differently, on the horizon arrays (`std::length_error` or
  `std::bad_alloc`, the overflow ledger's F3). The KAOC bitset is capped at a capacity of 4,096
  (`max_knapsack_capacity`). Above that, KAOC quietly degrades to TTHE-OC,
  which is a weakening, documented at the site.

### Interval efficiency

The relevant width here is the **horizon**: the span of the tasks' windows.
The start domains are contiguous in every model the family is used with, and
nothing reads a hole. So "per value" means "per time point", and that is the
axis the four questions are answered on.

1. **The propagation side.** These sites walk time points.
   - The profile build: `for t in [lst, eet)` per present task. That is
     bounded by the mandatory parts, but the array it fills is the **whole
     current span** (`vector<Integer> mand_load(range)`, guarded by
     `GCS_CHECK_LARGE_DOMAIN`), allocated and zeroed on every call.
   - The overflow scan over the same array: `O(span)` per call.
   - The overload sweep's `mand_prefix`: `O(span)` per call.
   - The elastic rungs reset a per-time array, and a `capacity/64`-word bitset
     per time point, for every window: `O(n² · span)` (#1126).
   - **The time-table bound scans** walk start values one at a time from
     `lb(s_j)` (and from `ub(s_j)`), each test `fits_at(s)` walking `d_j`
     points. That is `O(width × d_j)` per task per call (#705, item 1). A
     single push over a blocked prefix of `H/2` took 333 ms at `H = 10⁶` and
     `d = 1` (proofs off). The profile has plateaus, and a competitive
     time-tabler jumps them.
   - **The chain construction for a push runs with proofs off.** Its output
     is used only by the justification, but it is built eagerly, before the
     inference, whether or not anything will read it:
     - `build_lb_chain` (`cumulative.cc:3164-3180`, called at 3202 and 3245)
       and the ub chain built inline at 3269-3282, with `contributors_at`
       costing `O(n)` per step;
     - the (TTOC) `pins` vector (`2944-2965`), one entry per compulsory
       `(task, t)` in the window;
     - the overflow's `contributing` list.

     A long push therefore costs `O(steps × n)` extra on the propagation path
     with no proof to write. It is not guarded on `want_reasons()` or on a
     logger, unlike the energetic contributors and the published rule's
     `theta`, which are.
   - **The derived makespan initialiser's candidate scan**, on a derived
     constraint that names a makespan: once, at the root, every time point
     from `rows_lo` up to `min(ub(M), last window end)`, at `O(n)` each, with
     proofs on or off. With a loose `ub(M)` that is the horizon, whatever the
     bound found (#1267; see [`makespan-bound`](#rule-makespan-bound)).

   No site uses an interval primitive. None needs one for correctness, since
   the domains are not read as sets. What is missing is plateau-jumping over the
   profile and, for the makespan scan, event-based candidates or a stopping
   bound (#1267).
2. **The reason side.** The reason is `generic_reason` over every scoped
   variable. It is one or two bound literals per variable, plus one
   `not_in_range` literal per **run** of holes (never per value), plus a
   presence literal per present task. It is materialised lazily, only when a
   proof logger asks, so proofs-off pays nothing for it. The work of finding
   the runs is one step per run. Two oddities:
   - it is `generic_reason` and not `bounds_reason`, so it states holes that no
     rule reads. That makes a non-minimal reason a little larger where starts
     have holes;
   - it is whole-scope for every rule, so its size is `Θ(n)` whatever the rule
     touched. It covers every posted start, including tasks dropped as
     inactive and undecided optional tasks.

   The reason itself is lazy, but the proof-only *data* the justifications
   capture is not (the chains and pin lists above), and that is the part of
   this question the family fails.
3. **The proof side.** This is where the per-time-point cost is.
   - **Every rule's certificate sums capacity rows over the time points it
     argues about.** The overload family cites `C_t` for every `t` in the
     window. The window-energy lemma emits three lines per time point of the
     clipped window. The (TTOC) and TTEF pins are three lines per pinned
     `(task, t)`. The elastic rungs emit an availability line per time point.
     None of it has a width gate, and there is no interval form. The arguments
     are per-time-point by nature: a capacity row is a statement about one
     instant.
   - **The first citation of a time point** pays for its recovery (about
     `2m³` lines, `m` = tasks with a flag at `t`; 74 to 467 lines at `m = 3`
     to `6`, from the design note) and for its flags' definitions (6 `red`
     per task). Both are cached per constraint.
   - **A time-table push's chain has one step per blocked time it crosses**,
     advancing at most `d_j` per step, so its length is between
     `distance/d_j` and `distance`. At `d_j = 1` it is linear in the push
     distance, about 59 lines per unit (`hz.cc blocked`). At a push of 500,
     each unit's 59 lines are:
     - 30 `red` lines: 12 flag definitions for the two tasks' newly cited
       time point, 16 recovery definitions, and 2 shared order-literal
       definitions;
     - about 13 `rup`, 10 `pol`, 4 `core` and 2 `del` lines.

     Most of that is the first citation of a new time point, not the chain
     step's own `3k + 5` lines. The measured proofs:
     - 29,548 lines / 2.2 MB for a push of 500;
     - 295,048 lines / 24.6 MB / 10.3 s of VeriPB for a push of 5,000;
     - 2,950,048 lines / 268.8 MB for a push of 50,000, with VeriPB still
       running after 24 minutes;
     - at `d_j = 100` the same pushes cost 343 and 2,998 lines.

     That is the family's one emission that is proportional to a *distance*
     rather than to the instant being argued about.
   - The **encoding** is free of the horizon (`Θ(n² log H)` terms), which is
     #780's result. With proofs on and a free horizon of `10⁶`, a first
     solution's proof is 173 lines, the same as at `10³`.
4. **The audit lane.** `gcs/large_domain_audit_test.cc` has one row,
   `"Cumulative"`, pinned **`KnownTrip`**. Its comment reads "H3: the overload
   check's arrays are sized by the horizon": three tasks of length 2 over wide
   starts, constant lengths and heights. It reaches `prepare`'s
   `time_slot_prefix` and trips there. Axes the row does not vary:
   - a variable length or height;
   - optional tasks;
   - an edge-finding or elastic rule;
   - a derived constraint;
   - the time-table scans, which it never reaches, because it trips first;
   - proofs on.

   It has no `"Large domain proof sizes"` row. So the chain-length cost above
   and #705's scan are invisible to the lane, and [Next steps](#next-steps)
   has an item.

`Fine at any width` is **not** this family's answer on any of the four. It is
fine at scheduling widths: the benchmarks below have horizons of a few dozen.

## Inference catalogue

Facts true of every rule:

- **One propagator, `propagate_cumulative`**, runs every rule below except
  `makespan-bound`. A derived Cumulative and a `Disjunctive2D` projection run
  the same rules over other constraints' flags and rows (see
  [The derived constraint](#the-derived-constraint)).
- **Order inside one call:**
  1. the profile and `time-table-overflow`;
  2. one window sweep doing edge-finding, then not-first / not-last, then the
     elastic rungs, then the overload check (OC/TTOC), per window `[a, b)`
     with `a` an earliest start and `b` a latest completion;
  3. the time-table pushes and presence falsification.
- **The reason** is `generic_reason` over every posted start (inactive and
  undecided tasks included), the capacity if variable, every variable height
  and length, plus `p_i = 1` for every task known present. It is the same for
  every rule, whole-scope and not minimal. An undecided *presence* contributes
  no literal, since staying out of the profile is monotone, but its task's
  start bounds are still there.
- **The capacity rows** every certificate cites are recovered `C_t`s (posted
  constraint), donor-derived rows (derived constraint), or a projection's
  family (`Disjunctive2D`), through one `capacity_row(t)` accessor. Under the
  test-only arms they are model rows.
- **Hints.** Twelve of the seventeen rules (the time-table family, presence
  falsification, edge-finding and its forms, and both not-first / not-last
  detections) carry `hints::Cumulative`, wire form
  `cumulative:((constraint_id <id>))`. The four overload rules carry
  `hints::CumulativeOverload`, `cumulative:((constraint_id <id>) (subhint
  overload))`. The makespan bound carries `hints::CumulativeMakespan`,
  `(subhint makespan)`. A derived constraint's `<id>` is `unnamed`. **No hint
  carries a payload**: not the window, not the rule, not the time point. So a
  reconstructor cannot tell a time-table push from an edge-finding push from
  the hint.
- **Assertions, checked against real `a` lines** at
  `AssertionLevel::Inferences` (`rcpsp --dzn Bl2019`, every rule arm):
  - a bound push is `[conclusion] ∨ ¬reason`, e.g. `a 1 i[start6][ge2] 1
    ~i[start0][eq0] … 1 i[start19][ge16] >= 1 ::cumulative:(…)`;
  - a conflict is `¬reason` alone, from `contradiction()`.

  The reasons carried 21 to 39 literals across the arms on that 20-task
  instance, two per unfixed start and one per fixed one.
- **Every certificate is wrapped by the framework's RUP** (`ThenRUP::Yes`).
  The rule's own lines make the conclusion RUP; they need not reach it
  themselves.
- **Strength.** No rule here reaches a named consistency on the whole
  constraint (that is NP-hard), so every **Strength** is `partial`, with what
  the rule achieves said in words. `GAC`, `bounds(Z)` and the others are not
  claimed anywhere.
- **Tightness.** 41 ctest lanes run a corrupted derivation and expect VeriPB to
  reject it. Four of them are twins on the `BothRecovering` arm, and one
  (`cumulative_overload_mutation_recover_wrong_checkpoint_recovering`) runs only there. They are listed
  per rule. **Seven lanes were deleted at the encoding flip** (2026-09-12),
  because under the shipped encoding the corrupted step is no longer
  load-bearing: unit propagation over the checkpoint rows supplies what the
  step did (`gcs/CMakeLists.txt:683-699`). The certificates still emit those
  steps.

### Rule: time-table-overflow

- **Infers** — a contradiction.
- **Fires when** — always, on every call: some time point's mandatory load,
  `Σ lb(h_i)` over present tasks `i` with `ub(s_i) ≤ t < lb(s_i) + lb(d_i)`,
  exceeds `ub(capacity)`. It is not switched off by `CumulativeRules::time_table`.
- **Strength** — `partial`: `checker` at a full assignment (every present
  task's mandatory part is then its whole interval), and time-table
  infeasibility detection before that.
- **Algorithm** — builds the profile `mand_load` over the current span and
  takes the first `t` where it exceeds the capacity. `O(Σ mandatory lengths +
  span)`, in time points. Textbook time-tabling (Aggoun and Beldiceanu's
  compulsory parts).
- **Why it is true** — a present task with `ub(s) ≤ t < lb(s) + lb(d)` runs at
  `t` whatever its start and length turn out to be, with at least `lb(h)` of
  demand. So those tasks alone put more than the largest capacity still
  allowed on the resource at `t`.
- **Proof technique** — `pol` plus `RUP`. Each contributing task is pinned
  active at `t` by three `RUP` lines under the reason (`before`, `after`,
  `active`; plus the end-proxy materialisation for a task with variable start
  and length), and by a fourth for a variable height (`contrib ≥ lb(h)`). Then
  one `pol` adds the pins to `C_t`. The pins are licensed by unit propagation
  over the flags' reification halves against the reason's order literals
  (JP 3.1-style). The `pol` is the derivation itself. Ours, in the sense that
  no published procedure in `justification-techniques.md` names it. Flippo
  et al. (CP 2024) give pseudo-Boolean justifications for time-table
  reasoning, and whether theirs takes the same shape was not checked.
- **Reason** — whole-scope (see the preamble). The minimal reason is the
  contributing tasks' two bounds (or one each) and their lengths and heights.
- **Assertion** — `¬reason`.
- **Hint** — `hints::Cumulative`: `originator: ConstraintID`. No payload.
- **Offline reconstructibility** — `search`. The violating `t` is not in the
  hint, but recomputing the profile from the reason's bounds finds it in
  `O(span)`. That needs no guess, since the reason carries every bound, but
  nothing names `t`, or the rule. The derivation also needs `C_t`, which
  under the shipped encoding is a recovery from the checkpoint rows
  (`O(m³)` lines, a fixed procedure).
- **Proof size** — `3k + 1` lines per firing for `k` contributing tasks (one
  more per variable height). The first firing at a `t` pays the recovery and
  the flags' definitions, cached thereafter.
- **Gaps** — None.
- **Tightness** — Not shown by a dedicated lane. The `cumulative_unsat`
  chain case and every UNSAT fixture verify it.

### Rule: time-table-lower

- **Infers** — `s_j ≥ new_lb`.
- **Fires when** — `time_table` on (default). For a present task `j` that is
  not fixed, the smallest `s ∈ [lb(s_j), ub(s_j)]` at which `j` fits under the
  profile (its own mandatory load taken out) is above `lb(s_j)`.
- **Strength** — `partial`: time-table consistency on `lb(s_j)`. The new bound
  is the first start at which `j`, at its guaranteed height and length, fits
  under the other tasks' compulsory parts.
- **Algorithm** — scans `s` upward, testing `fits_at(s)` over `[s, s + lb(d_j))`.
  That is `O((new_lb − lb) × lb(d_j))` time points (#705). Then it builds the
  chain: from the running bound, take the **largest** blocked `t` in
  `[running, running + lb(d_j) − 1]` and jump past it.
- **Why it is true** — if `s_j ≤ t` for a blocked `t` with
  `running ≤ t < running + d_j`, then, given `s_j ≥ running`, `j` runs at `t`,
  and the load there exceeds the capacity. So `s_j > t`. Each step moves the
  lower bound strictly upward, and the steps reach the first fitting start.
- **Proof technique** — `RUP sequence` under an extended reason (the
  "chained bound pushes" of the design note). Per step:
  - pin each contributing task active at `t` (three `RUP`s);
  - pin `j` active at `t` under the reason **extended by** `s_j ≤ t`, which
    with the running bound puts `j` at `t`. Each of its lines carries the
    negation `[s_j ≥ t+1]` as a disjunct, so it reads
    `[s_j ≥ t+1] ∨ active_j,t` (`pin_pushed`, `cumulative.cc:1690`);
  - one `pol` adds them to `C_t`, dominated by `(load − capacity)·[s_j ≥
    t+1]`;
  - except at the last step, one `RUP` deposits `s_j ≥ t + 1` under the reason
    for the next step's unit propagation.

  The wrapping RUP closes the last step. Ours, from the design note's
  derivation.
- **Reason** — whole-scope. Minimally, `j`'s lower bound and the
  contributors' bounds at each blocked time.
- **Assertion** — `[s_j ≥ new_lb] ∨ ¬reason`.
- **Hint** — `hints::Cumulative`. No payload.
- **Offline reconstructibility** — `search`. Recompute the profile from the
  reason's bounds and replay the chain, which is a fixed procedure once the
  rule is known. Nothing says it is this rule rather than edge-finding's. One
  candidate check per rule family, polynomial.
- **Proof size** — per step `3k + 3 + 2` lines (`k` contributors), and the
  number of steps is between `(new_lb − lb)/lb(d_j)` and `new_lb − lb`. So it
  is **linear in the push distance in time points** when `d_j` is short:
  about 59 lines per unit at `d_j = 1`, counting lazy definitions and
  recoveries, which is 295,048 lines for one push of 5,000
  (`tmp/fd-sched/cumulative/horizon/`, `7e1c4178`).
- **Gaps** — None.
- **Tightness** — Not shown by a dedicated lane. The presence lane below
  replays the same chain.

### Rule: time-table-upper

- **Infers** — `s_j ≤ new_ub`, the mirror of `time-table-lower`.
- **Fires when** — as `time-table-lower`, scanning down from `ub(s_j)`.
- **Strength** — `partial`: time-table consistency on `ub(s_j)`.
- **Algorithm** — the mirror. The chain takes the **smallest** blocked `t` in
  `[running, running + lb(d_j) − 1]`, and each step turns it into
  `s_j ≤ t − lb(d_j)`.
- **Why it is true** — if `s_j ≥ t − d_j + 1` for a blocked `t ≥ running`,
  and `s_j ≤ running`, then `j` runs at `t`.
- **Proof technique** — as `time-table-lower`, with the reason extended by
  `s_j ≥ t − lb(d_j) + 1`, so each pin carries `[s_j < t − lb(d_j) + 1]` as
  its disjunct.
- **Reason** — whole-scope.
- **Assertion** — `[s_j < new_ub + 1] ∨ ¬reason`.
- **Hint** — `hints::Cumulative`.
- **Offline reconstructibility** — `search`, as `time-table-lower`.
- **Proof size** — as `time-table-lower`, in the push distance.
- **Gaps** — None.
- **Tightness** — Not shown.

### Rule: presence-falsification

- **Infers** — `p_j = 0`, for an optional task whose presence is undecided.
- **Fires when** — `time_table` on. `j` is undecided, and **no** start in
  `[lb(s_j), ub(s_j)]` fits under the profile of the tasks known present.
- **Strength** — `partial`: the presence half of time-table consistency. The
  undecided task's own bounds are never pruned (there is no conditional-bounds
  store; see [Known limitations](#known-limitations)).
- **Algorithm** — the `time-table-lower` scan over the whole domain, then its
  chain to `ub(s_j) + 1`. `O(width × lb(d_j))`.
- **Why it is true** — if `j` were present it would have to start somewhere
  in its domain, and every start overloads some time point.
- **Proof technique** — `RUP sequence`: the `time-table-lower` chain with
  `p_j = 0` carried as an extra disjunct on every line ("`j` starts later, or
  `j` is not here"). The start disjunct is dropped on the last step, whose
  blocked time is at or past `ub(s_j)`. Under the shipped encoding the chain
  is **no longer load-bearing on the test fixtures**: `EmitNothing` (no chain
  at all) and `WrongTask` (the chain about another task) both verify, because
  unit propagation over the checkpoint rows already reaches the conclusion.
  Both lanes were deleted at the flip.
- **Reason** — whole-scope, as for every rule. That means every posted
  start's bounds, including undecided optional tasks' and `j`'s own (the
  fact-check's `pf.cc` shows `~i[s2][ge5] i[s2][ge7]` for an undecided task),
  plus a presence literal for each task known present.
- **Assertion** — `[p_j = 0] ∨ ¬reason`.
- **Hint** — `hints::Cumulative`.
- **Offline reconstructibility** — `offline`. The conclusion `p_j = 0` names
  the rule, and the chain is a fixed procedure from the reason's bounds. On
  the fixtures, a bare RUP suffices.
- **Proof size** — as `time-table-lower`, over the whole domain.
- **Gaps** — None.
- **Tightness** — `cumulative_optional_mutation_one_too_far` (and its
  recovering twin): fire where exactly one placement still fits. VeriPB
  rejects it under every encoding. `wrong_task` and `emit_nothing` were
  deleted at the flip (see above).

### Rule: overload

- **Infers** — a contradiction: rule (OC') of Cloutier and Quimper (CP 2026).
- **Fires when** — `overload` on (default), the capacity is a constant, and
  some window `[a, b)` has `e(Ω) > C · |slots(a, b)|`. Here `Ω` is the eligible
  present tasks with `est ≥ a` and `lct ≤ b`, `e` is `Σ lb(d)·lb(h)`, and
  `slots` counts the time points in the window where some task can be active
  at all (`time_slot_prefix`).
- **Strength** — `partial`: the overload check over windows bounded by an
  earliest start and a latest completion.
- **Algorithm** — sorted by `lct`, for each distinct `est` as `a`, grows `Ω`
  as `b` advances: `O(n²)` windows, `O(1)` each from prefix sums. Plus the
  `O(span)` prefix per call.
- **Why it is true** — every task in `Ω` runs entirely inside `[a, b)`, so it
  consumes `d·h` units there. The window supplies at most `C` per time point,
  and nothing at a time point where no task can run.
- **Proof technique** — `pol`.
  - Sum `C_t` for every `t ∈ [a, b)`.
  - For each contained task, add its **window-energy** line,
    `Σ_{t∈[a,b)} active_t ≥ d`, scaled by `h`. That line is derived per
    firing by `derive_window_energy`: a `RUP sequence` of three lines per time
    point, two saturated two-line bridges of `before` and `after` to the
    start's order literals and one AND-gate line, then a `pol` in which the
    order literals telescope.
  - A variable height is converted back from its contribution bits by
    `guaranteed_contribution` lines.

  The activity terms cancel, leaving a constraint with only negative terms
  against a positive degree. The lemma is ours (`cumulative-proof-logging.md`,
  "The window-energy lemma"); the rule is Wolf and Schrader's energetic
  overload, in Cloutier and Quimper's formulation.
- **Reason** — whole-scope.
- **Assertion** — `¬reason`.
- **Hint** — `hints::CumulativeOverload`: `originator`, subhint `overload`.
- **Offline reconstructibility** — `search`. The subhint names the overload
  family but not the window or which rung. Recompute the `O(n²)` windows
  from the reason's bounds and test each, which is polynomial.
- **Proof size** — `(b − a)` row citations, plus about `3(b − a) + 1` lines
  per contained task (in time points, clipped to its window), plus one `pol`.
  Linear in the window width, per task.
- **Gaps** — None.
- **Tightness** — `cumulative_overload_mutation_{energy, capacity, window}`
  (overstate a task's window energy; omit the last capacity line; derive the
  lemma one point short). All are twinned onto the recovering arm.
  `cumulative_overload_mutation_recover_wrong_checkpoint_recovering` corrupts the recovery under it.

### Rule: overload-profile

- **Infers** — a contradiction: (TTOC), the overload check strengthened by
  the mandatory parts of the tasks the window does not contain.
- **Fires when** — `overload` and `profile_overload` on (both default),
  constant capacity, and `e(Ω) + F(a, b) > C · |slots(a, b)|` where (OC') alone
  does not fire. `F` is the profile load inside `[a, b)` of present tasks not
  in `Ω`.
- **Strength** — `partial`: the overload check plus compulsory parts.
- **Algorithm** — the same sweep; `F` is a difference of `mand_prefix`
  entries minus `Ω`'s own mandatory load. `O(1)` per window.
- **Why it is true** — a task not contained in the window still runs over its
  compulsory part, so the part of that inside the window takes supply the
  contained tasks cannot use.
- **Proof technique** — the `overload` `pol`, plus one pin (three `RUP`s) per
  `(task, t)` of compulsory load counted. That is `pin_contributor`, exactly
  as `time-table-overflow` pins.
- **Reason** — whole-scope.
- **Assertion** — `¬reason`.
- **Hint** — `hints::CumulativeOverload`.
- **Offline reconstructibility** — `search`, as `overload`.
- **Proof size** — the `overload` size plus `3` lines per pinned
  `(task, time)`. Linear in the profile's area in the window.
- **Gaps** — None. A pin claiming load the arithmetic never used would be
  accepted: the reason context is contradictory by then, and every RUP under
  it is vacuous. So the pin set is kept exactly to what `F` counted, by
  construction (`cumulative.cc:2944-2965`), and no lane can check it.
- **Tightness** — Not shown separately. The `overload` lanes run with the
  profile on.

### Rule: overload-elastic

- **Infers** — a contradiction: (TTHE-OC), the horizontally elastic overload
  check combined with the time table (Kameugne et al. 2024, in Cloutier and
  Quimper's equivalent formulation, CP 2026 §2.2.5).
- **Fires when** — `elastic_overload` (or `knapsack_overload`) and `overload`
  on, constant capacity, no bound pushed
  earlier in this sweep, and (TTOC) has declined on the window, but
  `required > supplied`. Here `required = e(Ω) − (Ω's compulsory load)`, and
  `supplied = Σ_{t∈[a,b)} min(C − profile(t), Σ heights of Ω's tasks that
  could run at t without being compulsory there)`.
- **Strength** — `partial`: strictly stronger than (TTOC).
- **Algorithm** — per window, a per-time-point height array grown task by
  task and reset when `a` moves. That is Cloutier and Quimper's incremental
  Profile, without their linked list over constant runs, so `O(n² · span)`
  rather than `O(C n²)` (#1126).
- **Why it is true** — at time `t` the contained tasks can between them use no
  more than what the profile leaves, and no more than the sum of the heights
  of those that could be there at all. A resource nobody can reach is not
  available.
- **Proof technique** — `pol` over one **availability line** per time point.
  That line is the capacity row with every compulsory contribution pinned off
  it and every term that is not a contained task's optional one weakened away.
  Where the heights already fit under what the profile leaves, the line is
  instead the items' literal axioms summed, with no row. It is weighed against
  each contained task's window-energy line, with its compulsory times weakened
  out. A self-check throws `ProofError` if the `pol`'s arithmetic disagrees
  with the detection (`cumulative.cc:2919`).
- **Reason** — whole-scope.
- **Assertion** — `¬reason`.
- **Hint** — `hints::CumulativeOverload`.
- **Offline reconstructibility** — `search`, as `overload`, plus the
  per-time-point caps, recomputed from the reason.
- **Proof size** — one availability `pol` per time point of the window (plus
  its pins), plus the energy lines. Linear in width × tasks.
- **Gaps** — None. **Not counted** by `GCS_SCHEDULING_RULE_STATS`: neither
  this rule nor `overload-knapsack` increments any counter (Bl2014's
  `overload` contradictions fall from 1,406 to 289 when it is on, and nothing
  else rises). [Next steps](#next-steps).
- **Tightness** — `cumulative_kaoc_mutation_<fixture>_capacity` (omit a
  capacity line) on three fixtures. All three run KAOC and strengthen a time
  point, so **no lane targets an unstrengthened (TTHE-OC) certificate**. This
  rule's own shape, availability lines with no subset-sum step, has no
  mutation lane.

### Rule: overload-knapsack

- **Infers** — a contradiction: (KAOC), the knapsack-augmented overload check
  (Cloutier and Quimper, CP 2026).
- **Fires when** — `knapsack_overload` and `overload` on, and `capacity ≤
  4096`. The knapsack flag turns the elastic machinery on by itself. As `overload-elastic`, with each time point's supply
  further capped by the largest subset sum of the candidate heights at most
  what the profile leaves.
- **Strength** — `partial`: dominates (TTHE-OC).
- **Algorithm** — a `capacity + 1`-bit reachability bitset per time point,
  shift-or per task (their Algorithm 3). That is `O(n² · span · C/64)`. The
  time points are then strengthened greedily by gain, only until the
  comparison tips.
- **Why it is true** — integer heights. The load at `t` from the candidate
  tasks is a subset sum of their heights, so it cannot exceed the largest
  subset sum within the cap.
- **Proof technique** — the `overload-elastic` certificate. At each time point
  the conflict needs, the availability line is put through
  `derive_subset_sum_strengthening`, under the reason. That is either
  Chvátal–Gomory rounding (`pol`, divide by the gcd) or a layered DP: per item
  and reachable partial sum, three reified flags (`redundance`) and clauses
  from their halves (`RUP`), ending in an at-least-one that dominates the
  strengthened line. A self-check throws if the strengthened bound is not the
  one the detection counted on (`cumulative.cc:2847`).
- **Reason** — whole-scope. The reason must also go into every RUP of the DP,
  because the source line was derived under it.
- **Assertion** — `¬reason`.
- **Hint** — `hints::CumulativeOverload`. Indistinguishable from
  `overload-elastic` by hint.
- **Offline reconstructibility** — `search`. The window, the rung and which
  time points were strengthened are all recomputable from the reason. The DP
  is a fixed procedure.
- **Proof size** — as `overload-elastic`, plus per strengthened time point
  `O(items × C)` flags in the worst case. That is pseudo-polynomial in the
  capacity, which is why the strengthening is applied only where needed.
- **Gaps** — None. The 4,096 cap degrades it to `overload-elastic` silently,
  which is documented at the site.
- **Tightness** — `cumulative_kaoc_mutation_<fixture>_{claim_one_better,
  strengthen_one_fewer, capacity}` on three fixtures (`cloutier_ex2`,
  `dp_path`, `compulsory`): claim one better than the subset sum; strengthen
  one fewer time point; omit a capacity line. Nine lanes.

### Rule: edge-finding-lower

- **Infers** — `s_j ≥ a + ⌈rest / h_j⌉`, for a task `j` that starts inside
  `[a, b)` and ends past it.
- **Fires when** — `edge_finding` and `overload` on, constant capacity, a window with
  `e(Ω) ≤ C·|slots|`, and `j` such that everything else plus all of `j` does
  not fit. Here `rest = e(Ω) − (C − h_j)·|slots| > 0`, and `j`'s energy
  *clipped* to the window at start bounds `[est_j, new_lb − 1]` still
  overflows. Under the strengthened forms, `e(Ω)` is replaced (see the next
  two rules).
- **Strength** — `partial`: edge-finding over the overload sweep's windows,
  with the detection restated as the certificate's own inequality. So it
  fires exactly where the certificate can prove it, and not on every window a
  textbook edge-finder would. The bound is pushed in one step.
- **Algorithm** — inside the `O(n²)` window sweep, a scan of the candidates
  tallest first. It breaks at the first task whose `rest`, computed against
  the full window charge, is not positive, since every shorter task's is then
  not positive either. `O(n³)` worst
  case (#742). The live bound is checked first, which counts `already_true`.
- **Why it is true** — if `s_j < new_lb`, then `j` overlaps the window by at
  least its clipped energy at those start bounds, and that, plus `Ω`'s whole
  energy, exceeds what the window supplies.
- **Proof technique** — `pol` under the negated conclusion. Sum `C_t` over
  the window. Add each contained task's **guarded** window-energy row (derived
  once at `Top` by `derive_guarded_window_energy` and cited from then on), and
  `j`'s guarded row with its high guard at the negated conclusion. Discharge
  the guards with one `RUP` each under the reason. The wrapping RUP turns the
  contradiction into the push. The guarded lemma is ours. Edge-finding is
  Vilím's (cumulative edge-finding, CP 2009), restated to fit the
  certificate.
- **Reason** — whole-scope.
- **Assertion** — `[s_j ≥ new_lb] ∨ ¬reason`.
- **Hint** — `hints::Cumulative`. No payload: the window `[a, b)` and `Ω` are
  not given.
- **Offline reconstructibility** — `search`. Over `O(n²)` windows and `n`
  tasks, recompute from the reason's bounds which window and set reach this
  bound, or try each with the certificate. Polynomial, but nothing points at
  it.
- **Proof size** — `(b − a)` row citations, plus at most three guard RUPs per
  task, plus one `pol`, per firing. The guarded rows are paid once per key: a
  row is cited 322 to 3,455 times per derivation on the Pack instances
  (`propagate.hh`, measured in #733).
- **Gaps** — None.
- **Tightness** — `cumulative_edge_finding_mutation_{drop, toofar, capacity}`
  (leave a contained task out; push one further; omit a capacity line).
  Re-checked for this audit only as part of the suite run.

### Rule: edge-finding-upper

- **Infers** — `s_j ≤ low_guard − 1`, for a task `j` that ends inside `[a, b)`
  and starts before it. The mirror of `edge-finding-lower`.
- **Fires when** — as `edge-finding-lower`, with `lct_j ≤ b` and `est_j < a`.
- **Strength** — `partial`, as `edge-finding-lower`.
- **Algorithm** — the same pass. The two directions share the candidate walk.
- **Why it is true** — the mirror.
- **Proof technique** — the same `pol`, with the negated conclusion on the low
  guard.
- **Reason** — whole-scope.
- **Assertion** — `[s_j < low_guard] ∨ ¬reason`.
- **Hint** — `hints::Cumulative`.
- **Offline reconstructibility** — `search`.
- **Proof size** — as `edge-finding-lower`.
- **Gaps** — None.
- **Tightness** — `cumulative_edge_finding_mutation_{mirror_drop,
  mirror_toofar}`.

### Rule: time-table-edge-finding

- **Infers** — a lower or upper start bound, as the two edge-finding rules.
  (TTEF) in both directions; counted under the edge-finding counters.
- **Fires when** — `edge_finding`, `overload` and `time_table_edge_finding` on, and
  `energetic_edge_finding` off. The window is charged `e(Ω) + F(a, b)`, the
  (TTOC) profile term, with the pushed task's own compulsory part taken back
  out.
- **Strength** — `partial`: edge-finding plus compulsory parts (Vilím,
  CPAIOR 2011).
- **Algorithm** — as edge-finding, with `F` from the prefix sums.
- **Why it is true** — as edge-finding, with the non-contained tasks'
  compulsory parts also occupying the window.
- **Proof technique** — the edge-finding `pol`, plus one pin (three `RUP`s)
  per compulsory `(task, t)` of a non-contained present task inside the
  window. The pins read the pushed task's bounds as the reason holds them,
  i.e. before the push, which matters where another task's start is the
  pushed variable or a view of it (`bounds_as_the_reason_has_them`).
- **Reason** — whole-scope.
- **Assertion** — as the edge-finding rule of the same direction.
- **Hint** — `hints::Cumulative`.
- **Offline reconstructibility** — `search`.
- **Proof size** — as edge-finding, plus `3` lines per pinned `(task, time)`:
  2.93 pin lines per firing on average on `data_bl` + `data_pack`
  (header comment; not re-measured).
- **Gaps** — None.
- **Tightness** — `cumulative_ttef_mutation_{drop, toofar, mirror_toofar,
  pins, mirror_pins}`. The `pins` lanes drop *every* profile pin. The `pin` /
  `mirror_pin` lanes, which dropped a single pin, were **deleted at the
  flip**: the checkpoint rows make one pin non-load-bearing on that fixture.

### Rule: energetic-edge-finding

- **Infers** — a lower or upper start bound, as the edge-finding rules, with
  every task's *guaranteed* energy in the window charged.
- **Fires when** — `edge_finding`, `overload` and `energetic_edge_finding` on. The latter
  takes precedence over TTEF. The window is charged `Σ_i h_i ·
  max(0, window_energy_bound(i))`: each task's least overlap with `[a, b)`
  over the starts its bounds allow.
- **Strength** — `partial`: subsumes TTEF (a contained task's guaranteed
  energy is its whole energy, and a non-contained one's is at least its
  compulsory part in the window).
- **Algorithm** — as edge-finding, plus an `O(n)` pass per window to sum
  guaranteed energies. That raises the sweep's cost per node (4.28× the
  default arm's median instructions per recursion on `data_bl`, below).
- **Why it is true** — every task, contained or not, must overlap the window
  by at least its guaranteed energy whatever its start.
- **Proof technique** — the edge-finding `pol`, citing one guarded
  window-energy row per contributing task, guarded by that task's own current
  bounds, which the reason carries. **No pins.** The rows for non-contained
  tasks are keyed on bounds that move, so they are reused far less than the
  contained rows (#755).
- **Reason** — whole-scope.
- **Assertion** — as edge-finding.
- **Hint** — `hints::Cumulative`.
- **Offline reconstructibility** — `search`.
- **Proof size** — `(b − a)` rows, plus one guarded row (`O(window)` lines
  when first derived) and up to three guard RUPs per contributor, per firing.
- **Gaps** — None.
- **Tightness** — `cumulative_energetic_mutation_{drop_energetic, drop,
  toofar, capacity, mirror_toofar}`. `drop_energetic` (leave out a
  non-contained task's row) is the lane this rule exists for: that energy is
  the only thing plain edge-finding would not have cited. The
  `mirror_drop_energetic` lane was deleted at the flip.

### Rule: not-first

- **Infers** — `s_j ≥ min_{k∈Ω} ect_k`, for a task `j` not contained in the
  window (typically one spanning it).
- **Fires when** — `not_first_not_last` and `overload` on (edge-finding is
  **not** needed in the library; `examples/rcpsp` turns it on alongside), and
  not `not_first_not_last_published`. `j`'s energy clipped to the window over
  starts `[low_guard, ECT(Ω) − 1]`, plus everything else, overflows. "Everything
  else" is the window charge of whichever edge-finding form is selected: TTEF
  adds the profile term and its pins, and energetic charges guaranteed energy.
- **Strength** — `partial`: a **weakening** of the published not-first rule.
  The detection is what the window-energy lemma can derive (least overlap over
  the whole negated range), so it fires less often than Schutt and Wolf's.
  Where `j` has one end inside the window, edge-finding pushes at least as
  far. Measured over the benchmark set, every firing is on a spanning task
  (header).
- **Algorithm** — in the window sweep, after the edge-finding block
  (which starts at `cumulative.cc:2445`), in its own `if` at 2553, `O(n)` per
  window over
  all candidates. That raises the per-node cost: 3.43× the default arm's
  median instructions per recursion, below.
- **Why it is true** — if `j` started before every contained task had ended,
  it would overlap the window by at least its clipped energy, which does not
  fit.
- **Proof technique** — edge-finding's certificate unchanged, with the guards
  at `[low_guard, ECT(Ω))`.
- **Reason** — whole-scope.
- **Assertion** — `[s_j ≥ ECT(Ω)] ∨ ¬reason`.
- **Hint** — `hints::Cumulative`.
- **Offline reconstructibility** — `search`.
- **Proof size** — as edge-finding.
- **Gaps** — None. The weakening is a strength choice, not a proof gap.
- **Tightness** — `cumulative_nfnl_mutation_{toofar, drop, roomy_toofar}`.
  `roomy_drop` was deleted at the flip.

### Rule: not-last

- **Infers** — `s_j ≤ max_{k∈Ω} lst_k − lb(d_j)`, the mirror of `not-first`.
- **Fires when** — as `not-first`, over starts `[max_lst − p_j + 1, ub(s_j)]`.
- **Strength** — `partial`, the mirror.
- **Algorithm** — the same loop.
- **Why it is true** — the mirror.
- **Proof technique** — edge-finding's certificate, with the negated
  conclusion on the low guard.
- **Reason** — whole-scope.
- **Assertion** — `[s_j < max_lst − p_j + 1] ∨ ¬reason`.
- **Hint** — `hints::Cumulative`.
- **Offline reconstructibility** — `search`.
- **Proof size** — as edge-finding.
- **Gaps** — None.
- **Tightness** — the `cumulative_nfnl_mutation_*` lanes exercise both
  directions where the fixture fires them. Which lane hits which direction was
  not separated.

### Rule: published-not-first

- **Infers** — `s_j ≥ ECT(Ω)`, under the **published** detection: Schutt and
  Wolf (CP 2010, Proposition 1) and Kameugne et al. (CPAIOR 2018, rule NF).
- **Fires when** — `not_first_not_last`, `not_first_not_last_published` and
  `overload` on. The published flag switches `not_first_not_last`'s detection
  to this one, and does nothing on its own (`cumulative.cc:2553`). Then `e(Ω) + h_j · (min(ect_j, lct(Ω)) − est(Ω)) >
  C · (lct(Ω) − est(Ω))` over the contained set's own window
  `[est(Ω), lct(Ω))`, while `lb(s_j) < ECT(Ω)`.
- **Strength** — `partial`. Incomparable with `not-first`: each fires where
  the other does not. It is worth under 1% of the search over `not-first`
  (0.991× summed recursions on `data_bl` + `data_pack`, header).
- **Algorithm** — as `not-first`, with `O(|Ω|)` captured per window when a
  logger is present.
- **Why it is true** — **contiguity**, not window energy (#746).
  - If `s_j < ECT(Ω)`, every task in `Ω` has `ect ≥ ECT(Ω)`, so any of them
    running before `ECT(Ω)` is still running at `ECT(Ω) − 1`.
  - If `j` is running at that one time point too, the capacity row there caps
    the prefix's load from `Ω` at `C − h_j` per point.
  - Summed over the window, that is exactly the published inequality.
  - When `ect_j < ECT(Ω)`, no single meeting point works, and the argument
    walks the bound up `p_j` at a time.
- **Proof technique** — `pol`, per rung of a `RUP sequence`.
  - Each rung is one `pol`: `Ω`'s guarded energy rows (in activity space),
    capacity rows (converted back to activity for variable heights) scaled by
    the rung's multiplicity, `j` pinned active at the meeting point under the
    rung's extended reason, and one **contiguity** line
    `active_{k,v} ∨ ¬active_{k,u}` (`RUP`, via a `flag_bridge` for a
    variable-length task) per contained task and prefix time.
  - Between rungs, a `RUP` deposits the advanced bound.
- **Reason** — whole-scope.
- **Assertion** — `[s_j ≥ ECT(Ω)] ∨ ¬reason`.
- **Hint** — `hints::Cumulative`.
- **Offline reconstructibility** — `search`.
- **Proof size** — per rung, `O(|Ω| × span)` contiguity lines plus pins, with
  rungs numbering `(ECT(Ω) − lb(s_j)) / p_j` at most. Quadratic in the
  window's span per firing in the worst case.
- **Gaps** — None.
- **Tightness** — `cumulative_published_nfnl_mutation_{emit_nothing, drop_pin,
  toofar, roomy_toofar, roomy_drop_pin}`. `emit_nothing` is the control that
  the certificate is load-bearing at all. **Dropping the contiguity rows can
  never be caught.** The detection's margin absorbs them and the wrapping RUP
  finishes, on about 1,700 firing instances (`cumulative_mutations.hh`). The
  `drop` lane was deleted at the flip.

### Rule: published-not-last

- **Infers** — `s_j < LST(Ω) − p_j + 1`, the published mirror.
- **Fires when** — as `published-not-first`, with `max_lst < lct_j` and the
  mirrored inequality.
- **Strength** — `partial`, the mirror.
- **Algorithm** — the same.
- **Why it is true** — contiguity over the suffix, at `LST(Ω)`.
- **Proof technique** — the same chain, walking down.
- **Reason** — whole-scope.
- **Assertion** — `[s_j < max_lst − p_j + 1] ∨ ¬reason`.
- **Hint** — `hints::Cumulative`.
- **Offline reconstructibility** — `search`.
- **Proof size** — as `published-not-first`.
- **Gaps** — None.
- **Tightness** — as `published-not-first`; the lanes include both directions
  where the fixtures fire them.

### Rule: makespan-bound

- **Infers** — `M ≥ μ + 1` for a makespan variable `M`, once, at the root.
  This happens only for a **derived** Cumulative whose spec names a makespan,
  i.e. a presolver's.
- **Fires when** — the derived constraint's initialiser
  (`InitialiserPriority::Expensive`) runs, and `makespan_energy_bound` finds a
  `μ` above what the model's makespan links already give. Only present
  eligible tasks count, and only those whose start is a plain
  `SimpleIntegerVariableID` and whose length is constant
  (`derived_cumulative.cc:334`). "Constant" is `is_constant_variable`, a type
  test, so a length variable whose domain is a single value is not counted.
  An undecided optional task counts as absent.
- **Strength** — `partial`: an energy lower bound on one variable. It is
  Sidorov's `L`, sometimes better (it divides by the rows actually present,
  not by `μ`) and sometimes worse (it counts only tasks the lemma can speak
  about) (`certified-makespan-bounds.md`).
- **Algorithm** — `makespan_energy_bound` walks **every** integer candidate
  `μ` from `rows_lo` (defined under Proof size below) up to the smaller of
  `ub(M)` and the end of the last task window, and returns the largest
  refuted. Each candidate sums every counted task's window energy, `O(n)`.
  So one initialiser call is `O(n · W)` for those `W` candidates, with proofs
  on or off. With a loose `ub(M)` that is the horizon, even when the bound
  and its certificate window are small (#1267). On #1267's helper-level
  probe (three length-2 tasks, bound 6 throughout) one call took 0.032,
  0.30, 3.03 and 30.3 ms at horizons of 10³, 10⁴, 10⁵ and 10⁶: linear in
  the unused horizon (`tmp/fd-codex-1005/sched/probes/hz1267.cc`,
  `7e1c4178`, fataepyc-10, 2026-10-05, serial, pinned to one core, malloc
  thresholds fixed; three runs agree within 1% from 10⁴ up and within a few
  per cent at 10³). This scan is separate
  from `time_slot_prefix`'s `O(n + H)` storage and from the certificate,
  whose window ends at `μ`.
- **Why it is true** — suppose `M ≤ μ`. Each counted task then has a start
  range: its own bounds, with the upper bound tightened to `μ − b` where a
  link row `M − s ≥ b` exists (`start_bounds_within`,
  `makespan_energy.cc:45`). The window-energy lemma gives the least overlap
  that range forces with `[lo, μ)`. A task the range keeps wholly inside the
  window counts its full `h·d`; one that could still start late counts only
  what it must run inside the window, possibly nothing. If those guaranteed
  energies add up to more than the window supplies, `C·|rows|`, then `M ≤ μ`
  is refuted. Every task finishing inside the window is the special case
  where every range is confined. So a missing link removes the deadline's
  confinement, not the task: an unlinked task keeps whatever overlap its own
  domain forces, and the bound may or may not weaken.
  - **With no linked task at all, nothing is certified on a feasible model.**
    The energies then do not depend on `M`, so a refuted `μ` refutes the
    root itself. That is why a spelling that loses every link certifies no
    bound (`inferred_cumulative.md`'s end-variable row).
  - Checked on three length-2 tasks made pairwise disjoint by one
    unit-capacity `Cumulative` per pair, starts `x ∈ [0, 2]`
    and `y, z ∈ [0, 8]`, `M ∈ [0, 10]`, with only `y` and `z` linked. Both
    inferred presolvers certify `M ≥ 6`, the same as with `x` linked too.
    Widening the unlinked `x` to `[0, 8]` lowers it to `M ≥ 4`, and with no
    link at all nothing is certified. Proofs on and off agree, and the root
    proofs verify (`tmp/fd-codex-1005/sched/probes/mk.cc`, `7e1c4178`).
- **Proof technique** — `derive_makespan_bound`, per counted task in turn:
  - for a linked task its own domain does not already confine
    (`ub(s) > μ − b`), one **confinement** `pol` in deview mode, which is
    unconditional: the link row plus the two order-literal definitions,
    giving `¬[s ≥ μ − b + 1] ∨ [M ≥ μ + 1]`, which the lemma's RUPs then use;
  - the window-energy lemma over the task's start range, derived under the
    reason plus the negated conclusion `M ≤ μ`. A task the lemma gives no
    energy is skipped.

  Then one final, unconditional `pol` sums the window's capacity rows and
  `h ×` each energy line, and the wrapping RUP concludes.
- **Reason** — `bounds_reason` over the counted tasks' starts, plus their
  presence literals.
- **Assertion** — `[M ≥ μ + 1] ∨ ¬reason`, hint `makespan`. Seen on `Bl2019`
  with `--infer-cumulative`: `… >= 1 ::cumulative:((constraint_id unnamed)
  (subhint makespan))`.
- **Hint** — `hints::CumulativeMakespan`: `originator`, which is `unnamed`
  for a derived constraint, and subhint `makespan`.
- **Offline reconstructibility** — `search`. `μ` is in the conclusion, but the
  derived constraint is not in the model. A reconstructor has to rediscover
  which implied Cumulative the presolver posted (its task set and capacity),
  and the link rows. The presolver documents give that search's cost.
- **Proof size** — one `pol` over `|window|` rows, plus at most `n`
  window-energy derivations and at most `n` confinement `pol`s. The window
  runs from `rows_lo` to `μ`. `rows_lo` is the minimum window start over **all** the derived constraint's
  active tasks, counted or not (`derived_cumulative.cc:137-139`, `:354`). So
  the cost is linear in `μ − rows_lo`, the bound measured from the earliest
  active window, and so in the task lengths, not in the horizon. Each of those rows is a donor row recovered at its first citation,
  at `Top`; on [`inferred_cumulative.md`](../presolvers/inferred_cumulative.md)'s
  scaled fixture the whole root proof grows by about 357 lines per time unit
  of the bound.
- **Gaps** — None. With proofs on, the derived constraint may decline at
  install (see [Proof-logging gaps](#proof-logging-gaps)).
- **Tightness** — `rcpsp_dzn_inferred_cumulative_mutated` and
  `rcpsp_dzn_inferred_disjunctive_mutated` (`--mutate-makespan-bound`: claim
  one more), and `derived_cumulative_test`'s own
  `MakespanEnergyMutation` cases. #829 records that the `deview` mode of the
  confining `pol` has no load-bearing fixture.

### The derived constraint

This is not a rule. It is where the derived rules' rows come from, and it is
the part a reader of the presolver documents needs.

- **`install_derived_cumulative(spec)`** builds `CumulativeInputs` whose flags
  are the **donors'**: per task, a `(donor, position)` from which the flags are
  looked up by key, on first citation (#1130). Its capacity rows come from
  `spec.recipe`, called **lazily** the first time a row is cited, at `Top`
  (`LazyCapacityRows`). It then installs `propagate_cumulative` with an
  `unnamed` owner. Heights and capacity are constants, so only starts, lengths
  and presences trigger it. A variable donor height reaches it as `lb(h)`,
  through `cumulative_donor_view` and `recover_constant_argument_row`.
- **Decline.** With proofs on, the install checks first. Each task's donor
  flags must exist at its window's two ends, a start-and-length-variable task
  needs the donor's `end_ge_<i>`, and the recipe is asked once per stretch
  between window edges (`DerivedCumulativeSpec::recipe`'s contract: its answer
  may depend on `t` only through which tasks can run). Any failure returns
  `false` and installs nothing, deleting any rows already derived. With proofs
  **off** it installs unconditionally.
- **What a recipe may do.** It may derive only: it has a `ProofLogger` and no
  `ProofModel`, so it cannot write to the OPB. It must never hand back a
  donor's own OPB row unchanged. A later decline deletes what it returned,
  and deleting a model row changes the problem.
- **Donor rows.** A posted donor has no `cap_<t>` row under the shipped
  encoding, so the recipe's row comes from the donor's `cap` family, which is
  the checkpoint recovery (`O(m³)` lines per first cited point). A published
  donor (a `Disjunctive2D` axis, #973) has only its family.
- **`cumulative_donor_view`** reduces a posted donor to constant arguments per
  task. It sets aside a task with a view height, a height that guarantees
  nothing, an optional task taller than the capacity, or a variable-length task
  whose donor published no `end_ge_<i>`. Set-aside tasks are weakened out of
  every derived row (`recover_constant_argument_row`, one `pol` per row). A
  variable capacity is replaced by its current upper bound through its order
  literal, and the result is exact. A **view** capacity makes the view
  `nullopt` (`donor_view.cc:117`), so such a donor is passed over entirely.
  The setting-aside of a variable-length task is the view's. If such a task
  reaches `install_derived_cumulative` without its `end_ge_<i>`, the whole
  install declines (`derived_cumulative.cc:172-175`), not just that task.
- **`cumulative_donors()`** lists every posted Cumulative, then every
  `PublishedCumulativeDonor` (`publish_cumulative_donor`), indexed by flag key
  position. A published donor's other-axis positions are holes.

## Evidence

### Tests

- **Twelve test binaries, all verifying.** The binaries are `cumulative_test`, `_overload_test`, `_edge_finding_test`,
  `_ttef_test`, `_energetic_test`, `_nfnl_test`, `_published_nfnl_test`,
  `_kaoc_test`, `_optional_test`, `_wide_horizon_test`, `derived_cumulative_test`
  and `subset_sum_strengthening_test`.
  - Nine compare `solve_for_tests` against a brute-force checker. None uses
    `solve_for_tests_checking_gac`, rightly, since no rule claims a
    consistency. `derived_cumulative_test`, `cumulative_wide_horizon_test` and
    `subset_sum_strengthening_test` make no `solve_for_tests` call: they check
    what was posted, how many names were written, and the strengthened bound.
  - VeriPB runs on every enumeration (`s VERIFIED COMPLETE ENUMERATION`
    throughout the uncapped run below).
  - Random instances are drawn from a fresh seed per run, which is printed,
    and `--seed=N` reproduces a run. `subset_sum_strengthening_test` is the
    exception: its seed defaults to a fixed 1.
  - `cumulative_test` also sweeps view-wrapped positions (`[w0_pall]`
    labels), and has view and mixed lanes.
- **108 ctest lanes for this family** (`ctest -N` at `7e1c4178`; the
  presolvers' own lanes, such as `cumulative_strengthening_presolver` and its
  `_recovering` twin, belong to their documents and are not counted here.
  Of the `rcpsp` example's lanes only `rcpsp_dzn_inferred_cumulative_mutated`
  is counted, since its mutation targets `makespan-bound`. The others also
  post a Cumulative but are not counted, `rcpsp_mm_energetic` (energetic
  edge-finding on) among them):
  - 21 modes of the twelve binaries (`subset_sum_strengthening_test`'s one
    lane included);
  - **23 `_recovering` lanes** on the test-only `BothRecovering` arm, which
    checks every recovered row against the model row standing beside it,
    not counting the example's `cumulative_encoding_both_recovering`
    (counted with the example below). Twenty-two are twins of a bare lane of
    the same name, `derived_cumulative_recovering` among them;
    `cumulative_overload_mutation_recover_wrong_checkpoint_recovering` has no
    bare partner. Five of
    the 23 are also among the 41 mutation lanes below: the four mutation
    twins, and `cumulative_overload_mutation_recover_wrong_checkpoint_recovering`;
  - **41 mutation lanes** (`run_test_and_expect_verify_failure.bash`), listed
    per rule above. Four are `BothRecovering` twins and one,
    `cumulative_overload_mutation_recover_wrong_checkpoint_recovering`, runs only on that arm;
  - **8 `cumulative_checkpoint_recovery_*` leak checks**, four `.scp` cases in
    two modes. `whole` rechecks a `BothRecovering` proof against an OPB with
    every per-time row stripped, so the recovery cannot be closing against the
    row it claims to derive. `no-block` solves under the shipped encoding and
    requires that no per-time row was written at all and that the proof still
    verifies, which is the tripwire on the encoder;
  - the six `scp_chain_cumulative*` cake-chain cases;
  - two XCSP3 lanes and six MiniZinc lanes (including two
    `cumulative_opt` lanes against Chuffed);
  - the `cumulative` example's five lanes (the default, two `--variant` arms,
    a generated instance, and a long-duration instance with lengths up to 500);
  - `rcpsp_dzn_inferred_cumulative_mutated`.
- **Runtime caps.** Every lane runs under the suite-wide caps (300 solutions,
  1,500 recursions) unless the build sets `GCS_TEST_CAP_DEFAULTS=OFF`, as the
  two Ubuntu CI lanes do. **The caps fire on two binaries**, run with the
  default environment for this audit: `cumulative_test` (10 truncated runs,
  "300 of ≤ 400 solutions checked sound" and similar) and
  `cumulative_overload_test` (10). The other ten never reach a cap. The counts
  depend on the seed: the fact-check saw 11 for `cumulative_overload_test` at
  `--seed=7`. The
  results reported here come from **uncapped** runs of all twelve, pinned,
  from `tmp/fd-sched/cumulative/suite/`, with no environment caps. All passed,
  in 0.3 to 4.2 s each.
- **Tightness harness.** The mutation lanes have a **control**: every mutated
  fixture's honest twin runs in the same binary's ordinary mode and verifies.
  `PublishedEmitNothing` and the deleted presence `EmitNothing` are the
  load-bearing controls: they ask whether the certificate is needed at all.
  What the lanes support is that these named corruptions are rejected on these
  named fixtures. That is not a claim that the derivations are tight.
- **Real instances.** None is ported into a data-driven test. The examples run
  `sample.dzn`, `.mm`, `.jss` and `.sch` (`examples/rcpsp`).

**What the tests do not cover:**

- **Any assertion level above `Off`** with a derived Cumulative (#1234).
  - **Posted donor.** Under the shipped encoding, the proof is rejected
    whenever a constraint was installed: at `Inferences` the presolver and
    derived tests abort with VeriPB syntax errors.
  - **`Disjunctive2D` donor.** At `Definitions`, `Inferences` and
    `Backtracking`, two presolvers decline and the proof verifies, so only a
    posting-count check sees it. The strengthening presolver throws a
    `ProofError` on `bars`.
  - **At `Links`,** a posted-donor proof with an install fails with
    #1234's parse error. Otherwise every proof of a satisfiable model is rejected at its first `solx` (#1210), including the
    projection runs where nothing was posted; unsatisfiable models verify.

  No lane sets `GCS_ASSERTION_LEVEL`.
- **Wide horizons, other than the name count.** `cumulative_wide_horizon_test`
  asserts at most 200 per-time names on a `10⁵` horizon (for #1111 and #1130).
  It does not time anything, and the large-domain lane trips in `prepare`
  before any rule runs. The chain-length cost and #705's scans are unmeasured
  by the suite.
- **Inputs near the range policy's edge.** `B`-sized heights and capacity
  throw (#1235, #1223), and no lane has them.
- **Elastic and knapsack firing counts.** Neither rung is counted, so a fixture
  cannot assert that it fired, except through a proof comment.
- **`with_encoding` from a user.** Nothing checks that a frontend run never
  writes the per-time block.
- **Derived-constraint declines with proofs on but not off.** Propagation can
  differ between the two (see [Proof-logging gaps](#proof-logging-gaps)), and
  no lane compares node counts across them on a declining shape.

### Benchmarks and examples

- **In-repo.** `examples/cumulative` (random instances, `--variant`), and
  `examples/rcpsp`, the workhorse. That one reads PSPLIB-style `.dzn` (the
  Pack, Pack_d, PSPLib, la_x, ksd15_d and bl sets), RCPSP/max `.sch`,
  multi-mode `.mm` (the one family with variable lengths and heights) and
  job-shop `.jss`. It has a flag for each rule that is off by default. There
  is none for `time_table`, `overload` or `profile_overload`, which are always
  on there. Two presolvers have flags: `--infer-disjunctive` and
  `--infer-cumulative` (`rcpsp.cc:1078`, `1092`). `DifferenceLogic` is reached
  through `--variant=presolved` (`rcpsp.cc:894`). There is no way to run
  `CumulativeStrengthening`.
- **Instances.** `/cluster/ciaran/claude/scheduling-instances/rcpsp/` holds the
  sets above, plus thirteen MiniZinc Challenge RCPSP instances (`00.dzn` to
  `15.dzn`, with gaps) and `rcpsp.mzn`.
- **For CPU benchmarking:** `data_bl` (40 instances, 20 or 25 tasks, three
  resources; `rcpsp` reports horizons of 19 to 31 on the four sampled,
  `Bl2001`, `Bl2020`, `Bl2501` and `Bl2520`). 33 close within 30 s under the default rules,
  which is enough to compare arms without timeouts. `data_pack` is the
  standard harder companion. Multi-mode `j10`/`j20` are needed for variable
  lengths and heights.
- **For proof verification:** `Bl2019` (203 nodes, 64k lines, 1.6 to 3.6 s
  of VeriPB) and `Bl2011` (687 nodes, 104k lines, 6.4 to 12.7 s) are cheap. `Bl2004`
  (8,917 nodes, 1.19M lines, 381 MB, 390 to 510 s) is the largest a routine run
  should attempt. Anything needing `10⁵` nodes is out of reach (see below).
- **Never run uncapped:** the `hz.cc blocked` probe at `d = 1` past a few
  thousand time points with proofs on. One push of 50,000 writes a 268.8 MB
  proof that had not finished verifying after 24 minutes.

### CPU performance

**The rule ladder**, GCS against itself, on `data_bl`, all 40 instances,
`examples/rcpsp --dzn` (its own in-order search, minimising the makespan),
30 s cap. Main at `7e1c4178`, Release, GCC 15.2, fataepyc-08, 2026-10-04.
`GLIBC_TUNABLES=glibc.malloc.mmap_threshold=33554432:glibc.malloc.trim_threshold=4294967295`.
Twenty jobs ran concurrently, each pinned to its own core, so **wall clock is
indicative only**. Instructions (`perf stat -e instructions:u`) are the
decision metric. Sums and medians are over the **30 instances every arm
closed**. Every arm that closed an instance found the same optimum.

| arm (flags beyond the default) | closed | Σ recursions | median recursions | Σ instructions | Σ wall | median instr./recursion |
|---|---|---|---|---|---|---|
| default (TT + OC + TTOC) | 33 | 2,400,420 (1.000) | 1.000 | 376.7 G (1.000) | 78.4 s | 1.000 |
| `elastic_overload` | 32 | 0.604 | 0.979 | 1.233 | 1.264 | 1.849 |
| `knapsack_overload` | 32 | 0.409 | 0.746 | 0.964 | 1.009 | 2.095 |
| `edge_finding` | 33 | 0.376 | 0.690 | 0.488 | 0.503 | 1.185 |
| `+ time_table_edge_finding` | 33 | 0.236 | 0.513 | 0.396 | 0.497 | 1.607 |
| `+ energetic_edge_finding` | 33 | 0.198 | 0.469 | 0.928 | 0.835 | 4.283 |
| `+ not_first_not_last` | 30 | 0.375 | 0.686 | 1.496 | 1.537 | 3.429 |
| `+ not_first_not_last_published` | 33 | 0.372 | 0.677 | 1.052 | 1.031 | 2.473 |

Ratios are to the default arm, per instance for the medians. The `+` arms
include `edge_finding`. Raw data: `tmp/fd-sched/cumulative/bench/`.

Two readings, and both need the caveat that this is one instance family under
one search.

- **On this search, edge-finding and TTEF are a net win**: half the
  instructions of the default, over 30 instances. That differs from the
  header's "off by default because the sweep taxes the solve whether or not
  anything fires" and from #742's 1.5× tax, which were measured at *identical
  search*. Here the search shrinks by more than the sweep costs.
- **Per node, every strengthening costs more than the default.** In median
  instructions per recursion: `energetic_edge_finding` 4.3×,
  `not_first_not_last` 3.4× (and fewer instances closed), the published
  detection 2.5×, KAOC 2.1×, the elastic rung 1.8×, TTEF 1.6× and plain
  edge-finding 1.2×. Where the total still falls, it is because the search
  shrinks by more. That is in line with each flag's documented reason for
  being off. The `+` arms run through `examples/rcpsp`, whose flags imply
  `edge_finding`. The library's do not (see [Options](#options)).

Which defaults are right is out of scope here. The numbers are recorded for
whoever decides.

**Against Gecode** (#868's comparison, re-run). MiniZinc 2.9.7, the upstream
`rcpsp.mzn` with its own pinned search (`int_search(s ++ [objective],
smallest, indomain_min)`), one pinned sequential run each, 60 s cap, same
machine and date. GCS uses `<build>/glasgow.msc` (absolute path) → `fzn-glasgow`
at `7e1c4178`. Gecode 6.3.0 from the bundle maps `cumulative` to its own
sweep propagator.

| instance | GCS nodes | Gecode nodes | GCS solveTime | Gecode solveTime | outcome |
|---|---|---|---|---|---|
| `data_bl/Bl2001` | 95 | 678 | 0.009 s | 0.005 s | both optimal |
| `data_bl/Bl2004` | 8,091 | 178,234 | 0.148 s | 1.001 s | both optimal |
| `data_bl/Bl2016` | 17,515 | 601,966 | 0.302 s | 2.670 s | both optimal |

The node counts are #868's to the digit. **The trees differ**: our default
(TT plus (TTOC)) is the stronger propagator here, by 7 to 34× in nodes. So no
time ratio is a per-propagator comparison.

**The same-search control.** Both solvers forced onto MiniZinc's
decomposition (`-G std`, so neither uses a cumulative propagator), the decision
variant `objective ≤ 15` on `Bl2001`, UNSAT: **312,333 nodes each**, GCS
16.33 s against Gecode 4.51 s, **3.6× per node**. That is the engine, not this
family. #868 reported 11.8× at `620a62e0`. The engine has improved since, and
this run is a single sample.

**What these benchmarks do not exercise.**

- `data_bl` has constant lengths and heights, no optional tasks and a constant
  capacity per resource. The variable-argument paths (multi-mode `.mm`) and
  presence falsification are not reached.
- Nor are the derived constraints (no presolver flag in the ladder).
- Horizons are short (around 20 to 30), so the horizon-shaped costs above never
  appear.
- On `Bl2014` under the default arm, time-tabling makes 53,535 pushes and
  11,444 overflow contradictions against 1,406 overload contradictions, so a
  per-inference average from it is mostly a time-table average.

### Proof performance

`examples/rcpsp --dzn ... --prove`, `veripb --force-checked-deletion`,
VeriPB 3.0.2, same build and machine, 2026-10-04 and 05. All 48 proofs
verify. Line, byte and `a` counts are deterministic, and the fact-check
reproduced every one. **Times are not.** The machine was shared with other
audits, at a load average of 56 to 71 on 192 cores, and proofs were written
to NFS. The times come from three runs:

- this audit's sweep, run 20-wide and pinned (`proof/proof.tsv`);
- a sequential re-run on one pinned core (`proof/quiet/`);
- the fact-check's run.

They disagree by up to 2.3× for VeriPB, and by up to 10× for the proof-writing
solve. The table gives each default row's range, and the strengthened arms'
times from the sweep only. Read the ratio column as an order of magnitude.

| instance, arm | nodes | OPB lines | proof lines (`Off`) | proof size | VeriPB | solve w/ proof | VeriPB / solve | proof lines (`Inferences`) | `a` lines | of them Cumulative's |
|---|---|---|---|---|---|---|---|---|---|---|
| Bl2019, default | 203 | 2,176 | 64,147 | 6.3 MB | 1.6–3.6 s | 0.12–1.15 s | ~3–26× | 1,834 | 1,401 | 151 (11%) |
| Bl2011, default | 687 | 1,801 | 103,936 | 15.9 MB | 6.4–12.7 s | 0.19–1.12 s | ~9–67× | 5,641 | 4,071 | 995 (24%) |
| Bl2004, default | 8,917 | 3,398 | 1,187,088 | 380.7 MB | 390–510 s | 4.7–14.2 s | ~36–92× | 75,763 | 49,524 | 36,262 (73%) |
| Bl2004, TTEF | 6,812 | 3,398 | 1,437,309 | 544.5 MB | 355.7 s | 7.74 s | 46× | 80,515 | 60,462 | 50,047 (83%) |
| Bl2004, energetic | 6,215 | 3,398 | 1,308,132 | 435.2 MB | 209.6 s | 7.26 s | 29× | 75,913 | 57,651 | 48,162 (84%) |
| Bl2004, KAOC | 8,779 | 3,398 | 1,327,749 | 423.6 MB | 432.3 s | 6.67 s | 65× | 72,177 | 46,352 | 33,440 (72%) |

The OPB is the same in every arm: the encoding does not depend on the rules.

**Own against shared, on Bl2004 default.**

- **Every line by kind.** 711,484 `rup`, 354,203 `pol`, 90,243 `del`, 19,668
  `red`, 9,895 comments, 1,583 `core`.
- **The `red` steps by what they define.**
  - Cumulative's own per-time flags: 990 each of `cb`, `ca` and `cact`.
  - Cumulative's checkpoint recovery: 15,650 (`ckpe` 9,044, `ckpw` 5,512, `ckpn`
    990, `ckpf` 104).
  - The shared order and equality literal definitions: **1,048** (`≥`: 610
    on starts and 20 on the makespan; `=`: 410 on starts and 8 on the
    makespan).
- **The assertion-level difference.** At `Inferences` the same search writes
  75,763 lines. Of the 49,524 assertions, 13,262 belong to the precedence rows
  and the objective. Each of those is at most a line or two when justified, so
  replacing Cumulative's 36,262 assertions with their justifications accounts
  for about 1.10M of the 1.19M lines.
- **So about 31 lines per Cumulative inference**, and about 95% of the proof is
  this family's own. That includes the lazy flag definitions and recoveries,
  which the first citation of a time point pays. The shared literal layers are
  under 1%.
- **Scaling.** On a generated single-resource instance (`--size 8 --seed 5
  --density 0.1 --resources 1 --capacity 4 --max-demand 3 --machine-fraction
  0 --max-duration D`, for `D` = 2, 4, 8, 16 and 32), the cost per Cumulative
  inference settles at **71 to 75 lines** once `D ≥ 8`. Below that it is 246
  at `D = 2` (11 inferences, so mostly the first-citation costs) and 84 at
  `D = 4`. The flag and recovery `red` counts grow linearly with the horizon:
  540 → 5,924 and 408 → 4,490. That is the first-citation cost being paid at
  more distinct time points.

**Too large to verify.** Bl2004's 381 MB proof took 390 to 510 s to check. A `data_bl` instance needing `10⁵` nodes or more (Bl2002, Bl2003,
Bl2007, Bl2012) would write proofs of several GB, and was not attempted.
Verification costing tens of times the proof-writing solve is the family's
headline cost. These timings cannot pin the ratio more closely than that.

**What an external justifier consumes.**

- At `Inferences`, Cumulative's assertions are 11% to 84% of all assertions.
- They come in exactly two wire forms: `cumulative:((constraint_id …))` (every
  push and the overflow) and `… (subhint overload)` (the four overload rungs).
  On Bl2004 default that is 35,288 and 974. The rule counters agree exactly:
  30,522 time-table pushes, 4,766 overflow contradictions and 974 overload
  contradictions.
- The `Inferences` proof is 6% of the `Off` proof's lines and of its bytes
  (22.8 MB against 380.7 MB), and verifies in 0.5 s.
- **But only with no derived Cumulative**, which is #1234.

## Status, gaps, and next steps

### Proof-logging gaps

- **None in the derivations.** Every inference of every rule is justified, at
  `AssertionLevel::Off`, with no `a` oracle anywhere.
- **The proof cannot be read at `Definitions`, `Inferences` or
  `Backtracking` when a derived Cumulative is installed over a posted
  `Cumulative` under the shipped start-checkpoint encoding** (#1234). The
  donor's row family is published at every level, but its flag definer only
  at `Off`, so the recovery cites undefined labels.
  - Reproduced on `examples/rcpsp/sample.dzn` with `--infer-cumulative` or
    `--infer-disjunctive` at `definitions`, `inferences` and `backtracking`,
    and in four test binaries at `definitions` and `inferences`.
  - With `GCS_CUMULATIVE_ENCODING=time-indexed` the same `sample.dzn` runs
    verify `UNDER ASSERTIONS`, and so do the cross-document re-check's
    `CumulativeStrengthening` and `InferredCumulative` runs on four fixtures at
    all three levels. Under the shipped encoding those runs give the syntax
    error. Under that encoding the rows are model rows, found by label before
    any recovery is asked for.
  - A presolver that installs nothing (strengthening on `nothing_to_gain` and
    `all_full`) verifies.
  - Evidence: `tmp/fd-sched/factcheck/crossdoc2/fx/runs.txt`, and
    `crossdoc3/fx/runs.txt` for the nothing-installed and `Links` runs.

  A hints-only proof with a presolver on is therefore unusable today, on the
  encoding that ships.
  - Lifting that one gate is not enough. With `cumulative.cc:935` changed to
    `if (! logger)`, `inferred_cumulative_presolver_test --seed=1` at
    `Inferences` still fails, at `rup 1 i[h3][ge1] >= 1`: a variable height's
    order literal is cited and never defined at that level, which is #1210's
    class (the fact-check's counterfactual,
    `tmp/fd-sched/factcheck/cumulative/a1/cf/`).
  - Over a `Disjunctive2D` donor the symptom is different, either a silent
    decline or a `ProofError` (see the next item but one).
- **The derived constraint's strength changes with proofs on.** With proofs
  on, `install_derived_cumulative` declines when a donor's flags or
  `end_ge_<i>` are missing, or when the recipe declines a stretch. With
  proofs off it never declines. So a presolver can propagate more without a
  proof than with one. This is by design (`derived_cumulative.hh`: "With
  proofs off there is nothing to cite and nothing to decline"), and the
  presolver documents measure how often it happens. It also means that at
  assertion levels above `Off` the end proxies are not derived. So
  `cumulative_donor_view` sets aside every donor task whose length and start
  both vary there (a constant start needs no proxy: the comment at `donor_view.cc:211-212`,
  the test at 215-217),
  and a spec that hands such a task to `install_derived_cumulative` directly
  makes the whole install decline.
- **Over a `Disjunctive2D` donor, the assertion level changes what the
  presolvers do.** Above `Off` the projection publishes neither its flag
  definer nor its row family. This is the `disjunctive_2d` audit's evidence,
  folded into #1234. The probes are
  `tmp/fd-sched/factcheck/disjunctive_2d/assertpz/`, re-run for this
  document:
  - on `disjunctive_2d_presolver_test`'s strip, `InferredDisjunctive` (minimum
    clique 2) posts 1 clique at `Off` and with proofs off, and 0 at
    `Definitions`, `Inferences` and `Backtracking`. It declines at install
    (`declined_by_install = 1`);
  - on the strip, `InferredCumulative` posts 5 cuts at `Off` and 0 above it,
    with `declined_by_install = 5`. On `bars` it posts 1 at `Off` and 0 above,
    with 1 declined;
  - on the test's `bars` instance, `CumulativeStrengthening` posts 1 (816
    solutions) with proofs off and at `Off`. At `Definitions`, `Inferences`
    and `Backtracking` it **throws a `ProofError`**, whose `what()` reads
    `unexpected problem: cumulative strengthening: the donor has no capacity
    row at time 0, which cannot happen for a constraint derived over all of
    its tasks` (`cumulative_strengthening.cc:512`; `ProofError` adds the
    prefix, `proof_error.cc:8`). The solve aborts. On the strip it posts
    nothing and verifies;
  - all of this is the same under `time-indexed`. The proofs verify `UNDER
    ASSERTIONS` wherever nothing throws;
  - at `Links` the same declines happen, but every proof is rejected, for
    #1210's reason. That includes strengthening on the strip, which posts
    nothing.

  The cross-document re-check, `tmp/fd-sched/factcheck/crossdoc2/d2/runs.txt`,
  has the full grid.
- **The posted constraint's strength never changes with proofs.** Every
  arithmetic decision reads the windows rather than the (empty with proofs off)
  flag vectors, and the reason is lazy.

### Known limitations

- **An undecided optional task's start bounds are never pruned.** Only its
  presence can be falsified. "If present, `j` cannot start before `b`" is
  derivable by the same chain stopped early, but there is no conditional-bounds
  store to put it in. The elastic rungs also treat undecided tasks as absent
  (#550 records the presence-by-energy rule as parked).
- **The energy rules ignore a variable capacity.** They also ignore tasks whose
  start is a constant, a view or `{0, 1}`, whose length is a view or `{0, 1}`,
  or (with proofs off) whose height is a view. Such tasks still count through the profile term. Every
  window-sweep rule also needs `overload` on, whatever its own flag says.
- **A view height cannot be proof-logged** (`UnimplementedException` with
  proofs on), though no frontend produces one.
- **No rule lowers a variable height's upper bound**, not even to the
  capacity. Search walks the height's values one at a time: three tasks of
  length 2 over starts `0..4`, heights `2`, `2` and `[2, u]`, capacity 5,
  take 1,002 recursions at `u = 10`, 96,042 at `u = 10³` and 9,600,042 at
  `u = 10⁵`, all for the same 252 solutions (heights above 5 have none).
  Measured at `7e1c4178` on fataepyc-08, 2026-10-05
  (`tmp/fd-sched/cumulative/vh/vh.cc`, from the `cumulative_strengthening`
  audit). #1239.
- **Wide horizons are expensive in time and memory on every call.** One first
  solution over `0..10⁹` took 77.5 s and 29.8 GiB. `0..10¹²` throws
  `std::bad_alloc`, with or without a memory limit. Spans the kernel will
  commit but cannot fill get the process OOM-killed: under a memory limit
  such as a Slurm allocation, any span past the limit; without one, arrays
  that fit singly but not together. Short tasks pushed far
  produce enormous certificates.
- **A derived constraint's makespan initialiser scans the candidate
  horizon** once at the root, proofs on or off: `O(n)` per time point up to
  `min(ub(M), last window end)`, however small the bound it finds (#1267).
- **Large heights, capacities and windows throw `IntegerOverflow`** at four
  sites, within the integer range policy. Three of them throw on feasible
  single-task instances.
- **Time-tabling is not plateau-jumping**, and edge-finding is cubic. Both are
  correct but slow at scale (#705, #742).
- **`cumulative_optional` is outside the cake chain**, and a user who sets
  `GCS_CUMULATIVE_ENCODING` writes a model cake would not reproduce.

### Next steps

Ranked by what they buy against what they cost.

1. **Fix #1234, assertion levels with a derived Cumulative.** It covers a
   rejected proof over a posted donor, and, over a `Disjunctive2D` donor, a
   silent decline (two presolvers) or a `ProofError` (the strengthening
   presolver). There are two directions: publish the definitions
   at every level, or stop deriving rows at assertion levels. Ciaran's call
   which, since it decides what a hints-only proof says about derived rows.
   The work in either direction is more than one gate:
   - `Cumulative`'s and `Disjunctive2D`'s initialisers;
   - the variable-height order literals that are cited and never defined at
     `Inferences` (#1210's class);
   - a lane at `Inferences`. That needs test changes, since
     `derived_cumulative_test` and `inferred_cumulative_presolver_test` check
     proof-comment markers and expect mutation rejections, and both hold only
     at `Off`.

   It is the only thing standing between a presolver run and a hints-only
   proof.
2. **Fix #1235 together with #1223.** That covers the overflow at `supply =
   capacity × width`, at the candidate energy `p × h` and at the profile sum,
   four sites with #1223's. Fix them together with a window product or
   `__int128` intermediates, and a profile sum that stops at the capacity.
   Small.
3. **Count the elastic and knapsack conflicts** in
   `GCS_SCHEDULING_RULE_STATS` (#1236). Each is a one-line increment on the
   elastic branch's `contradiction`, perhaps as its own row. Without it, the
   ladder's `overload` row reads as if those rungs did nothing. On `Bl2019`
   with the elastic rung at `Inferences` there are 45 overload-hinted `a`
   lines and the counter says 41. `rule-counters.md` names two wiring bugs:
   "a row with contradictions and no calls, or firings and no counter". A
   contradiction that no row counts is the same kind of hole, though not one
   that sentence names.
4. **Give the large-domain lane a row that reaches the time-table scans and a
   proof-size row for a long push** (#1237), say `d = 1` and a push of
   `10³`. That makes #705's scan and the chain's linear proof visible, so that
   a plateau-jumping time-tabler (#705, item 1) has a before-and-after. The
   chain itself could advance by whole blocked runs when one contributing set
   covers the run, which would make a push's certificate proportional to the
   profile's plateaus rather than to the distance. That is unmeasured, and a
   design question.
5. **Move `with_encoding` and `CumulativeEncoding` into `innards`** (#1238),
   beside the mutations, and stop reading `GCS_CUMULATIVE_ENCODING` outside
   test builds, or at least say in the header that any binary reads it. Small.
   It closes the one way a user can write an OPB cake would not derive.
6. **Bound a variable height by the capacity** (#1239). A present task
   with `lb(length) ≥ 1` is active at its start, so `h ≤ ub(capacity)`, and
   more generally `h ≤ ub(capacity) − (other mandatory load)` wherever its
   mandatory part lies. Cheap on the propagation side; the certificate needs
   writing, since the start is not fixed. Removes the search over height values
   above the bound, which is linear in how far the domain overshoots it.
7. **Use `bounds_reason` instead of `generic_reason`.** Every rule reads only
   bounds, so stating holes only makes a non-minimal reason larger.
   Proof-neutral on contiguous domains. Measure on an instance with holed
   starts first.
8. **Prune or bound the `Top` caches on long solves.** The guarded-energy map
   is keyed on moving bounds under the energetic rule (#755). Measure memory
   first; nothing here says it binds.
9. **Hints with a payload.** Twelve rules share one bare hint. The window, the
   rule and the time point would turn most `search` verdicts into `hinted`.
   Per the standing rule, that is for the justifier to show is needed, not for
   an issue now.
10. **Stop the makespan scan walking the unused horizon** (#1267). Event-based
    candidates, or a stopping bound past which no candidate can be refuted,
    preserving the bound found. Not "stop at the first candidate that fails":
    supply and energy both move with `μ`. A root-only cost, but it is paid
    with proofs off by every derived constraint that names a makespan. The
    regression should vary the unused horizon at a fixed bound.
11. **Tidy stale comments.** The `CumulativeRules` "All three are on"
    comment; `define_proof_model`'s "emitted alongside the time-indexed block"
    and "Nothing cites these yet" (`cumulative.cc:729-764`), both from before
    the flip.

Out of this document but found here:

- `dev_docs/cumulative-proof-logging.md`'s first ~100 lines have been
  run through clang-format as if they were C++ since `8cb5a9a7` (2026-08-14),
  and are unreadable.
- The same section still says KAOC is "not here", though it is certified (#550).

Both are an out-of-stack docs fix.

## Prior art

- **Propagation.**
  - Time-tabling over compulsory parts is the textbook rule, as in CHIP's
    cumulative (Aggoun and Beldiceanu).
  - The overload check is Wolf and Schrader's energetic one. This
    implementation follows Cloutier and Quimper's (OC') / (TTOC) presentation
    (CP 2026), and their (TTHE-OC) after Kameugne et al. (2024) and (KAOC),
    whose Profile data structure it does not reproduce (#1126).
  - Cumulative edge-finding is Vilím's (CP 2009), and TTEF is Vilím's (CPAIOR
    2011).
  - The guaranteed-energy charge in energetic edge-finding is energetic
    reasoning's quantity (Baptiste, Le Pape and Nuijten). The rule itself is
    edge-finding's, with that charge.
  - Not-first / not-last is Schutt and Wolf (CP 2010) and Kameugne et al.
    (CPAIOR 2018). The window-energy detection here is a deliberate
    weakening, and the published one is certified by a contiguity argument
    that neither paper states (#746).
- **Certification.** Flippo, Sidorov, Marijnissen, Smits and Demirović (CP 2024,
  *A Multi-Stage Proof Logging Framework to Certify the Correctness of CP
  Solvers*) give pseudo-Boolean justifications for time-table reasoning.
  McIlree's thesis (2026, §8.2.1) names scheduling as open beyond that. We
  know of no prior certification of the overload ladder, edge-finding,
  energetic edge-finding or not-first / not-last, over optional tasks or
  variable arguments, or of a horizon-free encoding from which per-time rows
  are recovered on demand.
- **Novel here.**
  - The window-energy lemma and its guarded form.
  - The start-checkpoint encoding and the in-proof recovery of `C_t`.
  - Derived (implied) Cumulatives that write nothing to the model.
  - The contiguity certificate for published not-first / not-last.

## Further reading

- [`cumulative-proof-logging.md`](../cumulative-proof-logging.md) is the long
  design note. It has every derivation step by step: the chained bound
  pushes, the window-energy lemma, the derived constraints, optional tasks,
  each rung of the overload ladder and edge-finding family, the
  start-checkpoint encoding and its recovery (with line costs), and the open
  follow-ups. **Read with care:** its opening section is format-mangled and
  partly stale (see Next steps).
- [`certified-makespan-bounds.md`](../certified-makespan-bounds.md): the
  makespan energy bound, where it differs from Sidorov's `L`, and why the
  deadline is a `pol`. Until #1265 its argument confined every task to
  `[lo, μ)`, which is the special case; see
  [`makespan-bound`](#rule-makespan-bound).
- [`rule-counters.md`](../rule-counters.md): `GCS_SCHEDULING_RULE_STATS`, and
  what `already_true` means for each rule.
- [`cumulative-strengthening.md`](../cumulative-strengthening.md),
  [`inferred-cumulative.md`](../inferred-cumulative.md) and
  [`inferred-disjunctive.md`](../inferred-disjunctive.md): the presolvers'
  design notes. Their audits are the presolver documents linked under
  [Relation to other families](#relation-to-other-families).
- [`subset-sum-strengthening.md`](../subset-sum-strengthening.md): the KAOC
  strengthening's DP and Chvátal–Gomory paths.
- [`disjunctive.md`](disjunctive.md) and [`disjunctive_2d.md`](disjunctive_2d.md):
  the unary resource, which shares the window-energy lemma, and the 2-D
  constraint, which runs this propagator over its projections.
