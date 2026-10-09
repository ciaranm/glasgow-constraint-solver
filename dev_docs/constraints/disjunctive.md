# `disjunctive`: tasks on one machine never overlap

> **Maturity** production ·
> **Audited** 2026-10-04 at `7e1c4178`; re-audited 2026-10-08 at `0a5b4ec6`
> for #1243 to #1249 ·
> **Open issues** filed by this audit: none is still open; filed since, from
> the re-audit: #1299 (what #1248 left: the overload reason, reasons built
> with proofs off, holes); more to file from [Next steps](#next-steps).
> **Closed since the audit**: all seven it filed.
> #1243 and #1244, two strength bugs that made the fixpoint depend on rule
> order, by #1275. #1245 (time-tabling's scan) by #1279, #1246 (the folds) by
> #1287 and #1248 (the reasons) by #1283. #1247 and #1249, the two
> restrictions on not-first / not-last's Θ, by #1288 and #1289, for the
> published detection only. See [Re-audit, 2026-10-08](#re-audit-2026-10-08).
> Also cited: #1234 (derived Cumulatives above `AssertionLevel::Off`). Already
> open and touching this family: #1099 (optional
> tasks in the sorting-network certificate), #762 (what the set-based
> precedence's derived windows cost), #833 (the large-domain policy; this
> family's audit row is `KnownTrip`), #868 (cross-solver comparisons; this
> document gives one, by hand), #742 (`Cumulative`'s cubic edge-finding sweep,
> which this family's has the same shape as). Tracked under #871 and #976.

### Re-audit, 2026-10-08

All seven issues this audit filed were closed on 2026-10-08. This pass brings
the text into line with them at `0a5b4ec6`. Code citations into
`disjunctive.cc`, `disjunctive.hh` and the XCSP3 frontend are now at
`0a5b4ec6`.

| Issue | Fixed by | What changed here |
|---|---|---|
| #1243, the set rule skipped a fixed task | #1275 | the loop keeps a fixed task when the set rule is on, and its push clips to `ub + 1` and fails: the summary, both set-rule entries and the pairwise rules' **Fires when**, [Tests](#tests), the CPU table, [Known limitations](#known-limitations), [Next steps](#next-steps) item 1 |
| #1244, edge-finding and not-first / not-last skipped an overloaded window | #1275 | either switch turns `overload` on at install: [Options](#options), the [overload](#rule-overload), edge-finding and sweep not-first / not-last entries, the CPU table, item 2 |
| #1245, time-tabling's redundant pushes and quadratic scan | #1279 | the scans jump past blocked times; the pushes stay, by decision: the summary, [Interval efficiency](#interval-efficiency), the time-tabling and presence entries, the reconstructibility preamble, item 4 |
| #1246, the folds were derived again at every firing | #1287 | each fold is kept beside the bridges: [Options](#options), [Proof-time state](#proof-time-state), the energetic entries' proof sizes, [Proof performance](#proof-performance), item 5 |
| #1247 and #1249, the restrictions on not-first / not-last's Θ | #1288, #1289 | **for the published detection only**, which now asks about every Θ that can fire, by two sweeps of its own; the sweep detection is unchanged: the summary, both published entries, the sweep entries' **Strength**, [Mutable state](#mutable-state-and-incrementality), the comparison against Gecode, [Known limitations](#known-limitations), item 3 |
| #1248, every reason was the whole scope | #1283 | the pairwise, conflict and time-tabling reasons name only the tasks their certificates cite, and the window rules' whole-scope reason is built once at install; holes are still stated: the summary, the catalogue's preamble, every entry's **Reason**, the reason side of [Interval efficiency](#interval-efficiency), item 6 |
| #1251, `Disjunctive2D`'s negative sizes from MiniZinc | #1272 (documented) | the frontend paragraph's pointer |

**Corrected from review**, not from a fix:

- the comparison against Gecode said its GCS column came from
  `examples/rcpsp`; it came from the `jss_gcs.cc` probe that builds the same
  model as the Gecode side, which is what this pass re-ran.

**What was measured again.** At `0a5b4ec6`, on fataepyc-10, one run at a
time on one pinned core, with `GLIBC_TUNABLES` pinned, and with the probes
in `tmp/fd871-comments-1008/disjunctive/probes/`:
- the job-shop CPU table, except the `la03` timeouts of the default, overload
  and `Cumulative` arms, whose search no fix here changes, and which stay at
  `7e1c4178`, labelled (the default and overload arms are faster now, and
  the old rows ran 16 jobs at once, so the count a 300 s timeout reaches
  would differ); time-tabling on and off in `jss_gcs.cc`, at
  this commit and at `7e1c4178`;
- the comparison against Gecode: both random draws, and the job-shop
  searches and roots, with both detections;
- the `ft06` proof table, the line-kind and per-firing breakdowns, and the
  overload-alone `Off` proof's size (not checked);
- the horizon and scan probes, the four assertion-shape fixtures,
  `sample.jss`, the lanes (uncapped, and capped at `--seed=1`), and the
  `energy` lane's sorting-network seeds.

**Not re-measured**, and still at `7e1c4178`: the perf profile and the
propagator-time split, the strength and `ttdp` probes (no fix changes the
default rules' inferences), the cake chain runs, the MiniZinc Challenge
survey, the fact-check's fixpoint-model figures, and `sample.jss` with
`time_table` off. Figures quoted from a fixing PR are attributed to it.

`Disjunctive` is the unary resource: tasks with variable starts, durations that
are constants or variables, and optionally a `{0, 1}` presence each, such that
no two present tasks run at the same time. The OPB encoding is purely
pairwise: a reified "`i` finishes before `j` starts" flag per ordered pair and
one clause per pair. Every rule is justified against those rows and nothing
else. There are sixteen rules. The mandatory-overlap check runs on every call,
and the strict zero-length check on every call in strict mode. Five more are
on by default. The rest are the standard energetic suite behind switches, all
certified, with the time index re-encoded inside the proof rather than in the
model.

Five things to know before touching it.

- **The default is time-tabling plus pairwise detectable precedences, and the
  first's bound pushes are redundant given the second.** At capacity one, a
  time-tabling step of `j` past a blocker `k` is exactly a detectable
  precedence `k ≪ j`. Over full enumeration of random instances without
  optional tasks, the two settings of `time_table` give the same solution and
  recursion counts. At `0a5b4ec6`, on `ft06` at 54 in the job-shop probe
  `jss_gcs.cc`, whose default arm takes `examples/rcpsp`'s 5,450,366
  recursions, turning the pushes off saves 4.7% of the `instructions:u`
  (387.4·10⁹ against 369.1·10⁹) at the same recursion count. At `7e1c4178`,
  before #1279 and #1283, it saved 10.7% in `examples/rcpsp`. The pushes stay,
  by decision (#1245, closed by #1279): the mandatory-overlap check and
  presence falsification still need the profile, and presence falsification is
  switched by `time_table` too. What #1279 changed is the start scan, which
  now jumps past blocked times rather than trying each start.
- **Two rules whose strength depended on rule order are fixed (#1275).** At
  `7e1c4178` the set-based detectable precedence skipped a task that was
  already fixed (#1243), so its fixpoint depended on whether something else
  fixed the task first. Edge-finding skipped an overloaded window, leaving it
  to an overload check that was off by default (#1244). The set rule now
  keeps a fixed task, and `edge_finding` or `not_first_not_last` turns the
  overload check on. On `ft06` the set rule's infeasible tree at 54 is 12,574
  recursions (53,944 before), and edge-finding's at 55 is 28 (758 before).
- **Not-first / not-last has two detections, and only one is the published
  rule.** The sweep detection (`not_first_not_last`) is a window-energy
  argument: its Θ is always a window's whole contents, and it never pushes a
  task the window contains. That is a deliberate weakening. The published
  detection (`not_first_not_last_published`) asks, since #1288 and #1289,
  about every Θ that can fire. With it and every other rule on, the root
  fixpoint is weaker than Gecode's `unary` on none of 20,000 random
  single-machine instances (197 at `7e1c4178`). In the job-shop model of
  [the comparison against Gecode](#cpu-performance), `la01` at its optimum
  finds a schedule in 240 recursions, where Gecode needs 200 nodes and the
  sweep detection finds none in 320 s. `la03` at 597 still takes 312
  recursions against Gecode's 75, from the same root as Gecode's.
- **The time-indexed certificates put the time index in the proof, not the
  model.** At `7e1c4178`, about half of the proof in the three energetic
  arms measured was per-time at-most-one folds, and 84 to 99% of those
  repeated an earlier fold exactly. #1287 keeps each fold beside the bridges
  (#1246). With that and the other fixes, edge-finding's `ft06`
  proof is 222,313 lines and 13.7 MB at `0a5b4ec6`, against 595,891 and
  29.5 MB, and folds are 9.3% of its lines. Both energetic proofs this
  audit put through `cake_pb_cp`'s full verified chain at `7e1c4178` passed
  it; that was not re-run.
- **A reason names the tasks its certificate cites** (#1248, fixed by #1283).
  That is two tasks for the pairwise push and the two pairwise conflicts, and
  the pushed task and its blockers for time-tabling and presence
  falsification. The set rule, edge-finding and not-first / not-last still
  name every task's start and variable duration, now built once at install.
  The overload check names every start and its window's variable durations,
  built at each firing as before. Every reason still states holes
  (`generic_reason`). Both are #1299. #1283's body measured VeriPB's
  `instructions:u` on the set rule's `ft06` proof at 32.7% fewer.

The long design note is
[`disjunctive-proof-logging.md`](../disjunctive-proof-logging.md). It has
every derivation in more detail than this document repeats, and the
measurements that decided each rule's default. `Disjunctive2D` was in this
family in the template's plan. It is now [`disjunctive_2d.md`](disjunctive_2d.md),
because it is large, and it cites this document for `ComparatorNetwork`.

## What it is

### Semantics

`Disjunctive(starts, lengths)` and `Disjunctive(starts, lengths, presences)`
(`disjunctive.hh:400`). Task `i` is active at time `t` iff `starts[i] ≤ t <
starts[i] + lengths[i]`. For every pair of distinct tasks `i`, `j` that are both
present, one finishes before the other starts:

```
starts[i] + lengths[i] ≤ starts[j]   ∨   starts[j] + lengths[j] ≤ starts[i]
```

`with_strict(bool)` decides zero-length tasks, and defaults to strict.

- **Strict** (MiniZinc `disjunctive_strict`, XCSP3 `zeroIgnored = false`): a
  zero-length task is still a point that may not sit strictly inside another
  task. The pairwise clause above, applied as written, says exactly that.
- **Non-strict** (MiniZinc `disjunctive`, XCSP3 `zeroIgnored = true`): a pair
  in which either task has length zero is unconstrained.

Presences must have domains within `{0, 1}`. An absent task is unconstrained
and constrains nothing. A presence posted as the constant 1 is the same as no
presence, and one posted as the constant 0 removes the task altogether
(`innards::task_presence`, shared with `Cumulative`).

Degenerate cases:

- **Fewer than two participating tasks:** `prepare()` returns false and the
  constraint posts nothing at all, not even an OPB row (`disjunctive.cc:340`).
  Participating means not constantly absent and, in non-strict mode, not of
  constant length zero.
- **Negative durations:** a negative constant throws
  `InvalidProblemDefinitionException` from the constructor. So does a variable
  duration whose initial lower bound is negative, from `prepare()`.
- **Two tasks sharing one start variable:** UNSAT when both have positive
  length, which `disjunctive_test`'s `dup` runs check.

The header's class comment says that in non-strict mode "durations must
currently be constant (variable non-strict durations are future work)". That
is stale. `prepare()` gives every variable duration in a non-strict
constraint a zero-length escape flag, and the `disjunctive_var_sat` chain case
is exactly that shape. Two more comments are stale: `DisjunctiveRules`' "Both
are on by default", from when there were two switches, and `with_rules`'
"(all of them, by default)" (`disjunctive.hh:514-515`). All three are
stale at `0a5b4ec6`; #1265, a comments-only PR merged after it, rewrites
them.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Disjunctive` (strict) | `fzn_disjunctive_strict` ✓ | `noOverlap` 1-D, `zeroIgnored="false"` ✓ | ? | `disjunctive_strict` ✓ | constant or variable durations |
| `Disjunctive` (non-strict) | `fzn_disjunctive` ✓ | `noOverlap` 1-D, `zeroIgnored="true"` ✓ | ? | `disjunctive` ✓ | |
| `Disjunctive` with presences | `fzn_disjunctive_opt`, `fzn_disjunctive_strict_opt` ✓[^opt] | `n/a` (XCSP3's `noOverlap` has no optional form) | ? | `disjunctive_optional`, `disjunctive_strict_optional` ✓ | outside the cake chain |

`gcspy` has no binding for `Disjunctive` at all: `n/a` there, not a gap
anyone has asked about.

[^opt]: The redefinition passes `deopt(s)` and `occurs(s)`, with an absent
fixed start mapped to 0 (`minizinc/mznlib/fzn_disjunctive_opt.mzn`).

The MiniZinc redefinitions post `d[i] >= 0` before the global, as the
standard library's own decomposition does. So a duration that could be
negative does not reach `prepare()`'s check. On a three-task model with
durations in `-1..2`, `glasgow.msc`, Chuffed and Gecode all report 952
solutions (non-strict) and 829 (strict). `Disjunctive2D` does not behave this
way: `diffn` gives `=====ERROR=====` there (#1251), which #1272 documented
as deliberate in `frontend-support-matrix.md`'s noOverlap footnote.

XCSP3 binds both `buildConstraintNoOverlap` overloads, with integer and with
variable lengths (`xcsp_glasgow_constraint_solver.cc:561`, `:570`).

**No frontend can switch on a rule beyond the default.** `fzn-glasgow`,
`xcsp_glasgow_constraint_solver` and `glasgow_scp_solver` never call
`with_rules`, so they all get `DisjunctiveRules{}`. The only route to the energetic rules is the C++ API,
which in practice means `examples/rcpsp`'s `--disjunctive-*` flags.

`frontend-support-matrix.md:90` is stale on this family. It says variable
durations go "via the Cumulative end-proxy technique ... see #384", but there
is no end proxy any more: the duration term cancels inside the pairwise pol
(see [OPB encoding](#opb-encoding)). #1265, merged after `0a5b4ec6`,
rewrites that line to say so. The matrix is being retired, so this
document is where the row now lives.

### Options

**`with_strict(std::optional<bool>)`**, default strict. It changes the **OPB
model**, which is right: strict and non-strict are different constraints. A
`nullopt` means strict, so a runtime flag can be passed straight through.

**`with_rules(DisjunctiveRules)`** (`disjunctive.hh:59`) picks propagation
strength and proof strategy. It never changes the model: the OPB is
byte-identical under every setting. The switches:

| field | default | what it does |
|---|---|---|
| `time_table` | on | time-tabling's two bound pushes, and presence falsification. Not the mandatory-overlap check, which always runs |
| `detectable_precedences` | on | the pairwise rule, both directions |
| `detectable_precedences_set` | off | Vilím's set-based form (#754), both directions. Has no effect unless `detectable_precedences` is on too: it runs inside that rule's loop |
| `overload` | off | the overload check (#730). Turned on whatever this says when `edge_finding` or `not_first_not_last` is (#1275, `disjunctive.cc:468-470`) |
| `edge_finding`, with `edge_finding_lb`, `edge_finding_ub` | off; both halves on | edge-finding (#751) |
| `not_first_not_last`, with `not_first`, `not_last` | off; both halves on | not-first / not-last (#752), sharing edge-finding's sweep |
| `not_first_not_last_published` | off | the published detection instead (#757), over every Θ that can fire, by two sweeps of its own (#1288, #1289). Has no effect unless `not_first_not_last` is on too |
| `overload_max_window` | 0 (no cap) | decline overload conflicts on bigger windows; exists to reproduce a negative result |
| `overload_vocabulary_at` | `ProofLevel::Top` | where the activity flags and guarded rows live |
| `overload_cache_bridge` | on | keep each per-time pairwise at-most-one, and each window's per-time fold of them (#1287) |
| `overload_certificate` | `Cheaper` | time-indexed, sorting network, or per window |
| `overload_crossover` | 300 | `Cheaper` takes the network when the span exceeds 300 × the window's task count |

Each default is set by a measurement in the design note, on 68 generated
RCPSP instances with a unary machine. The energetic rules are off because
their sweeps cost a solve that never fires them. Not-first / not-last is off
because on top of edge-finding it is 2.4% worse in summed recursions, at a
median of 1.000×. That is the sweep detection. #1289's body measured the
published detection, over every Θ, closing 64 of 69 generated unary RCPSP
instances in 60 s against 31 with edge-finding and 27 with neither, and left
the default alone. Those runs predate #1275, which turns `overload` on with
`edge_finding` or `not_first_not_last`. A re-run of #1289's sweep at
`0a5b4ec6` (60 s, 30 jobs at once) closes 64 with either not-first /
not-last detection, 65 with edge-finding and 27 with neither; the published
detection's summed recursions are 0.984× the sweep detection's (median
1.000×) over the 64 instances both close (`tmp/pr1301-factcheck/sweep/`).
The set rule is off pending #762. #1243 and #1244 changed the measured value
of the set rule and of edge-finding, and #1275 has fixed both, but the
design note's tables, which predate it, have not been re-taken.

The last four fields only change the proof, never the inferences.
`overload_max_window` does change the inferences: it declines conflicts, with
or without proofs.

No `with_consistency()`: there is no `gcs::consistency` tag here.
`with_proof_mutation` and `with_presence_mutation` corrupt one step of a
derivation, for the mutation lanes only.

### Variable kinds and views

Starts may be any `IntegerVariableID`: plain variables, constants or views.
Durations may be constants or variables. Presences may be the constant 0 or 1
or a `{0, 1}` variable. Views and constants are handled by the propagator
everywhere. The proof handles them in every pairwise rule:
`emit_before_pol` cites an order-literal definition row through
`need_pol_item_defining_literal`, which works for views (#882). For a
constant start it cites nothing, since the value is already folded into the
flag's row.

**The energetic rules leave some tasks out, and do so whether or not proofs
are on**, so that the inferences do not depend on proofs:

- the overload check skips a task with a constant start
  (`disjunctive.cc:2715`);
- edge-finding and both not-first / not-last detections skip a task whose
  start is not a `SimpleIntegerVariableID`, so views too (`:2349`); the
  published detection's own sweeps take the same candidates;
- the set-based detectable precedence counts only such tasks, and only at
  their declared duration (`:2120`), and a pushed task that is a view or a
  constant gets the pairwise push instead (`:2213`);
- the sorting-network certificate also refuses a view, a signed bit
  encoding, a variable duration, an optional task, or a width past 40 bits
  (`:964`, `:983`). Those windows fall back to the time-indexed certificate
  rather than losing the conflict.

Leaving a task out is sound: it is energy the window is not charged. It
weakens the rule, and `add_view_tests` only exercises the default rules, so
no test measures by how much.

### Reification

None. The pairwise before-flags are full reifications inside the encoding,
but there is no reified `Disjunctive`. Nothing asks for one. An optional task
is the nearest thing, a task-level half-reification, and it is native.

### Relation to other families

- **Decomposes into this family:** nothing. MiniZinc's `disjunctive` reaches
  it directly. A capacity-one `Cumulative` says the same thing with a
  different encoding and different rules, and `examples/rcpsp --unary` picks
  between them.
- **Child constraints:** none.
- **Shared code.**
  - `innards::task_presence`: the presence resolution, shared with
    `Cumulative` so the two agree on what a presence means.
  - `window_energy::derive_guarded_window_energy` and `window_energy_bound`
    (`constraints/innards/window_energy.hh`): the guarded window-energy row,
    shared with `Cumulative`'s energy rules through the `WindowRows` form
    (`cumulative.md`).
  - `recover_am1_from_pairs` (`innards/proofs/am1_from_pairs.hh`): the
    per-time fold. Its other callers are `all_different`'s justification,
    `SubCircuit`, `MinDistance`, `Sort`, `InferredDisjunctive` and the
    `recover_am1` helpers.
  - `ComparatorNetwork` (`innards/proofs/comparator_network.{hh,cc}`): the
    sorting-network certificate. **This document owns its description**
    ([Developer commentary](#developer-commentary)). `Disjunctive2D`'s
    relaxation uses it too.
- **Presolvers.** None rewrites a posted `Disjunctive`, and none reads one as a
  donor: a posted `Disjunctive` is invisible to every presolver.
  `InferredDisjunctive` is named after this family but installs a derived
  capacity-one **`Cumulative`**, not this propagator. Its runtime machinery is
  documented in `cumulative.md`, and its detection in
  [`presolvers/inferred_disjunctive.md`](../presolvers/inferred_disjunctive.md).
  Above `AssertionLevel::Off`, derived Cumulatives break in two ways
  (#1234):
  - **Over a posted `Cumulative` donor**, VeriPB rejects the proof. This
    happens only under the default start-checkpoint encoding, and only when a
    presolver actually installs something.
  - **Over a `Disjunctive2D` projection donor**, `InferredDisjunctive` and
    `InferredCumulative` silently decline. At `Definitions`, `Inferences` and
    `Backtracking` the proof then verifies. At `Links` it is rejected, because
    there every proof of a satisfiable model is rejected at its first `solx`
    (#1210) and the projection fixtures are satisfiable.
    `CumulativeStrengthening` throws, but only where it would
    strengthen something (the fact-check's `bars` instance); where it has
    nothing to strengthen (`strip`) it posts nothing and the proof verifies.

  Neither touches a posted `Disjunctive`.
- **Frontend-only reachability:** none. The C++ API, `.scp`, MiniZinc and
  XCSP3 all post the class directly.

`Disjunctive2D` was this family's candidate merge in the template. That is
settled: **separate**. The two share `ComparatorNetwork` and the pairwise idea,
but no propagator code and not the encoding.

## The proof model

### OPB encoding

For every unordered pair `{i, j}` of participating tasks, with `i < j`
(`define_proof_model`, `disjunctive.cc:359`):

```
bf_{i,j}  ⇔  s_i + l_i ≤ s_j            (constant l_i:  s_i − s_j ≤ −l_i)
bf_{j,i}  ⇔  s_j + l_j ≤ s_i
bf_{i,j} + bf_{j,i} [+ zw_i + zw_j] [+ ¬p_i + ¬p_j]  ≥ 1
```

- `zw_i ⇔ l_i ≤ 0` appears only in **non-strict** mode, and only for a
  **variable** duration. It is added for every such task whatever its bounds,
  because cake does the same (#482). A constant zero-length task is dropped
  from the constraint instead.
- `¬p_i` appears only for a task with a variable presence.

The flags are full reifications, two rows each, with the big-M chosen by the
reifier. The encoding is **definitional**: it is the constraint's meaning and
nothing else. It has no time index, no proof-only variables and nothing
emitted before search.

**Size: `Θ(n²)` rows of `O(bits)` terms each.** Each row carries the bits of
two starts, and of a variable duration. That is logarithmic in the horizon,
not linear. It is the reason the design note gives for the pairwise encoding
(#495).

### Labels

| label | rows | cited by |
|---|---|---|
| `@x[id][i_j][bf][r]` | the forward half, `bf_{i,j} → s_i + l_i ≤ s_j` | every pairwise pol (`emit_before_pol`); the bridge; the sorting network's `ModelSeparation` |
| `@x[id][i_j][bf][f]` | the reverse half | not cited by name by any justification; it is there because the flag is fully reified, and a RUP may propagate over it |
| `@c[id][i_jsepal1]` | the separation clause | the bridge, the set-based and published certificates' ordering step, the sorting network; otherwise only the closing reason-wrapped RUPs, unlabelled |

These names, along with the zero-length flag `x[id][i][zw]`, are cake's own,
which is what lets the proofs chain-verify.

### Cake conformity

The non-optional forms match `cake_pb_cp`'s `disjunctive` encoder,
`strct` included. Four chain cases cover it:

- `disjunctive_sat`;
- `disjunctive_unsat`;
- `disjunctive_var_sat` (non-strict with a variable duration, so the `zw`
  escapes);
- `disjunctive_strict_sat` (a zero-length task inside a wider one, the only
  shape where strict and non-strict differ).

All four pass the full workflow-2 chain at `7e1c4178` with cake `a402078`.
They are mode `none`, with no `opbdiff` label oracle. The comment in
`verified_encodings/scp_cases/CMakeLists.txt` gives the bit encodings (#358)
as the reason; #358 closed on 2026-06-30. Run in `strict` mode today:

- `disjunctive_sat`, `disjunctive_var_sat` and `disjunctive_strict_sat`:
  `opbdiff` matches every row of ours, and cake's OPB has one extra row per
  pair, the same separation clause written a second time for the reversed
  pair (`@c[_1][1_0sepal1]` beside `0_1`). `disjunctive_sat` gives 21
  matches and 3 rows only in cake.
- `disjunctive_unsat`, whose starts are `{0, 1}`: 16 matches, 2 differing and
  6 only in cake. Ours writes one unlabelled `1 i[Sk][b0] >= 0` per start
  variable (three rows), where cake writes a labelled lower- and upper-bound
  row per variable (six rows, e.g. `@i[S0][ub]`, `@i[S1][lb]`), besides the
  duplicated clauses. The CMakeLists comment calls this the binary-encoding
  subcase of #358. #358 itself is about order and equality ladders, and it
  was closed as not planned ("Byte-match (strict `opbdiff`) is not the
  goal"), which is why the
  divergence persists.

All four still verify through cake; only the label oracle would fail.

The in-repo cases only exercise the default rules. **Two energetic proofs
also chain-verify.** `ft06` was minimised with edge-finding alone, and again
with overload, edge-finding, sweep not-first / not-last and the set-based
precedence. Each produced a `.scp`, which went through `cake_pb_cp` to an
OPB, `veripb --elaborate` to a core, and `cake_pb_cp` again on the core. Both
came back `s VERIFIED BOUNDS 55 <= OBJ <= 55`. That covers the time-indexed
overload certificate, edge-finding, sweep not-first / not-last and the set
rule. The published not-first / not-last and the sorting-network
certificate were never put through the chain. They cite the same kinds of
row, but that is reasoning, not a run.

The optional forms are **outside the chain**: cake has no encoder for them.
`constraint_type()` names them `disjunctive_optional` and
`disjunctive_strict_optional`, so the gap is a miss rather than a silent
mismatch.

### Proof-time state

- **At the root.** Nothing beyond the OPB.
- **Lazily, at `ProofLevel::Top` by default** (`overload_vocabulary_at`), for
  the energetic rules only:
  - activity flags `act_{i,t} ⇔ [s_i ≥ t − p_i + 1] ∧ [s_i < t + 1] [∧ p_i]`.
    These are minted by `ProofLogger::create_proof_flag("dovl")`: three `red`s,
    or four with a presence. One is minted per (task, time, counted duration)
    on first use and cached in the propagator.
  - per-time pairwise at-most-ones, the "bridges" (`overload_cache_bridge`),
    one per (pair, time, durations).
  - per-time folds of those bridges into one at-most-one over a window's
    tasks, under the same switch, one per (sorted task set with durations,
    time) (#1287, `disjunctive.cc:829`).
  - one `l_i ≥ declared lb` RUP per variable-duration task, and one `¬zw_i`
    RUP.
  - guarded window-energy rows, one per (task, window, guards, duration).
- **Everything else is at `Temporary`** and is deleted on backtrack: every
  pairwise pol, every energy telescope, every fold when
  `overload_cache_bridge` is off, and every sorting-network wire, comparator
  and lemma.

**Naming is the weak point for an external tool.** An activity flag is
`f[N][dovl]`, with `N` a logger counter. Nothing in its name says which task
or time it is about. It can be located only by reading its defining `red`s,
which do state the conjunction. The sorting network's wires are fresh flags
named by stem and counter, and exist only between their `red` and the
backtrack. The `bf` and `zw` flags are named structurally, after cake.

**Proof-only versus OPB.** The `bf` and `zw` flags are in the OPB. Activity
flags and network wires are introduced in the proof. An activity flag is a
conjunction of order literals, so unit propagation determines it on a
solution. The wires never survive to a solution line.

**Proof-only state with proofs off.** `define_proof_model` fills
`_before_flags` and `_clause_lines` only when proofs are on. The propagator
captures them either way and reads them only inside justifications, which do
not run without a logger. The activity, bridge, fold, floor, escape and
guarded caches are `shared_ptr` maps that stay empty with proofs off.

## The implementation

### Initialisation and global data

No `install_initialiser`. `prepare()` (`disjunctive.cc:282`) resolves
constant durations and the declared lower bounds of variable ones, which the
energetic rules count tasks at. It also resolves presences, drops absent and
(non-strict) zero-length tasks, and decides which tasks get a `zw` escape.
The root cost is the `Θ(n²)` pairwise OPB above, and only with proofs on.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| the one `Disjunctive` propagator | `on_bounds` on every start and variable duration; `on_instantiated` on every variable presence | derived (none) | all sixteen | always; rules within it by `DisjunctiveRules` | not claimed | `DisableUntilBacktrack` after any contradiction |

A single lambda runs the rules in this order:

1. the mandatory-overlap check;
2. time-tabling, including presence falsification;
3. the two detectable-precedence rules;
4. edge-finding and the sweep not-first / not-last over one sweep, then the
   published not-first / not-last's two sweeps;
5. the overload check;
6. the strict zero-length check.

Every inference is made in the same call that detected it. It returns
`Enable` and never claims idempotence. **It is not idempotent**, by reading:

- Time-tabling builds its profile once per call, before any push. A push that
  creates a mandatory part is therefore invisible to the tasks the loop has
  already passed.
- The energetic sweep reads `est` and `lct` once into `candidates`.

The engine re-runs it on its own changes, so the per-node fixpoint is reached
anyway. The fixpoint is unique only where every rule is monotone. The two
rules this audit found that were not (#1243 and #1244) are fixed by #1275;
the re-audit did not look for others.

**Holes affect** is `derived` and says nothing. Every rule reads bounds only:
`state.bounds`, `lower_bound`, `upper_bound`, `has_single_value`. A presence
is `{0, 1}`, so it has no interior. Every reason does state holes, through
`generic_reason`, but that is a cost, not a sensitivity. #1283 narrowed which
tasks a reason names and left that as it was (#1299).

### Mutable state and incrementality

No backtrackable state at all: everything is recomputed from the domains on
every call. That includes:

- the profile, in `O(H)`;
- the detected sets, in `O(n²)`;
- the energetic sweep, in `O(n³)`, and the published detection's two
  sweeps, `O(n³)` each (#1289);
- the overload sweep, in `O(n²)`.

The only state that persists is proof-side: the vocabulary caches above.
They grow monotonically over the search and are never trimmed. At `Top` they
are bounded by about `n²·H` bridges and `n·H` flags, plus one fold per time
point for each distinct window task set an energetic rule has cited. The design note
measured the database tax of keeping them as flat, from 4,692 to 38,460
standing rows.

What could be maintained instead:

- an incremental profile, or the sorted mandatory parts instead of a profile
  at all. #1245 raised it, and #1279 closed #1245 with the jump only;
- Θ-trees for the sweeps (#742's suggestion on the `Cumulative` side). At
  `7e1c4178` this document said they would also close #1247 and #1249 if
  they reported the set they used. #1289 closed both another way, with two
  more `O(n³)` sweeps over a complete family of sets, so a Θ-tree is now only
  the route to a cheaper sweep.

### Interior values and optional pruning

**What this family offers:** `None.` It installs no
optional-interior-pruning pair, and has no `consistency::Auto`.

**What this family observes:** nothing in anyone else's holes. **The whole
vocabulary of this family is bounds.** Starts and variable durations are
`on_bounds`, and presences are `on_instantiated` on a `{0, 1}` domain. So a
model whose only consumers of some variables are `Disjunctive`s lets every
other constraint's `consistency::Auto` drop its interior pruning on them,
which is the case that makes the mechanism pay. No propagator here understates
its sensitivity, so nothing was declared through
`Triggers::holes_affect_propagation`.

### Robustness and limits

- **Unbounded domains.** The profile is a `vector<int>` sized by the horizon
  (see [Interval efficiency](#interval-efficiency)), so every call allocates
  `4H` bytes. Whether a solve survives depends on memory. Under a 16 GB
  `ulimit`, the 8-task probe at `H = 10⁹` completes (59 s, 4 GB per call),
  but a start domain of `0..2⁴⁰` aborts with `std::bad_alloc` from inside
  propagation on the first call, and so does the integer-range policy's
  limit, `2⁶⁰ − 1`. This is #833's `KnownTrip`. Every other path is
  width-independent.
- **Negative values and zero.**
  - Negative starts are fine for every rule.
  - The sorting-network certificate refuses a start whose bit encoding is
    signed, and falls back.
  - Negative durations are rejected (see [Semantics](#semantics)).
  - Zero-length tasks:
    - Strict mode keeps them, but only the all-fixed leaf check constrains
      them ([strict-zero-length-leaf](#rule-strict-zero-length-leaf)). A zero-length task
      whose start can lie only inside a fixed task is not pruned. It is
      enumerated value by value until both are fixed.
    - Non-strict mode drops a constant zero-length task. A variable duration
      with lower bound 0 takes part in no inference until its lower bound
      rises.
- **Degenerate shapes.**
  - Fewer than two participating tasks posts nothing.
  - Aliased starts are handled by the pairwise rows.
  - Two tasks sharing one presence variable are handled explicitly in the
    bridge, which adds the forward presence row once per presence *variable*
    (`disjunctive.cc:785`).
  - A constant start is folded into the `bf` rows.
- **Overflow.** All arithmetic is in checked `Integer`. The sorting network
  caps its width at 40 bits, so that its `2^width` guard coefficients cannot
  overflow. Edge-finding's sweep keeps adding past an overloaded window
  (`continue`, not `break`), so it can sum `n` durations. But any instance
  whose durations could make that overflow has a horizon beyond `2⁶⁰`, and
  the profile's allocation fails first. No overflow is reachable before the
  horizon array is.

### Interval efficiency

1. **The propagation side.** One site has cost proportional to something
   other than the task count, and two more are linear in a domain's width:
   - **The profile** (`disjunctive.cc:1662`). It is a `vector<int>` over the
     smallest `lb(s)` to the largest `ub(s) + ub(l) − 1`, over the tasks that
     are not absent and can have positive length. It is allocated, filled
     with every present task's mandatory part, and scanned in full for an
     overlap, on every call.
     - On 8 tasks over `[0, H]` (`horizon.cc`), the 16 propagator calls to a
       first solution take 0.18 ms at `H = 10⁴`, 5.9 ms at `10⁶`, 506 ms at
       `10⁷` and 5.2 s at `10⁸` (`0a5b4ec6`, fataepyc-10, the median of three
       pinned runs). At `7e1c4178` they took 0.2 ms, 11 ms, 455 ms and 4.7 s
       on fataepyc-08.
     - It is guarded by `GCS_CHECK_LARGE_DOMAIN`, which is why the audit row
       trips.
     - All three of its consumers could read sorted mandatory parts instead:
       the overlap check, the pushes and presence falsification. #1245
       raised this, and #1279 did not take it up.
   - **Time-tabling's start scan** (`:1855`, `:1982`). Since #1279 it asks
     for the last (upwards) or first (downwards) blocked time in a
     candidate's window and jumps past it (`last_blocked` and
     `first_blocked`, `:1789`, `:1795`), finding the start the old
     start-by-start scan found. By reading: each jump walks at most `p_j`
     times, and every two jumps move the candidate at least `p_j`, so a scan
     costs `O(distance moved + p_j)`, where at `7e1c4178` it was
     `O(blocked span × p_j)`.
     - Task A fixed at `[L, 2L)` and task B in `[L/2, 3L]` of length `L`
       (`scan.cc`, two tasks) take 0.13 ms at `L = 10³`, 0.32 ms at `10⁴`,
       0.82 ms at `3·10⁴` and 2.6 ms at `10⁵` (same build and machine).
       At `7e1c4178` they took 4 ms, 40 ms, 354 ms and 3.9 s.
     - This is the capacity-one form of `Cumulative`'s #705 item 1.
   - **Presence falsification's detection** is the same jump scan run to
     `ub(s_j)` (`:1855`), for every undecided task on every call, so it is
     linear in that task's domain width plus `p_j`. Only the chain the
     justification walks, with a logger, is bounded by blockers.

   Everything else is bounded by the task count:
   - detectable precedences are `O(n²)` per call, `O(n² log n)` with the set
     rule's sorts;
   - the energetic sweep is `O(n³)`, and so is each of the published
     detection's two sweeps;
   - the overload sweep is `O(n²)`.

   No energetic sweep walks values: windows and the published detection's
   sets are bounded by tasks' `est`, `ect`, `lst` and `lct`. `State`'s
   per-value iterators are used nowhere.
2. **The reason side.** Since #1283 a reason names the tasks its
   certificate cites (see the [catalogue's preamble](#inference-catalogue)),
   but it is still `generic_reason`, materialised **per run**, not per value
   (#935): two bound literals per variable, plus one `not_in_range` per hole
   run. Holes are never needed. Building the reason is still **not guarded
   on `want_reasons()`**, but what is built changed:
   - the set rule's, edge-finding's and not-first / not-last's whole-scope
     reason is built once at install (`disjunctive.cc:458`), and each call
     only adds the presence literals;
   - a pairwise or zero-length reason builds a list of its two tasks'
     variables at each inference (`reason_for_tasks`, `:543`);
   - a time-tabling or presence reason is the whole scope with proofs off,
     and the pushed task plus its chain's blockers with them on
     (`chain_reason`, `:1559`);
   - the overload check copies every start into a fresh list at each firing
     (`:2787`).

   The `presence_lits` list is built once per call.
3. **The proof side.**
   - The pairwise rules emit `O(1)` lines per dichotomy, each `O(bits)` terms,
     whatever the width. On the 8-task probe (`horizon.cc ... prove`), the
     proof is 527 lines at `H = 10³` and at `H = 10⁶`. Only its bytes grow,
     from 28 KB to 46 KB, with the bits. At `7e1c4178`, before #1283
     narrowed the reasons, it was 539 lines, 32 KB to 51 KB.
   - The time-indexed energetic certificates are **per time point** of the
     window: activity flags, bridges, folds and energy telescopes are all
     linear in the window's span. Bridges and, since #1287, folds are kept,
     so a window seen before cites one fold per time point and derives
     nothing.
   - The sorting network is flat in the span but `O(w³)` in the window's task
     count. `Cheaper` picks between them by a **width test**, span > 300·w,
     which is the shape the template asks for. On job shops it never picks
     the network.
   - Presence falsification is linear in blockers.
4. **Where the family stands in the audit lane.**
   - `large_domain_audit_test.cc:766`, `Disjunctive`, is `KnownTrip`: three
     wide starts with constant durations of 2 trip the horizon array.
   - It has no row in the proof-size case.
   - **What the row does not vary:**
     - **duration**. At `7e1c4178` the start scan was quadratic in it, a
       hazard the lane could not reach; #1279 made the scan linear;
     - **the energetic rules**, which are off in the row, so their per-time
       certificates at a wide span are never reached;
     - **variable durations, optional tasks and views.**

## Inference catalogue

Facts that hold for every rule:

- **Reason.** Since #1283, `generic_reason` over the tasks the certificate
  cites: for each, its start, its duration if that is a variable, and
  `presences[i] = 1` if it is known present (`reason_for_tasks`,
  `disjunctive.cc:543`). Per rule:
  - mandatory overlap, the pairwise detectable precedences and the strict
    zero-length check: the two tasks;
  - time-tabling and presence falsification: the pushed task and the
    blockers its chain cites, with proofs on, and the whole scope with them
    off, where nothing reads it (`chain_reason`, `:1559`);
  - the set-based precedence, edge-finding and both not-first / not-last
    detections: every start and variable duration, built once at install
    (`:458`), plus every task known present;
  - the overload check: every start, its window's variable durations, and
    every task known present (`:2787`).

  It is per run, not per value, and not guarded on `want_reasons()`. An
  undecided presence is left out, because it has no fact to state. At
  `7e1c4178` every rule's reason was every start, plus durations, plus every
  present task's presence.
- **Hint.** `hints::Disjunctive` (`disjunctive/hints.hh`), wire name
  `disjunctive`, with one field:
  - `originator : ConstraintID`, the owning constraint.

  Nothing says which rule fired, which pair, or which window.
- **Every justification reads only its reason and the model.** Bounds that
  the arithmetic needs are captured at detection time and carried into the
  closure, because by the time a justification runs an earlier push has
  landed (the trap #754's build hit).
- **Escapes.** Before any non-strict pol, a justification pins every involved
  task's `zw` false under the reason (`pin_escapes`).
- **Assertion shapes.** These were checked against `a` lines at
  `AssertionLevel::Inferences` with `tmp/fd-sched/disjunctive/assert/`, and
  the four `shapes.cc` fixtures were re-run at `0a5b4ec6`. Three
  rules are conflicts that call `contradiction()` and assert `¬reason`:
  mandatory overlap, overload, and the strict zero-length check. Every other
  rule asserts `conclusion ∨ ¬reason`. A failed push takes that shape too,
  and is closed by the backtrack.
- **Offline reconstructibility, for every rule: `search`.** The baseline
  context's reason states the bounds of every task the certificate cites
  (of every task, for the window rules), the durations the rule reads, and
  their presences known to be 1. Those are the facts the detection that
  fired read about the tasks it used. So a reconstructor can re-run
  detection on them, with every other task at its declared domain, and take
  the rule and witness that yield the asserted literal:
  - the pair, for a pairwise rule;
  - the blocker chain, for time-tabling;
  - the window and Θ, or the cut, for the energetic rules.

  Then it emits that rule's derivation. The cost is one propagator call per
  assertion, plus trying up to sixteen rules. Replayed literally, that call
  is `O(n³ + H)` with every rule on, plus time-tabling's and presence
  falsification's start scans, which since #1279 are linear in a domain's
  width plus `p_j` per task (see [Interval efficiency](#interval-efficiency)).
  At `7e1c4178` that term was `O(blocked span × p_j)` and could exceed the
  rest with only two tasks. This reconstruction
  assumes the detection code, or an equivalent oracle, is available to the
  reconstructor. A hint naming the rule and its witness would make every
  rule `hinted`. Whether that is worth carrying is
  [Next steps](#next-steps) item 9.

### Rule: mandatory-overlap

- **Infers** — contradiction.
- **Fires when** — two present tasks' mandatory parts `[ub(s_i), lb(s_i) +
  lb(l_i))` overlap at some time point. It runs on every call, whatever
  `DisjunctiveRules` says (`disjunctive.cc:1686`). At an all-fixed leaf it is
  what makes the propagator a checker.
- **Strength** — `partial`: it refutes any state where two mandatory parts
  overlap, which at an all-fixed leaf is the full check.
- **Algorithm** — fill the profile, then scan it for a count above 1. It costs
  `O(H + Σ mandatory parts)`, and the first two tasks covering the time
  are named in `O(n)`. Time-tabling (Nuijten 1994; Baptiste, Le Pape and
  Nuijten 2001).
- **Why it is true** — both tasks must occupy the common time point whatever
  their starts. So neither can finish before the other starts, and the
  pair's clause is violated.
- **Proof technique** — `pol`: two of them, each over a `bf` row's forward
  half plus the operands' order-literal definition rows (the starts cancel),
  forcing both `bf` flags false under the reason. Then `RUP`: the closing
  reason-wrapped step unit-fails the separation clause. Ours, the "pairwise
  vocabulary" of the design note. The bare RUP alone is not enough when the
  overlap margin is smaller than the residual bit range: that is the
  cross-variable limit in [`veripb-facts.md`](../veripb-facts.md).
- **Reason** — the two tasks (#1283). The pols need only their start
  bounds and duration lower bounds.
- **Assertion** — `¬reason`, from `contradiction()`. Checked:
  `a 1 ~[a ≥ 0] 1 [a ≥ 2] 1 ~[b ≥ 1] 1 [b ≥ 3] >= 1`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search` (preamble): find the pair whose
  mandatory parts overlap under the reason, in `O(n²)`.
- **Proof size** — two pols, plus up to four order-literal definitions, plus
  the closing RUP. `O(bits)` terms per line, constant in the task count.
- **Gaps** — None.
- **Tightness** — Not shown. No mutation lane targets it.

### Rule: time-table-lb

- **Infers** — `s_j ≥ new_lb`.
- **Fires when** — `time_table` is on, `j` is present with `lb(l_j) > 0`, its
  start is not fixed, and `[lb(s_j), lb(s_j) + lb(l_j))` meets the mandatory
  part of some other present task. `new_lb` is the smallest start at which
  `j` fits the profile, with `j`'s own mandatory part discounted
  (`disjunctive.cc:1847-1860`).
- **Strength** — `partial`: time-table consistency at capacity one on `s_j`'s
  lower bound. The root-fixpoint probe found no start endpoint touching
  another task's mandatory part on 2,000 random four-task roots. It is not
  `bounds(Z)`: 457 of those 2,000 roots under the default rules have an
  unsupported start endpoint. **Subsumed** by
  [detectable-precedence-lb](#rule-detectable-precedence-lb) at the
  fixpoint: see that rule. It is kept anyway, by decision (#1245, closed by
  #1279).
- **Algorithm** — from `lb(s_j)`, jump past the last blocked time in each
  candidate window until one fits (#1279). That is `O(distance pushed +
  lb(l_j))`; at `7e1c4178` it tried each start in turn, `O(blocked span ×
  lb(l_j))` (see [Interval efficiency](#interval-efficiency)). With a
  logger, the blockers are then chosen greedily, deepest mandatory end first,
  `O(n)` each.
- **Why it is true** — any start in `[lb(s_j), new_lb)` would make `j` overlap
  a present task's mandatory part, which that task occupies whatever its
  start.
- **Proof technique** — a `RUP sequence`. Per blocker `k` there are two
  `pol`s, as in [mandatory-overlap](#rule-mandatory-overlap):
  1. one refutes `bf_{j,k}` from the running bound;
  2. one folds `bf_{k,j}` onto the target order literal.

  Every step but the last deposits `[s_j ≥ target]` under the reason by
  `RUP`, and the closing RUP concludes. Ours (#495).
- **Reason** — `j` and the blockers its chain cites, whose bounds and
  duration lower bounds are what the chain needs (#1283).
- **Assertion** — `[s_j ≥ new_lb] ∨ ¬reason`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`: rebuild the profile from the
  reason and re-run the scan and blocker choice.
- **Proof size** — two pols plus one deposit per blocker. It is linear in
  the **blockers**, not in the distance pushed (one step per blocker,
  however long). The terms are `O(bits)`.
- **Gaps** — None.
- **Tightness** — Not shown. The dichotomy is shared with detectable
  precedences, but the time-tabling chain always passes
  `disjunctive_proof_mutation::None{}` (`disjunctive.cc:1648`, `:1657`), so no
  lane can corrupt a time-tabling step.

### Rule: time-table-ub

- **Infers** — `s_j ≤ new_ub`.
- **Fires when** — the mirror of [time-table-lb](#rule-time-table-lb),
  scanning downward from `ub(s_j)`. Blockers are chosen leftmost mandatory
  start first.
- **Strength** — `partial`: time-table consistency on the upper bound.
  Subsumed by
  [detectable-precedence-ub](#rule-detectable-precedence-ub), and kept, as
  time-table-lb is.
- **Algorithm** — the downward scan, jumping to `p_j` before the first
  blocked time in each candidate window (`disjunctive.cc:1982`), at the same
  cost.
- **Why it is true** — the mirror: a start in `(new_ub, ub(s_j)]` would put
  `j` across a mandatory part.
- **Proof technique** — a `RUP sequence`: the mirrored dichotomy per blocker
  (`emit_ub_dichotomy`), with deposits `[s_j < target + 1]`.
- **Reason** — as time-table-lb.
- **Assertion** — `[s_j < new_ub + 1] ∨ ¬reason`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`, as time-table-lb.
- **Proof size** — as time-table-lb.
- **Gaps** — None.
- **Tightness** — Not shown. The chain passes `None{}` (`disjunctive.cc:1657`),
  as for time-table-lb.

### Rule: presence-falsification

- **Infers** — `p_j = 0`.
- **Fires when** — `time_table` is on, `j` is undecided, and no integer start
  in `[lb(s_j), ub(s_j)]` fits the profile of the **present** tasks
  (`disjunctive.cc:1862`). This applies even when `j`'s start is fixed.
- **Strength** — `partial`: falsification against time-table consistency.
- **Algorithm** — the lb jump scan run to `ub(s_j)`, linear in `s_j`'s
  domain width plus `p_j` since #1279, for every undecided task on every
  call. Then, with a logger, a greedy blocker chain over the whole range.
- **Why it is true** — if `j` were present, every start would overlap a
  present task's mandatory part.
- **Proof technique** — a `RUP sequence`: the lb chain of
  [time-table-lb](#rule-time-table-lb), with `¬p_j` carried as an extra
  disjunct on every deposit (`[s_j ≥ target] ∨ ¬p_j`). The last target is one
  past `ub(s_j)`, which the reason refutes, so the closing RUP concludes
  `¬p_j`. The pols themselves are unchanged, because the `bf` rows are
  reified unconditionally. Ours (#735).
- **Reason** — as time-table-lb: `j`'s start and the blockers', with each
  present blocker's presence literal (#1283).
- **Assertion** — `¬p_j ∨ ¬reason`. Checked at `0a5b4ec6`, with `j` = `b`
  and blocker `a`, and the third task `x` no longer named:
  `a 1 ~[pb][b0] 1 ~[b ≥ 0] 1 [b ≥ 3] 1 ~[a = 0] 1 ~[pa = 1] >= 1`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`, as time-table-lb.
- **Proof size** — linear in blockers.
- **Gaps** — None.
- **Tightness** — `disjunctive_optional_mutation_{wrong_task, one_too_far}`
  are rejected, with `emit_nothing` as the control. The rule is
  conflict-shaped: once the chain has cornered the task, every RUP under the
  extended context is vacuous. So the lanes corrupt the destination, not the
  route (`disjunctive_mutations.hh`).

### Rule: detectable-precedence-lb

- **Infers** — `s_j ≥ max over detected predecessors k of (lb(s_k) +
  lb(l_k))`, clipped to `ub(s_j) + 1`.
- **Fires when** — `detectable_precedences` is on (the default), `j` is present
  with `lb(l_j) > 0`, `s_j` is not fixed (or is, when the set rule is on:
  #1275, `disjunctive.cc:2089`), and some present `k` has
  `lb(s_j) + lb(l_j) > ub(s_k)` (`:2128`). If the set rule is
  on and reaches further, [set-detectable-precedence-lb](#rule-set-detectable-precedence-lb)
  takes the push instead.
- **Strength** — `partial`: detectable-precedence consistency. The probe found
  no root violating it on 2,000 random four-task roots. **It subsumes
  time-tabling's pushes** at the fixpoint. A time-tabling step over `k` needs
  `[lb(s_j), lb(s_j) + lb(l_j))` to meet `[ub(s_k), lb(s_k) + lb(l_k))`, which
  is exactly this detection, and this rule pushes to `lb(s_k) + lb(l_k)`, at
  least as far. Measured with `time_table` on and off, under full enumeration
  (`strength/ttdp.cc`): the same solution and recursion counts on 5,000
  random instances without optional tasks, constant and variable durations.
  `ft06 --deadline 54` also has the same recursion count, but not the same
  propagations: at `7e1c4178`, 69.57 million against 74.59 million with
  time-tabling off. At `0a5b4ec6`, in `jss_gcs.cc`, the
  recursion count is again 5,450,366 both ways.
  With optional tasks the counts do differ (130 of 1,000 four-task instances
  at seed 1 in the fact-check's `ttdp2`, and 190 to 217 at five tasks over seeds 1 to 5), because `time_table` also switches presence
  falsification, which this rule does not replace.
- **Algorithm** — one `O(n)` scan per task, so `O(n²)` per call. Pairwise,
  pushing to the latest single predecessor's end, rather than Vilím's
  Θ-tree `ect(Ω)` (Vilím 2004).
- **Why it is true** — `j` cannot finish before `k` starts, so by the pair's
  disjunction `k` finishes before `j` starts, and `s_j ≥ s_k + l_k ≥ lb(s_k) +
  lb(l_k)`.
- **Proof technique** — `pol` + `RUP`: one dichotomy (two pols), exactly one
  step of the time-tabling chain with no deposit. The detection condition is
  the refuting pol's positive degree. Ours (#731, #734).
- **Reason** — `j` and `k` (#1283). The certificate needs `lb(s_j)`,
  `ub(s_k)`, `lb(s_k)` and the two duration lower bounds.
- **Assertion** — `[s_j ≥ target] ∨ ¬reason`. Checked: `a 1 [j ≥ 3] 1 ~[j ≥ 2]
  1 [j ≥ 10] 1 ~[k ≥ 0] 1 [k ≥ 4] >= 1`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`: the pair, in `O(n²)`.
- **Proof size** — two pols, plus definition rows, plus a `%` comment. The
  median is 4 lines per firing on `ft06` (`proofs/perfiring.py`).
- **Gaps** — None.
- **Tightness** — `disjunctive_precedences_mutation_{skip_refutation,
  skip_fold, loose_bound, one_too_far}` are rejected, with `emit_nothing` as
  the control, on the `tight` fixture, where each pol is needed. Every push
  that fixture's mutated proofs contain is an lb push. On other fixtures
  either pol alone can suffice (design note, "Which of the two pols is
  load-bearing").

### Rule: detectable-precedence-ub

- **Infers** — `s_j ≤ min over detected successors k of ub(s_k) − lb(l_j)`,
  clipped to `lb(s_j) − 1`.
- **Fires when** — the mirror: `lb(s_k) + lb(l_k) > ub(s_j)`.
- **Strength** — `partial`, the mirror. It subsumes
  [time-table-ub](#rule-time-table-ub).
- **Algorithm** — the same scan.
- **Why it is true** — `k` cannot finish before `j` starts, so `j` finishes
  before `k` starts, and `s_j ≤ s_k − l_j ≤ ub(s_k) − lb(l_j)`.
- **Proof technique** — `pol` + `RUP`, the mirrored dichotomy.
- **Reason** — `j` and `k`, as the lb rule.
- **Assertion** — `[s_j < target + 1] ∨ ¬reason`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`.
- **Proof size** — as the lb rule.
- **Gaps** — None.
- **Tightness** — Not shown. The lanes' fixture fires no ub push: with
  `--mutate=skip_refutation` its proofs carry `push=lb` twice and `push=ub`
  never.

### Rule: set-detectable-precedence-lb

- **Infers** — `s_j ≥ ect(Ω') = est(Ω') + p(Ω')` for the maximising left cut
  `Ω'` of the detected predecessors, when that exceeds the pairwise target.
- **Fires when** — `detectable_precedences_set` and `detectable_precedences`
  are both on (the first is off by default, and runs inside the second's loop,
  `disjunctive.cc:2069`), `j` is present with `lb(l_j) > 0`, and `s_j` is a
  simple variable, **fixed or not**. Only predecessors that are simple
  variables with a positive declared duration count, at that duration
  (`:2120`). A fixed `j`'s push clips to `ub(s_j) + 1` and fails.
- **Strength** — `partial`: Vilím's detectable-precedence rule, restricted to
  the vocabulary above. At `7e1c4178` **it did not see a task whose start
  was already fixed**, so its fixpoint depended on whether time-tabling
  fixed `j` first (#1243). #1275 keeps a fixed `j` when the set rule is on
  (`:2089`), and its `fixed` fixture checks the root refutation with
  time-tabling on and off. On `ft06 --deadline 54` the rule now takes 12,574
  recursions, where it took 53,944 at `7e1c4178`.
- **Algorithm** — sort the detected predecessors by `est`, descending, and
  accumulate. The maximum over subsets is attained at a left cut. That is
  `O(n log n)` per task, a measurement implementation rather than a
  Θ-tree (#754).
- **Why it is true** — every `k ∈ Ω'` precedes `j`. So under `s_j < T` all of
  `Ω'` lies in `[est(Ω'), T − 1)`, which is `p(Ω') − 1` wide, one unit too
  narrow to hold `p(Ω')` of work on one machine.
- **Proof technique** — a `RUP sequence` with `pol`s:
  1. Per cut task, a derived two-literal clause `[s_j ≥ T] ∨ ¬[s_k ≥ T −
     p_k]`. It is built from the pairwise refutation pol, the separation
     clause and the ordering's arithmetic (`precedence_clause`).
  2. The guarded window-energy rows over the derived window
     (`derive_guarded_window_energy`). Their high guards are discharged by
     those clauses, and their low guards by the reason.
  3. The per-time at-most-ones (bridge, then fold), both kept and cited
     again since #1287.
  4. One summed `pol` that derives `[s_j ≥ T]`.

  It is #757's derived-window mechanism mirrored. Ours.
- **Reason** — the whole scope (preamble). The certificate needs the cut's
  bounds, captured at detection.
- **Assertion** — `[s_j ≥ target] ∨ ¬reason`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`: recompute the detected set and
  its best cut from the reason.
- **Proof size** — the fold dominates. It is per time point of the derived
  window, `O(|Ω'|)` lines with `O(|Ω'|)` terms each, so `O(|Ω'|²·span)`
  terms, plus guarded rows that are cached across firings. The median is
  35 lines per firing on `ft06`, with the set rule alone and with every rule
  on, at `0a5b4ec6`; at `7e1c4178`, before the folds were kept, it was 62 and
  101.
- **Gaps** — None.
- **Tightness** — Not shown for this half. The set rule's lanes run on a
  fixture whose set-based firings are all ub pushes
  (`disjunctive_set_precedences_test.cc:207`); see the ub rule.

### Rule: set-detectable-precedence-ub

- **Infers** — `s_j ≤ lst(Ω') − lb(l_j)`, with `lst(Ω') = lct(Ω') − p(Ω')`
  over the minimising right cut of the detected successors.
- **Fires when** — the mirror, with the same restrictions. A fixed `j` takes
  part here too.
- **Strength** — `partial`, the mirror.
- **Algorithm** — sort by `lct`, ascending.
- **Why it is true** — the mirror: all of `Ω'` lies in `[L + 1, lct(Ω'))`.
- **Proof technique** — as the lb rule, with the guards swapped. The low
  guard is discharged by the derived clause, the high guard by the reason.
- **Reason** — the whole scope, as the lb rule.
- **Assertion** — `[s_j < target + 1] ∨ ¬reason`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`.
- **Proof size** — as the lb rule.
- **Gaps** — None.
- **Tightness** — `disjunctive_set_precedences_mutation_{skip_fold,
  drop_energy, drop_clause, rup_clause, one_too_far}` are rejected, with
  `emit_nothing` as the control, on a generated fixture with a cut of three,
  which fires this half twice and the lb half never. The design note says
  `|Ω'| ≥ 3` is what makes the fold load-bearing.

### Rule: overload

- **Infers** — contradiction.
- **Fires when** — `overload` is on (off by default, but turned on by
  `edge_finding` or `not_first_not_last` since #1275). Some window `[a, b)`
  with `a` an `est` and `b` an `lct` contains present tasks with non-constant
  starts whose declared durations sum to more than `b − a`
  (`disjunctive.cc:2687`). It takes the **smallest** such window, by task
  count. `overload_max_window` can decline it.
- **Strength** — `partial`: overload checking (Vilím 2004) over the counted
  tasks.
- **Algorithm** — a full `O(n²)` sweep over windows, with tasks in `lct`
  order, keeping the minimum. A Θ-tree would make it `O(n log n)`; this sweep
  measures the smallest refuting window instead.
- **Why it is true** — the contained tasks must all run inside `[a, b)` on one
  machine, and they need more than `b − a` time.
- **Proof technique** — one of two certificates over the same unchanged OPB:
  - **Time-indexed** (#737). `redundance` introduces activity flags. Each
    per-time pairwise at-most-one, the bridge, is a `pol` over two `bf` rows,
    the operands' definitions and the separation clause, halved. It cannot be
    a bare RUP: the `RupOverloadBridge` lane is rejected.
    `recover_am1_from_pairs` folds the bridges into one at-most-one per time
    (`counting argument`), and since #1287 the fold is kept and cited again by
    any later firing over the same tasks and time. The energies are telescoped
    from the flags' backward rows, with the window-edge literals discharged by
    `RUP` under the reason. One `pol` sums it all to a contradiction.
  - **Sorting network** (#738–#740), `sorting network`. The window's starts
    are read as wires over their own bits, selection-sorted inside the proof
    by `ComparatorNetwork`, with each pair's separation carried across every
    comparator. The sorted chain then telescopes to the window being wider
    than it is ([Developer commentary](#developer-commentary)).

  `Cheaper` takes the network when the span exceeds `overload_crossover × w`
  and the window qualifies. A window that does not qualify falls back to the
  time-indexed certificate. Both certificates are ours.
- **Reason** — every start, the window's variable durations and every
  present task's presence, built at each firing (`disjunctive.cc:2787`);
  #1283 left it as it was (#1299). The certificate cites the contained
  tasks' bounds. Durations are counted at their **declared** lower bound, so the
  bridge and the fold are reason-free and cacheable.
- **Assertion** — `¬reason`, from `contradiction()`. Checked on
  `disjunctive_overload_test`'s `sharp` fixture: six literals, three tasks'
  bounds.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`: re-run the sweep on the reason's
  bounds, then emit either certificate.
- **Proof size** — time-indexed: `O(w²·span)` bridges for an unseen window,
  about 99% of which are reused once the pairs have been seen (design note),
  plus `w` fold pols with `O(w)` terms per time point for a task set and time
  not folded before, plus `O(w·span)` energy rows. The median is 55 lines per
  firing on `ft06` with every rule on, at `0a5b4ec6` (192 at `7e1c4178`). The
  sorting network makes `w(w−1)/2` comparators, `Θ(w²·bits + w³)` lines in all
  ([Developer commentary](#developer-commentary)), all `Temporary`. Overload
  alone on `ft06` (537,809 recursions) writes a 5.12 GB proof of 56.7 million
  lines at `0a5b4ec6`, not checked here; at `7e1c4178` it was 7.18 GB, and
  VeriPB had not finished it after 2,203 s. At `Inferences` it is 968 MB (1.62
  GB before), with 5,167,189 assertions, checked in 24 s.
- **Gaps** — None.
- **Tightness** — `disjunctive_overload_mutation_{skip_fold, skip_energy,
  rup_bridge}` are rejected, with `emit_nothing` as the control. An overload
  context is not contradictory until the argument makes it so, which is why
  route corruptions bite here. `comparator_network_test` covers the
  network's own lemmas ([Developer commentary](#developer-commentary)). The
  network is emitted by `disjunctive_overload_test`'s `sorted` and `wide`
  fixtures. `disjunctive_optional_test`'s `energy` mode has a forced
  `SortingNetwork` configuration, but the network refuses any window holding
  an optional task (`disjunctive.cc:986`), so whether it is emitted there
  depends on the seed. A presence is `{1, 1}` with probability 1/4, so a
  window can be all mandatory: at `0a5b4ec6`,
  `--seed=270` and `--seed=14` each emit the network in two of their 18
  `overload_sorting` proofs, and seeds 1 to 3 emit none (the
  test deletes its proofs unless `GCS_PRESERVE_PROOF_FILES=1` is set, so
  check with that set).

### Rule: edge-finding-lb

- **Infers** — `s_j ≥ a + p(Θ)`.
- **Fires when** — `edge_finding` and `edge_finding_lb` are on (off by
  default). For a window `[a, b)` with contained set Θ that is **not**
  overloaded, `j` starts inside (`est_j ≥ a`) and ends outside (`lct_j > b`),
  and `p(Θ)` plus `j`'s guaranteed overlap exceeds `b − a`
  (`disjunctive.cc:2397`). The overlap is computed by `window_energy_bound` at
  exactly the guards the certificate will use.
- **Strength** — `partial`: edge-finding (Carlier and Pinson 1994; Vilím 2004)
  over task-interval windows, as published, so #1249 does not apply to it.
  Its pushed task is never contained by definition, and in the fact-check's
  fixpoint model #1247's restriction costs it nothing; every remaining gap
  there is not-first / not-last's. An overloaded window is skipped
  (`:2394`), which at `7e1c4178` left nothing at all with the overload check
  off (#1244). Since #1275 `edge_finding` turns the overload check on, and
  its sweep over a superset of these tasks refutes such a window later in
  the same call, unless `overload_max_window` declines it. The `overloaded`
  fixture checks that with time-tabling on and off.
- **Algorithm** — for each `est` `a`, tasks are taken in `lct` order with the
  energy accumulating, and every candidate `j` is tested at each `b`.
  `O(n³)` per call, #742's shape.
- **Why it is true** — `j` cannot fit inside the window alongside Θ. Starting
  inside, it must therefore end after everything in Θ, and so start no
  earlier than `a + p(Θ)`.
- **Proof technique** — `redundance`, `pol`, `counting argument` and
  `RUP sequence`: the overload check's time-indexed certificate, emitted
  under the negated conclusion. The energy rows are the **guarded**
  window-energy rows (`derive_guarded_window_energy`, shared with
  `Cumulative`), which are model facts kept at `Top` and cited again.
  Contained tasks' guards are discharged by the reason. The pushed task's
  high guard is the conclusion literal, left standing, so the summed `pol`
  *derives* the push (#751). It never sorts.
- **Reason** — the whole scope (preamble). The certificate cites Θ's and
  `j`'s bounds.
- **Assertion** — `[s_j ≥ a + p(Θ)] ∨ ¬reason`. Checked on
  `disjunctive_edge_finding_test`: `a 1 [_3 ≥ 7] 1 ~[_1 ≥ 2] … >= 1`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`: the window and Θ from the
  reason.
- **Proof size** — the fold dominates, at `O(|Θ|²)` terms per time point of
  the window, for a window not folded before. On `ft06` at `0a5b4ec6`,
  edge-finding alone, which now brings the overload check: a median of 25
  lines per firing, mean 54.7, maximum 2,908. With every rule on: 26, 63.9 and
  3,099, and folds are 8.3% of the proof. At `7e1c4178`, with every fold
  derived again, these were 191, 211.3 and 2,936, and 189, 219.5 and 3,132
  with folds at 55.6%.
- **Gaps** — None.
- **Tightness** — `disjunctive_edge_finding_mutation_{skip_fold,
  drop_contained, one_too_far, drop_pushed}` are rejected, with
  `emit_nothing` as the control, on the hand-built `sharp` fixture. One
  deliberately absent lane is worth
  knowing about: citing the pushed row at an unclipped threshold yields a
  *stronger* row, which verifies, so the invariant that the propagator asks
  the lemma for exactly the guards it cites is enforced by reading the code,
  not by a test.

### Rule: edge-finding-ub

- **Infers** — `s_j ≤ b − p_j − p(Θ)`.
- **Fires when** — `edge_finding` and `edge_finding_ub` are on. The mirror:
  `j` ends inside and starts before `a`.
- **Strength** — `partial`, the mirror, with the same overloaded-window
  skip, refuted by the overload check as for the lb rule.
- **Algorithm** — the same sweep.
- **Why it is true** — the mirror: `j` must start before everything in Θ.
- **Proof technique** — as the lb rule. The negated conclusion sits on the
  low guard.
- **Reason** — preamble.
- **Assertion** — `[s_j < b − p_j − p(Θ) + 1] ∨ ¬reason`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`.
- **Proof size** — as the lb rule.
- **Gaps** — None in the proof.
- **Tightness** — Not shown. The `mirror` fixture fires this half, but it is
  verify-only. The mutation lanes run on `sharp`, which fires the lb half.

### Rule: not-first

- **Infers** — `s_j ≥ min_{i∈Θ} ect_i`.
- **Fires when** — `not_first_not_last` and `not_first` are on, and the
  published detection is off (`disjunctive.cc:2466`). `j` is not contained
  in the window (it spans it, or has one end inside: `:2473` tests only
  containment), and the guarded energy with the negated conclusion overfills
  `[a, b)` (`:2496-2502`). Where `j` has one end inside and edge-finding is on,
  edge-finding's push subsumes this one: the fact-check found skipping those
  candidates leaves every root unchanged with edge-finding on, but changes
  658 of 20,000 roots without it (at `7e1c4178`).
- **Strength** — `partial`: a strict weakening of the published not-first
  (Baptiste, Le Pape and Nuijten; Torres and Lopez 2000), and deliberately
  so. Its Θ is always a window's whole contents, the restriction #1249
  recorded, and it never pushes a task the window contains, #1247's. #1288
  and #1289 lifted both for the published detection only. For this rule's
  window-energy argument the second costs nothing: a contained `j` has all
  of its energy in the window wherever it starts, so the window plus `j` is
  overfilled only if the window is, which is the overload check's case
  (#1288's comment at `:2468-2472`). An overloaded window is still skipped,
  but `not_first_not_last` has turned the overload check on since #1275.
- **Algorithm** — edge-finding's sweep, `O(n³)`.
- **Why it is true** — if `j` started before every task in Θ had ended, the
  window would have to hold Θ and at least the part of `j` the bound
  guarantees inside it. That is more than its width.
- **Proof technique** — `redundance`, `pol`, `counting argument` and
  `RUP sequence`: edge-finding's certificate, unchanged, with a different
  threshold and guard (#752).
- **Reason** — the whole scope (preamble).
- **Assertion** — `[s_j ≥ min ect] ∨ ¬reason`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`.
- **Proof size** — the median is 27 lines per firing on `ft06`, with every
  rule on, at `0a5b4ec6` (43 at `7e1c4178`).
- **Gaps** — None in the proof.
- **Tightness** — `disjunctive_nfnl_mutation_*`, edge-finding's five lanes
  unchanged, are rejected, on a generated fixture. Only one in 222
  generated instances made all five bite.

### Rule: not-last

- **Infers** — `s_j ≤ max_{i∈Θ} lst_i − p_j`.
- **Fires when** — the mirror, under `not_last`.
- **Strength** — `partial`, as not-first.
- **Algorithm** — the same sweep.
- **Why it is true** — the mirror.
- **Proof technique** — `redundance`, `pol`, `counting argument` and
  `RUP sequence`: edge-finding's certificate. The low guard is the negated
  conclusion, and the high guard is `ub(s_j) + 1`, a bound that moves,
  so this row is the one that does not share a cache key with edge-finding.
- **Reason** — the whole scope (preamble).
- **Assertion** — `[s_j < max lst − p_j + 1] ∨ ¬reason`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`.
- **Proof size** — the median is 37 lines per firing on `ft06` at
  `0a5b4ec6` (84 at `7e1c4178`).
- **Gaps** — None.
- **Tightness** — As not-first.

### Rule: not-first-published

- **Infers** — `s_j ≥ min_{i∈Θ} ect_i`.
- **Fires when** — `not_first_not_last`, `not_first` and
  `not_first_not_last_published` are on (`disjunctive.cc:2558`), and
  `p(Θ) > lct(Θ) − ect_j` (`:2618`) for some Θ of the family below and some
  candidate `j`. Since #1289 the family is every set `{k ≠ j : ect_k ≥ E,
  lct_k ≤ b}` over the sweep's candidates, with `E` an `ect` and `b` an `lct`
  among them: an ect floor and an lct ceiling. A `j` that meets a set's
  bounds is left out of it (#1288), and a set must keep at least one task.
  At `7e1c4178` Θ was a window's whole contents and `j` had to lie outside
  the window.
- **Strength** — `partial`: the published condition over every Θ of candidates
  that can fire. What a Θ claims depends only on `p(Θ)`, `lct(Θ)` and `min
  ect(Θ)`, so a firing Θ lies inside the family's set of the same floor and
  ceiling, which fires with the same conclusion (#1289's argument,
  `disjunctive.hh:214-223`). The candidates are the vocabulary restriction
  above: present tasks with simple starts, at their declared durations. With
  it and every other rule on, the root is weaker than Gecode's `unary` on none
  of the 20,000 and 40,000 random instances below, and stronger on 19 and 16.
  At `7e1c4178`, over windows, it fired 1.6 to 1.7× as often as
  [not-first](#rule-not-first) (#757).
- **Algorithm** — a sweep of its own after the window loop, sharing only
  its candidates (#1289): for each `ect` floor, tasks in `lct` order, and
  every `j` asked of each whole set. That is `O(n³)`. Each threshold is kept
  with its runner-up (`Extremum`), so leaving `j` out costs `O(1)`.
- **Why it is true** — under `s_j < min ect(Θ)`, no `k ∈ Θ` precedes `j`, so `j`
  precedes all of them. Then Θ lies in `[ect_j, lct(Θ))`, which is too
  narrow.
- **Proof technique** — a `RUP sequence` with `pol`s over the **derived**
  window `[ect_j, lct(Θ))`. Each contained task's guarded row has its low
  guard discharged by a derived two-literal clause carrying the conclusion
  literal, and its high guard by the reason. There is also a **shortcut**: a
  contained task too long for the derived window needs only its clause plus
  one reason RUP, with no energy (`published_justification`). Ours (#757).
  It is unchanged by #1288 and #1289: it needs only `k ≠ j` and bounds that
  every member of the family has by construction. A push on a `j` left out
  of its own set writes `contained` at the end of its proof comment.
- **Reason** — the whole scope (preamble).
- **Assertion** — `[s_j ≥ min ect] ∨ ¬reason`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`.
- **Proof size** — as not-first, over a window keyed on `ect_j`, so its rows
  share nothing with the sweep's. The shortcut is a few lines.
- **Gaps** — None.
- **Tightness** — `disjunctive_published_nfnl_mutation_{skip_fold,
  drop_energy, drop_clause, rup_clause, one_too_far, contained_emit_nothing}`
  are rejected, with `emit_nothing` as the control. The last, from #1288,
  drops only the certificates of pushes on a `j` left out of its own set.
  #1289 replaced the fixture, because the old one had no solutions and the
  stronger rule refuted it by a route every corruption left standing. Its
  body reports that of 300 generated instances of five to eight tasks, 258
  fired the rule and 32 rejected all seven lanes, and the fixture is the
  first of those with search under it. At `7e1c4178` the fixture was one of
  24 of 172. The `disjunctive_regression_test` case
  `published_shortcut_temporary_escape` pins #1084. The fixtures
  `contained_nf`, `contained_nl`, `subset_nf` and `subset_nl` pin #1247's and
  #1249's pushes at the bounds Gecode and enumeration give. Only
  `contained_nf` is too small to test the certificate: with no certificate
  for any published push (`PublishedEmitNothing`), its root proof still
  verifies, and the other three are rejected at their push's closing RUP
  (fact-check probe, at `0a5b4ec6`). No lane runs that check on them.

### Rule: not-last-published

- **Infers** — `s_j ≤ max_{i∈Θ} lst_i − p_j`.
- **Fires when** — the mirror: `p(Θ) > ub(s_j) − est(Θ)` (`:2673`), over
  the family with an est floor and an lst ceiling.
- **Strength** — `partial`, as not-first-published.
- **Algorithm** — the mirrored sweep, `O(n³)`, tasks in `lst` order.
- **Why it is true** — the mirror, over `[est(Θ), ub(s_j))`.
- **Proof technique** — as not-first-published, with the guard roles swapped:
  the low guard is from the reason, the high guard derived.
- **Reason** — the whole scope (preamble).
- **Assertion** — `[s_j < max lst − p_j + 1] ∨ ¬reason`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`.
- **Proof size** — as not-first-published.
- **Gaps** — None.
- **Tightness** — The same lanes.

### Rule: strict-zero-length-leaf

- **Infers** — contradiction.
- **Fires when** — strict mode. A present task `z` with maximum duration 0
  and a fixed start lies strictly inside a present task `k` that has a fixed
  start and a fixed positive duration (`disjunctive.cc:2905`).
- **Strength** — `checker`, on fixed pairs only. A zero-length task whose start
  can lie only inside a fixed task is not pruned.
- **Algorithm** — `O(n²)` over the fixed pairs.
- **Why it is true** — `z`'s point lies strictly inside `k`'s interval, so
  neither ordering of the pair holds.
- **Proof technique** — `RUP` (`JustifyUsingRUP`): with both values fixed,
  both `bf` flags unit-propagate to 0 and the separation clause fails.
- **Reason** — the two tasks (#1283). At `7e1c4178` it was every task's
  bounds, and the `a` line named a third, irrelevant task, `y`.
- **Assertion** — `¬reason`, from `contradiction()`. Checked at `0a5b4ec6`:
  `a 1 ~[z = 1] 1 ~[k = 0] >= 1`.
- **Hint** — `hints::Disjunctive`.
- **Offline reconstructibility** — `search`: the pair.
- **Proof size** — one RUP.
- **Gaps** — None.
- **Tightness** — Not shown.

## Evidence

### Tests

**Lanes**, all in `gcs/CMakeLists.txt`:

- **`disjunctive_constraint_{strict,nonstrict}`** (`disjunctive_test`).
  Constant, variable and constant-start-variable-length data, the duplicate
  start, and random cases. The default rules only. Plain `solve_for_tests`,
  with no per-node GAC assertion, which would be wrong here: the rules are
  partial. View-wrap lanes come from `add_view_tests(... 4 ...)`.
- **`disjunctive_optional_constraint_{enumerate, falsify, bijection,
  cumulative, objective, energy}`.** The optional form:
  - `bijection` and `cumulative` compare against an encoding and against
    `Cumulative`, with no proofs, and clear the caps;
  - `energy` runs every energetic rule over optional tasks. Its forced
    `SortingNetwork` configuration usually falls back, because most windows
    hold an optional task. Whether any proof emits the network depends on the
    seed.

  The mutation lanes are `disjunctive_optional_mutation_{emit_nothing,
  wrong_task, one_too_far}`.
- **Per-rule lanes.**
  - `disjunctive_precedences`, plus five mutation lanes.
  - `disjunctive_overload`, plus four.
  - `disjunctive_edge_finding`, `_search`, plus five.
  - `disjunctive_nfnl`, `_search`, plus five.
  - `disjunctive_set_precedences`, `_search`, plus six.
  - `disjunctive_published_nfnl`, `_search`, plus seven (#1288 added
    `contained_emit_nothing`).

  Each fixture lane writes and checks its own proofs with VeriPB in-process,
  with a rule-off control where the fixture needs one. The `--search 28`
  lanes generate 60 instances each and verify a proof for every one. They
  are the lanes that matter, because hand-built fixtures verify straight
  through certificate bugs. Fixtures added since `7e1c4178`:
  - `disjunctive_set_precedences`' `fixed` and `disjunctive_edge_finding`'s
    `overloaded` (#1275): #1243's and #1244's five-task instance, run with
    time-tabling on and off, each needing a root refutation and a verified
    proof;
  - `disjunctive_overload`'s `permutations` now also counts the folds each
    run writes, kept against re-derived (#1287);
  - `disjunctive_published_nfnl`'s `contained_nf`, `contained_nl`,
    `subset_nf` and `subset_nl` (#1288, #1289).
- **`disjunctive_regression`**: fuzz-found shapes, each with a proof (#1084
  among them).
- **`comparator_network_test`**: the network's refutations and its mutation
  battery, checked internally.
- **Four chain cases**, registered in
  `verified_encodings/scp_cases/CMakeLists.txt` (see
  [Cake conformity](#cake-conformity)).
- **`large_domain_audit_test`'s `Disjunctive` row.**

**VeriPB runs** in every lane above except `bijection` and `cumulative`.

**Caps.** Every lane runs under the default caps (`GCS_TEST_CAP_DEFAULTS`:
300 solutions, 1,500 recursions) unless it clears them. Only `bijection` and
`cumulative` do. **The caps do fire.** One run with the default caps, at one
seed each, truncated these solves. The counts depend on the seed: across
seeds the fact-check saw `energy` truncate between 180 and 288 times.

| lane | truncated solves, `7e1c4178`, random seed | `0a5b4ec6`, `--seed=1` |
|---|---|---|
| `energy` | 252 | 216 |
| `enumerate` | 4 | 4 |
| `disjunctive_precedences` | 1 | 3 |
| `strict` | 2 | 2 |
| `nonstrict` | 2 | 2 |

So the default configuration checks only soundness and a partial proof on
those solves. The fixture and `--search` lanes never truncate. The results
in this document come from running each binary directly, uncapped. At
`0a5b4ec6` all fifteen of the lane invocations listed above pass (`energy`
takes 60 s), and so do the four `--search` lanes and the four view lanes,
and all 35 mutation lanes are rejected. At `7e1c4178` the same held for the
34 lanes there were.

**Seeding.** The random lanes call `establish_and_announce_seed` and branch
randomly from the seed (`--seed=N`), so they reproduce byte for byte.

**Real instances.** No real instance is ported into a test.
`examples/rcpsp/sample.jss` is a hand-written 4×4 job shop chosen so that
most rules change the search. At `7e1c4178` two did not: the published
not-first / not-last gave 144 recursions, the same as the sweep detection,
and `time_table` off gave 164, the same as the default. At `0a5b4ec6` both
detections give 132, now that either brings the overload check, and the
default 164; `time_table` off was not re-run.

**Mutation lanes and controls.** Every per-rule lane battery has its
`emit_nothing` control. The pairwise battery runs on the `tight` fixture,
the overload and edge-finding batteries on the hand-built `sharp`, and the
not-first / not-last, set-rule and published batteries on generated
fixtures that were scanned for lanes that bite. What the lanes show is that
the named corruptions are rejected on those fixtures, no more. **No mutation
lane reaches** time-tabling's pushes (the chain passes `None{}`), mandatory
overlap, the zero-length check, `detectable-precedence-ub`,
`set-detectable-precedence-lb` or `edge-finding-ub`. Fixture and `--search`
lanes do verify those rules' proofs (edge-finding's `mirror`, for example);
only corruption is untested. The not-last halves are covered, through the
same batteries as not-first.

**What the tests do not cover:**

- **Rule interactions.** Only #1275's two fixtures compare a rule with and
  without time-tabling, on the one instance behind #1243 and #1244. No lane
  looks for other order dependences: every other lane tests one rule, or
  every rule, against the default.
- **Strength against a reference.** No lane runs Gecode or any published
  algorithm. #1288 and #1289 compared root fixpoints against Gecode by
  probe, not in a lane. Their four fixtures pin single pushes at the bounds
  Gecode and enumeration give.
- **Long durations.** Every fixture's durations are at most 10 (the overload
  test's `wide` fixture has `{10, 10, 10}`), so no lane has a long blocked
  span. #1279's jump scan finds the start the old scan found by
  construction, and #1279 added no test for it.
- **The energetic rules through a frontend or the cake chain.** The four
  chain cases use the default rules. This audit ran two energetic proofs
  through the chain by hand.
- **Views and constants in the energetic rules.** Edge-finding, not-first /
  not-last and the set rule exclude views and constants, and the overload
  check excludes constants, and the view lanes run the default rules anyway.
- **The sorting-network certificate on a solve.** It is chosen at span > 300w,
  which no job shop reaches. `disjunctive_overload_test`'s `sorted` and
  `wide` fixtures emit it every time. The `energy` mode does so only on some
  seeds.

### Benchmarks and examples

- **In repo.** `examples/rcpsp` is the benchmark. `--jss` reads OR-Library
  job shops, `--unary disjunctive` posts one `Disjunctive` per machine, and
  `--disjunctive-*` selects rules. `sample.jss` is the 4×4 fixture.
- **Instances.** `ft06`, the `la` and `abz` sets and others are in
  `/cluster/ciaran/claude/scheduling-instances/jobshop/`.
- **MiniZinc Challenge** (the `mzn-challenge-a8448864` checkout). Of the
  models that post `disjunctive`, `test-scheduling` (2018, 2023) posts three
  `disjunctive_strict` and `stripboard` (2022, 2025) posts one. **None is
  dominated by it.** In a 60 s `fzn-glasgow` run:
  - `test-scheduling` spends 89 to 95% of its propagation time in `ArrayMin`
    and `ArrayMax` (#1166), and too little in Disjunctive to register;
  - on `stripboard`, Disjunctive is 0.5 to 0.9%. On `2022_stripboard` none
    of its 134,787 calls changed a domain.
  - the four 2026 models that use it have no data files in this checkout.
- **CPU.** `ft06 --deadline 54` is a complete infeasible tree of 5.45 million
  recursions in about 60 s under the defaults, and a 30-recursion tree with
  edge-finding. `ft06 --deadline 55` and `la03 --deadline 597` are
  satisfiable trees that distinguish the arms.
- **Proofs.** `ft06` minimised with edge-finding, or with every rule on: 14
  to 15 MB, about 9 s to check at `0a5b4ec6`. **Never verify** `ft06` with
  overload alone (5 GB) or with the defaults (millions of recursions).

### CPU performance

**Rule arms on job shops.** `examples/rcpsp --jss --unary disjunctive
--deadline D`, at `0a5b4ec6`, 2026-10-08, fataepyc-10, Release,
`GLIBC_TUNABLES` pinned, one run at a time on one pinned core, with a 300 s
timeout. "all" is edge-finding, the set rule, overload and the sweep
not-first / not-last; "all, published" swaps in the published detection.
Since #1275, "edge-finding" and "nfnl" have the overload check on too, so
"edge-finding" and "ef + overload" are now the same arm. Recursion counts at
a timeout are approximate: other measurements ran on other cores meanwhile.

| instance | D | arm | result | recursions | propagations | wall s | instructions:u |
|---|---|---|---|---|---|---|---|
| ft06 | 54 | default | infeasible | 5,450,366 | 69,569,536 | 57.2 | 388.1·10⁹ |
| ft06 | 54 | overload | infeasible | 528,658 | 14,601,777 | 9.2 | 62.5·10⁹ |
| ft06 | 54 | nfnl | infeasible | 356,158 | 10,704,660 | 10.0 | 69.9·10⁹ |
| ft06 | 54 | published | infeasible | 172,886 | 6,665,338 | 8.9 | 62.9·10⁹ |
| ft06 | 54 | set rule | infeasible | 12,574 | 91,529 | 0.12 | 0.89·10⁹ |
| ft06 | 54 | edge-finding, or ef + overload | infeasible | 30 | 3,065 | 0.003 | 0.023·10⁹ |
| ft06 | 54 | all | infeasible | 1 | 263 | 0.001 | 0.008·10⁹ |
| ft06 | 54 | all, published | infeasible | 1 | 291 | 0.001 | 0.009·10⁹ |
| ft06 | 54 | `Cumulative` capacity one | infeasible | 924,277 | 24,634,421 | 25.6 | 184.4·10⁹ |
| ft06 | 55 | default | sat | 13,740 | 275,852 | 0.17 | 1.17·10⁹ |
| ft06 | 55 | nfnl | sat | 2,775 | 73,325 | 0.072 | 0.52·10⁹ |
| ft06 | 55 | published | sat | 1,303 | 41,679 | 0.060 | 0.42·10⁹ |
| ft06 | 55 | set rule | sat | 670 | 30,334 | 0.018 | 0.12·10⁹ |
| ft06 | 55 | edge-finding, or ef + overload | sat | 28 | 1,232 | 0.002 | 0.013·10⁹ |
| ft06 | 55 | all | sat | 28 | 1,218 | 0.002 | 0.016·10⁹ |
| ft06 | 55 | all, published | sat | 28 | 1,204 | 0.002 | 0.020·10⁹ |
| la03 | 596 | edge-finding (alone or with more), all, all published | infeasible | 1 | 272–273 | 0.001 | 0.010–0.012·10⁹ |
| la03 | 596 | published | timeout | 5.83 M | | 300 | |
| la03 | 596 | set rule, nfnl | timeout | 20.9 M, 12.4 M | | 300 | |
| la03 | 596 | default, overload, `Cumulative` (at `7e1c4178`, 16 concurrent jobs) | timeout | 8–16 M | | 300 | |
| la03 | 597 | edge-finding / ef + overload / all / all, published | sat | 312 | 4,316–6,971 | 0.01–0.02 | 0.11–0.16·10⁹ |
| la03 | 597 | published | timeout | 5.90 M | | 300 | |
| la03 | 597 | set rule, nfnl | timeout | 20.9 M, 11.9 M | | 300 | |
| la03 | 597 | default, overload, `Cumulative` (at `7e1c4178`, 16 concurrent jobs) | timeout | 8–18 M | | 300 | |

At `7e1c4178` (fataepyc-08, 16 jobs at a time), edge-finding without the
overload check took 758 recursions on `ft06` at 55 against 28 with it, which
was #1244's overloaded-window gap on a real instance, and the set rule took
53,944 at 54, #1243's. Every arm the fixes did not touch gives the same
recursion and propagation counts here as there. The set rule at 55 keeps its
670 recursions, with 30,334 propagations against 32,333.

**Where the time goes**, at `7e1c4178`, not re-measured. On `ft06
--deadline 54` with the default rules, `GCS_PROPAGATOR_STATS=time` put
Disjunctive at about 90% of the 55.3 s spent propagating (18 million calls,
2.8 µs each with six tasks). `lin_less_equal` had the rest. A `perf`
profile of the same run:

- **Disjunctive's own body:** about 26% of samples self.
- **Exception unwinding:** about 15%, in `__gxx_personality_v0`,
  `_Unwind_*` and the unnamed `libstdc++` addresses, from 5.4 million failures.
- **`State::bounds`:** 3%.

Turning `time_table` off gives the same recursion count in fewer
instructions. At `0a5b4ec6`, in `jss_gcs.cc` (below), whose default arm
reproduces this table's 5,450,366 recursions, that is 4.7% fewer at
`--deadline 54`: 387.4·10⁹ against 369.1·10⁹. At `7e1c4178` it was 10.7%
in `examples/rcpsp` (412.4·10⁹ against 368.2·10⁹, and 414.6·10⁹ against
370.3·10⁹ minimised, from shipped code plus one `getenv` in `rcpsp.cc`,
fact-check `bench/rcpsp_tt`, serial, pinned), with propagations rising
from 69.57 million to 74.59 million. The same probe built against
`7e1c4178` gives 412.1·10⁹ against 368.1·10⁹, also 10.7%, so the arm with
the pushes got 6.0% cheaper and the arm without them did not move. This
re-audit did not split that between #1279's jump and #1283's reasons. An
earlier figure of 16% was taken in an instrumented build whose default arm
runs 9.5% over the shipped one (#1245).

**Against Gecode** (#868). The same decision model was written in Gecode
6.3.0's API, using its `unary` propagator. `IPL_DEF` resolves to
basic-and-advanced: overload checking and time-tabling, then detectable
precedences, not-first / not-last and edge-finding, the last four Θ-tree
(Vilím). When every duration is 1, `unary` posts `distinct` instead
(`unary.cpp:64-75`).
Gecode's `IPL_BASIC` alone is overload checking plus time-tabling, which is
not our default either. The GCS side is a probe building the identical model:

- starts in `[est, H − p − tail]`;
- the makespan in `[0, H]`;
- precedences as two-variable linear inequalities;
- branching in order over the starts, then the makespan, smallest value
  first.

`tmp/fd-sched/disjunctive/gecode/`, re-run at `0a5b4ec6` with the same
sources. The GCS columns are that probe, `jss_gcs.cc`, with every rule on,
under each detection. These are **not identical trees**, because the
propagators differ in strength, so the table compares search, not
throughput. Nor are the failure counts the same quantity: GCS counts failed
subtrees, internal nodes included, and Gecode counts failed nodes.

| instance | Gecode | GCS, every rule, sweep detection | GCS, every rule, published detection |
|---|---|---|---|
| ft06, H = 54 | root failure, 0 nodes | root failure, 1 recursion | root failure, 1 recursion |
| ft06, H = 55 | sat, 34 nodes, 7 failures | sat, 28 recursions, 8 failures | sat, 28 recursions, 8 failures |
| la01, H = 665 | root failure | root failure | root failure |
| la01, H = 666 | sat, 200 nodes, 10 ms | no solution in 320 s | sat, 240 recursions, 206 failures |
| la03, H = 596 | root failure | root failure | root failure |
| la03, H = 597 | sat, 75 nodes | sat, 312 recursions | sat, 312 recursions |

At `7e1c4178` the table had one GCS column, the sweep detection, with the
same entries; `la01` at 666 had no solution in 300 s with either detection.

At the root, with the published detection, GCS agrees with Gecode on every
start variable of `ft06` at 55, `la01` at 666 and `la03` at 597. With the
sweep detection four, 13 and 22 start variables are wider, as at
`7e1c4178`, when the published detection was wider on the last two too. At
`7e1c4178` the fact-check's Python fixpoint model
(`tmp/fd-sched/factcheck/disjunctive/d5/jsref.py`) reproduced GCS's `la01`
root exactly, still had the same 13 wider with #1247's restriction lifted,
and found only not-first / not-last firings over sets that are not a
window's whole contents (for example machine 4, `j` = 17,
Ω = {2, 11, 27, 31}). That was #1249, and #1289 closed it. `la03`'s
remaining gap is not at the root: its search is 312 recursions against 75,
from equal roots, and #1289 did not look into why.

Over 20,000 random single-machine instances
(`gecode/gen20k.py 7 20000 3 6 12 10 5`: 3 to 6 tasks, each start in
`[lo, lo + U(0, 10)]` with `lo` in `0..12`, duration `1..5`), and the
audit's second draw of 40,000 (seed 11, 3 or 4 tasks), which #1288 used
too, at `0a5b4ec6`:

| GCS root fixpoint against Gecode's | published, 20,000 | sweep, 20,000 | published, 40,000 | sweep, 40,000 |
|---|---|---|---|---|
| same | 19,981 | 19,548 | 39,984 | 39,530 |
| GCS weaker | 0 | 452 | 0 | 470 |
| GCS stronger or incomparable | 19 | 0 | 16 | 0 |

At `7e1c4178` the published detection was weaker on 197 of the 20,000 and
the same on 19,784; the sweep column is unchanged. #1288's and #1289's
bodies give 197 → 24 → 0 and 175 → 4 → 0 over the two fixes. The 19
stronger cases are the same count as at `7e1c4178`, when all 19 were
checked sound against enumeration; #1288 and #1289 report every root bound
on both draws containing every brute-force solution. None of the
differing instances has every duration 1, so Gecode's `distinct`
substitution plays no part in these counts (on the fact-check's own draw it
accounts for some "stronger" cases).

At `7e1c4178` the gap on random roots was mostly #1247. On the seed-7 draw,
the fact-check's model (`ref2.py`, mode `gcsx`) with not-first / not-last
allowed to push a contained task matched Gecode on 173 of GCS's 197 weaker
roots, and #1288's change matched it on all but 24.

**What this does not exercise.** Optional tasks, variable durations, views,
non-strict mode and the sorting-network certificate. Job shops have none of
them.

### Proof performance

**`ft06` minimised** (`examples/rcpsp --jss --unary disjunctive --prove`), at
`0a5b4ec6`, 2026-10-08, fataepyc-10, one run at a time on one pinned core.
VeriPB 3.0.2 with `--force-checked-deletion`. The OPB is 131,924 bytes.
Since #1275 the edge-finding arm has the overload check on too.

| arm | level | recursions | solve s | lines | bytes | `a` lines (`disjunctive`) | VeriPB s | verdict |
|---|---|---|---|---|---|---|---|---|
| edge-finding | Off | 1,588 | 0.28 | 222,313 | 13.7 MB | — | 8.7 | VERIFIED BOUNDS 55 |
| edge-finding | Inferences | 1,588 | 0.11 | 31,300 | 2.9 MB | 8,658 | 0.10 | UNDER ASSERTIONS |
| all | Off | 1,588 | 0.30 | 235,623 | 14.6 MB | — | 8.3 | VERIFIED BOUNDS 55 |
| all | Inferences | 1,588 | 0.12 | 30,992 | 2.9 MB | 8,703 | 0.10 | UNDER ASSERTIONS |
| set rule | Off | 17,195 | 1.4 | 1,366,208 | 98.3 MB | — | 57.4 | VERIFIED BOUNDS 55 |
| set rule | Inferences | 17,195 | 0.54 | 226,163 | 21.3 MB | 94,141 | 0.55 | UNDER ASSERTIONS |
| overload | Off | 537,809 | 60.2 | 56,650,208 | 5.12 GB | — | not run | — |
| overload | Inferences | 537,809 | 23.6 | 10,635,128 | 968 MB | 5,167,189 | 23.7 | UNDER ASSERTIONS |

At `7e1c4178` (fataepyc-08) the same arms were: edge-finding 595,891 lines,
29.5 MB, 10.5 s to check; "all" 538,796 lines, 27.8 MB, 10.5 s; the set
rule, at 58,579 recursions before #1243's fix, 4,820,193 lines, 276 MB,
224 s; overload alone 90,847,641 lines and 7.18 GB, unfinished after
2,203 s, and 1.62 GB at `Inferences`. The `Inferences` rows had 32,016,
31,054 and 546,736 lines.

Checking is 27× ("all") to 40× (the set rule) the solve-with-proof time.
The `Inferences` rows are what an external justifier starts from. For
edge-finding and "all", the proof shrinks by about 5× in bytes and its check
time by 86 to 89×. For the set rule it is 4.6× in bytes and 104× in check
time, and for overload alone 5.3× in bytes.

**Own against shared, by line type.** A breakdown by line kind
(`proofs/classify.py`, `folds.py`), at `0a5b4ec6`:

| arm | per-time folds (own) | pols on a `bf` row (own) | activity-flag `red`s (own) | rest: definitions, ladders, RUPs, deletions, backtracking |
|---|---|---|---|---|
| edge-finding | 9.3% | 8.4% | 1.7% | 81% |
| all | 8.3% | 10.5% | 1.5% | 80% |
| set rule | 0.9% | 21.0% | 0.2% | 78% |

No fold repeats an earlier one now. At `7e1c4178` the folds dominated, at
59.8%, 55.6% and 49.0%, and 84 to 99% of them repeated an earlier fold
exactly. #1287 keeps them. Its body measured the change alone: the
edge-finding proof 29.5 to 14.3 MB, the set rule's 276 to 191 MB, and
VeriPB's `instructions:u` −6.5% for edge-finding and +3.5% for the set rule.

**Per firing**, counting from a rule's `%` comment to the next comment, so an
upper bound that includes interleaved lines from other propagators, at
`0a5b4ec6`:

| rule | arm | median lines | mean | max | at `7e1c4178`: median, mean, max |
|---|---|---|---|---|---|
| detectable precedence | set rule | 4 | 12.4 | 517 | 4, 7.1, 533 |
| set-based precedence | set rule | 35 | 34.0 | 1,797 | 62, 95.3, 1,831 |
| edge-finding | all | 26 | 63.9 | 3,099 | 189, 219.5, 3,132 |
| overload | all | 55 | 57.3 | 68 | 192, 194.6, 270 |
| not-first | all | 27 | 34.5 | 95 | 43, 46.8, 98 |
| not-last | all | 37 | 49.0 | 131 | 84, 83.4, 227 |

**The pairwise rules' proofs do not grow with the horizon.** On 8 tasks over
`[0, H]` the proof is 527 lines at `H = 10³` and at `10⁶`, at `0a5b4ec6`. Only
the bytes grow (28 KB to 46 KB) with the start variables' bit widths. The
shared layers there are the order-literal definitions the pols cite. The
energetic rules' proofs are linear in each window's span.

**Measured elsewhere.** These figures come from the design note and #762,
are about generated RCPSP, and are not to be mixed with the tables above:

- bridge reuse is about 99%, growing with size;
- the time-indexed certificate is cheaper than the network by 16.6× to 5.92×
  at horizons 140 to 542;
- per-firing medians are 4 (pairwise), 33 (set rule) and 83 (edge-finding)
  lines.

## Status, gaps, and next steps

### Proof-logging gaps

None. Every rule is certified, and no `a` oracle remains: the published
not-first / not-last, once the one rule that threw under `--prove`, has its
certificate. The propagator's strength does not change with proofs: every
vocabulary restriction (simple starts, non-constant starts, declared
durations) is applied with proofs off too, the certificate choice never
changes an inference, and `overload_max_window` declines conflicts either
way.

### Known limitations

- **Default strength is time-tabling plus pairwise detectable precedences.**
  No frontend can turn on the energetic rules, so a MiniZinc or XCSP3 model
  gets none of them. On job shops that is the difference between 30
  recursions and 5.45 million.
- **With every rule on and the sweep detection, it is weaker than Gecode's
  `unary`** on some instances, because that detection asks only about
  windows' whole contents and never pushes a task a window contains. The
  published detection does not have either restriction (#1288, #1289).
  With the sweep detection the root is weaker than Gecode's on 452 of
  20,000 random instances, and `la01` at its optimum finds no schedule in
  320 s where Gecode needs 200 nodes. With the published detection both
  gaps close, but `la03` at 597 still takes 312 recursions against Gecode's
  75 from the same root.
- **An undecided optional task is never pruned**, because there is no
  conditional bounds store. A precedence conditional on a presence is not
  used either. Only falsification touches it.
- **A strict zero-length task is only checked at all-fixed leaves.**
- **Wide horizons.** Each call allocates `4H` bytes. Once that exceeds the
  memory available, the solve aborts with `std::bad_alloc` (#833): `0..2⁴⁰`
  aborts under 16 GB, where `0..10⁹` completes. (Long durations made
  time-tabling's scan quadratic until #1279.)
- **Views and constant starts** are left out of edge-finding, not-first /
  not-last and the set rule, and constant starts out of the overload check.
- **No cake encoder** for the optional forms, so those proofs are not
  chain-verified.
- **No `gcspy` binding.**

### Next steps

1. **Fix the set rule's fixed-task skip (#1243).** Done by #1275, as
   proposed: the loop keeps a fixed task when the set rule is on. `ft06` at
   54 goes from 53,944 recursions to 12,574. #762's tables have not been
   re-taken.
2. **Make edge-finding and not-first / not-last refute an overloaded window
   (#1244).** Done by #1275, the first way proposed: either switch turns the
   overload check on at install. `ft06` at 55 goes from 758 recursions to
   28 with edge-finding. The design note's edge-finding table, which ran
   without the overload check, has not been re-taken.
3. **Let not-first / not-last push a contained task (#1247)** and **take Θ
   from more than whole windows (#1249).** Done by #1288 and #1289, for the
   published detection only, and not by a Θ-Λ tree: two more `O(n³)` sweeps,
   one per direction, over a family of sets shown complete (an ect floor and
   an lct ceiling for not-first, and the mirror), with each threshold's
   runner-up kept so that `j` can be left out. The certificate needed
   nothing new, as predicted. The sweep detection is unchanged. A contained
   `j` costs its window-energy argument nothing, but #1249's restriction
   does cost it: the same argument over a proper subset of a window's
   contents is sound and can push further, and the sweep still takes only
   whole contents. On tasks `A` (start `[1, 10]`, length 1), `B` (`[1, 3]`,
   8) and `j` (`[0, 25]`, 5), the sweep alone leaves `s_j ≥ 2`, `Θ = {B}`
   gives `s_j ≥ 9` by the window-energy argument, the published detection
   alone gives 9, and Gecode and every rule give 10 (fact-check probe).
4. **Time-tabling's scan and redundancy (#1245).** Done by #1279, as "jump
   only" (Ciaran's call): the scans jump past blocked windows, and the
   pushes stay, with the subsumption recorded in the design note. The
   horizon-sized profile was not replaced by sorted mandatory parts, so the
   audit row still trips.
5. **Keep the per-time folds (#1246).** Done by #1287, keyed on the sorted
   task set, durations and time, under `overload_cache_bridge`. #1287's body
   measured edge-finding's `ft06` proof at 29.5 to 14.3 MB, and VeriPB's
   instructions at −6.5% for edge-finding and +3.5% for the set rule.
6. **Narrow the reasons (#1248).** Partly done by #1283, for the tasks:
   each rule names the tasks its certificate cites, and the window rules'
   whole-scope reason is built once at install. The rest is filed as #1299,
   with the overload reason as a third part. The other two parts are still
   open. Holes are still stated, and the narrow pairwise and conflict reasons
   are still built with proofs off; time-tabling's falls back to the prebuilt
   whole scope without a logger (`disjunctive.cc:1560-1561`), and the overload
   check's is built at each firing either way. #1283's body measured VeriPB's
   instructions on `ft06` at −32.7% for the set rule's proof and −6.8% for
   edge-finding's.
7. **Expose `DisjunctiveRules` to the frontends.** At least `fzn-glasgow`,
   which needs a flag or annotation design, so the Challenge corpus can
   reach the rules.
8. **An audit-lane row with the energetic rules on.** The row with long
   durations this item also asked for, to reach the quadratic scan, is moot
   since #1279.
9. **A richer hint** naming the rule and its witness (pair, chain, window and
   Θ, or cut) would make every rule `hinted` instead of `search`. Settle it
   against the justifier.
10. **#1099** (optional tasks in the sorting network) and **#762** stay as
    they are. Item 1 has now changed the set rule's numbers, so #762's
    tables can be re-taken.

## Prior art

- **Propagation.**
  - Time-tabling: Nuijten (1994), and the unary case in Baptiste, Le Pape
    and Nuijten, *Constraint-Based Scheduling* (2001).
  - Edge-finding: Carlier and Pinson (1989, 1994).
  - Not-first / not-last: Baptiste and Le Pape (1996), and Torres and Lopez
    (2000).
  - Overload checking, detectable precedences, and the `O(n log n)` versions
    of all four: Vilím's Θ-tree (Vilím 2004; Vilím, Barták and Čepek 2005).
  - Ours are sweep and scan implementations of the same rules, with the
    restrictions recorded above. Gecode's `unary` implements Vilím's.
- **Certification.** Lazy clause generation solvers (Chuffed, CP-SAT,
  Pumpkin) explain disjunctive inferences as clauses, and Pumpkin's proof
  logging (Flippo et al., CP 2024) has those explanations checked. We know of
  no earlier cutting-planes certificate for the unary energetic rules. What
  is new here:
  - every certificate is over the **pairwise** OPB, with the time index
    re-encoded inside the proof by `red` rather than placed in the model;
  - the **derived-window** certificates of the published not-first /
    not-last and the set-based precedence, where the negated conclusion
    supplies a window edge;
  - the **comparator-network** certificate, flat in the span.

## Further reading

- [`disjunctive-proof-logging.md`](../disjunctive-proof-logging.md), 2,223
  lines at `0a5b4ec6`. The pairwise vocabulary, each rule's derivation in
  full, the measurements that set each default (the 68-instance tables), the
  bridge and fold caching and crossover measurements, which Θ the published
  not-first / not-last asks about (#1247, #1249), and the open follow-ups. Its
  2-D section, about 630 lines of it, is `Disjunctive2D`'s, cross-referenced
  from [`disjunctive_2d.md`](disjunctive_2d.md).
- [`cumulative-proof-logging.md`](../cumulative-proof-logging.md): the
  time-indexed proof machinery `Disjunctive` no longer shares, and the
  guarded window-energy lemma it does.
- [`rule-counters.md`](../rule-counters.md): `GCS_SCHEDULING_RULE_STATS=1`,
  which prints the per-rule `calls`, `firings`, `already_true` and
  `contradictions` counters behind `disjunctive.cc:97`. `already_true` counts
  detections for the edge-finding rows here, and candidates everywhere else.
- [`veripb-facts.md`](../veripb-facts.md): the cross-variable RUP limit
  that makes the pairwise pols load-bearing.

## Developer commentary

### `ComparatorNetwork`, described once

`gcs/innards/proofs/comparator_network.{hh,cc}` (1,611 lines) builds
proof-only sorting networks over bit-encoded integer wires. It is the
sorting-network overload certificate here, and the 2-D lemma's engine in
`Disjunctive2D`'s relaxation, which relies only on the result that
pairwise-disjoint intervals in a window sum to at most the window.

**Two layers.**

- **The generic layer.** A `ProofWire` is a vector of bits. It is either fresh
  (`fresh_wire`, which emits nothing: its bits are unconstrained flags until
  something pins or defines them by `red`) or a reading of bits that already
  exist
  (`wire_over`, a model variable's own encoding, padded with constant zeroes,
  no copy). `pin` fixes a fresh wire. `compare` introduces a comparator: a
  selector reifying `a ≤ b`, plus bitwise muxes for both outputs and both
  outputs' durations, plus the conditional record rows (`lo ≥ a` under the
  selector, and so on) by `pol`.
- **The task layer.** `add_task` gives a wire a pinned duration and derives
  `duration ≥ 1`. `add_separation` takes a pair's model separation (the `bf`
  rows, their per-direction big-M, and the clause) and raises it to the
  network's guard coefficient. `set_bounds` emits the window bounds.
  `sort` selection-sorts, carrying every separation across every
  comparator through the gap, dominance, positivity, bound and transfer
  lemmas. `sum_up` telescopes the sorted chain and turns the sorted
  durations back into the instance's through one preservation row per
  comparator. That lands on `window ≥ total work`.

**What a caller must respect:**

- **The guard is uniform** (`assume`). A propagator's window is a fact about
  the state, so every bound row is guarded by the reason at the network's
  own coefficient. Rows guarded at different coefficients do not cancel in a
  case split.
- **Big-M is per direction.** `ModelSeparation` carries each direction's own
  `M`, read from `reification_shape`, because `bf_{i,j}` and `bf_{j,i}` differ
  whenever durations or widths do.
- **Wires are unsigned.** A two's-complement sign bit at index 0 is refused by
  the caller (`sorting_network_bits`).
- **Width is at most 40 bits** here, because guard coefficients are `2^width`.
- **Optional tasks** (`add_optional_task`, parking an absent task at the
  window's top) need `fits_optional_tasks`. Their constants are quadratic in
  the window. 1-D does not use them (#1099): it refuses optional windows and
  falls back.

**Cost.** Selection sort makes `w(w−1)/2` comparators
(`comparator_network.cc:904-1011`). Each one's muxes are `16·width` `red`s,
and carrying the separations across it costs `O(w)` lemmas. So it is
`Θ(w²·bits + w³)` lines, independent of the span except through the bit
width. Everything is emitted
at the network's level, which is `Temporary` here.

**Tightness.** `comparator_network_test` corrupts single steps:

- **Rejected:** `DropPositivity`, `SwapDurations` (invisible at equal
  durations, which is what shows the network handles unequal ones),
  `RupGap`, `RupPreservation` and `DropPreservation`.
- **Accepted, as documented:** `RupPositivity`. With pinned durations,
  propagation reaches `d ≥ 1` on its own. The case split is kept for
  predictable cost, and the lane stays runnable for the day durations become
  variables.
- **`DropParking`** concerns the optional-task mode, which 1-D does not use.
  Its lane is in `route_a_probe_test.cc:300` (`Disjunctive2D`'s; see
  `disjunctive_2d.md`).
