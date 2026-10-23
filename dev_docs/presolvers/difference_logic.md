# `difference_logic`: lift two-term difference rows into one global difference-logic propagator

> **Maturity** production, opt-in: off unless added; reached from the C++ API,
> `fzn-glasgow --difference-logic` and `xcsp_glasgow_constraint_solver
> --difference-logic` · **Audited** 2026-10-19 at `86caad24` · **Open issues**
> filed by this audit: #1373, fully reified donors are never lifted, which is
> how MiniZinc delivers every conditional difference; #1374,
> `glasgow_scp_solver` has no switch for the presolver. Shared with
> [`difference.md`](../constraints/difference.md), which owns the machinery:
> #1371 and #1372. In-range models that the donors answer throw
> `IntegerOverflow` through this presolver, from the installed machinery's
> shortest-path arithmetic (#1371). Its refutation pass (#1372) is reached
> through the presolver only with `incrementally(false)`, the donors retired and
> simplification off, which no front end selects. Already open and touching this
> presolver: #598 (the negated forms, deliberately not lifted), #1309
> (installing its one propagator is quadratic in its scope), #816 (the root
> initialiser it installs does not observe `--timeout`), #983 (no `gcspy`
> plumbing), #582 (no runtime
> propagator priorities), #1072, #594 and #1210 (owned by `difference.md`), and
> #868 (cross-solver). Filed since: #1378, added before an `AutoTable`, in
> its default incremental mode, it throws `UnexpectedException` whenever it
> installs a propagator. Also filed since, in the installed machinery and
> owned by `difference.md`: #1384 (a negative cycle's or root witness's reason
> deduplicates its conditions quadratically) and #1385 (root simplification
> counts isolated nodes as removed, but the propagator still seeds, scans and
> wakes on them). Tracked under #871.

`DifferenceLogic` scans a posted `Problem` for two-term difference
constraints, `x − y ≤ d`, written either as a two-term linear inequality or
as a comparison, unconditionally or half-reified. It hands the edges to
`install_difference_propagator`, which installs one global difference-logic
propagator over all of them, plus a root initialiser, **alongside** the
donors' own propagators. Nothing is written to the OPB. Every inference the
installed machinery makes cites the donors' own labelled rows. The
propagator, its initialiser, their proof rules, their state and their hole
sensitivity are documented in
[`difference.md`](../constraints/difference.md). That document owns them
whichever entry point installs them. This document owns detection, the
rewrite catalogue, what the pass costs, and what it does to the rest of the
model. The long design note is
[`difference-logic.md`](../difference-logic.md). This document audits the
presolver against the presolver variant of the
[template](../constraints/TEMPLATE.md#the-presolver-variant).

Four things to know before touching it.

- **It is invisible by design, so the counters are the only evidence.** It adds
  no OPB content and changes no solution. A version that lifted nothing would
  pass every solution, OPB and VeriPB check in the tree. The test file says so
  in capitals. The counters in `DifferenceLogicStats` are pinned by exact counts
  in the presolver's test and in the MiniZinc and XCSP3 lanes. See [Evidence
  that it fired](#evidence-that-it-fired).
- **From a front end, only unconditional edges are ever lifted.**
  - MiniZinc flattens `b -> x - y <= d` to `int_lin_le_reif`, because
    `mznlib/` declares no `*_imp` predicates. XCSP3 turns
    `imp(b, le(...))` into an `Or` over a reified comparison on walked
    operands.
  - Both arrive fully reified, and a fully reified donor is skipped.
  - On the 2024 and 2025 MiniZinc Challenge instances that printed counters,
    the presolver lifted 17,449 edges and skipped 550,365 reified donors, of
    every shape. Not one half-reified edge was lifted, and no condition was
    fixed at the root.
  - A prototype that lifts the two halves of an `Iff` showed that about a
    quarter of those skipped donors are differences: about 129,000 donors, as
    258,634 half-reified edges. They fixed 13,016 conditions at the root
    (#1373).
  - The half-reified path is reached today only from C++ (`examples/rcpsp
    --machine difference`).
- **It installs a default-on root pass with no budget.** The root
  simplification stage runs Johnson's all-pairs pass. With the lazy binary
  heap it uses, a round is `O(n·m log(n + m))` in nodes `n` and edges `m`
  (`O(n·m log n)` while parallel edges are bounded by a polynomial in `n`), and
  it repeats while a round fixes a condition. It cost 15 s on
  a synthetic connected graph of 10,000 nodes and 30,000 edges, and it
  ignores `--timeout` (#816). On
  `difference_chain` at `n = 640` it more than doubles the presolver's wall
  time: 1.45 s against 0.68 s with it off. On the order where the presolver
  has nothing to win, that makes the presolver 2.4 times slower than leaving
  it out. On every challenge instance it ran on, it took at most 1 ms. See
  [Initialisation](#initialisation-and-global-data).
- **At the edge of the integer range it can turn an answer into an error.** With
  in-range weights close to `2⁶⁰`, models the donors answer throw
  `IntegerOverflow` once the presolver is on, in the default configuration too.
  Nine heavy edges is not the threshold: eight heavy edges plus one light one
  throw as well. Two MiniZinc models print `=====UNSATISFIABLE=====` without the
  presolver and `=====ERROR=====` with it. The causes and the fixes are the
  installed machinery's: #1371 for everything a front end reaches, and #1372 for
  a C++-only configuration. See [Robustness and limits](#robustness-and-limits)
  for the shapes measured here.

## What it is

### Semantics

`DifferenceLogic{stats}` is a `Presolver`, added with
`Problem::add_presolver`. `solve_with` calls its `run` once.

**When it runs.** `run` comes after `create_propagators` and after the proof
model is finalised. The posted constraints' initialisers have run by then
(`solve.cc:373`), but nothing has propagated yet. If those initialisers
already refuted the model, no presolver runs at all. After `run` returns,
`solve_with` initialises what it installed before the next presolver runs
(`:383–395`).

**What it may do.** It may install propagators and initialisers, and with
`disabling_lifted_donors()` it may disable donors' propagators. It never
removes or rewrites a posted constraint, never writes to the OPB
(`Presolver::run` is handed no `ProofModel`), and always returns `true`.

What it lifts, per donor row `positive − negative ≤ value` with an optional
condition `cond`:

- **Operands.** Each operand is reduced by `deview_difference_operand`
  (`difference_graph.cc:1135`) to a bare variable plus an offset. An operand
  `X + c` becomes `(X, c)`.
- **Weight.** The edge `X → Y` gets weight `d = value − c₁ + c₂`
  (`difference_logic.cc:207`), the same arithmetic `DifferenceConstraints`
  uses.
- **Condition.** With `cond` engaged, the edge is `cond → X − Y ≤ d`, and it
  takes part only while `cond` is entailed.
- **Nodes.** A node is a distinct bare variable, keyed in a
  `map<SimpleIntegerVariableID, size_t>`. Two views of one variable are one
  node, which is why the proof needs deview mode
  ([Proof-time state](#proof-time-state)).
- **Posting order.** Edges are numbered in posting order, every linear donor
  before every comparison donor (two passes, `:235` and `:291`).

The propagator is installed only if at least two edges were lifted (`:336`):
over one edge it would compute what that edge's own propagator computes. It
is installed under `CurrentlyUnnamedConstraint`.

Degenerate cases:

- **No donors**: the summary is `lifted nothing`, and nothing is installed.
- **One edge**: `edges_lifted = 1`, `propagator_installed = 0`, and the
  summary ends `, but no propagator was installed`.
- **An aliased or constant operand** is skipped as `skipped_degenerate` and
  left to the donor, even under a condition. Examples are `x − x ≤ d`,
  `(x + 3) − x ≤ d`, `x − 5 ≤ d` and a comparison against a constant. The
  design note's table shows the donor refuting the unconditional `d < 0`
  case in one recursion, or inferring `¬cond` for the conditional one.
- **A condition on a constant**, such as `LinearLessThanEqualIf{…, 1_c == 1}`,
  is lifted as a half-reified edge whose condition is always entailed, or
  never. It is counted under `half_reified_edges_lifted`, its donor is never
  retired, and the answers are right (the detection probe, below).
- **A condition on one of the edge's own operands** (`x ≥ 2 → x − y ≤ −2`) is
  lifted like any other condition. Its variable is then both a node and a
  condition variable, triggered on both, deliberately
  (`difference_graph.cc:1183–1185`).
- **The same donor posted twice** gives two parallel edges. The root
  simplification keeps one of them. MiniZinc merges the duplicate before the
  presolver sees it.

### Concrete constraints and frontend coverage

This is the entry-point table, with one row because there is one class:

| Entry point | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `DifferenceLogic` (presolver) | `--difference-logic` ✓¹ | `--difference-logic` ✓² | `frontend gap (#983)`³ | `frontend gap (#1374)`⁴ | C++ API; `examples/difference_chain --variant presolved`, `examples/rcpsp --variant presolved` |

1. `fzn-glasgow --difference-logic [--difference-logic-simplify on|off]`
   (`fzn_glasgow.cc:381–386`, `:1297–1306`). Both are `extraFlags` in
   `glasgow.msc`, so `minizinc --solver glasgow.msc --difference-logic`
   forwards them. The FlatZinc reader recovers a two-term unit-coefficient
   `int_lin_le` as `LessThanEqual` (`:728–729`), so every lifted MiniZinc
   edge counts as a comparison edge. Checked on 554 differential instances
   under 2.9.7 and 2.10.1 (identical counters), and on every challenge
   instance that lifted anything. `int_lin_le_reif` posts
   `LinearLessThanEqualIff` (`:751`), which is skipped.

   [`comparison.md`](../constraints/comparison.md) used to say otherwise, in its
   lead, its `[^lin]` footnote and its "Not to do" list: that no such recovery
   existed, and that the family was nearly unreachable from MiniZinc. It was
   corrected alongside this document. The claim was wrong when written: the
   recovery landed in `8c6cb43d` (2026-09-04), an ancestor of all three of that
   audit's commits (`76bfd836`, `6b220c79`, `61112ed0`) and of the stack's base,
   and `minizinc-two-term-lin-le` pins it.
2. `xcsp_glasgow_constraint_solver --difference-logic` (`:1944–1949`,
   `:2035–2046`). The affine peephole `try_post_ordering_as_linear`
   (`:1701`) posts a two-term `LinearLessThanEqual`, so XCSP3 edges arrive
   through the linear family. Where the peephole declines, the walk invents
   auxiliaries, and the edge then lies on the auxiliaries rather than on the
   instance's variables.
   - That happens on self-cancelling orderings such as `le(sub(x,x),1)`.
   - It also happens on any ordering containing a `mul`, even a constant
     one, which is affine. `accumulate_affine` has no multiplication case, so
     `le(sub(mul(1,x),y),1)` and `le(sub(mul(2,x),mul(2,y)),4)` each lift as
     a comparison edge over an auxiliary.
   - The walk can also leave no edge at all. `le(add(sub(x,y),mul(0,z)),1)`
     ends as a comparison against a constant, counted `skipped_degenerate`
     (probe `xcspmul/`).

   `imp(b, le(...))` becomes `Or{¬b, r}` over a `LessThanEqualIff` on
   walked operands (`:1565`, `:1842`), which is skipped.
3. `gcspy` (`python/gcspy.cc`) has no presolver plumbing at all, so CPMpy,
   which drives gcs through it, cannot reach it.
4. A `.scp` is a model and a presolver is a solve option, so this is a gap in
   `glasgow_scp_solver` (no flag, checked by `--help` at `86caad24`), not in the
   format. No issue records it: #983's table has no `.scp` column. There is no
   environment variable or option that reaches it either. Since the binary is
   in-tree, that is now filed as #1374.

This is the only presolver in the tree that any front end can turn on (#983's
table).

### Options

None of the options changes the OPB, and none changes what is lifted. Each
one decides what the installed machinery runs, or whether the donors keep
running.

- **`disabling_lifted_donors(bool = true)`**, default off. It also retires the
  propagators of every unconditional donor whose edge was lifted, through
  `Propagators::disable_propagators_for_constraints`. This is the presolver's
  own option, and the [retire-donors
  rewrite](#rewrite-retire-unconditional-donors) covers it. No front end exposes
  it, and only `examples/difference_chain --disable-donors` and the tests call
  it.
- **`simplifying_at_root(bool = true)`**, default on. It controls whether the
  installed initialiser runs the root simplification stage. Front ends take
  `--difference-logic-simplify on|off`. The stage is `difference.md`'s. Its
  one model-visible effect, fixing a condition, is the
  [root-condition-fixing rewrite](#rewrite-root-condition-fixing) here.
- **`reporting_simplification_to(shared_ptr<DifferenceSimplificationStats>)`**:
  the stage's stats block. `install_difference_propagator` registers it
  (`difference_graph.cc:1160`), so a front end prints it.
- **`incrementally(bool = true)`** and
  **`auditing_incremental_propagation(bool = true)`**: these are passed
  through to the installed propagator, unchanged from `DifferenceConstraints`
  (`difference.md`). Neither front end sets them. The audit can also be
  switched on from the environment (`difference_graph.cc:1162`).

There is no `with_consistency()`, and neither `consistency::Auto` nor
`consistency::Dynamic` applies. What the installed propagator achieves is
`difference.md`'s.

**Defaults, and why.** The presolver is off because it costs something on
models it cannot help. On `difference_chain`'s lucky order at `n = 640` it is
2.4 times slower than not adding it ([CPU performance](#cpu-performance)).
The paper's own MiniZinc-wide result is small (Kletzander, Dekker, Schutt and
Stuckey, Table 1 in section 6.4): Huub without difference logic scores 310.00,
with the global propagator but no simplification 312.94, and with both
320.95.

The donors stay on for two reasons:

- The header says the paper measures the hybrid as best. This audit could not
  find that comparison in the paper. Section 4.4 describes the hybrid as a
  possible variation. The configuration study (section 6.3) varies the level,
  the priorities, `IncImp` and the bound-propagation mode, and Huub's own
  component does bounds propagation and falsifies implied edges by bounds
  (section 5.4).
- Only the unconditional donors can be retired without losing propagation
  strength. A half-reified donor also infers `¬cond` from its own bounds,
  which the global propagator never does during search
  ([retire-unconditional-donors](#rewrite-retire-unconditional-donors)).

Simplification is on because the paper measures it as most of the win on two
of its three benchmarks (section 6.4):

| Benchmark | without | global only | global + simplification |
|---|--:|--:|--:|
| MiniZinc (Table 1) | 310.00 | 312.94 | 320.95 |
| ProdCons (Table 2) | 540.00 | 573.40 | 637.50 |
| RCPSPmax (Table 3) | 550.00 | 570.78 | 586.55 |

On RCPSPmax it is the smaller half of the gain. The paper says that its benefit
there "is mostly seen in the number of unknown instances", which fall from 41 to
31. It also says that most unsatisfiable instances are "identified during
simplification": the average time to prove unsatisfiability is 0.26 s with the
global propagator alone and under 0.01 s with simplification (1.98 s with no
difference logic).

### Variable kinds and views

These are what a donor's operands and condition may be:

| Position | Accepted | What happens |
|---|---|---|
| operand | `SimpleIntegerVariableID` | a node |
| operand | `+X + c` view | the node `X`, with `c` folded into the weight |
| operand | `-X + c` (negated) view | refused: `skipped_negated_view`. `−X − Y ≤ d` is not a difference constraint, and lifting it would be unsound (`difference_graph.hh:99–108`). That includes `(−y) − (−x) ≤ d`, which *is* `x − y ≤ d` but is refused anyway |
| operand | constant | `skipped_degenerate`: a plain bound, left to the donor |
| condition | an `IntegerVariableCondition` with `==`, `!=`, `<` or `>=`, over a variable, a view or a constant | carried as the edge's condition; the installed propagator tests it with `literal_is_entailed` |
| condition | `in_range` or `not_in_range` | throws `UnimplementedException` with proofs on, while the model is written and before any presolver runs (#1225) |

The detection probe ran the plain, view, negated-view and constant
conditions with proofs on, and all of them verify
([Can it weaken the model?](#can-it-weaken-the-model)).

**The proof handles views** because the installed propagator cites each
donor row in **deview mode**. A donor's row is written over the user's views'
bits, while the propagator's arithmetic is over the bare variables. Deview
mode substitutes the framework's deview-form line, so the telescoping sum
cancels. `DifferenceConstraints`'s own rows have no deview-form registered,
so for them it is a no-op. The design note records a mutation: removing it
fails VeriPB on the `view_negcycle_wide` fixture in the shipping hybrid. That
was not re-run here.

### Reification

The presolver has no reified form of its own. It reads the donors'
reification conditions:

| Donor's `ReificationCondition` | Lifted as | Counter |
|---|---|---|
| `reif::MustHold` | an unconditional edge | `edges_lifted` (and `comparison_edges_lifted` for a comparison) |
| `reif::If{cond}` | `cond → X − Y ≤ d` | `half_reified_edges_lifted` too |
| `reif::Iff{cond}` | not lifted | `skipped_reified` |
| `reif::MustNotHold` | not lifted | `skipped_reified` |
| `reif::NotIf{cond}` | not lifted | `skipped_reified` |

The last three are each one or two difference edges, and two different
reasons keep them out:

- **`Iff`.** Its rows are labelled `@c[<id>][r]` (`cond → x − y ≤ d`) and
  `@c[<id>][f]` (`¬cond → y − x ≤ −d − 1`). `primary_row_role` publishes
  neither, so the presolver cannot cite them without hard-coding the donor's
  roles.
  - That is an API gap, not a proof obstacle. A prototype that lifts both
    halves agrees with brute force on 4,300 fuzzed systems (strict and
    swapped forms too, in the fact-check's rerun), and every proof it was
    given verifies.
    - Its proofs contain root fixings that cite the halves and occur only
      with it, such as `pol @c[_3][r] -1 + s ;`.
    - On `aircraft-disassembly` 06 it fixes 3,154 conditions at the root,
      and the proof verifies.
    - The design note calls this "a real obstacle, not a choice" ("Deliberately
      deferred"); that overstates it (#1373; corrected by #1396, open).
  - This is the gap that matters, because it is how MiniZinc delivers every
    conditional difference.
  - Lifting it would open MiniZinc routes to two shapes of #1371:
    - the drift: on the prototype, the fact-check's `drift.mzn` gives 31
      solutions and then `=====ERROR=====`, where the shipped build gives 72;
    - shape B, UNSAT from MiniZinc today, throws at the root through the
      prototype in the default `--difference-logic` configuration.
- **`MustNotHold` and `NotIf`.** These are a deliberate gap (#598).
  - Their rows state the integer negation, under the empty role `@c[<id>]`, in
    both families. The linear `NotIf` has had the empty role since #908
    (`f85e63bf`, PR #915; `linear_inequality.cc:187-197`), and
    `constraint_row_test` pins it. #644 fixed the row's content and kept the
    invented `ltn` role. So all four are citable. `primary_row_role` publishes
    none of them, because the row is not the `sum ≤ value` a citer asks for. Two
    code comments still say the linear `NotIf` row is under `ltn`
    (`difference_logic.cc:248`, `linear_inequality.hh:151`). Both are stale
    (corrected by #1396, open).
  - Nothing in gcs constructs these forms except through the base classes'
    constructors.
  - The issue's argument for closing both families together still holds, and
    so does its warning: the strictness flip is where an off-by-one becomes
    unsound.

### Relation to other families

- **What it reads.** Two enumerations, both by `dynamic_cast` over the
  constraints `Problem` stores:
  - `Problem::each_constraint_of_type_with_proof_data<ReifiedLinearInequality>`;
  - `Problem::each_constraint_of_type_with_proof_data<ReifiedCompareLessThanOrMaybeEqual>`.

  That covers `LinearLessThanEqual`, `LinearGreaterThanEqual` (normalised to `≤`
  in its constructor), their `If` and `Iff` forms, the twelve comparison
  classes, and `Problem::post(expr <= rhs)`. Nothing else is read. Neither
  `LinearEquality` (an equality `x − y = d` is two edges; in the paper's section
  5.1 an unconditional one is a view, and level 2 adds half-reified equalities),
  `Equals`, `NotEquals`, `Plus` with a constant, `Increasing` or
  `StrictlyIncreasing` (whose chain rows are difference rows, but unlabelled;
  [`increasing.md`](../constraints/increasing.md) next step 5), `AllEqual`,
  `Disjunctive`, a posted `DifferenceConstraints`, nor any child constraint a
  family installs directly rather than posting. The detection probe confirmed
  for `LinearEquality`, `Equals`, `Plus`, `Increasing`, `StrictlyIncreasing` and
  `AllEqual` that each leaves no counter at all. The rest follow from the class
  hierarchy.
- **What it reads them through.** These are the published accessors:
  - `coefficients_and_variables()`, `value()` and `reification_condition()`
    on the linear side ([`linear.md`](../constraints/linear.md),
    "Presolvers");
  - `left_variable()`, `right_variable()`, `or_equal()` and
    `reification_condition()` on the comparison side
    ([`comparison.md`](../constraints/comparison.md), "Read by a
    presolver");
  - `ConstraintProofModelData<…>::primary_row_role` for both, resolved
    against the emitted label set by
    `NamesAndIDsTracker::constraint_row_label`
    (`names_and_ids_tracker.cc:2239–2247`).

  `static_assert`s at `difference_logic.cc:132–140` pin nine of the eighteen
  family members to their bases. The other nine are not listed:
  `LinearGreaterThanEqualIf`, `LessThanIf`, `GreaterThanIf` and the six `Iff`
  classes. That is harmless, because the enumeration asks for the base.
  `gcs/constraint_enumeration_test.cc` pins the clone contract.
- **What it installs.** It calls `install_difference_propagator` with no
  static bounds and no disallowed conditions: the presolver skips the shapes
  that would produce either. So the installed initialiser
  (`difference_graph.cc:1261–1283`) runs only the root simplification. The
  machinery is [`difference.md`](../constraints/difference.md)'s.
- **Shared code.** The presolver shares these pieces with other code:
  - `deview_difference_operand` and `DifferenceGraph`, with
    `DifferenceConstraints`;
  - `each_constraint_of_type_with_proof_data`, over the same two families,
    which `find_makespan_links` (`presolvers/innards/makespan_links.cc:24`,
    `:82`) also reads. The two scans are independent, and neither sees the
    other's results;
  - `Propagators::disable_propagators_for_constraints` (`propagators.cc:864`).
    Its other caller is `parity_system_gathering`
    (`parity_system_gathering.cc:239`).
- **Other presolvers, and order.** It runs in the order the presolvers were
  added:
  - `examples/rcpsp` adds it before `InferredDisjunctive` and
    `InferredCumulative` (`rcpsp.cc:894`, `:1078`, `:1092`).
  - The front ends add no other presolver.
  - It never reads another presolver's output. A derived `Cumulative` is no
    donor of its own, and it lifts nothing from one.
  - **Others read what it changes.** Its initialiser fixes conditions at the
    root, and a condition can be a bound literal on a start or a capacity. So
    a later scheduling presolver can see tighter windows or capacities. Three
    probes re-run here at `86caad24` reproduce the scheduling documents'
    claims exactly; all their root or full proofs verify.

    | Later presolver | Probe | DifferenceLogic first | DifferenceLogic after, or absent | Agrees with |
    |---|---|---|---|---|
    | `InferredCumulative` | `ord.cc` | posts 3 cuts | posts 1 cut | [`inferred_cumulative.md`](inferred_cumulative.md) |
    | `InferredDisjunctive` | `ord.cc` | finds 3 conflicting pairs, posts 1 clique | finds 0, posts 0 | [`inferred_disjunctive.md`](inferred_disjunctive.md) |
    | `CumulativeStrengthening` | `o.cc` | takes 2 units off the capacity | takes 1 unit off | [`cumulative_strengthening.md`](cumulative_strengthening.md) |

    In `ord.cc` the probe's capacity ends with an upper bound of 3 at the
    root whichever order DifferenceLogic runs in, against 4 without it.
  - **Makespan links.** These are the `s + d ≤ m` rows that
    `find_makespan_links` reads. They are difference edges, and this
    presolver lifts them. The new probe `mk2.cc` runs three tasks
    pairwise disjoint with all three linked. With donors disabled and this
    presolver first, `InferredDisjunctive` and `InferredCumulative` still
    certify `m ≥ 6`, as they do with no difference logic at all. Every
    configuration verifies its complete enumeration of 160 solutions. The
    links are posted constraints whose labels stay in the `.opb`, and
    disabling a propagator does not remove them. That settles the
    combination `inferred_disjunctive.md` reports as untested, on that
    probe.
  - **Added before an `AutoTable`, it throws** `UnexpectedException`
    ("difference logic incremental state was initialised below a decision")
    in its default incremental mode, whenever it installs a propagator (two
    edges or more, `difference_logic.cc:336`). The `AutoTable`'s throwaway
    root search guesses `TrueLiteral` and then makes the installed
    propagator's first call
    ([`difference.md`](../constraints/difference.md#initialisation-and-global-data),
    item 4; #1378). With `incrementally(false)`, or added after the
    `AutoTable`, it solves. On `x < y`, `y < z` over
    `0..5` with `AutoTable{{x, z}}`, both give 20 solutions in 30 recursions,
    against 29 with no `AutoTable` (`tmp/fd-pre/older/dlat/dlat.cc`,
    `86caad24`, 2026-10-20).
  - So run it before the scheduling presolvers, as `examples/rcpsp` does, and
    after any `AutoTable` unless it is `incrementally(false)`.
- **Candidate merge.** There is none. The presolver is a detection pass over
  the comparison and linear families, and its machinery is `difference`'s.

## The proof model

### OPB encoding

None. The presolver writes nothing to the OPB. `difference_logic_presolver_opb`
checks the `.opb` is byte-identical with and without it on three fixtures:

- a linear one;
- a comparison one;
- one on which the root simplification both fixes a condition and drops a
  redundant edge.

The donors' encodings are [`linear.md`](../constraints/linear.md)'s and
[`comparison.md`](../constraints/comparison.md)'s. Each donor's row is
definitional: one inequality, half-reified for `If`.

### Labels

It writes no labels of its own. Every edge carries the label of its donor's
primary row, `@c[<id>]` with the empty role, for `MustHold` and `If` in both
families. That label is resolved through the donor's published role, never
built here. The design note's "Citing the donor's row" explains why: an
earlier constructed label would have named the negated row for a comparison's
`MustNotHold`.

`constraint_row_test` checks the published role against the `.opb` text for
every reification kind of both families. `difference_logic_presolver_opb`
counts the `@c[` rows of each comparison form (1, 1, 1, 1, 2). With proofs
off no label is looked up, and every right-shaped donor lifts.

### Cake conformity

There are no rows to conform. A `.scp` has no notion of a presolver, and no SCP
chain case runs one. None can, because the chain solves with
`glasgow_scp_solver`, which has no switch for it (#1374). The chain's steps do
work on a presolved proof, though, because cake labels the donor rows `@c[<id>]`
too. The test is the steps of `verified_encodings/run_scp_chain.bash`, run by
hand: `cake_pb_cp` re-derives the OPB from the `.scp`, `veripb --elaborate`
checks the solver's proof against it, and `cake_pb_cp` re-checks the core.

- **Linear donors pass.** These were re-run here on `86caad24`:
  - `difference_chain --mode refute --variant presolved`: cake core
    `s VERIFIED UNSATISFIABLE`;
  - `rcpsp --size 10 --seed 5 --machine-fraction 0.7 --machine difference
    --variant presolved`, whose half-reified linear donors give 9 root
    fixings: cake core `s VERIFIED BOUNDS 20 <= OBJ <= 20`.

  The fact-check passed the fixpoint, donors-off and two more rcpsp cases the
  same way.
- **Comparison donors over offset views cannot be checked.** cake rejects the
  `.scp` with or without the presolver (`less_equal y[0] (y[20] + 19)`), because
  views do not parse ([`workflow2_testing.md`](../workflow2_testing.md)). That
  is a format limit, not the presolver's.

### Proof-time state

**At the root, from the pass: nothing.** The pass emits no line, no comment
and no marker. The proof has no line that says the presolver ran.

**At the root, from the installed initialiser.** Each condition the root
simplification fixes is one `JustifyExplicitly` at `ProofLevel::Temporary`
(`difference_graph.cc:361`):

1. a `pol` of the candidate edge's row and its witness path's rows, all cited
   by the donors' labels, in deview mode, closed by `s`;
2. a `rup` of the unit clause `¬cond`;
3. a `del`.

On `rcpsp --size 9 --machine-fraction 0.9 --max-lag-density 0.4 --max-lag-slack
0 --machine difference --seed 4 --variant presolved` the stage writes 13 such
triples in one round. The first is `pol @c[_22] @c[_1] + s ; rup 1
i[machine_before0_1][b0] >= 1 ; del id -2`, and the pols cite two to five rows,
the candidate and a path of one to four. Twelve fix their condition
(`conditions_fixed = 12`). The thirteenth infers `~i[machine_before2_3][b0]`,
the opposite of what the tenth inferred, so the inference fails and the model is
refuted. That is a 45-line, 1,212-byte proof, in 0 recursions, and it verifies.
Redundant- and dead-edge removal, and the lower round bound, leave no trace
anywhere. The
derivation is `difference.md`'s.

**During search.** The installed propagator's proofs are `difference.md`'s:

- a negative cycle is refuted by one telescoping `pol` over the cycle's rows,
  then `rup >= 1`;
- a bound push is its own `pol` over two lines, its edge's donor row and the
  predecessor bound's definition, so a chain of pushes cites one donor row per
  push.

From this entry point, every cited row is a donor's `@c[<id>]`. In the
refutation on `difference_chain --mode refute -n 20`, one `pol` cites 23
donor labels.

**Deletion.** Only the scaffolding inside each `JustifyExplicitly`, at
`Temporary`, is deleted. Nothing the presolver route adds lives at `Top`.

**Naming.** None of its own. A reconstructor finds what the propagator used
by the labels in its `pol`s, and the labels are the donors'.

**Hints-only content.**

- The installed machinery's assertions carry **no hint at all**. No
  justification in `gcs/constraints/difference/` names a hint type, so each
  takes the default (`NoHint`), and no `a` line at any level showed one. They do
  not even carry the `constraint_id unnamed` that `CurrentlyUnnamedConstraint`
  gives the scheduling presolvers' derived constraints.
- At `AssertionLevel::Inferences`, a refutation is a bare `a >= 1;` and a
  root fixing a bare `a 1 i[machine_before0_1][b0] >= 1;`.
- The comparison donors' own assertions say `::comparison:((constraint_id
  _N))`; the linear donors' are bare too.

So a reconstructor has to recognise a difference row by its shape: two
`BinEnc` sums with opposite unit coefficients, or the deview-form of one. It
then has to search the rows for the cycle or path. `difference.md` owns that
verdict per rule. From this side, the point is that the presolver route
makes the search range over every two-term row in the model, not over one
constraint's rows.

**The assertion levels.** On `difference_chain --variant presolved`, with
linear and with comparison donors, in both modes:

| Level | Result |
|---|---|
| `Definitions` | `UNDER ASSERTIONS` |
| `Inferences` | `UNDER ASSERTIONS` |
| `Backtracking` | `UNDER ASSERTIONS` |
| `Links` | `UNDER ASSERTIONS` on the unsatisfiable refute mode. The satisfiable fixpoint mode is rejected at its first `solx`: at line 317 with linear donors, line 773 with comparison donors |

The `Links` rejection is #1210's, which affects only range-declared variables
wider than `{0, 1}`. `difference_chain`'s variables are `0..k·n`. The
fact-check's three-variable probe (one linear and one comparison donor over
`0..5`) is rejected at `Links` with range domains, and is `UNDER ASSERTIONS`
with the same values as a value list. The rcpsp root-fixing instance, which
refutes before any solution, is `UNDER ASSERTIONS` at `Definitions`, `Links`,
`Inferences` and `Backtracking`. Nothing here is specific to the presolver.

**Auxiliaries.** None. The presolver creates no variable, flag or
proof-only vector. With proofs off, `edge_lines` stays empty
(`difference_logic.cc:213`), and nothing is indexed by it.

## The implementation

### Initialisation and global data

Four costs, kept apart as the template asks.

**1. The pass** (`difference_logic.cc:108–352`):

1. Register the stats block, always (`:115`), so that a run which lifts
   nothing still reports having looked.
2. Walk every posted constraint twice: once for the linear family, once for
   comparisons. Each is a `dynamic_cast` per constraint. With proofs on,
   each donor's label is looked up before its shape is tested, which is one
   string build and one `set<string>` lookup per donor.
3. Per right-shaped donor, two `deview_difference_operand` calls and two
   `map` lookups for the nodes, then a `push_back`.
4. Call `install_difference_propagator` once.

The pass's own work is `O(C + E log N)` in constraints `C`, edges `E` and
nodes `N`. With proofs on, add one label lookup per enumerated donor:
`O(C log L)` string comparisons over a label set of size `L`. That is the
20 ms to 157 ms difference in the padding rows below. No step reads a domain,
and none depends on a weight's or a domain's size.

The install is where it stops being linear. `Propagators::install_returning_id`
deduplicates the propagator's scope with a linear `contains` per trigger
(`propagators.cc:721–748`), and this propagator's scope is every node plus
every condition variable. So the install is quadratic in the node count:
#1309, already open. It covers both the scope loop and the constraint-scope
loop. At 100,000 nodes, `perf` puts about 61% of the process's samples in that
function, inside `install_difference_propagator`. That is about 3.0 s of a 4.9 s
process (the fact-check's rerun): nearly all of the 3.1 s pass.

`install_difference_propagator` has a quadratic of its own:
`find(condition_vars, c.var)` per conditional edge
(`difference_graph.cc:1186–1190`) is `O(conditional edges × distinct condition
variables)`. No front end lifts a conditional edge today, so it does not show.
It would matter after #1373: the prototype lifts 81,252 conditional edges on
`aircraft-disassembly` 09.

Measured with `tmp/fd-diff/difference_logic/scan/scan.cc`, which wraps
`DifferenceLogic::run` in a timing presolver and puts a marker presolver
after it. Conditions: `86caad24`, Release, fataepyc-09, one pinned core,
`GLIBC_TUNABLES` mmap threshold 32 MiB and trim threshold 4 GiB, one run
each, 2026-10-20. The model is a connected random graph: `n − 1` chain edges
through every node, plus random edges of weight `w` up to the edge count, a
third of them as comparisons:

| nodes | edges | other constraints | proofs | pass (incl. install) |
|--:|--:|--:|---|--:|
| 1,000 | 3,000 | 0 | off | 1.8 ms |
| 3,000 | 9,000 | 0 | off | 7.5 ms |
| 3,000 | 9,000 | 0 | on | 10.8 ms |
| 10,000 | 30,000 | 0 | off | 49 ms |
| 30,000 | 90,000 | 0 | off | 326 ms |
| 30,000 | 90,000 | 0 | on | 381 ms |
| 100,000 | 300,000 | 0 | off | 3.12 s (3.14 s at `w = 10¹²`) |
| 10,000 | 0 | 300,000 three-term linears | off | 20 ms |
| 10,000 | 0 | 300,000 three-term linears | on | 157 ms |

**2. The initialiser it installs**, at `InitialiserPriority::Expensive`. It
runs once, at the root, with proofs on or off, before any propagation. With
`simplifying_at_root` on (the default) it runs Johnson's all-pairs pass,
which `difference.md` owns:
- each round is Bellman-Ford from the implicit `v0`, `O(n·m)`;
- then one Dijkstra on reduced costs from each node that is the tail of an
  edge or the head of a candidate. The Dijkstra uses a `std::priority_queue`
  with lazy deletion (`difference_simplify.cc:201`), which keeps one entry
  per improving relaxation, stale ones included, so each is
  `O((n + m) log(n + m))`, and a round is `O(n·m log(n + m))` in the worst
  case. That is `O(n·m log n)` when the parallel edges are bounded by a
  polynomial in `n`, but the donor scan merges nothing: each donor is its
  own edge, so MiniZinc's flattening of 200 constraints `x − y ≤ k` over one pair (200
  `int_lin_le` on 2.9.7 and 2.10.1) is lifted as 200 parallel edges between
  two nodes (`differenceLogicEdgesLifted=200`,
  `differenceLogicNodes=2`). The stage then drops 199 as redundant, but only
  after its Dijkstras have scanned them, and with
  `--difference-logic-simplify off` all 200 reach the propagator, whose heaps
  are lazy too, as `difference.md` measures. These counts were measured at
  `86caad24` on fataepyc-08, 2026-10-21;
- it repeats while a round fixes a condition, so there is at most one round
  more than the conditions it fixes.

A per-source distance threshold prunes paths that cannot matter. The design
note's `O(n² log n + nm)` is the Fibonacci-heap bound (corrected by #1389,
open). The pass has no
budget, and it does not observe `--timeout`: #816 is about initialisers in
general, and a `--timeout 0.05` run took 1.32 s at the root in the
fact-check. Measured in the same runs:

| nodes | edges | simplification | edges dropped |
|--:|--:|--:|--:|
| 1,000 | 1,000 (a chain, plus one random edge) | 7.4 ms | 1 |
| 3,000 | 3,000 (a chain, plus one random edge) | 75 ms | 1 |
| 10,000 | 10,000 (a chain, plus one random edge) | 864 ms | 1 |
| 1,000 | 3,000 | 107 ms | 966 |
| 3,000 | 9,000 | 1.15 s | 2,985 |
| 10,000 | 30,000 | 15.0 s | 9,946 |

The weight does not matter: `w = 100` and `w = 10¹²` agree to the
millisecond. What the cost is proportional to is how much of the graph each
node reaches, and these graphs are connected.

On real models it was negligible. Over the 2024 and 2025 MiniZinc Challenge
instances that lifted anything (54 instances, up to 3,686 edges over 6,223 nodes
on `aircraft-disassembly`), the stage reported at most 1 ms. The survey records
only edge and node counts, so the shape was not measured. With 3,686 edges over
6,223 nodes, at least 1,388 components are single edges. That does not bound how
far a source reaches, since one component could still hold over 1,100 nodes.
Short reach is the likely reason it is cheap, but it was not measured. The
near-chains above are as sparse and are not cheap. On `difference_chain`, which
is dense and connected, it more than doubles the wall time at `n = 640` ([CPU
performance](#cpu-performance)).

**3. Propagation during search** is `difference.md`'s. Two things about it
are specific to this entry point:

- The donors keep running, whenever they are woken. There are no runtime
  priorities (#582), and the queue is seeded in registration order only on the
  first pass (`propagators.cc:1100–1128`). So the global propagator, registered
  last, runs after every donor at the root. After that, only woken propagators
  run. On the `n = 640` fixpoint, 206,400 donors and the global propagator give
  825,607 propagations over 643 nodes. That includes the root's first pass,
  which runs all 206,402 propagators: the donors, the one-term `y₀ ≥ n` bound
  and the global propagator. During search it is at most (825,607 − 206,402) /
  642, about 965 per node.
- Its triggers add one to the degree of every node and condition variable
  (`propagators.cc:773–775`). So under the default `dom_then_deg` heuristic,
  installing it can change the search tree even where it never propagates
  anything ([Can it weaken the model?](#can-it-weaken-the-model)).

**4. Certificates** are the installed machinery's, and are paid only when it
infers something ([Proof performance](#proof-performance)).

### Propagator inventory

The pass itself installs nothing that runs during search. These rows
summarise, for this presolver's configuration, the two things
[`difference.md`](../constraints/difference.md) documents:

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| global difference propagator (`install_difference_propagator`) | `on_bounds` every node; `on_change` every condition variable | derived: the condition variables (over-reported except for `!=` and `not_in_range`), including a node that is also a condition variable | `difference.md`'s bound-push and negative-cycle rules | `edges_lifted ≥ 2` | no: returns `Enable`; a bound can snap past a hole and seed a further push (`run_hole_snap_test`) | no |
| root initialiser | none (initialiser, `InitialiserPriority::Expensive`) | n/a | [root-condition-fixing](#rewrite-root-condition-fixing); redundant- and dead-edge removal, a lower round bound | as above; the stage only with `simplifying_at_root` | n/a | n/a |

The donors' own propagators, and their idempotence and hole sensitivity, are
[`linear.md`](../constraints/linear.md)'s and
[`comparison.md`](../constraints/comparison.md)'s. They stay installed unless
[retired](#rewrite-retire-unconditional-donors).

### Mutable state and incrementality

The pass keeps no state. The stats block is shared with the clone that
`add_presolver` stores, and is filled by assignment at the end (`:349`), so a
caller's handle reads what this solve did. Running the presolver twice in
one solve, by adding it twice, would install two propagators over the same
edges. Nothing stops that, and nothing tests it. The installed machinery's
state is `difference.md`'s: one trailed constraint-state slot, and an undo
trail.

### Interior values and optional pruning

**What this presolver offers:** none. It installs no
optional-interior-pruning pair.

**What it observes.** Its pass runs before
`choose_optional_interior_pruning()` (`solve.cc:406–407`), so what it installs
is counted.

- **Nodes.** The installed propagator triggers on their bounds only, so it
  reports no hole sensitivity on a node that is only a node. That is the right
  answer by [`optional-interior-pruning.md`](../optional-interior-pruning.md)'s
  definition: a bound that snaps past a hole does not count. A node that is
  also some edge's condition variable, as in `x ≥ 2 → x − y ≤ −2`, is
  declared hole-sensitive through that condition. The two trigger lists are
  deliberately not deduplicated (`difference_graph.cc:1183–1185`).
- **Condition variables.** It triggers `on_change` on these whatever the
  operator, so holes in them count. That is accurate only for `!=` and
  `not_in_range`, whose entailment an interior removal can decide. The comment
  at `difference_graph.cc:1172` names `!=`; `not_in_range` is the same case over
  a range. It over-reports for the rest:
  - `==` is entailed only once the domain is a singleton, which removing
    interior values never produces;
  - `>=`, `<` and `in_range` are questions about bounds.

  Disentailment, which a hole can decide, does not matter: a false condition
  only removes an arc. Over a variable wider than `{0, 1}`, the
  over-reporting keeps somebody else's interior pruning alive needlessly.
  That errs on the safe side, and it agrees with
  [`difference.md`](../constraints/difference.md).

On every front-end model the survey reached, no condition was lifted at all.
The only conditions in practice are those of `examples/rcpsp --machine
difference`, which are Booleans and have no interior.

The pass reads no domain at all: it is a scan over constraint arguments. Its
whole vocabulary is the donors' arguments, and what it installs reads bounds
on its nodes.

### Robustness and limits

- **Unbounded domains and the integer range.** The pass's one piece of
  arithmetic is `d = value − c₁ + c₂`. With every input in
  `±(2⁶⁰ − 1)` that is at most about `3·2⁶⁰`, inside `Integer`, and it is
  checked anyway. The installed machinery is a different matter:
  - **It can throw on in-range inputs.** Its potential functions are computed by
    Bellman-Ford from `v0` with every seed at zero, ignoring the domains, and
    they are held in a plain `Integer`. So is some of what is formed from them.
    Its refutation pass narrows a candidate bound before testing it against the
    node's domain. The front ends reach only the shortest-path arithmetic
    (#1371). The refutation pass (#1372) is reached through the presolver only
    with `incrementally(false)`, the donors retired and simplification off,
    which no front end selects. From C++ that configuration throws on chain-10
    and on cycle-8 (`ext2fs.cc`), and solves chain-8 and chain-9.

    The sites, how far the list goes, and the fixes are `difference.md`'s: see
    its [Robustness and
    limits](../constraints/difference.md#robustness-and-limits), #1371 and
    #1372. This document records only what the presolver's configurations do.
  - **What was measured.** Domains are `±M`, with `M = 2⁶⁰ − 1`, unless stated.
    The donors are `LinearLessThanEqual` (or `LessThanEqual{x + M, y}` for the
    chains), and `LinearLessThanEqualIf` for B and the drift. The probes are
    `extreme/ext.cc`, `ext2.cc` and `ext3.cc`, at `86caad24`. The shapes are
    #1371's:

    | shape | no presolver | hybrid, simplification on (default) | hybrid, simplification off | donors retired, simplification on | donors retired, simplification off |
    |---|---|---|---|---|---|
    | chain-8: `x[i] − x[i+1] ≤ −M`, `i < 8` | UNSAT | UNSAT | UNSAT | throws | throws |
    | chain-9 | UNSAT | throws | UNSAT | throws | throws |
    | cycle-8: chain-8 closed by `x[8] − x[0] ≤ −M` (nine edges) | UNSAT | throws | UNSAT | throws | throws |
    | A: chain-8 plus a redundant `x[0] − x[8] ≤ 8` | UNSAT | throws | UNSAT | throws | throws |
    | B: chain-8 plus an undecided `b → x[8] − x[0] ≤ −M` | UNSAT | throws | UNSAT | throws | throws |
    | drift: `b → x − y ≤ −M`, `c → y − x ≤ 0`, `x, y ∈ {0, M}`, `g ∈ 0..8`, searched `g, c, b, x, y` largest first | 72 solutions | throws | throws | throws | throws |

    "UNSAT" means refuted in one recursion; "throws" means `IntegerOverflow`.
    Chains of 7 and cycle-7 (eight edges) are fine in every configuration. In
    the default hybrid, nine heavy edges is the threshold for the pure chain
    and cycle; with simplification off the hybrid solves chain-9, chain-10 and
    cycle-8. A throws with eight heavy edges plus one light one, and B is
    cycle-8 with its closing edge made conditional. With the donors retired,
    chain-8 already throws.
  - **The donors answer every one.** Without the presolver each is solved, and
    the proof verifies. In the hybrid with simplification off, the donors refute
    every chain-based shape at the root, before the global propagator's first
    call. The default configuration still throws on all of them but chain-8, in
    the root initialiser, which runs before any propagation. The drift has no
    such protection: the donors cannot refute it, so it throws in every
    configuration. Only C++ reaches it today, since front ends deliver
    conditional edges as `Iff`. Lifting `Iff` (#1373) would open a MiniZinc
    route to it, and to shape B.
  - **The front-end symptom.** `fzn-glasgow --difference-logic` (MiniZinc 2.9.7
    and 2.10.1) prints `=====ERROR=====` (exit 1) where it otherwise prints
    `=====UNSATISFIABLE=====`, on two models from #1371. With proofs on, the
    `.pbp` is truncated. With `--difference-logic-simplify off`, both are
    `=====UNSATISFIABLE=====`.

    ```minizinc
    % chain9.mzn
    array[0..9] of var int: x;
    constraint forall (i in 0..8) (x[i] + 1152921504606846975 <= x[i + 1]);
    solve satisfy;
    ```

    ```minizinc
    % chain8plus.mzn: shape A over 0..1
    array[0..8] of var 0..1: x;
    constraint forall (i in 0..7) (x[i] + 1152921504606846975 <= x[i + 1]);
    constraint x[0] <= x[8] + 8;
    solve satisfy;
    ```
  - **What `integer-ranges.md` says.** It accepts the nine-edge chain's throw
    for a posted `DifferenceConstraints`, as a sum "genuinely" needed. Through
    the presolver, the inputs are linears and comparisons that never throw on
    these models.
  - **The other routes.** XCSP3 cannot reach any of this, because its parser
    refuses integers wider than `int`. The differential harness's `±(2⁶⁰ − 1)`
    instances, which had no eight-edge heavy chain, lifted and solved without
    error.
- **Negative values, zero.** These are fine. Negative and zero weights,
  negative domains and zero-weight cycles are all in the test corpus, the
  fuzz and the differential harness.
- **Degenerate shapes.** See [Semantics](#semantics). An aliased pair or a
  constant operand is left to its donor. A one-edge system installs
  nothing. A system with no difference constraint installs nothing, and
  leaves the `.pbp` byte-identical (the `opb` lane's negative control).
- **Proofs on and off.** With proofs off, every right-shaped donor lifts.
  With proofs on, a donor whose primary row was not emitted is declined
  (`skipped_uncitable_row`), and then the two would search differently.
  - No honest run produced one. `define_proof_model` always emits the row for
    `MustHold` and `If`. The counter was 0 in every proof-on run here:
    detection probe, fuzz, harness.
  - The only measured non-zero is the design note's deliberate revert of
    #596, under which a whole comparison model was declined.
- **Exceptions.** None reached from a front end other than the overflow
  above. Across the differential harness, the fuzz and the challenge survey,
  no other exception came from the presolver.

### Interval efficiency

1. **Propagation side (the pass).** Fine at any width.
   - The pass reads constraint arguments, never a domain. "Reaches for
     `State`'s per-value iterators nowhere at all" is true of
     `difference_logic.cc`, which has no `State` read.
   - The scan is proportional to the number of posted constraints, plus the
     install's quadratic in nodes (#1309).
   - Neither the weights nor a domain's width changes the pass time: the
     table above, at `w = 100` and `w = 10¹²`.
   - The installed initialiser is width-free too (`difference.md`).
2. **Reason side.** The pass gives no reasons. A push's reason is its
   predecessor's bound literal and its edge's condition. A cycle's or a root
   fixing's reason is the distinct conditions on it, at most one per edge. None
   is ever per value (`difference.md`).
3. **Proof side.** The pass emits nothing.
   - A root fixing is one `pol` of `1 + path length` rows, then one `rup`
     and one `del`, whatever the domains.
   - The donors' rows are in `BinEnc`, logarithmic in the domains' magnitudes,
     not their widths (`difference.md`, OPB encoding).
   - There is no width gate to report, since nothing is chosen by width.
4. **Audit lane.** No row in `gcs/large_domain_audit_test.cc` posts the
   presolver. The `difference` family's rows there are `difference.md`'s.
   - What no test varies, through this entry point:
     - a wide declared domain with lifted donors;
     - a lifted graph of more than five nodes in the unit tests (the example
       lanes reach 42 and 13);
     - a condition that is not a Boolean.
   - The scan probe above is the only measurement at scale.

## Rewrite catalogue

These facts hold for every entry:

- The presolver adds nothing to the OPB.
- Lifting itself emits no proof line.
- Every inference the installed machinery then makes is certified by its own
  derivations ([`difference.md`](../constraints/difference.md)), citing the
  donors' rows by label.
- Nothing the presolver route writes is an assertion at `AssertionLevel::Off`.

### Rewrite: lift-linear-edge

- **Pattern.** A `ReifiedLinearInequality` with `reif::MustHold`, exactly two
  terms, one with coefficient `+1` and one with `−1`. Both deview to bare
  variables, and those are distinct (`difference_logic.cc:235–285`). With
  proofs on, it must also have an emitted `@c[<id>]` row.
  `LinearGreaterThanEqual` matches after its constructor negates it.
- **Posts.** Edge `X → Y` with weight `value − c₁ + c₂`, citing `@c[<id>]`.
  The donor's propagator stays.
- **Derived mode.** Yes. No OPB row; nothing is proved at install.
- **Why it is true.** The donor row says `(X + c₁) − (Y + c₂) ≤ value`, which
  is `X − Y ≤ value − c₁ + c₂` over the integers. The edge states exactly
  what the donor states, so the global propagator infers only consequences of
  posted constraints.
- **Proof technique.** None for the lift: nothing is derived. The installed
  propagator's `pol`s cite the row in deview mode, which is what makes the
  donor's view-bit form telescope against bare-variable reasoning
  (`difference.md`'s rules).
- **Neutral?** For propagation, yes: the global propagator's fixpoint
  subsumes the donor's single-edge bound push. That is what the
  [retire-donors](#rewrite-retire-unconditional-donors) tripwire rests on. It
  is not neutral for search under the default heuristic, because the
  installed propagator raises the node's degree ([Can it weaken the
  model?](#can-it-weaken-the-model)).
- **Offline reconstructibility.** There is nothing to reconstruct for the
  lift. The installed rules' verdicts are `difference.md`'s. This entry point
  adds one thing to them: the rows a reconstructor must search are every
  two-term row in the model, and no hint names them
  ([Proof-time state](#proof-time-state)).
- **Proof size.** Zero lines for the lift. Each later inference that uses the
  edge cites its label once, in one `pol` term.
- **Gaps.** None.
- **Tightness.** Not shown by a committed lane: the presolver has no mutation
  hooks. The design note records ad hoc mutations from the presolver's
  bring-up, not re-run here. The one that touches this rewrite is asking the
  enumeration for `LinearLessThanEqual` instead of the base class, so that it
  finds nothing. All five test modes caught it.

### Rewrite: lift-comparison-edge

- **Pattern.** A `ReifiedCompareLessThanOrMaybeEqual` with `reif::MustHold`
  (`LessThanEqual`, `LessThan`, `GreaterThanEqual`, `GreaterThan`), over two
  operands that deview to distinct bare variables (`:291–326`). With proofs
  on, it must also have an emitted `@c[<id>]` row.
- **Posts.** Edge `left → right` with weight `0` for `≤` and `−1` for `<`,
  adjusted by the offsets. The `Greater*` constructors already store the
  operands swapped. `comparison_edges_lifted` counts it.
- **Derived mode.** Yes.
- **Why it is true.** `x ≤ y` is `x − y ≤ 0`, and `x < y` is `x − y ≤ −1`
  over the integers. The row the donor emits is exactly that inequality, under
  the empty role (`comparison.cc:119–124`).
- **Proof technique.** As [lift-linear-edge](#rewrite-lift-linear-edge).
- **Neutral?** As lift-linear-edge. A comparison spelling over offset views
  costs more proof than the linear one. That cost is mostly the view
  scaffolding, not the donors' logging, so retiring the donors removes little
  of it (see [Proof performance](#proof-performance)).
- **Offline reconstructibility.** As lift-linear-edge.
- **Proof size.** Zero lines; one `pol` term per later use.
- **Gaps.** None.
- **Tightness.** Not shown by a committed lane. The design note's ad hoc
  table records these mutations as caught by the counts, the equivalence,
  the tripwire and VeriPB:
  - an inverted edge;
  - a dropped strictness;
  - an approximated negated view.

  It records un-labelling the rows as caught only by the `opb` lane's label
  count and by VeriPB.

### Rewrite: lift-half-reified-linear-edge

- **Pattern.** As lift-linear-edge, with `reif::If{cond}`.
  `LinearLessThanEqualIf` and `LinearGreaterThanEqualIf` match.
- **Posts.** Edge `cond → X − Y ≤ d`, citing the `@c[<id>]` row, which
  `define_proof_model` emits under `HalfReifyOnConjunctionOf{cond}`
  (`linear_inequality.cc:185`). `half_reified_edges_lifted` counts it. The
  donor's propagator is never retired.
- **Derived mode.** Yes.
- **Why it is true.** The donor states the same implication. The global
  propagator uses the edge only while `cond` is entailed, and puts `cond` in
  the reason of anything derived through it (`difference.md`).
- **Proof technique.** As lift-linear-edge. The row's big-M residual on
  `¬cond` survives the telescoping sum, and is the condition literal the
  propagator's reason carries.
- **Neutral?** No, and deliberately not retired. The donor also infers `¬cond`
  from its own bounds. The global propagator infers nothing about a condition
  during search: neither the paper's section 5.4 bounds check nor its `IncImp`
  is implemented (`difference.md`). It does so only at the root
  ([root-condition-fixing](#rewrite-root-condition-fixing)).
- **Offline reconstructibility.** As lift-linear-edge.
- **Proof size.** Zero lines; one `pol` term per later use, plus a
  `saturate` where a residual survives (`difference.md`).
- **Gaps.** None. It is unreachable from either front end (see [Detection and
  its failure modes](#detection-and-its-failure-modes)).
- **Tightness.** Not shown by a committed lane. The design note records, as
  caught by counts, equivalence, tripwire and VeriPB, a mutation that drops
  the condition from the edge. The test's `reified_impossible` fixture is the
  reusable instance: a conditional edge that is impossible over its domains,
  so ignoring the condition loses every solution with `cond` false.

### Rewrite: lift-half-reified-comparison-edge

- **Pattern.** As lift-comparison-edge, with `reif::If{cond}`: `LessThanIf`,
  `LessThanEqualIf`, `GreaterThanIf` and `GreaterThanEqualIf`.
- **Posts.** A conditional edge, citing `@c[<id>]` under
  `HalfReifyOnConjunctionOf{cond}` (`comparison.cc:126`). Never retired.
- **Derived mode.** Yes.
- **Why it is true.** As lift-half-reified-linear-edge.
- **Proof technique.** As lift-half-reified-linear-edge.
- **Neutral?** No, and never retired, as lift-half-reified-linear-edge.
- **Offline reconstructibility.** As lift-linear-edge.
- **Proof size.** As lift-half-reified-linear-edge.
- **Gaps.** None. It is unreachable from either front end.
- **Tightness.** Not shown by a committed lane. The design note records
  lifting an `Iff` as though it were an `If` as caught *only* by the
  detection counts. The `r` half really says `cond → x − y ≤ d`, so solutions
  and proofs do not notice. `skipped_reified` is the whole guard.

### Rewrite: retire-unconditional-donors

- **Pattern.** `disabling_lifted_donors()` was set, and at least two edges
  were lifted. The rewrite covers the `ConstraintID` of every
  unconditional donor whose edge was lifted. It never covers a half-reified
  donor (`:222–230`), nor a donor that was skipped.
- **Posts.** Every propagator of those constraints is permanently disabled:
  marked permanently disabled (`propagators.cc:864–884`), partitioned past
  `idle_end` when the queue is built, by a boundary that nothing restores
  (`:1100–1128`), and skipped if already queued (`:1310`).
  `donor_propagators_disabled` counts propagators. The constraints keep their
  OPB rows, scopes, adjacency and degrees.
- **Derived mode.** Not applicable: nothing is posted.
- **Why it is true.** Disabling a propagator never loses a solution. The
  question is propagation strength.
  - **Bounds.** The global propagator's fixpoint is closed under every
    lifted edge's bound push, `lb(Y) ≥ lb(X) − d` and
    `ub(X) ≤ ub(Y) + d`. It is re-woken by its own inferences until nothing
    changes, so it reaches the donors' greatest fixpoint, or refutes the
    system where they would crawl to a wipe-out.
  - **Interior values.** A binary inequality's arc consistency prunes only
    bounds, so the donor's propagator has nothing finer to lose.
  - **Redundant edges.** The root simplification may drop a redundant
    edge only when a path no longer than its weight implies it: all but one
    of several equal-weight parallel edges, or an edge with a strictly
    shorter path. That path implies the same push, and a push through an
    intermediate node that snaps past a hole lands at least as high.
  - **Conditional donors.** These are excluded because they also infer
    `¬cond`, which nothing else here does during search.
- **Proof technique.** None: no line. The OPB still holds every donor row,
  and the installed propagator cites them.
- **Neutral?** Yes, and it is the presolver's tripwire. Degrees do not move,
  because both arms carry the installed propagator. So under the default
  heuristic, solutions and recursions must match with the donors on and off.
  - `difference_logic_presolver_tripwire` asserts that over 18 fixtures in
    five donor spellings.
  - The fuzz here asserts it over 8,300 random systems. Those have holes,
    views, constants, every spelling, and conditions on Booleans and on node
    bound literals. All matched.
  - `difference_chain` matches too: 23 recursions both ways at `n = 20`;
    163 and 643 at `n = 160` and `640`.
- **Proof size.** It does not just subtract what the retired donors would
  have logged. An inference a donor made first is made by the global
  propagator instead, with its own derivation. That is a two-row `pol` per
  push, about what a donor writes, but a negative cycle is one `pol` over
  every row on the cycle, where a donor may need only its own row. Measured
  at `86caad24` on fataepyc-08, 2026-10-21, kept against retired, `.pbp`
  bytes:
  - `difference_chain`:
    - refute: 1,923 against 762 at `n = 20`, and 3,935 against 2,432 at
      `n = 160` (linear donors); 40,091 against 35,621 at `n = 160`
      (comparison donors).
    - fixpoint: identical for linear donors, two lines and about 30 bytes
      larger retired for comparison donors.
  - A chain `x_i + 1 ≤ x_{i+1}` of `L` donors whose pushes start from an
    `Equals` posted first (at either end or the middle, or from a decision):
    36.5% to 47.0% smaller retired, for example 2,803,417 against 1,499,017
    at `L = 1,000` with linear donors. Kept, the donors run first and write
    pushes, with their bound-literal definitions, that the global
    propagator's final pushes supersede. At `L = 1,000` with the `Equals`
    on `x_0`, the kept proof has 3,997
    `rup`s, 7,990 `pol`s and 9,998 `red` definitions, against 2,001, 3,000
    and 6,006 retired. Among the kept `rup`s are 999 units restating an
    upper bound that the retired proof never writes.
  - A ring of `L + 1` edges closed by one edge that its own domains already
    refute (`x_0 − x_1 ≤ −(2L + 1)` over `0..2L`): larger retired once the
    ring is long. With linear donors that holds from `L = 100` (1,050
    against 1,195). With comparison donors `L = 100` is still smaller
    retired (2,263 against 1,389). At `L = 1,000` both are larger retired:
    1,267 against 11,097 (linear) and 2,741 against 11,294 (comparison).
    Kept, that edge's donor refutes the model from its own row. Retired,
    the global propagator's `pol` cites all 1,001 rows.

  Every proof sampled from these verifies with VeriPB 3.0.2
  `--force-checked-deletion`; proofs were capped at 2 GB.
- **Gaps.** None.
- **Tightness.** Not applicable: there is no derivation. The tripwire's
  failure messages are the guard against a half-reified donor being retired,
  and against a fixture that retires nothing.

### Rewrite: root-condition-fixing

- **Pattern.** `simplifying_at_root` is on (the default), and the lifted graph
  has a conditional edge `u → v` of weight `d`, condition `b`. The stage's
  shortest-path pass finds `d + D(v, u) < 0` over the base graph:
  - the unconditional edges;
  - conditional edges whose condition was entailed when the initialiser ran;
  - edges this stage has already activated, round by round.

  This needs a half-reified donor, so from a front end it never fires.
- **Posts.** `¬b`, inferred at the root by the installed initialiser
  (`difference_graph.cc:361`). That is permanent, since it is a root fact. The
  same stage also drops redundant and dead edges from the propagator's
  internal graph, and lowers the from-scratch passes' round bound to the
  number of nodes that still have an edge. It reports the others as
  `isolated_nodes_removed`, but they are not removed: the propagator still
  seeds them (on the incremental route's first call, and on every call from
  scratch), scans them on every wake and is woken by their bounds (#1385).
  That is a decision about what to propagate, with no trace in the OPB or the
  proof, and it is `difference.md`'s.
- **Derived mode.** Yes: an inference, certified in the proof.
- **Why it is true.** If `b` held, the edge and the witness path would form a
  cycle of negative total weight. A system of difference constraints with a
  negative cycle has no integer solution.
- **Proof technique.** `difference.md`'s condition-fixing rule:
  - one `pol` summing the candidate's row and the path's rows, in deview
    mode, closed by `saturate`;
  - then `RUP` of `¬b`.

  From this entry point every summed row is a donor's `@c[<id>]`.
- **Neutral?** No: it is a bound push on `b`, and through `b` possibly on
  anything `b` is a literal of. That is what changes later presolvers'
  answers ([Relation to other families](#relation-to-other-families)).
- **Offline reconstructibility.** `difference.md`'s rule.
- **Proof size.** Three lines per fixed condition. The `pol` has
  `1 + path length` terms. On the rcpsp root-refutation instance above it
  was 12 fixings, and a thirteenth inference that refutes, in a 45-line
  proof.
- **Gaps.** None.
- **Tightness.** Not shown here. The design note records two mutations of the
  stage that still verify:
  - the `saturate` is not load-bearing;
  - at the root, the path conditions in the reason are not either.

  The presolver test's `reified_root_fix` and `reified_root_fix_views`
  fixtures exercise it through this entry point, and the latter only
  telescopes in deview mode.

## Detection and its failure modes

What the scan recognises was established directly, by the detection probe
(`tmp/fd-diff/difference_logic/detect/detect.cc`, 43 shapes, each under no
presolver, the hybrid and donors off, with proofs on and off).

**Lifted:**

- two-term `+1`/`−1` linears and `Problem::post(expr <= rhs)`;
- `LinearGreaterThanEqual`;
- the four comparison classes;
- every `If` form of either family;
- offset views on either operand;
- conditions over variables, views, negated views and constants, and on an
  edge's own node.

Every solution count matched brute force, and the 129 proofs verified. The
scan fails as follows, and only the first four are counted:

1. **Fully reified donors** (`Iff`, both families): `skipped_reified`. From a
   front end this is the important one.
   - From MiniZinc, every conditional difference arrives this way, as [Concrete
     constraints and frontend
     coverage](#concrete-constraints-and-frontend-coverage) explains. From XCSP3
     it arrives the same way, but over walked operands.
   - **The counter overstates the opportunity.** `skipped_reified` counts
     every reified linear inequality of any shape, because the reification
     test runs before the two-term and coefficient tests
     (`difference_logic.cc:252–270`). In the 2024 and 2025 MiniZinc
     Challenge survey it counted 550,365 across the 162 instances that
     printed counters. The half-reified count was 0 on every instance.
   - **How many are differences.** The prototype that lifts both halves ran
     over the same instances (the fact-check's run). In the 159 that printed
     counters both times, it reclassified the shipped build's 533,183:
     - about 129,300 Iff difference donors, lifted as 258,634 half-reified
       edges;
     - 351,430 not two terms;
     - about 51,350 comparisons against a constant;
     - 1,072 with other coefficients.

     So about a quarter are liftable. The differences are concentrated in
     `aircraft-disassembly` (137,096 half-reified edges over five instances),
     `cable-tree-wiring` (65,830), `ihtc-2024-kletzander`, `hoist-benchmark` and
     `EchoSched`. All 335,160 on `products-and-shelves` are not two terms. The
     prototype fixed 13,016 conditions at the root, and 45 instances gained
     half-reified edges. See #1373.
   - **An `Iff` whose condition is a constant literal is skipped as well**,
     though under a true constant it is a plain unconditional donor: the scan
     tests the condition's kind, not its value (`difference_logic.cc:252–264`,
     `:312–323`). Two `LessThanEqualIff` or two `LinearLessThanEqualIff`
     donors under `1 = 1` lift nothing and count `skipped_reified` 2, where
     two `LessThanEqual`s lift 2 edges
     (`tmp/fd-pre/parity_system_gathering/p10-boolxor/dl.cc`, re-run at
     `86caad24` on 2026-10-20). A constant-condition `If` is lifted (below).
     `parity_system_gathering` skips a constant-condition `Iff` the same way
     ([`parity_system_gathering.md`](parity_system_gathering.md), Detection,
     item 2).
2. **The negated forms** (`MustNotHold`, `NotIf`): `skipped_reified` (#598).
3. **Coefficients other than `±1`.** No `gcd` normalisation is done:
   - `2x − 2y ≤ 4` and `2x − y ≤ 3` give `skipped_coefficients`;
   - so do two spellings of `x − y` itself, `1·x + 1·(−y)` and
     `−1·(−x) − 1·y`;
   - so does XCSP3's `x + y ≤ 4`. MiniZinc's arrives as a comparison over a
     negated view, and counts as `skipped_negated_view` instead.
4. **More than two terms**, even when they cancel or are constant:
   - `x − y + 3 ≤ d`, with the constant as a third term;
   - `x − y + 0·z ≤ d`;
   - `x + x − x − y ≤ d`.

   Each gives `skipped_not_two_terms`. No `tidy_up_linear` merging is done
   before the shape test. MiniZinc's flattener cancels and folds these before
   the solver sees them, and XCSP3's peephole combines repeated variables.
   So MiniZinc delivers the folded form. So does XCSP3, unless the ordering
   holds a `mul`, where the peephole declines (item 6).
5. **Shapes that are never looked at, with no counter at all.** These are:
   - `LinearEquality` (`x − y = d`, two edges);
   - `Equals` with an offset;
   - `Plus` with a constant;
   - `Increasing` and `StrictlyIncreasing`, whose rows are difference
     rows ([`increasing.md`](../constraints/increasing.md));
   - `AllEqual`;
   - `NotEquals`;
   - `Disjunctive`;
   - a posted `DifferenceConstraints`;
   - any constraint a family installs as a child rather than posting.

   Nothing says these were seen. A model that writes its precedences as
   `increasing` gets nothing, and nothing tells it so.
6. **XCSP3 orderings the peephole declines.** These are walked with
   auxiliary variables, and the edge lands on an auxiliary.
   - Examples are `le(sub(x,x),1)` and `le(x,add(x,2))`, and any ordering
     with a `mul`, even `mul(1,x)` (`accumulate_affine` has no
     multiplication case).
   - The lift is sound, but it is over a node per invented variable. The
     differential harness counted 69 such comparison edges among 1,099
     XCSP3 edges, and the fact-check's 179 among 651.
   - Or the edge is lost: `le(add(sub(x,y),mul(0,z)),1)` ends as a comparison
     against a constant, `skipped_degenerate`.

`skipped_negated_view`, `skipped_degenerate` and `skipped_uncitable_row` are
refusals rather than misses. A negated view is not a difference constraint.
A degenerate edge is the donor's to handle. An uncitable row would make the
proof invalid ([Robustness and limits](#robustness-and-limits)).

**The counters account for every enumerated donor.** Each one is in
`edges_lifted` or in exactly one `skipped_*` bucket
(`difference_logic.cc:235–326`). A half-reified donor with a constant condition
is no exception: it is lifted, and counted in `edges_lifted` and
`half_reified_edges_lifted`. Nothing counts a donor family the scan does not
enumerate. The tests can and do catch a regression in the enumeration ([Evidence
that it fired](#evidence-that-it-fired)). A model built from an unrecognised
class cannot be caught: it gets `lifted nothing`, the same answer as a model
with no difference constraints.

## Evidence that it fired

The `DifferenceLogicStats` block is registered on every run, before anything
is decided (`difference_logic.cc:115`). Its twelve entries reach every
report:

| Report | Form | Example |
|---|---|---|
| C++ API | the entries themselves | `edges_lifted` |
| MiniZinc | `%%%mzn-stat:` lines, with `-s` | `differenceLogicEdgesLifted` |
| XCSP3 | `d` lines | `d DIFFERENCE LOGIC EDGES LIFTED` |

`DifferenceSimplificationStats` reaches the same reports as
`differenceLogicSimplify…` and `d DIFFERENCE LOGIC SIMPLIFY …`. The names are
pinned by `difference_logic_presolver_detection`, which checks them and
`sizeof` both structs. They are also pinned by `minizinc/CMakeLists.txt` and
`xcsp/CMakeLists.txt`. The summary line tells the cases apart:

- `lifted nothing`;
- `N edges lifted over M nodes, C from comparisons and H half-reified`;
- the same, ending `, but no propagator was installed` (one edge), or
  `, retiring D donor propagators`.

The counters that tell "ran and found nothing" from "ran and did nothing" are
`edges_lifted` and `propagator_installed`. `comparison_edges_lifted` and
`half_reified_edges_lifted` say which path was taken, and the simplification
block's `conditions_fixed` says whether the root rewrite fired. The proof has
no marker at all. The only proof-side sign is a `pol` that cites donor labels
across several constraints.

Expected values on named instances at `86caad24`. All of these were
re-measured, and every proof verifies:

| Instance | Command | Expected counters |
|---|---|---|
| `difference_chain`, refute | `--mode refute --variant presolved` (`n = 20`, `k = 2`) | 251 edges over 42 nodes (`n(n+5)/2 + 1` and `2n + 2`); 0 from comparisons; the simplification stops on a negative cycle in the base graph |
| `difference_chain`, comparison donors | the same with `--donor comparison` | 251 comparison edges |
| `difference_chain`, fixpoint | `--mode fixpoint` | 250 edges |
| `examples/rcpsp` | `--size 12 --seed 3 --max-lag-density 0.3 --variant presolved` | 27 edges over 13 nodes; 7 redundant edges dropped; optimum 14 |
| `examples/rcpsp`, machine as conditional edges | `--size 10 --seed 5 --machine-fraction 0.7 --machine difference --variant presolved` | 89 edges over 11 nodes, 72 half-reified; 14 redundant edges dropped; 9 conditions fixed over 2 rounds; optimum 20 in 3,000 recursions, against 3,172 with `--simplify off` and decomposed |
| `minizinc/tests/differencelogic.mzn` | the `minizinc-differencelogic` lane | `differenceLogicEdgesLifted=4`, `ComparisonEdgesLifted=4`, `Nodes=4`, `SkippedNotTwoTerms=1`, `SkippedCoefficients=1`, `PropagatorInstalled=1`, `SimplifyRan=1` |
| `xcsp/tests/difference_logic.xml` | the `xcsp_difference_logic` lane | 4 edges, 0 from comparisons, 4 nodes, 1 not two terms, 0 uncitable rows, propagator installed, simplification ran |
| `minizinc/tests/twotermlinle.mzn` | the `minizinc-two-term-lin-le-difference-logic` lane, under `GCS_PROPAGATOR_STATS=calls` | `differenceLogicEdgesLifted=6`, `ComparisonEdgesLifted=6`, and `propagatorCallsLessEqualConstraints=8` |

**On real models.** The 2024 and 2025 MiniZinc Challenge instances were run
with `fzn-glasgow --difference-logic -s` and a 20 s limit that includes
flattening (`tmp/fd-diff/difference_logic/survey/`):

- 162 of 200 printed counters. Of the other 38:
  - five failed to parse their data;
  - five raised `IntegerOverflow` with or without the presolver
    (`work-task-variation`, not this presolver's; #244 cites them);
  - one was found unsatisfiable by the flattener, so the solver never ran;
  - the other 27 did not finish inside the limit. Most were still
    flattening. The rest ran `fzn-glasgow` past the limit, without the
    presolver too:
    - `ihtc-2024-marte` i01 and i03 overran `-t 20000` in all three
      configurations of the re-run below, at 37 s and 87 s;
    - i06, i11 and i14 ran for over seven minutes with no presolver and were
      stopped, so they never reached a run with it.

    Where that time went was not located.
- 54 of the 162 installed a propagator, in 11 problems:
  - `accap`, `aircraft-disassembly`, `cable-tree-wiring`, `harmony` and
    `hoist-benchmark`;
  - `yumi-dynamic`, `EchoSched`, `black-hole` and `carpet-cutting`;
  - `fbd1` and `groupsplitter`.

  A re-run of the 27 that ran out of time, compiling separately with a 600 s
  compile limit, added four more, one `yumi-dynamic` and three `gt-sort`, with 7
  to 15 edges. That makes 12 problems.
- Every one of the 17,449 lifted edges came through the comparison family.
- None was half-reified, and no condition was fixed.

## Can it weaken the model?

**Lose solutions: no.** Nothing reaches the OPB, which the `opb` lane checks
byte for byte. Every lifted edge states exactly its donor's row. The
installed machinery derives only cutting-planes consequences of those rows,
and VeriPB checks each one. The solution sets were checked against an
independent oracle in four ways:

- **The test's equivalence and proof lanes.** 18 fixtures in five spellings,
  three configurations each, 270 VeriPB runs.
- **The fuzz** (`fuzz/fuzz.cc`, 8,300 random systems, 33,200 runs). The
  systems have holes, views, constants, six spellings and conditions. It ran
  under no presolver, the hybrid, donors off and no simplification. There
  were no mismatches, and the 400 proofs verify.
- **The detection probe's 43 shapes.**
- **The differential harness.** It ran:
  - 554 MiniZinc instances on 2.9.7 and on 2.10.1, against Gecode;
  - 497 XCSP3 instances, against ACE;
  - every instance against brute force;
  - with and without `--difference-logic`, and with simplification off, with
    and without proofs.

  It saw no wrong set, status or completeness, and no error or timeout. All
  2,697 proofs verify. Where a reference could not run, which was Gecode's
  int32 literal limit on 48 instances and ACE errors on 40, CP-SAT and brute
  force settled it.

The harness's soundness result covers only the unconditional path, because no
front end reaches the conditional one. The fuzz and the C++ tests cover the
conditional path.

**Lose propagation strength: no.** It only adds a propagator. Retiring donors
is restricted to the unconditional ones, whose pushes the global propagator
subsumes. The tripwire and the fuzz check that node for node, and the
argument is under
[retire-unconditional-donors](#rewrite-retire-unconditional-donors). There
is no proof-only budget and no decline that depends on proofs. The one
proofs-on difference, `skipped_uncitable_row`, needs a donor whose row was not
emitted, and none exists among the classes it reads.

**It is not search-neutral under the default heuristic.** The installed
propagator raises the degree of every node and condition variable, and
`dom_then_deg` breaks ties by degree. The probe `degree/deg.cc` has two slack
difference edges that never propagate, plus two three-term linears. It
explores 636 nodes without the presolver and 666 with it, finding the same
456 solutions. The differential harness saw one such case among its XCSP3
instances, 624 nodes against 625. The tripwire is unaffected, since both of
its arms carry the propagator. But a recursion count compared across
presolver on and off, under the default heuristic, measures this as well as
the propagation. Their tables compare cleanly for different reasons:
- `examples/rcpsp` branches in order by default (`--branch in-order`);
- `difference_chain` uses the default `dom_then_deg`
  (`difference_chain.cc:438–449`, `solve.cc:423`), but every variable there is
  a node, so every degree goes up by the same one.

**The wrong line, soundly derived.** There is no `ia` pin, because the
presolver derives no line. What ties each cited row to the intended
inequality is two checks:

- **The label lookup.** It goes through the donor's published role, which
  `constraint_row_test` checks against the `.opb` for every reification kind
  of both families.
- **The closing step.** Each installed derivation ends in a `RUP` of the
  inferred literal, or of the contradiction.

If an edge were lifted with the wrong weight or direction, its row would not
cancel in the telescoping sum, and the closing `RUP` would fail. The design
note's mutation table shows the inverted-edge and dropped-strictness
mutations caught by VeriPB. A lift that is too *weak* is invisible to every
proof: dropping a condition's strength, or lifting nothing. Only the counts,
the equivalence lanes and the tripwire catch those.

## Evidence

### Tests

- **`difference_logic_presolver_{detection,equivalence,tripwire,opb,proofs}`**,
  in `gcs/presolvers/difference_logic/difference_logic_test.cc`, run through
  `run_test_only.bash`. All five pass at `86caad24`, on one pinned core with
  `--seed=1`. `detection` takes under 0.1 s and `proofs` 7.1 to 7.3 s. The four
  modes other than `proofs` print identical output under `--seed=2`; the
  fixtures are fixed.
  - **`detection`** covers the report names and both structs' sizes, plus
    seven exact-count fixtures:
    - `five_plain_linears`;
    - `every_skip`: 1 not two terms, 2 coefficients, 2 reified, 1 negated
      view and 3 degenerate, with no uncitable row;
    - `comparison_donors`, which includes a directly constructed
      `MustNotHold`;
    - `mixed_donors`;
    - `reified_donors`;
    - `single_edge`, which installs nothing;
    - `nothing_to_lift`, an `AllDifferent`.

    It also runs the paper's Example 1 differential in five spellings: 252
    propagations without the presolver (314 for the mixed spelling), 3 with
    it, and 1 with donors off.
  - **`equivalence`** and **`proofs`** run 18 fixtures in five spellings
    (`Linear`, `Le`, `Lt`, `Ge`, `Mixed`) under three configurations,
    against a brute-force oracle. The fixtures include:
    - chains, trees, negative domains, negative and zero-weight cycles;
    - views, a view-shared node and a wide-domain view cycle;
    - aliasing, constants and a negated view;
    - six half-reified fixtures, two of them root fixings.

    `proofs` runs VeriPB on all 270 proofs: 225 complete enumerations and 45
    unsatisfiable.
  - **`tripwire`** compares hybrid against donors-off over the same corpus.
  - **`opb`** checks:
    - the comparison label counts;
    - `.opb` byte-identity on linear and comparison fixtures;
    - a negative control with both files identical;
    - the simplification fixture, which must fix a condition and drop an
      edge.

  The enumerations use `solve_for_tests`, not
  `solve_for_tests_checking_gac`. None of these lanes sets a cap of its own.
  Under the default caps (300 solutions, 1,500 recursions) none fires: the
  largest fixture has 236 solutions. `tripwire` and `opb` call `solve_with`
  directly, uncapped. The results above came from running the binary directly
  in each mode, with no cap set.
- **`constraint_enumeration_test`** pins the `dynamic_cast` contract the scan
  rests on. **`constraint_row_test`** pins every published role against the
  `.opb`. Both pass.
- **Front-end lanes:**
  - `minizinc-differencelogic` (verified, with counters);
  - `minizinc-two-term-lin-le-difference-logic`, six edges, all via
    comparisons, 2,430 solutions verified;
  - `xcsp_difference_logic` (verified, with counters).

  All pass when run from a scratch directory.
- **Examples:**
  - `difference_chain-presolved-{fixpoint,refute}`;
  - `difference_chain-presolved-comparison-{fixpoint,refute}`;
  - `rcpsp_presolved`;
  - `rcpsp_machine_difference_presolved`, and its `_nosimplify` twin.

  Every proof verifies when re-run here.

**Not covered:**

- **A real lifted graph in a unit test.** The largest test graph is
  `difference_chain`'s 42 nodes; the C++ fixtures have at most five.
  Nothing exercises #1309's install cost or the root pass at scale.
- **Any front-end route to a conditional edge**, which does not exist.
- **The `±(2⁶⁰ − 1)` chain** of [Robustness](#robustness-and-limits). The
  presolver tests' weights are small; `difference.md`'s `run_overflow_test`
  covers the posted constraint only.
- **A mutation lane.** There is none, though the scheduling presolvers have
  one. Every mutation result in the design note was a one-off at
  bring-up, and the tightness claims rest on them.
- **Assertion levels.** No test runs the presolver above
  `AssertionLevel::Off`.
- **Two presolvers in one model, through this one.** That is tested only by
  the probes cited above.
- **`incrementally(false)` and `auditing_incremental_propagation`** through
  the presolver. The incremental audit runs in `difference.md`'s tests.

### Benchmarks and examples

These are the in-repo drivers:

- `examples/difference_chain` (`--variant presolved`, `--donor
  linear|comparison`, `--disable-donors`, `--simplify on|off`): the paper's
  Example 8, the pathology the presolver exists for.
- `examples/rcpsp --variant presolved`, with `--machine difference` for
  conditional edges.

For **CPU**, use `difference_chain --mode fixpoint` at `n = 160` to `640`, both
orders, which is dense. Use the scan probe at thousands of nodes for the pass
and the root initialiser. For a real model, use `aircraft-disassembly` or
`EchoSched` from the 2024 and 2025 challenge with `--difference-logic`.

For **proof verification**, use `difference_chain --mode refute`. A 44-line
proof against 17,430 lines decomposed at `n = 20` is the headline. For
conditional edges, use `rcpsp --machine difference --variant presolved`, where
seed 5 at size 10 is an 11 MB proof that verifies.

Do not run the scan probe with simplification on beyond about 10,000
connected nodes. Each round is a Dijkstra per source, and it does not stop on
a timeout.

### CPU performance

`difference_chain -k 2`, measured at `86caad24`: Release, fataepyc-09, one
pinned core, `GLIBC_TUNABLES` as above, 2026-10-20. Wall time is the
program's own `wall_time_s`, and the instructions are `instructions:u` for
the whole process; each is the median of three. These figures replace the
design note's, which were taken on another machine at an earlier commit and
should not be mixed with them.

| mode, n, order | variant | recursions | propagations | wall (s) | instructions (G) |
|---|---|--:|--:|--:|--:|
| fixpoint 160 unlucky | decomposed | 163 | 2,126,002 | 0.162 | 1.26 |
| | presolved | 163 | 52,807 | 0.0519 | 0.360 |
| | presolved, donors off | 163 | 167 | 0.0501 | 0.340 |
| | presolved, simplification off | 163 | 52,807 | 0.0379 | 0.228 |
| | global | 323 | 327 | 0.0241 | 0.192 |
| fixpoint 160 lucky | decomposed | 163 | 52,801 | 0.0332 | 0.205 |
| | presolved | 163 | 52,807 | 0.0518 | 0.360 |
| fixpoint 640 unlucky | decomposed | 643 | 132,305,602 | 9.75 | 69.3 |
| | presolved | 643 | 825,607 | 1.46 | 11.1 |
| | presolved, donors off | 643 | 647 | 1.41 | 10.8 |
| | presolved, simplification off | 643 | 825,607 | 0.681 | 3.48 |
| | global | 1,283 | 1,287 | 0.931 | 8.38 |
| fixpoint 640 lucky | decomposed | 643 | 825,601 | 0.608 | 3.13 |
| | presolved | 643 | 825,607 | 1.45 | 11.1 |
| | presolved, simplification off | 643 | 825,607 | 0.683 | 3.48 |
| refute 160 unlucky | decomposed | 1 | 4,139,782 | 0.304 | 2.33 |
| | presolved | 1 | 13,203 | 0.0522 | 0.426 |
| | global | 1 | 1 | 0.0197 | 0.196 |
| refute 640 unlucky | decomposed | 1 | 262,458,715 | 19.4 | 138.0 |
| | presolved | 1 | 206,403 | 1.85 | 17.5 |
| | presolved, donors off | 1 | 2 | 1.89 | 17.5 |
| | global | 1 | 1 | 1.04 | 10.8 |

`recursions` is identical across the decomposed and presolved rows of each
group, so those compare propagation and nothing else. The global variant
posts a different model and searches differently. What the table says:

- **The presolver removes the unlucky-order pathology.** At `n = 640` the
  fixpoint drops from 9.75 s to 1.46 s and the refutation from 19.4 s to
  1.85 s.
- **The default root simplification is most of what remains.** At `n = 640`
  it costs 0.78 s of the 1.46 s fixpoint, and 7.6 G of the 11.1 G
  instructions. On this dense graph it drops about `n − 1` of `n(n+5)/2`
  edges.
- **On the lucky order the default is 2.4 times slower than not adding the
  presolver** (1.45 s against 0.61 s), and is roughly break-even with
  simplification off (0.68 s).
- **Retiring the donors saves at most 3.5% of the wall time**, however many
  propagations it removes: 825,607 against 647 in the `n = 640` fixpoint,
  1.46 s against 1.41 s. On the `n = 640` refutation it saves nothing
  (1.85 s against 1.89 s).

On 20 challenge instances (`aircraft-disassembly`, `cable-tree-wiring`,
`EchoSched`, `carpet-cutting`), a 60 s comparison with and without
`--difference-logic` was run as 20 concurrent runs on 20 cores, so only node
counts and answers are read. The solution counts printed and the best
objectives that were compared (`cable-tree-wiring`, `carpet-cutting`) were the
same. Fewer nodes were explored in the 60 s on `aircraft-disassembly`, for
example 2.28 M against 1.43 M on `B737NG-600-01`. Concurrent runs show only
node throughput, so that instance was rerun under control. The runs follow
each model's search annotation (no `-f`), and every one of the 20 has one:
`input_order` for `aircraft-disassembly` and `carpet-cutting`, `first_fail`
for the other two, which `fzn-glasgow` maps to plain smallest domain. The
degree tie-break of [Can it weaken the model?](#can-it-weaken-the-model)
enters only through the default `dom_then_deg` fallback for variables an
annotation leaves unfixed. On `B737NG-600-01` the tree is the same both ways:
run to its 18 solutions (`-n 18`), both explore 894,522 nodes with 890,135
failures and print identical solutions. Serial, pinned to one core, three runs
each, the solve takes 22.53 s and 168.77 G `instructions:u` without the
presolver against 36.37 s and 280.23 G with it (medians; `86caad24`,
fataepyc-08, 2026-10-21). So each node of the same tree costs 1.6 times the
wall time and 1.66 times the instructions there. Where that cost goes was not
measured. Elsewhere the node counts moved both ways. They were higher with the
presolver on `cable-tree-wiring` A046 (47,206 against 32,017) and on
`EchoSched` 12-12 and 15-15 (38% and 26%), and within about 4% on the rest.
Those are 60 s runs under load, whose trees were not compared, so they are not
cost measurements.

No identical-tree comparison against another solver was made (#868). This
audit ran no other solver with difference logic. It knows of detection of
difference constraints in a flattened model only from the source paper's
description of Huub.

What these benchmarks do not exercise: conditional edges, except the rcpsp
rows above; and large graphs outside `difference_chain`'s dense family.

### Proof performance

The presolver's own contribution to a proof is zero lines. What it changes is
which machinery logs the inferences, so the two figures that matter are the
whole proof with and without it, and how much of it the donors still log.
Measured at `86caad24` on fataepyc-09, each proof verified with VeriPB 3.0.2
`--force-checked-deletion`:

| instance | variant | `.pbp` lines | bytes | VeriPB |
|---|---|--:|--:|---|
| `difference_chain` refute, `n = 20` | decomposed | 17,430 | 672,487 | `VERIFIED UNSATISFIABLE` |
| | presolved | 44 | 1,923 | verified |
| | presolved, comparison donors | 202 | 8,946 | verified |
| | presolved, donors off | 18 | 762 | verified |
| `difference_chain` fixpoint, `n = 20` | decomposed | 6,079 | 284,393 | `VERIFIED SATISFIABLE` |
| | presolved | 778 | 40,671 | verified |
| | presolved, comparison donors | 1,384 | 82,898 | verified |
| | presolved, donors off | 778 | 40,671 | verified |
| `rcpsp --size 12 --seed 3 --max-lag-density 0.3` | decomposed | 5,132 | 431,514 | `VERIFIED BOUNDS 14 <= obj <= 14` |
| | presolved | 5,041 | 375,208 | verified |
| `rcpsp --size 10 --seed 5 --machine-fraction 0.7 --machine difference` | decomposed | 173,976 | 13,672,635 | `VERIFIED BOUNDS 20 <= obj <= 20` |
| | presolved, simplification off | 164,586 | 11,875,828 | verified |
| | presolved | 159,969 | 11,147,766 | verified |

Own against shared:

- **The refutation.** On the `n = 20` refutation, the global propagator's
  share is one `pol` citing 23 donor rows, plus one `rup`. The rest of the
  44 lines is the donors' own pushes before the global propagator ran, and
  the framework's order-literal definitions.
- **Comparison donors cost more, mostly through views.** The comparison
  spelling's proof is 202 lines against 44 for the refutation. With the
  donors retired it is still 146 lines (5,441 bytes), against 18 for linear
  donors. In the fixpoint mode it is 1,386 lines against 1,384 in the hybrid.
  The cause is the view scaffolding: 62 of the 63 `pol`s in the donors-off
  refutation involve `@c[view_of_…][viewge|viewle]` deview lines, because the
  comparison spelling's rows are over offset views. Retiring the donors
  removes 56 of the 202 lines on the refutation, and adds two on the
  fixpoint.
- **The assertion levels.** On those shapes, at `Inferences`, the
  refutation is 13 lines with 6 `a` lines. None of them carries a constraint
  hint: the only annotation is the framework's `::backtrack:`. The fixpoint
  is 69 lines, 63 of them `a`.

## Status, gaps, and next steps

### Proof-logging gaps

None in the presolver.

- **At `Off`.** Every inference the installed machinery makes is checked,
  and none is an assertion.
- **Proofs on and off.** Strength does not change between them. The
  uncitable-row decline exists, but no class it reads can trigger it.
- **Above `Off`.** The installed machinery's assertions carry no hint, which
  is `difference.md`'s work item. The presolver adds the fact that a
  reconstructor must search every two-term row of the model, with nothing
  naming which were lifted.

### Known limitations

These are phrased as a user meets them:

- **"I turned on `--difference-logic` and my disjunctions were not lifted."**
  Every conditional difference reaches gcs fully reified, and the presolver
  skips fully reified donors. `skipped_reified` counts them (#1373).
- **"My precedences are an `increasing`, or a `LinearEquality`, and nothing
  was lifted."** The scan reads only two-term inequalities and comparisons,
  and reports nothing about what it does not read.
- **"`--difference-logic` made my solve slower."** On a model where the
  donors already propagate in a good order, the presolver adds the global
  propagator and a root pass. `--difference-logic-simplify off` removes the
  root pass, which was most of the cost on `difference_chain`.
- **"It sat at the root for seconds and ignored my time limit."** On a
  connected lifted graph, each round of the root simplification is one
  Dijkstra per source node. Initialisers do not observe `--timeout` (#816).
- **"It printed `=====ERROR=====` on a model that is plainly unsatisfiable."**
  Weights near `2⁶⁰` along a chain of about eight edges overflow the installed
  machinery's shortest-path arithmetic (#1371). In the shapes measured here,
  `--difference-logic-simplify off` avoids it while the donors are kept. It does
  not avoid the drift of conditional edges, which only C++ reaches today.
- **"It threw `UnexpectedException` when I added an `AutoTable` as well."**
  Only C++ can add both. Added before the `AutoTable`, in the default
  incremental mode, with two or more edges lifted, the solve throws before
  search (#1378). Add it after the `AutoTable`, or use `incrementally(false)`.
- **"The search tree changed though nothing was lifted that could
  propagate."** The installed propagator raises the degree of its
  variables, and that changes `dom_then_deg`'s tie-breaks.
- **"I can't turn it on from Python or a `.scp`."** Neither has a switch:
  `gcspy` is #983's, and `glasgow_scp_solver`'s is #1374.

### Next steps

1. **Lift `Iff` donors as two half-reified edges** (#1373). Small in the
   presolver (the prototype changes about 25 lines), with an API change to
   publish the `r` and `f` roles. Get the strictness flip right; #598 could be
   closed in the same change.

   It depends on #1371. The prototype opens MiniZinc routes to that issue's
   drift and shape B.

   It is the only way a MiniZinc model reaches the conditional path; XCSP3
   would also need a reified-ordering peephole. Of the challenge survey's
   skipped reified donors, about a quarter would lift. On the prototype the
   gain was mixed:
   - `cable-tree-wiring` A046 gave its first solution in 60 s, where neither
     shipped configuration found any;
   - elsewhere the nodes explored in 60 s fell by up to three quarters
     (`cable-tree-wiring` A033: 171,205 to 45,654);
   - the root refutation on `aircraft-disassembly` 09 went from 1.1 s to
     3.3 s.

   Measure serially before landing it.
2. **The overflows** (#1371, #1372). These are `difference.md`'s to fix, in the
   machinery. Which sites each shape meets, and what each fix covers, are those
   issues'. Once they are fixed, the presolver configurations x shapes table
   under [Robustness and limits](#robustness-and-limits) is the presolver's
   test: every cell should solve. An earlier version of this document suggested
   seeding the potentials with the variables' bounds. It was never tried, and it
   is withdrawn.
3. **#1309** (open): deduplicate the install's two scope loops (the scope and
   the constraint scope) with sets. Small. At 100,000 nodes that function is
   nearly all of the 3.1 s pass. Do `install_difference_propagator`'s
   `condition_vars` `find` at the same time, before #1373 makes it matter.
4. **Reconsider the default of `simplifying_at_root` for this entry point,
   or make the root pass cheaper.** Do not add a budget. On real models the
   pass is a millisecond. On a dense connected graph it is the largest cost
   there is.
   - The pass already starts a Dijkstra only from tails of edges and heads
     of candidates, and prunes by a distance threshold.
   - Its worst case is still one `O((n + m) log(n + m))` Dijkstra per
     source, per round (`log n` while parallel edges are bounded by a
     polynomial in `n`).
   - Making that cheaper is `difference.md`'s to do.
   - Until then, #816 applies.
5. **Report what the scan does not read.** Medium. Count the posted
   `LinearEquality` (two-term, unit), `Increasing` and `Equals`-with-offset
   constraints the scan could have used, the way `skipped_*` counts the near
   misses it does see. That would give "nothing was lifted" a reason.
6. **Normalise before testing the shape.** Small. Merge repeated variables,
   drop zero coefficients, fold constant terms into `value` and divide by a
   common coefficient. That catches the C++ API's unfolded spellings.
   MiniZinc already folds. XCSP3 folds except under a `mul`, which is the
   peephole's gap rather than the scan's.
7. **A lifted graph of hundreds of nodes in a test.** Small. It would put the
   install and the root pass under a lane.
8. **A mutation hook for the presolver**, as the scheduling presolvers have
   (`presolvers/innards/*_mutations.hh`). This only matters if the detection
   changes, as items 1 and 6 would change it. The design note's mutation
   table was the bring-up's and is not re-runnable.
9. **Reconsider whether a presolver-installed propagator should count towards
   degree.** This is a design question for the engine, not for this
   presolver. It affects every presolver that installs a propagator.

## Prior art

**The propagation algorithm.** The algorithm is not this presolver's, and its
lineage is `difference.md`'s to record. In brief:

- Shostak (JACM 1981) and Dechter, Meiri and Pearl ("Temporal constraint
  networks", Artificial Intelligence 49, 1991) for the graph view;
- Cotton and Maler (SAT 2006) for incremental negative-cycle detection in
  DPLL(T);
- Feydy, Schutt and Stuckey ("Global difference constraint propagation for
  finite domain solvers", PPDP 2008) for the CP propagator;
- the arXiv preprint extending that paper, Kletzander, Dekker, Schutt and
  Stuckey ("Global Difference Constraint Propagation for Constraint
  Programming", arXiv:2607.20022, July 2026), which names no journal. It
  implements the algorithm in Huub.

The first four were checked against the arXiv paper's own reference list,
and the paper itself against its arXiv front page.

**The detection.** Huub "captures" difference constraints "when the model is
built" (the paper, section 5.1), at a chosen level:

- level 1 is difference constraints and their half- and fully reified forms,
  a full reification becoming two half-reified edges;
- level 2 adds half-reified equalities;
- level 3 adds disequalities and reified equalities.

Its configuration study found level 1 best (section 6.3). The paper's
section 4.4 describes the hybrid, the global propagator alongside the
per-constraint ones, and suggests prioritising it before them. So the idea of
reading a flattened model for difference constraints and running both is the
paper's.

The configuration study chose otherwise. Its final configuration (the closing
paragraph of section 6.3.2) has five parts, and gcs compares with each as
follows:

- **Level 1.** This presolver lifts level 1 without the fully reified donors
  (#1373).
- **Lowest priority for bound propagation.** gcs has no runtime priorities
  (#582), but it registers the global propagator last, which is roughly that at
  the root's first pass. After it, only woken propagators run.
- **Highest priority for Boolean propagation.** In the paper's terms (section
  5.4) this means acting on a fixed Boolean: dropping its edge when it is false,
  moving it into the active edges and running `IncSat` when it is true. gcs does
  both, in the same propagator call that handles bounds. Its `on_change` wake on
  condition variables re-snapshots the active arcs. What it cannot do is give
  that step its own, higher, priority.
- **No `IncImp`.** gcs matches. The root simplification does an `IncImp`-like
  check once, at the root.
- **Lifted explanations.** These are `difference.md`'s to compare.

Section 5.4 also has a bound-side step that gcs's global propagator lacks. After
`IncLB`/`IncUB`, it checks the implied edges at nodes whose bounds moved. An
edge the bounds imply is dropped; an edge they falsify propagates `b ↦ ⊥`. In
the hybrid, the kept half-reified donors supply that inference from their own
bounds, which is why they are never retired.

This audit did not survey other solvers' detection; it knows only Huub's, from
the paper.

**What is new here** is the certification. The pass runs after the proof model
is final, so it can add nothing to it. Instead it lifts exactly the rows the
donors already emitted, and resolves each one through the donor's published
role. The installed propagator then cites those rows, in deview mode, so
every inference from the hybrid is a cutting-planes derivation from rows the
model already contains, with no new OPB content. This audit knows of no
earlier proof-logged difference-logic presolver.

McIlree's thesis does not treat difference constraints by name. Its
section 8.2.2 does propose justifying any inference implied by a totally
unimodular linear representation of a constraint (a "TULIP") by a single
linear combination. A system of difference constraints is a network matrix,
which is totally unimodular, so the installed propagator's telescoping
`pol`s are an instance of that idea. The novelty claimed here is only the
presolver's: citing the donors' own rows after the model is closed. The
certified propagator itself is `difference.md`'s to place in the
literature.

## Further reading

- [`difference-logic.md`](../difference-logic.md): the design note, which
  stays as the long note for this presolver and for `difference`.
  - **What it covers here.** Its section "The presolver" is this presolver's
    design history:
    - what is lifted and why the negated and `Iff` forms are not;
    - labelling `Comparison`'s rows, and the cake check behind it;
    - citing published roles rather than constructed labels;
    - deview mode;
    - why `DisableUntilBacktrack` could not be reused for retiring donors;
    - why the tests assert on counts, with its mutation table;
    - gating, and the original measurements.
  - **Its other sections.** RCPSP/max, root simplification, "Frontends" and
    "Deliberately deferred" cover the paper's results, the stage, and the
    front-end story.
  - **Stale at `86caad24`, out of this stack:**
    - The section "Why the tests assert on counts" says, in its last
      paragraph, that "the cross-check is on unconditionally". Its own
      earlier paragraph, and `941a7837`, say the runtime self-audit was
      removed. Corrected by #1396, open.
    - "Frontends" says MiniZinc's `int_lin_le` is "exactly the two-term
      `LinearLessThanEqual` the presolver lifts". The FlatZinc reader now
      recovers it as `LessThanEqual`, and `minizinc-differencelogic` pins
      `differenceLogicComparisonEdgesLifted=4`. Corrected by #1396, open.
    - "Deliberately deferred" refers to "the RCPSP/max measurement below",
      which is above it (corrected by #1389, open).
    - "Deliberately deferred" also calls `Iff` lifting "a real obstacle, not a
      choice", and "What is lifted" says it "cannot be lifted as things stand".
      The obstacle is the one-role-per-donor API (#1373). Both corrected by
      #1396, open.
    - "Deliberately deferred" says a linear `NotIf`'s "`ltn` row" does not say
      what a citer wants. Since #908 (`f85e63bf`) that row is under the empty
      role and states the integer negation. Corrected by #1396, open.
    - ":870" says "the hybrid is what the paper measures as best", and so
      does `difference_logic.hh`. That comparison is not in the paper (see
      [Options](#options)). Both corrected by #1396, open.
    - Its measurement tables predate incremental propagation and this audit
      (see [CPU performance](#cpu-performance)).
- **Stale text in code and other notes at `86caad24`, out of this stack:**
  - **The `ltn` role.** `difference_logic.cc:248` and `linear_inequality.hh:151`
    still put a linear `NotIf`'s row under `ltn`; it has been under the empty
    role since #908 (`f85e63bf`). Corrected by #1396, open.
  - **`difference_logic.hh`.**
    - `:62–64` says half-reified edges are "where the paper's scheduling wins
      come from". The paper does not say that. Its RCPSPmax gain comes from
      unconditional precedences and simplification. Corrected by #1396,
      open.
    - `:230` cites "section 6.3" for simplification being most of the win;
      the figures are section 6.4's, and do not hold for RCPSPmax. Corrected by
      #1396, open.
    - `:216–220`, and `difference_logic.cc:226–228`, say the global
      propagator infers nothing about a condition "at all", the `.hh` calling
      that the paper's `IncImp`. Root simplification fixes some conditions,
      and inferring one from bounds is section 5.4's check (corrected by
      #1389, open; the same words in the failure message at
      `difference_logic_test.cc:391` are corrected by #1396, open).
  - **The difference sources.**
    - `difference_graph.hh:146–148` cites "section 6.3" for 320.95 against
      312.94; that is Table 1 in section 6.4. Corrected by #1396, open.
    - `difference_graph.cc:249–253` says "let the from-scratch pass below
      refute it"; the stage now runs in an initialiser. Corrected by #1396,
      open.
  - **The presolver's test.** `difference_logic_test.cc:16–17` names a
    "`differential` mode"; the differential runs inside `detection`. Corrected
    by #1396, open.
  - **The int_lin_le shape.** The FlatZinc reader recovers it as
    `LessThanEqual` (`8c6cb43d`), but these still say it arrives as a
    two-term `LinearLessThanEqual` (all four corrected by #1396, open):
    - `minizinc/fzn_glasgow.cc:375–380`, the option comment;
    - `minizinc/CMakeLists.txt:277–281` ("The zero says all four arrived as
      `int_lin_le`", above a pin of `ComparisonEdgesLifted=4`);
    - the header of `minizinc/tests/differencelogic.mzn`;
    - [`minizinc.md`](../minizinc.md):232–238;
    - [`frontend-support-matrix.md`](../frontend-support-matrix.md)'s
      `[^cmp]`.
  - **In this stack, wrong rather than stale, and now corrected.**
    [`comparison.md`](../constraints/comparison.md)'s lead, its `[^lin]`
    footnote and its "Not to do" item, and its `README.md` bullet, all said the
    family was nearly unreachable from MiniZinc. `8c6cb43d` predates every one
    of that document's audit commits. They were corrected alongside this
    document.
- [`difference.md`](../constraints/difference.md): the installed propagator and
  initialiser, their rules, proofs, state and hole sensitivity.
- [`comparison.md`](../constraints/comparison.md) and
  [`linear.md`](../constraints/linear.md): the two donor families, and the
  published rows this presolver cites.
- [`inferred_disjunctive.md`](inferred_disjunctive.md),
  [`inferred_cumulative.md`](inferred_cumulative.md) and
  [`cumulative_strengthening.md`](cumulative_strengthening.md): the
  presolvers whose answers this one's root fixings can change.
- [`optional-interior-pruning.md`](../optional-interior-pruning.md): why the
  installed propagator's `on_change` on condition variables counts, and its
  `on_bounds` on nodes does not.
