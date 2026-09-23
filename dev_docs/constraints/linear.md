# Linear: `Σ cᵢ·xᵢ` against a constant

> **Maturity** production ·
> **Audited** 2026-09-23 at `00797a97` ·
> **Open issues** filed by this audit: #1032 (XCSP3 `<sum>` with `ne` gives
> wrong answers, and its wrong `UNSATISFIABLE` verifies), #1033 (the `If`
> forms with a constant condition enforce the wrong constraint), #1034 (the
> incremental propagator's state is a heap allocation per slot per node),
> #1035 (reasons and justifications name every term's bound, even untouched
> ones), #1036 (`gcspy`'s `post_linear_greater_equal_iff` posts `≤`). Already
> open and touching this family: #868 (cross-solver). More to record under
> [Next steps](#next-steps). Tracked under #871.

The linear family is `LinearEquality`, `LinearNotEquals`,
`LinearLessThanEqual`, `LinearGreaterThanEqual` and their `If`/`Iff` reified
forms. That is twelve named classes over two base classes,
`ReifiedLinearEquality` and `ReifiedLinearInequality`, which are public too
and which the `.scp` reader posts directly, and one bound-sweep algorithm.
**It reaches more models than any other family.** In one instance of each of
298 MiniZinc Challenge models (285 of which produced statistics in 10 s) it
appears in 250 (the next, `equals`, in 206),
and it takes a median 8.4% of their propagation time and at least half in 44
of them. Its shared helper, `propagate_linear`, also runs the arithmetic
family's linear stages.

Three things to know before touching it.

- **Its whole vocabulary is bounds.** Every inference but two reads and writes
  bounds, the propagators wake on bounds, and the proof is order literals
  over a bit-sum encoding. So its costs are all proportional to the **number
  of terms**, never to domain width. That includes the proof: every bound push
  names every term, which is how a 0.92 s `shortest_path` search writes a
  15 GB proof (#1035).
- **The three wrong-answer bugs found here are all at the edges**, not in the
  propagator: an XCSP3 translation that predates `LinearNotEquals` (#1032), a
  constant-condition mapping that no front end reaches (#1033), and a Python
  binding that posts `≤` where its name says `≥` (#1036).
- **The implementation choice matters more than any algorithm.** The
  stateless sweep and the incremental one give identical searches, and each
  beats the other by up to 3× on some real model. The default, incremental from
  8 terms up, loses 2.2× on one of them for a reason that is not linear's at
  all (#1034).

## What it is

### Semantics

For weighted terms `Σ cᵢ·xᵢ`, where `xᵢ` may be a view or a constant, and an
integer `v`:

| Class | Meaning |
|---|---|
| `LinearEquality(s, v)` | `s = v` |
| `LinearNotEquals(s, v)` | `s ≠ v` |
| `LinearLessThanEqual(s, v)` | `s ≤ v` |
| `LinearGreaterThanEqual(s, v)` | `s ≥ v`, stored as `−s ≤ −v` |
| `…If(s, v, c)` | `c → (…)` |
| `…Iff(s, v, c)` | `c ↔ (…)` |

The inequality's reified forms take an `IntegerVariableCondition`. **The
equality's take a full `innards::Literal`**. The `Iff` forms map a
`TrueLiteral` or `FalseLiteral` correctly; the `If` and `NotIf` forms do not
(#1033). `LinearNotEqualsIff(s, v, c)` is stored as
`ReifiedLinearEquality` with `Iff(¬c)` and a `flipped_cond` flag, which only
changes its `.scp` spelling.

`tidy_up_linear` normalises the terms before anything else. It moves constants
and a view's offset into the right-hand side, resolves a view's negation into
the coefficient, merges repeated variables, drops zero coefficients, and
classifies the result as all `+1`, all `±1`, or general. So `x + x` is `2x`,
`x − x` is nothing, and an empty sum is a constant check (rules 4 and 5). The
inequality classes' `clone()` returns a `ReifiedLinearInequality` whatever the
derived type was, so a presolver distinguishes the forms by their reification
condition, not their C++ type.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `LinearEquality` | ✓ `int_lin_eq`, `bool_lin_eq`[^mznvar]; a two-term unit-coefficient one becomes `Equals`[^mzntwo] | ✓ `sum` with `eq`; `decompose` for `dist`[^xdist] | ? | ✓ `lin_equals` | also `Problem::post(s == v)` |
| `LinearNotEquals` | ✓ `int_lin_ne`; two-term becomes `NotEquals`[^mzntwo] | **wrong** for `sum` with `ne` (#1032)[^xne] | ? | ✓ `lin_not_equals` | |
| `LinearLessThanEqual` | ✓ `int_lin_le`, `bool_lin_le`; two-term becomes `LessThanEqual`[^mzntwo] | ✓ `sum` with `le`, `lt` | ? | ✓ `lin_less_equal` | also `Problem::post(s <= v)` |
| `LinearGreaterThanEqual` | `n/a`: MiniZinc normalises to `int_lin_le`, which posts `≤` | `n/a`: `sum` with `ge`/`gt` builds `s >= v`, which `Problem::post` turns into a negated `LinearLessThanEqual` | ? | ✓ `lin_less_equal`, negated | |
| `LinearEqualityIff` | ✓ `int_lin_eq_reif`, **and `int_lin_ne_reif`** as `Iff(r ≠ 1)` | `n/a`: reified intensions go to the comparison family | ? | ✓ `lin_equals_iff` | |
| `LinearLessThanEqualIff` | ✓ `int_lin_le_reif` | `n/a`, as above | ? | ✓ `lin_less_equal_iff` | |
| `LinearNotEqualsIff` | `n/a` (MiniZinc reaches the `EqualityIff` above) | — | ? | ✓ `lin_not_equals_iff` | |
| `…If` forms | `unsupported`: `mznlib` declares no `*_imp` | — | ? | ✓ `…_if` | posted by `examples/rcpsp` (`LinearGreaterThanEqualIf`) and the `.scp` reader |

[^mznvar]: `bool_lin_eq` passes a variable right-hand side; the glue moves it
    onto the left with coefficient −1 and compares with 0.

[^mzntwo]: MiniZinc writes `x = y`, `x ≠ y` and `x − y ≤ d` as two-term
    `int_lin_*` rather than `int_eq` and friends. The glue recovers any two
    `±1` coefficients as `Equals`, `NotEquals` or `LessThanEqual` over a view.
    Checked by hand for this audit, for all four sign cases of each, including the operand swap a
    negative first coefficient forces on the inequality. By the glue's own
    count that is 13,605 `int_lin_eq` and 37,850 `int_lin_le` in 75 sampled
    instances. So a large share of what a model *writes* as linear never
    reaches this family, and the corpus figures below count only what does.

[^xdist]: The intension translator's `dist(a, b)` posts `a − b = diff` and
    `Abs{diff, r}`, with `diff` bounded by the operands' spans. Checked:
    correctly bounded.

[^xne]: `sum` with `ne` posts `sum + diff = bound` and `diff ≠ 0` over an
    auxiliary `diff ∈ [−range, range]`. But `bound − sum` can exceed `range`,
    and a variable operand is not counted in `range` at all. So `x ∈ 0..5`,
    `x ≠ −3` finds 3 solutions of 6, and `x ∈ 0..2`, `x ≠ y` with
    `y ∈ 10..12` is reported `UNSATISFIABLE`, which the proof verifies. The
    workaround is from 2022; `LinearNotEquals`, which is exactly the
    constraint, arrived in 2024. #1032.

`gcspy` binds `LinearEquality`, `LinearNotEquals`, `LinearLessThanEqual`,
`LinearGreaterThanEqual`, `LinearEqualityIff` and `LinearLessThanEqualIff`,
and its `post_linear_greater_equal_iff` **posts `LinearLessThanEqualIff`**
(#1036). CPMpy's upstream GCS interface, checked 2026-09-23, calls none of the
`_iff` bindings and posts every linear constraint through the four plain ones.

### Options

**`ReifiedLinearEquality::with_consistency()`** takes `LinearEqualityConsistency
= std::variant<consistency::BC, consistency::Tabulated>`. The default is
`BC`, and no front end asks for anything else directly. `Tabulated` enumerates
every satisfying tuple at install, via `install_tabulation`, introducing
selector flags in the proof, and is then `GAC`. Its cost is the product of the
domain sizes, which is what the tag says. It is asked for more than it looks:
`Multiply` with a constant operand hands off to a `LinearEquality`, and at its
default `consistency::Auto` that equality is `Tabulated` when the product of
the domain sizes is under the tabulation threshold (`multiply.cc`). The
`knapsack`, `odd_even_sum`, `sudoku` and `skyscrapers` examples post it
directly, `crystal_maze` behind an option, and
`benchmarks/tabulated_linear_random` measures it. The header's comment on the variant says "bounds consistency (the
default), or generalised arc consistency", which is right about the level and
not the tag.

`ReifiedLinearInequality` has no `with_consistency()`.

**The incremental threshold**, `with_incremental_threshold()` on the equality
and a constructor argument on the inequality, defaulting to
`GCS_LINEAR_INCREMENTAL_THRESHOLD` or 8. At or above it, a direction the
dispatcher can reach gets a backtrackable fold state and the incremental
propagator, which folds fixed terms out of the sum. Below it, the stateless
sweep runs. The two make identical inferences, so this picks a strategy and
never a model. What it costs either way is under [CPU
performance](#cpu-performance) and #1034.

**Slack-based waking**, `GCS_LINEAR_SLACK_WATCH_THRESHOLD` (default: off) and
`GCS_LINEAR_SLACK_WATCH_COVER_PERCENT` (default 15). This is for an inequality
whose direction is decided at install, is long enough, and has a small
covering set. It wakes only when a covering term's contributing bound moves,
through refined watches, instead of on every bound. Identical inferences again.
The design and measurements are in [Developer
commentary](#developer-commentary). On the corpus, turning it on at the
recommended 128 terms changed nothing measurable.

None of the three changes the OPB model.

### Variable kinds and views

Any `IntegerVariableID` in any term: plain, constant or view. `tidy_up_linear`
removes views before propagation. The proof handles them through `PolBuilder`'s
**deview mode**, which substitutes the framework's line over the underlying
variable's bits for the view's, so the justification's order literals are over
the underlying variables. Fourteen `…_view_mixed` lanes, one per posted form,
wrap the terms in views. Because the family's facts are all bounds, it is
outside #882's range-literal problem by construction.

### Reification

Both classes are reified through the shared dispatcher
(`install_reified_dispatcher`) for the inequality, and a hand-written undecided
branch for the equality.

- **Inequality.** Undecided: rules 8 and 9 decide the condition from the sum's
  bounds, and the dispatcher infers `c` or `¬c` as the form licenses. `If` and
  `Iff` infer `¬c` when the inequality cannot hold, and `Iff` and `NotIf` act
  when it must hold. Decided: rule 1 runs on the enforced direction, the
  negation being `−s ≤ −v − 1`.
- **Equality.** Undecided: nothing is inferred while two or more terms are
  unset. With one left, rules 11 and 12 decide the condition from its
  domain, and with none left rule 10 does.
  Decided true: rules 1–3, as for `LinearEquality`. Decided false: rules 6 and
  7, as for `LinearNotEquals`.

That asymmetry is a strength gap: the equality never asks whether its bounds
already exclude `v`. `c ↔ (Σ xᵢ = 100)` over `xᵢ ∈ 0..3` fails once on `c = 1`,
where the `≥` form infers `¬c` at the root. It costs nothing measurable on the
corpus; see [Next steps](#next-steps).

### Relation to other families

**Into this family.** Both front ends, as in the table. MiniZinc's reified `ne`
arrives as a reified equality. XCSP3 also posts linear rows for `ordered`, the
intension translator's `add` and `dist`, and a peephole over intensions.
`Problem::post(s <= v)` and `(s == v)`, which the tests and examples use
heavily.

**Other families posting it as a child.** `Path` and `Tree` post a
`LinearEquality` for their cardinality. `Multiply` with a constant operand
hands off to one, which is `Tabulated` on small domains (see
[Options](#options)). And this family's code is not only its own.

**Shared code.**

- `propagate_linear` is called by `linear_stages.hh` (`propagate_stages`), so
  the linear stages of `divide`/`modulus` and `power` run this sweep. They pass `hints::LinearEquality{owner}`, so those inferences arrive on
  the wire as `linear_equality` **under the arithmetic constraint's id**. That
  is the hint naming the procedure, not the family, as `element` found for
  `equals`.
- `justify_linear_contrapositive` is used only by the gated stages.
- `tidy_up_linear` and `PositiveOrNegative` are the family's own.

**Presolvers.**

- `difference_logic` enumerates `ReifiedLinearInequality` donors, recognises
  two-term `±1` rows as difference edges, and builds `pol`s on the row named by
  `ConstraintProofModelData<ReifiedLinearInequality>::primary_row_role`.
  That role is public API: changing which row it names breaks the presolver.
- `makespan_links` reads the same donors for `start + d ≤ makespan` links.
- None rewrites into this family.

**Reached only through a decomposition?** No.

No candidate merge. The family list's entry is `linear/` alone.

## The proof model

### OPB encoding

Definitional, over `BinEnc` of each term's variable (the user's views, in the
view's bits), and **logarithmic in every domain width**. `S = Σ cᵢ·BinEnc(xᵢ)`.

**`ReifiedLinearInequality`**, one row per reachable direction:

| Form | Row(s) | Label |
|---|---|---|
| `MustHold` | `S ≤ v` | `c[id]` (empty role) |
| `MustNotHold` | `S ≥ v + 1` | `c[id]` |
| `If c` | `c → S ≤ v` | `c[id]` |
| `NotIf c` | `c → S ≥ v + 1` | `c[id]` |
| `Iff c` | `c → S ≤ v`; `¬c → S ≥ v + 1` | `c[id][r]`, `c[id][f]` |

`NotIf`'s row was `c → S ≤ v`, the opposite of what it means, until #644.

**`ReifiedLinearEquality`**:

| Form | Rows | Labels |
|---|---|---|
| `MustHold` | `S ≤ v`, `S ≥ v` | `c[id][le]`, `c[id][ge]` |
| `MustNotHold` | flag `b[id][ne]`; `ne → S ≥ v + 1`; `¬ne → S ≤ v − 1` | `c[id][gt]`, `c[id][lt]` |
| `If c` | `c → S ≤ v`, `c → S ≥ v` | `c[id][le]`, `c[id][ge]`, invented: "not chain-verified" |
| `NotIf c` | unlabelled flag `linne`; `c ∧ linne → S ≥ v + 1`; `c ∧ ¬linne → S ≤ v − 1` | none |
| `Iff c` | `c → S = v` as `le`/`ge`; unlabelled flags `lineqgt`, `lineqlt` with `gt → S ≥ v + 1`, `lt → S ≤ v − 1`; `lt + gt + c ≥ 1` | `c[id][le]`, `c[id][ge]` only |

Every row is linear in the number of terms, and every form is a handful of
rows. `NotIf` and `Iff`'s flags are OPB variables, created with no
constraint id, and are defined by unit propagation on a solution: the flags
are one-directional (`flag → row`). `Iff`'s disjunction row forces one of
its flags; `NotIf` uses both polarities of its one flag.

### Labels

The propagators cite rows by the `ProofLine`s the model hands back, not by
label. The labels are cake's, and matter to `opbdiff`, except for two:

- **`primary_row_role`** is public API. `ConstraintProofModelData<ReifiedLinearInequality>`
  names the `S ≤ v` row as the empty role for `MustHold` and `If`, and
  nothing for the other three forms. The difference-logic presolver builds
  `pol`s on it, so changing which row it names breaks a caller.
- The `If` equality's `le`/`ge` labels are marked as invented, because no
  chain lane covers them.

### Cake conformity

| Case | `opbdiff` |
|---|---|
| `lin_equals_{unsat,sat,neg_coeff_sat,3var_sat}` | `strict` |
| `lin_less_equal_{unsat,sat}`, `lin_greater_equal_unsat` | `strict` |
| `lin_equals_{minimize,maximize,maximize_neg}_opt` | `strict` |
| `lin_not_equals_{sat,unsat}` | `strict` |
| `lin_equals_iff_sat`, `lin_less_equal_iff_sat` | `none` |

Twelve of the fourteen are byte-for-byte label matches with cake. The two
reified cases are chain-only. No
lane covers `If`, `NotIf` or a reified not-equals.

### Proof-time state

- Everything the justifications cite is in the OPB. Nothing is emitted at the
  root, and every justification line is `ProofLevel::Temporary`.
- **Order literals are introduced lazily**, one per bound a justification or
  reason names, by the names-and-IDs tracker (the `red` lines in a proof). On a
  long sum that is every term's current bound, at every inference (#1035).
- **The `Tabulated` arm** introduces its selector flags in the proof, at
  install, through `install_tabulation`. It shares the extensional family's
  machinery, which `table.md` will own.
- **Justifications read `state`**, in rules 8 and 9 (`justify_cond` asks
  `state.upper_bound`/`lower_bound`). The bound pushes read the propagator's
  own bounds snapshot, which the reason also states. The caveat about
  re-emitting justifications later is the one in `all_different.md`.
- **Proof-only vectors**: the `_proof_line`/`_proof_lines` pairs are empty
  when proofs are off, and read only inside justifications. The fold states
  are propagation state, not proof state.

## The implementation

### Initialisation and global data

`prepare()` does all the deciding, and none of it is proof-related:

- it evaluates the reification condition against the initial state;
- it runs `tidy_up_linear` on the terms (and on their negation, for the
  inequality);
- it allocates a backtrackable `LinearIncrementalState` for each direction the
  dispatcher can reach, **if** the sanitised length is at least the threshold;
- for the inequality, it sizes the slack cover against the initial domains, if
  slack waking is on.

An `Iff` inequality gets **two** fold states, one per direction, as long as it
has 8 terms or more, which doubles the slots #1034 is about on
`pattern-set-mining-k2`.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| stateless sweep (`propagate_linear`) | `on_bounds`, every term | derived: none | 1–4 | below the threshold | **claims it** (`EnableButIdempotent`) | only for an empty sum |
| incremental sweep (`propagate_linear_incremental`) | `on_bounds`, every term | derived: none | 1–4 | at or above the threshold | **claims it** | only for an empty sum, via the stateless path |
| slack-watched sweep | `scope_only`, plus refined watches on covering terms' bounds | **declared** none (`holes_affect_propagation = {}`) | 1, 3, 4 | an inequality decided at install, if slack is on | no: returns `Enable` so the watches can wake it | no |
| not-equals (`propagate_linear_not_equals`) | `on_instantiated`, every term (#807) | derived: none | 6, 7 | equality decided false | not claimed | yes, once it has acted |
| reified inequality (dispatcher) | the enforce direction's triggers ∪ `c` | derived | 1, 3, 4, 8, 9 | an undecided inequality | stripped: the dispatcher does not pass the sweep's claim on | on a verdict |
| reified equality, undecided | `on_change`, every term; `c` | derived: yes | 10–12 undecided; 1–3 once decided true; 6, 7 once decided false | an undecided equality | forwards the sweep's claim when decided true | on acting |
| equality, constant row | initialiser | — | 5 | a fixed equality with no terms | — | — |
| `Tabulated` | `install_tabulation`'s | the extensional family's | 13 | `with_consistency(Tabulated{})` | as `table.md` | as `table.md` |

**Idempotence.** The stateless and incremental sweeps claim it, and the claim
is argued in `propagate_linear`. The forward sweep writes only upper bounds of
positive-coefficient terms and lower bounds of negative ones, and reads only
the other side. So reads and writes are disjoint per variable, and a single
pass is the `≤` fixpoint, even across a write that snaps past a hole. The
equality alternates the forward and inverse sweeps until one is clean, which
reaches its own fixpoint in one call. The test harness sets
`GCS_CHECK_IDEMPOTENT_CLAIMS`, which re-runs every honoured claim and aborts
if it infers anything. The slack-watched form cannot claim it, since a coarse
re-wake would defeat the watches.

**The two reified classes disagree about passing the claim on.** When the
condition is undecided at install, the shared dispatcher strips an enforced
sweep's `EnableButIdempotent`, because a re-run also re-tests the condition and
"nobody has audited that interplay yet". The equality's hand-written undecided
branch returns the sweep's claim unchanged once the condition is decided true.
The harness's re-run check has not caught a problem in the `eq_if` and
`eq_iff` lanes, but the two classes should agree; see [Next steps](#next-steps).

**Holes affect.** Only one propagator in the family observes holes: the
undecided reified equality, which asks, once one term is left, whether the
value that would satisfy the equality is in its domain (rule 11). Its
`on_change` triggers are the truth. The sweeps read only bounds and are
triggered `on_bounds`. **This family's whole vocabulary is bounds**, apart from
that one rule and the not-equals, which acts only on fixed values. So a
linear constraint is never a reason for another constraint's interior pruning
to stay on. The slack-watched form declares that explicitly, because
`scope_only` would otherwise read as "holes affect everything".

### Mutable state and incrementality

**Backtrackable**: `LinearIncrementalState {n_active, fixed_lower}`, one per
reachable direction at or above the threshold. The engine copies it at every
search node, as a heap allocation, because 16 bytes exceeds `std::any`'s
in-place storage (#1034).

**Not backtrackable, and sound**: the incremental propagator's `active`
permutation. A fold swaps a newly fixed term to the end of the active prefix
and decrements `n_active`. Swaps stay inside the current prefix, so every
earlier level's prefix keeps the same *set* of terms, in a different order.
Backtracking restores `n_active`, and the sweep does not depend on order. The
propagator keeps at least one term active, so a fully fixed, violated
assignment still reaches a check.

**Recomputed per call.** The stateless sweep re-reads every term's bounds into
a `small_vector` (inline up to 8 terms) and recomputes the minimum sum. That is
`O(n)` per call. The incremental sweep does the same over the active terms
only. The slack form re-sorts the potentials after every clean wake, which is
`O(n log n)`. The design note records why an incremental cover does not help.

### Interior values and optional pruning

**What this family offers:** `None.` No class installs a pair, or accepts
`consistency::Auto`.

**What this family observes:** bounds, stated in those words, except for the
undecided reified equality's last-value rule and the not-equals, which acts on
fixed values only. A variable that appears only in linear constraints lets any
neighbour's optional interior pruning be dropped.

### Robustness and limits

- **Unbounded domains**: no width limit, since everything is bounds and
  `BinEnc`. Domains are capped at `Integer::max_bounded_value()` (`2⁶¹`) by the
  solver, not the family.
- **Overflow**: coefficient × bound products are checked `Integer` arithmetic
  and **throw** on overflow; they never wrap. With coefficients of `2⁴⁰` and
  bounds of `2²⁹` to `2³⁰`, the forward sweep throws `Integer overflow` (a
  lower sum of `2⁷⁰`); so do the reified inequality's undecided check (its
  maximum sum) and an equality with a negative coefficient, whose forward
  sweep multiplies it by an upper bound. The model writer diagnoses a
  row too large to write (#852). **The propagator does not**: its throw is a
  bare `UnexpectedException` that names no constraint. It needs a coefficient
  times a bound past `2⁶³`, so it is a limit of the model, not a bug.
- **Negative values and zero**: negative coefficients are first-class
  throughout, and the chain has negative-coefficient and sign-bit lanes. A
  zero coefficient is dropped by `tidy_up_linear`.
- **Degenerate shapes**: an empty sum is a constant check (rules 4 and 5).
  `linear_constant_test` posts empty equality and not-equals sums; the
  inequality's empty sum is one data row in `linear_test`. A single term is an ordinary sweep. A
  repeated variable is merged, so `x − x ≤ 3` is empty. A constant term moves
  to the right-hand side. A two-term `±1` constraint from MiniZinc never
  arrives here (it becomes `Equals`, `NotEquals` or `LessThanEqual`).
- **A constant condition** on the equality's reified forms: wrong answers for
  `If` and `NotIf` (#1033).

### Interval efficiency

`Fine at any width`, on all four questions, for the default arms.

1. **Propagation.** The sweeps read and write bounds only. The not-equals asks
   `in_domain` for one value, once. The undecided equality asks `in_domain` for
   one value on its last unset term. Nothing in `propagate.cc`,
   `linear_equality.cc` or `linear_inequality.cc` walks a domain's values.
   That can be checked by reading. The `Tabulated` arm enumerates tuples, which
   is the product of the domain sizes and is what its tag means.
2. **Reasons.** One bound literal per term, never per value, and assembly is
   guarded on `want_reasons()`, so plain search pays nothing. What is wrong
   with them is not width but **triviality**: every term's bound goes in,
   including terms still at their initial bound (#1035).
3. **Proofs.** Order literals over `BinEnc`, one `pol` per bound push with one
   term per variable. Width only enters through the logarithmic bit count.
   There is no per-value form, so no width gate.
4. **The audit lane**: `LinearEquality`, `ReifiedLinearEquality` and
   `ReifiedLinearInequality` are all `Clean`, and there is no proof-size row.
   **Axes they do not vary**: coefficients other than ±1 (so no overflow and
   no rounding), holes (irrelevant to the sweeps, but rule 11 reads them), the
   not-equals, the `Tabulated` arm, and the incremental versus stateless
   choice. None of those is a width hazard. The `Tabulated` arm is the only one
   that would trip, by design.

## Inference catalogue

Thirteen rules. Rules 1–4 are the sweep, shared by every enforced direction,
both classes, the stateless, incremental and slack-watched propagators, and the
arithmetic family's linear stages. Rules 5–7 are constant rows and the
not-equals. Rules 8–12 decide a reification condition. Rule 13 is the
`Tabulated` arm.

Four facts hold across them.

**The wire inventory.**

| Wire form | Hint type | Rules |
|---|---|---|
| `linear_equality:((constraint_id N))` | `hints::LinearEquality` | 1–5, 10–12 for an equality; and the arithmetic stages' sweeps, under *their* id |
| `linear_not_equals:((constraint_id N))` | `hints::LinearNotEquals` | 6, 7 |
| `linear_inequality:((constraint_id N) (subhint cond))` | `hints::LinearInequalityCond<…>` | 8, 9 |
| *(none)* | `NoHint` | **1, 3, 4 for an inequality** |

**An inequality's bound pushes carry no hint at all.** `propagate_linear` is
instantiated with `NoHint` for the reified-inequality propagators ("which pass
no hint"), so in hints-only mode their assertions are bare `a <clause> >= 1;`
lines: 174 of them in `linear_constraint_le`'s proofs at seed 1, and 203 in
`ge`'s. `hints::LinearInequality` exists, and is used only as the base of the
`cond` hint. **None of the five earlier family documents records an
unattributed assertion.** An external justifier has to find the row that licenses one by
searching every inequality's scope for the clause's literals.

**What licenses them.** Rules 1–3 are **JP 3.15 (linear inequality
propagation)** and its infeasibility case, from McIlree's thesis. The rest are
single RUPs against the encoding, or ours, as each entry says. Our JP 3.15
departs from the thesis in three ways:

- it divides the summed line by the changed variable's coefficient and closes
  by RUP, where the thesis closes by syntactic implication;
- deview mode substitutes each view's underlying variable's bits;
- the equality's inverse direction cites the `ge` row where the forward cites
  `le`.

Like the thesis's procedure, **it names every other term's bound**, which is
#1035.

**Justifications mostly read their own snapshot.** The sweeps build the `pol`
from the `bounds` snapshot the propagator took, which the reason also states.
Only rules 8 and 9 (`justify_cond`) read `state` directly.

**Tightness.** No mutation lane exists in this family. The slack lanes do
exercise the claim that slack waking changes nothing but the wake condition:
the same instances, the same verified proofs.

### Rule: linear-bound

(Rule 1.)

- **Infers** — `xⱼ ≤ ⌊(v − L₋ⱼ)/cⱼ⌋` for `cⱼ > 0`, or the mirror lower bound
  for `cⱼ < 0`, where `L₋ⱼ` is the least the other terms can contribute.
- **Fires when** — a sweep of an enforced `≤` direction: `LinearLessThanEqual`,
  `LinearGreaterThanEqual` (negated), an equality's forward half, a negated
  inequality (`−S ≤ −v − 1`), and the arithmetic stages. Only when the new bound
  is tighter.
- **Strength** — `bounds(Z)` on every term, with rule 2 for an equality.
- **Algorithm** — one pass: the minimum sum from each term's contributing
  bound, then each term's slack against it. `O(n)` in **terms**. The forward
  sweep's writes never touch what it reads, so one pass is its fixpoint. The
  incremental form does the same over the unfixed terms only.
- **Why it is true** — the others contribute at least `L₋ⱼ` whatever they
  take, so `cⱼxⱼ ≤ v − L₋ⱼ`; divide, rounding towards the feasible side.
- **Proof technique** — `pol` then `RUP`, by **JP 3.15**, with the departures
  above. The row, plus `|cᵢ|` times each other term's bound literal
  (`add_for_literal`), divided by `|cⱼ|`. Precondition: every other term's bound
  in the reason is the one the minimum sum used.
- **Reason** — every other term's contributing bound, and the reification
  condition for a reified form. **Not minimal**: terms still at their initial
  bound are included (#1035). One literal per term. Guarded on `want_reasons()`.
- **Assertion** — the new bound literal, `∨ ¬reason`.
- **Hint** — `hints::LinearEquality` for an equality, none for an inequality.
- **Offline reconstructibility** — `hinted` for an equality: the constraint id
  names the row, and the reason gives every bound JP 3.15 needs.
  **`solver-side` for an inequality**: nothing names the constraint, so the
  reconstructor needs the identity of the row, which the assertion does not
  carry.
- **Proof size** — one `pol` over `n` rows and `n − 1` bound definitions, one
  RUP, and a definition for each bound literal not yet introduced. In
  **terms**, never width. On `2008_shortest_path`, whose objective sum has
  about 215 terms, the `pol`s average 656 fields.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: linear-inverse-bound

(Rule 2.)

- **Infers** — the mirror of rule 1 from the `≥` half of an equality.
- **Fires when** — an equality's inverse sweep, alternated with the forward one
  until either is clean.
- **Strength** — `bounds(Z)`, with rule 1.
- **Algorithm** — as rule 1, on the negated sum.
- **Why it is true** — as rule 1.
- **Proof technique** — as rule 1, citing the `ge` row.
- **Reason, Assertion, Hint, Proof size** — as rule 1. The hint is always
  `hints::LinearEquality`.
- **Offline reconstructibility** — `hinted`.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: linear-bound-conflict

(Rule 3.)

- **Infers** — a contradiction, when rule 1 or 2 would empty a domain.
- **Fires when** — the tracker's `_or_stop` inference fails. The propagator
  stops reading `state` and returns.
- **Strength** — as rules 1 and 2.
- **Algorithm** — none beyond rules 1 and 2.
- **Why it is true** — the other terms' minimum already exceeds what this
  term's remaining values allow: the thesis's infeasibility argument (JP 3.14).
- **Proof technique** — as rule 1: the same `pol`, and the tracker's RUP
  closes the conflict with the failing literal.
- **Reason, Hint** — as rule 1.
- **Assertion** — `¬reason`.
- **Offline reconstructibility** — as rule 1.
- **Proof size** — as rule 1.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: linear-empty-sum

(Rule 4.)

- **Infers** — a contradiction, when the tidied sum is empty and `0 ≤ v` is
  false.
- **Fires when** — the first sweep of a constraint whose terms all cancelled or
  were constants.
- **Strength** — `checker`.
- **Algorithm** — one comparison.
- **Why it is true** — the constraint reduces to a false constant inequality.
- **Proof technique** — `RUP` against the row.
- **Reason** — the reification condition, if any.
- **Assertion** — `¬reason`.
- **Hint** — as rule 1.
- **Offline reconstructibility** — `offline` for an equality, and as rule 1 for
  an inequality.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: linear-constant-equality

(Rule 5.)

- **Infers** — false, at install, for an equality whose condition is decided
  and whose sum is empty, when the constant makes it false: `MustHold` with
  `v + modifier ≠ 0`, or `MustNotHold` with `v + modifier = 0`.
- **Fires when** — an initialiser, once.
- **Strength** — `checker`.
- **Algorithm** — one comparison, at install.
- **Why it is true** — as rule 4.
- **Proof technique** — `RUP`.
- **Reason** — the decided condition.
- **Assertion** — `¬reason`.
- **Hint** — `hints::LinearEquality`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: not-equals-last-value

(Rule 6.)

- **Infers** — `xⱼ ≠ (v − Σ_fixed)/cⱼ` for the one unfixed term, when that is
  an integer in its domain.
- **Fires when** — `LinearNotEquals`, or an equality decided false, once every
  term but one is fixed. It wakes `on_instantiated` (#807), which cannot miss
  that moment.
- **Strength** — `GAC`. With two or more unfixed terms, every value of each has
  a support, so there is nothing to prune; the tests check `GAC`.
- **Algorithm** — one pass over the terms; stops at the second unfixed one.
- **Why it is true** — the last term taking that value would make the sum `v`.
- **Proof technique** — `RUP` against the not-equals rows: `S ≥ v + 1` and
  `S ≤ v − 1` under the `ne` flag and its negation, or the `Iff` form's
  `gt`/`lt` flags and their disjunction row.
- **Reason** — `generic_reason` over the whole scope, built when this fires.
- **Assertion** — `xⱼ ≠ w ∨ ¬reason`.
- **Hint** — `hints::LinearNotEquals`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: not-equals-all-fixed

(Rule 7.)

- **Infers** — a contradiction, when every term is fixed and the sum is `v`.
- **Fires when** — as rule 6, with no term unfixed. It stops rather than
  throws: this is the failure detector for half the nodes of some searches
  (#820).
- **Strength** — `GAC`, with rule 6.
- **Algorithm** — as rule 6.
- **Why it is true** — the constraint is violated.
- **Proof technique** — `RUP`, as rule 6.
- **Reason** — as rule 6.
- **Assertion** — `¬reason`.
- **Hint** — `hints::LinearNotEquals`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: inequality-cannot-hold

(Rule 8.)

- **Infers** — `¬c`, for `If c` and `Iff c`, when the least the sum can be
  exceeds `v`.
- **Fires when** — the reified inequality's undecided verdict.
- **Strength** — `bounds(Z)` on the sum, deciding the condition.
- **Algorithm** — the minimum and maximum sums, one pass: `O(n)` in terms.
- **Why it is true** — no assignment within the bounds satisfies `S ≤ v`, so the
  condition that demands it is false.
- **Proof technique** — `pol` then `RUP`, ours (`justify_cond`): the `c → S ≤ v`
  row plus every term's contributing bound. It is JP 3.15's shape with the
  condition left over. It reads `state`. The comment above the verdict says
  "only Iff and NotIf get here undecided, and of those only Iff licenses an
  inference". **That is out of date**: `If` gets here too (`linear_constraint_le_if`
  reaches this rule 22 times at seed 1), and it licenses `¬c`
  (`set_not_cond_if_must_not_hold`). The code is right, and the row `If`
  cites is its own.
- **Reason** — `generic_reason` over the scope, built once at install.
- **Assertion** — `¬c ∨ ¬reason`.
- **Hint** — `hints::LinearInequalityCond`: `originator`, plus the sanitised
  terms, the rows and a pointer to `state` for the emitter. Wire:
  `(constraint_id N) (subhint cond)`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — one `pol` over `n + 1` rows, one RUP.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: inequality-must-hold

(Rule 9.)

- **Infers** — `c` for `Iff c`, or `¬c` for `NotIf c`, when the most the sum can
  be is at most `v`.
- **Fires when** — as rule 8.
- **Strength** — as rule 8.
- **Algorithm** — as rule 8.
- **Why it is true** — every assignment satisfies `S ≤ v`, so its negation's
  row cannot hold.
- **Proof technique** — as rule 8, on the negated sum and the `S ≥ v + 1` row.
- **Reason, Hint, Offline reconstructibility, Proof size** — as rule 8.
- **Assertion** — `c ∨ ¬reason` (or `¬c`).
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: equality-decided-at-leaf

(Rule 10.)

- **Infers** — `c` or `¬c`, when every term is fixed and the sum is or is not
  `v`, as the form licenses.
- **Fires when** — the undecided equality, with no unfixed term.
- **Strength** — `checker` for the condition.
- **Algorithm** — one pass over the terms.
- **Why it is true** — the sum is known.
- **Proof technique** — `RUP`. For `Iff`, `¬c` (the sum is not `v`) comes from
  the `c → le`/`ge` rows, and `c` (the sum is `v`) from the `gt`/`lt` flags'
  rows and the disjunction row. For `NotIf`, `¬c` comes from the `linne` rows.
- **Reason** — `generic_reason` over the scope and the condition, built once.
- **Assertion** — the condition literal, `∨ ¬reason`.
- **Hint** — `hints::LinearEquality`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — **a strength gap, not a proof one.** The undecided equality never
  asks whether its bounds already exclude `v`. `c ↔ (Σ xᵢ = 100)` over
  `xᵢ ∈ 0..3` fails once on `c = 1`, where the `≥` form infers `¬c` at the root.
  On the corpus it costs nothing: a local experiment adding the check fired
  millions of times, on `grid-colouring`, `diameterc-mst` and `gfd-schedule`,
  and changed no solution. `l2p`, which finishes, searched an identical
  119,187 nodes either way.
- **Tightness** — `Not shown.`

### Rule: equality-last-value-missing

(Rule 11.)

- **Infers** — `¬c`, as the form licenses, when one term is unfixed and the
  value that would satisfy the equality is not in its domain.
- **Fires when** — the undecided equality, one term left. The only rule in the
  family that reads a hole.
- **Strength** — `partial`.
- **Algorithm** — one `in_domain` test.
- **Why it is true** — no value of the last term completes the equality.
- **Proof technique** — `RUP`, as rule 10.
- **Reason, Assertion, Hint, Offline reconstructibility, Proof size** — as
  rule 10.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: equality-non-integer

(Rule 12.)

- **Infers** — `¬c`, when one term is unfixed and `(v − Σ_fixed)/cⱼ` is not an
  integer.
- **Fires when** — as rule 11.
- **Strength** — `partial`.
- **Algorithm** — one remainder.
- **Why it is true** — no integer completes the equality.
- **Proof technique** — `RUP`. Whether unit propagation alone sees a
  divisibility argument depends on the encoding; the tests verify it, on unit
  and non-unit coefficients, but no fixture targets a large coefficient.
- **Reason, Assertion, Hint, Offline reconstructibility, Proof size** — as
  rule 10.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: linear-equality-tabulated

(Rule 13.)

- **Infers** — every value with no supporting tuple.
- **Fires when** — `with_consistency(consistency::Tabulated{})` on an equality.
- **Strength** — `GAC`, checked by the tests.
- **Algorithm** — enumerate the satisfying tuples at install, and hand them to
  the extensional family's propagator. The cost is the product of the domain
  sizes.
- **Why it is true** — a value is supported iff some solution tuple uses it.
- **Proof technique** — the extensional family's, over the in-proof selector
  flags `install_tabulation` introduces. `table.md` will own it.
- **Reason, Assertion, Offline reconstructibility, Proof size** — the
  extensional family's.
- **Hint** — `hints::LinearEquality`, passed to `install_tabulation`.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

| Lane | What it checks |
|---|---|
| `linear_constraint_{eq,ne,le,ge,le_not}` × `{incremental,stateless}` and their `_if`/`_iff`/`_notif` forms | `linear_test`, random instances of three terms, enumeration against brute force. Consistency is checked only for single-constraint instances: `bounds(Z)` on each term for the inequalities (`GAC` for not-equals), **never for `LinearEquality`**, and never for the reified equality and not-equals forms; `GAC` for the `Tabulated` rows |
| `linear_constraint_*_view_mixed` (14) | the same with the terms wrapped in views |
| `linear_constraint_*_slack` (8) | the inequality forms with slack waking forced on at any length and any cover |
| `linear_constant_constraint_{incremental,stateless}` | constant and empty sums |
| `mini_linear_constraint` | a private refined-watch test harness (`MiniLinearGreaterEqual`); posts nothing from this family |
| `linear_utils_test` | `tidy_up_linear` |
| `scp_chain_lin_*` (14) | see [Cake conformity](#cake-conformity) |
| `minizinc-two-term-lin-{eq,ne,le,le-difference-logic}` | the two-term recovery |
| `rcpsp_deadline`, `rcpsp_mm_deadline` | linear rows as makespan deadlines |

VeriPB runs in every data-driven lane when it is on the path. Every lane is
seeded. The incremental/stateless split is by `GCS_LINEAR_INCREMENTAL_THRESHOLD`
in the lane's environment, and the slack lanes set
`GCS_LINEAR_SLACK_WATCH_THRESHOLD=0` and `…_COVER_PERCENT=100`. All 74 pass at
`00797a97`.

**Runtime caps.** No lane sets or clears one, and **the default caps fire on
almost every lane**. Measured with a local print over three reseeded runs: 108
truncated solves per run on each `ne_if` lane, 56–64 on each `eq_if` and
`eq_iff`, 30–42 on the `le_notif`, `le_if` and `ge_if` lanes, 10–14 on
`mini_linear`. They **never** fire on the plain `eq` lanes or
`linear_constant`. So for most of this family's lanes, the default run checks
soundness and a partial proof, and only the uncapped Ubuntu CI lanes check
completeness. This document's figures come from an uncapped build.

**Rules the tests reach**, from local counters at seed 1: rules 1–4 and 6–12,
and rule 13 by construction in the `Tabulated` rows. Rule 4 (the empty sum)
fires in the `le`, `le_if`, `le_iff` and `ge_iff` lanes. Rule 5 and the
slack-watched wake were not counted; the slack lanes force that path on.

**What the tests do not cover**, which is the point of this section:

- **A constant condition** on the equality's reified forms. The `_if` lanes
  use variable conditions only, which is how #1033 survived.
- **An XCSP3 `<sum>` with `ne` whose bound or operand escapes the
  auxiliary's range**. `xcsp/tests/sum_not_equals.xml` stays inside it (#1032).
- **The `gcspy` linear `_iff` bindings**. No Python test calls either (#1036).
- **Coefficients other than small ones**: every random instance uses
  coefficients within a few units, so nothing exercises overflow, the rounding
  of rule 1's division by a large coefficient, or rule 12's divisibility.
- **Long sums.** Every `linear_test` instance has three terms. So the
  incremental propagator's folding is exercised on three terms at threshold 0,
  and the slack path only by forcing it. Every instance's reason is short, which
  is why nothing in the suite would notice #1035.
- **Inferences-level attribution.** Nothing checks that an assertion carries a
  hint, which is how the inequality's bare assertions went unnoticed.

### Benchmarks and examples

- **In-repo**: `benchmarks/linear_prop_cost` (per-propagation cost of the two
  sweeps), `benchmarks/linear_slack_bench` and `slack_watch` (the slack
  design's measurements), `benchmarks/wake_cost`, and
  `benchmarks/tabulated_linear_random`. Among the examples, `money` (one long equality with large coefficients)
  and `knapsack` are small. minicp's `magic_series` (default options, `00797a97`) has
  90,301 propagators over two types, and `equals` takes 66% of its
  propagation time, so `lin_equals` takes the rest. No example is dominated by the family.
- **The corpus is where the family lives.** Linear is 100% of propagation time
  on `triangular` (2015, 2019, 2022, 2024), `multi-knapsack` 2014, `vrp`
  (2011–2013), `wmsmc-int` 2021 and `shortest_path` 2008, and over 90% on
  `unit-commitment`, `pattern-set-mining` and `nfc`.
- **For CPU**: `vrp` 2012, `unit-commitment` 2023 and
  `pattern-set-mining-k2` 2012. Between them, the default configuration wins
  by 1.9–3× or loses by 2.2×, and they have identical trees under every
  configuration. `shortest_path` 2008 finishes in under a second.
- **For proofs**: nothing linear-dominated in the corpus is a practical size.
  `shortest_path` is the smallest that finishes, and its proof is 15 GB (#1035).
  The test lanes are the only verified proofs.

### CPU performance

All at `00797a97`, Release, GCC 15.2.0, fataepyc-09 (EPYC 7643, boost off),
pinned, 2026-09-23, one run each unless stated.

**Where the family is the cost.** Share of propagation time over the whole
corpus (10 s each, `GCS_PROPAGATOR_STATS=time`): linear appears in 250 models,
with a median share of 8.4%, and at least 50% in 44 of them.

**The implementation, measured.** Nodes in 30 s under four configurations.
Solution sequences are identical in every row, and the one model that finishes
under all four (`shortest_path` 2008) searches 42,437 nodes in each.

| Model | default (8) | stateless | incremental (0) | slack (128) |
|---|---|---|---|---|
| 2023 unit-commitment | 471,523 | 158,211 | 148,469 | 446,340 |
| 2012 vrp | 770,794 | 412,411 | 246,163 | 758,066 |
| 2013 vrp | 981,078 | 560,813 | 342,718 | 994,873 |
| 2021 wmsmc-int | 8,037,088 | 5,083,124 | 8,033,480 | 8,053,127 |
| 2014 multi-knapsack | 5,396,316 | 4,652,850 | 5,380,892 | 5,377,040 |
| 2012 pattern-set-mining-k2 | 210,254 | **440,699, finished** | 204,382 | 204,406 |
| 2011 pattern-set-mining | 91,114 | 100,751 | 91,048 | 90,943 |
| 2021 mapping | 1,307,336 | 1,494,824 | 1,132,123 | 1,304,804 |
| 2024 triangular | 3,808,225 | 3,532,664 | 617,957 | 3,826,472 |
| 2021 flowshop-workers | 891,071 | 889,551 | **50,914** | 896,411 |
| 2024 hoist-benchmark | 328,279 | 331,050 | 116,305 | 330,491 |

(Twenty-three models were run; these are representative.)

- **Threshold 0 is far worse on models of short constraints**: `flowshop-workers`
  runs 17 times slower, and `triangular` 6 times. So the threshold earns its
  keep.
- **The default beats stateless by 1.6–3×** where there are a few long sums:
  `unit-commitment` 3.0×, `vrp` 1.9× and 1.7×, `wmsmc-int` 1.6×.
- **The default loses 2.2×** on `pattern-set-mining-k2`: stateless finishes
  440,699 nodes in 27.5–27.6 s over three runs, where the default reaches about
  220,000 in 30 s. `perf` puts a quarter of the default run in `malloc` and
  `free` copying the fold states, a thousand of them, since each of its 500
  long `Iff` inequalities gets two (#1034).
- **Slack waking at 128 terms changes nothing** measurable on any model: the
  corpus has almost no constraint that long and loose. That is consistent with
  it shipping off.

**The reified equality's missing bounds check**: a local experiment adding it
fired 13.9 million times on `grid-colouring` 2011 and 5.7 million on
`diameterc-mst`, and changed no solution anywhere. `l2p` searched an identical
119,187 nodes. So its absence costs nothing measurable here.

**What these benchmarks exercise**, from local counters over 10 s each:

- `triangular`, `multi-knapsack`, `vrp` and `wmsmc-int` are rules 1–3,
  inequality and equality, and nothing else.
- `grid-colouring` 2011 is rules 10 and 11 alone.
- `hoist-benchmark` and `flowshop-workers` are dominated by rules 8 and 9.
- **Rule 12 (non-integer) is reached by none of the 18 models counted**, only
  by the test.
- Rules 6 and 7 appear in `l2p`. Rules 5 and 13 were not counted.

**Cross-solver**: `Not measured.` (#868).

### Proof performance

**`2008_shortest_path`**: 216 variables in `0..1` and an objective in
`0..6,778` whose defining equality has about 215 terms; 42,437 nodes.

| | solve | proof | VeriPB |
|---|---|---|---|
| proofs off | 0.92 s | — | — |
| `AssertionLevel::Off` | 106.2 s | 7,343,416 lines, 14.97 GB | not finished after 707 s |
| `AssertionLevel::Inferences` | 44.1 s | 1,960,330 lines, 9.76 GB | 191 s, `UNDER ASSERTIONS` |

**Own against shared.** The OPB is 348 constraint rows. The proof is almost all this
family's bound pushes. In the first 200 MB of the `Off` proof there are 28,171
`pol`s averaging 656 fields, 28,770 `rup`s and 55,200 `del`s, and one `pol`
per bound push. In the first 300 MB of the `Inferences` proof, the 62,507
assertions average 167 literals, and **95.6%** of the literals in the
`linear_equality` assertions are `~x[ge0]` on a 0/1 variable. That is the clause
form of a reason literal, `x ≥ 0`, that was true before search started (#1035).
So the proof's size is set by how many terms each assertion names, not by how
many assertions there are.

**The test lanes at both assertion levels**, seed 1, every proof kept:

| Lane | lines, `Off` | lines, `Inferences` | family assertions |
|---|---|---|---|
| `eq` | 8,429 | 1,365 | 368 `linear_equality` |
| `eq_iff` | 689,317 | 383,321 | 1,317 `linear_equality`, 388 `linear_not_equals` |
| `ne` | 337,791 | 190,608 | 192 `linear_not_equals`, 189 `linear_equality` |
| `le` | 33,014 | 22,333 | **174 unhinted** |
| `le_iff` | 84,893 | 56,555 | **733 unhinted**, 48 `linear_inequality … cond` |
| `ge` | 12,338 | 7,119 | **203 unhinted** |

The rest of each proof is search (`backtrack`, `solx_block`). The core's own
final `a >= 1;` for an unsatisfiable instance is also unhinted, in these
lanes, and is not this family's.

## Status, gaps, and next steps

### Proof-logging gaps

**One attribution gap**: the inequality's bound pushes (rules 1, 3 and 4 for an
inequality) carry no hint, so in hints-only mode nothing names the constraint
that licenses them. Every inference is justified, nothing is asserted, and
no propagator changes strength when proofs are on.

### Known limitations

- **XCSP3 `<sum>` with `ne` gives wrong answers** when the bound or a variable
  operand escapes the auxiliary's range, and a wrong `UNSATISFIABLE` verifies
  (#1032).
- **`LinearEqualityIf` and `LinearNotEqualsIf` with a constant condition
  enforce the wrong constraint** (#1033). No front end reaches them.
- **`gcspy`'s `post_linear_greater_equal_iff` posts `≤`** (#1036). CPMpy does not
  call it.
- **Proofs on long sums are very large.** Every bound push names every term, so
  a 0.92 s `shortest_path` search writes 15 GB (#1035).
- **The default incremental threshold can be slower than stateless** by 2.2×
  on a model with many long reified inequalities (#1034). It is 1.6–3×
  faster where there are a few long sums.
- **A coefficient times a bound past `2⁶³` throws** an undiagnosed `Integer
  overflow` from inside propagation.
- **A reified equality waits for its last unfixed term** before deciding its
  condition, even when its bounds already exclude the value. This costs nothing
  measurable on the corpus.
- **No `If` forms from MiniZinc**, since `mznlib` declares no `*_imp`.

### Next steps

Ranked by what they buy for what they cost.

1. **#1032** — post `LinearNotEquals` for XCSP3's `sum ≠`, and add lanes for a
   negative bound and a variable operand. A wrong answer, a one-line fix.
2. **#1036** — post `LinearGreaterThanEqualIff`, and add Python tests for both
   linear `_iff` bindings. Trivial.
3. **#1033** — map constant conditions per form, or take an
   `IntegerVariableCondition` as every other family does. Small.
4. **#1035** — drop untouched bounds from the reason, and decide with a
   proofs consultant whether the `pol` can drop them too. The largest proof-size
   lever in the family, and on 0/1 sums likely an order of magnitude.
5. **Hint the inequality's bound pushes** with `hints::LinearInequality{owner}`,
   which already exists. Unfiled, and cheap. It is the only thing standing
   between rule 1 and `hinted` for an inequality. It is attribution, not a
   subhint, so it is outside the policy of waiting for the justifier to ask.
6. **#1034** — make the fold state fit in `std::any`, make slot copies cheap
   engine-wide, or allocate an `Iff`'s second direction lazily. Then re-measure
   `pattern-set-mining-k2`, `unit-commitment` and `vrp` together.
7. **Tests**: long sums (tens of terms, so folding and reasons have something to
   do), large coefficients, a constant condition on every form, and an
   inferences-level check that every assertion carries a hint. Unfiled.
8. **Tidying**, unfiled:
   - delete `propagate_linear`'s dead `pair<bool, SimpleIntegerVariableID>`
     branches, which never match `PositiveOrNegative`;
   - correct `infer_cond_when_undecided`'s comment about which forms reach it;
   - correct `LinearEqualityConsistency`'s comment, which names a level where
     the variant has a tag;
   - decide whether the equality's undecided branch should strip the sweep's
     idempotence claim, as the dispatcher does for the inequality;
   - fold `linear-slack-waking.md` into this document's commentary. That also
     means updating the comment in `propagate.cc` that cites it, so it waits for
     a non-docs change.
9. **A bounds check in the undecided reified equality.** Cheap, and it would
   remove the one-failure probe case, but the corpus shows no benefit. Record,
   don't prioritise.
10. **#868** — cross-solver, against Gecode's `linear` on the linear-only corpus
    models, which is the family's natural benchmark.

## Prior art

Bounds propagation for linear constraints is folklore; Harvey and Schimpf
(*Bounds consistency techniques for long linear constraints*, 2002) is the
usual reference for doing it in one pass, and for the incremental folding of
fixed terms. Slack-based watching is the pseudo-Boolean "watch enough to cover
the slack" scheme. `Tabulated` is GAC by enumeration, which is exact and
exponential. The proof side is JP 3.14 and 3.15 of McIlree's thesis, which
also sketches them from Gocht et al.'s earlier proof-logging work. What is new
here is small: the incremental propagator's fold, the deview mode, and dividing
by the changed variable's coefficient to close by RUP.

## Further reading

- [`linear-slack-waking.md`](../linear-slack-waking.md): the slack-waking design,
  why it ships off, and why an incremental cover does not help. Measured with
  `benchmarks/linear_slack_bench`, `slack_watch` and `wake_cost`. Due to be
  folded in here; see Next steps.
- [`justification-techniques.md`](../justification-techniques.md): why a
  general linear row is outside Theorem 2.9, and so needs JP 3.15.
- [`reification.md`](../reification.md) and the reified dispatcher's header:
  which forms infer what from each verdict.
- `subset-sum-strengthening.md` is *not* this family's. It is an
  `innards/proofs` helper that `knapsack` and `cumulative` use for tighter
  derived lines.

## Developer commentary

**The bugs were all outside the propagator.** The sweep has been heavily used
and heavily tuned, and the audit found nothing wrong in it. It found three
wrong answers in the code around it: a translation that predates the
constraint it should have used, a constant-literal mapping nobody posts, and
a binding nobody calls. Each survived because the tests post exactly the
shapes the propagator expects: variable conditions, small bounds, three
terms. A family this central is worth auditing at its edges more than at its
core.

**"Identical inferences" is a claim the tree can test cheaply.** The
stateless, incremental and slack-watched forms are all documented as making
the same inferences, and running them side by side on 23 corpus models,
comparing solution sequences, confirmed it in minutes. That made the CPU
comparison trustworthy. Without it, a 2× difference could have been a
different tree.

**The proof cost of a long linear constraint is its reasons.** At
`AssertionLevel::Inferences` there is no justification at all, and
`shortest_path`'s proof is still 9.8 GB. That is because each assertion
restates about 170 bound literals, nearly all of them trivially true. Trimming
justifications would not touch that; trimming reasons does both.
