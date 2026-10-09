# Linear: `Σ cᵢ·xᵢ` against a constant

> **Maturity** production ·
> **Audited** 2026-09-23 at `00797a97`; re-audited 2026-09-25 at `61112ed0`,
> for #1108 on 2026-09-26 at `c9ceea25`, and on 2026-10-08 at `0a5b4ec6` for
> #1035 (#1055) and the integer-range PRs (#1214, #1215, #1220) ·
> **Open issues** filed by this audit: #1034 (the incremental propagator's
> state is a heap allocation per slot per node), #1042 (the reified equality
> ignores its bounds), #1043 (tidying, items 4 and 5 left). Filed from review:
> #1091 (an equality's fixpoint can take a number of sweeps linear in the
> domain width). Filed from the 2026-10-08 re-audit: #1298 (every reified
> inequality throws on a partial sum or a maximum that only its undecided
> check computes). Already open and touching this family: #868 (cross-solver),
> #310 (a range-literal reification condition cannot be written into the
> model), and #1225, filed since by the integer-range audit (the same condition
> throws with proofs on). **Fixed since the audit**: #1032, #1033, #1035,
> #1036, #1043's first three items, and #1103 (filed from review: under
> `Tabulated`, a released form built a table); see
> [Re-audit, 2026-09-25](#re-audit-2026-09-25), [Re-audit,
> 2026-09-26](#re-audit-2026-09-26) and [Re-audit,
> 2026-10-08](#re-audit-2026-10-08). Tracked under #871.

### Re-audit, 2026-09-25

The audit's fixes merged on 2026-09-24. This pass brings the text into line
with them at `61112ed0`, and also takes in review corrections to claims the
first pass got wrong.

| Issue | Fixed by | What changed here |
|---|---|---|
| #1032, XCSP3 `<sum>` with `ne` | #1074 | the translation posts `LinearNotEquals` directly, so the frontend cell is ✓ and two new lanes cover the escaping shapes; the known limitation and next step are gone |
| #1033, constant-condition `If` forms | #1077 | a constant condition is resolved per form, and a false one on `If`/`NotIf` releases the constraint ([Semantics](#semantics)); `linear_constant_test` has a row for each form and constant |
| #1036, `gcspy`'s `≥` binding | #1073 | it posts `LinearGreaterThanEqualIff`, and `post_linear_less_equal_iff` is registered at last; Python tests exist, but CI does not run them |
| #1043, tidying | #1075, **items 1–3 only** | the dead `pair<bool, …>` branches are gone, and the two comments are corrected (rule 8, [Options](#options)); item 4 (the idempotence-claim disagreement) and item 5 (folding `linear-slack-waking.md` in) are still open |
| #1035, trivial reason literals | #1055, **open** at the time | nothing yet; done in [Re-audit, 2026-10-08](#re-audit-2026-10-08) |

**Corrected from review**, not from a fix:

- the equality's strength is `bounds(R)`, not `bounds(Z)`, and a single
  inequality's is `GAC` (rules 1 and 2);
- one call can take a number of sweeps linear in the width (#1091), so "every
  cost is in terms" holds per sweep, not per call;
- rule 3's assertion keeps the attempted bound;
- the inequality's unattributed assertions are `search`, not `solver-side`;
- a range-literal reification condition throws with proofs on (#310).

**What was measured again.** At `61112ed0`, only the new facts: the strength
probe and #1091's proof sizes (both in [Interval
efficiency](#interval-efficiency) and rule 1), rule 3's `a` line, and the
range-literal condition. The CPU and proof tables were **not** re-run. They
stay at `00797a97`. Since then two commits have touched the family's source:
#1077, which changes only how a constant condition is mapped at construction,
and #1075, whose PR reports byte-identical objects.

### Re-audit, 2026-09-26

One more fix to this family has merged, for an issue filed from review of the
first re-audit. This pass brings the text into line with it at `c9ceea25`.

| Issue | Fixed by | What changed here |
|---|---|---|
| #1103, a released form under `Tabulated` | #1108 | a released `If`/`NotIf` installs nothing under either arm: [Semantics](#semantics), the `Tabulated` row of the [propagator inventory](#propagator-inventory), rule 13's **Fires when**, and [Tests](#tests) |

**What was measured again.** Only the [Semantics](#semantics) probe, at
`c9ceea25`. No rule, encoding or proof line changed, and nothing else was
re-run.

### Re-audit, 2026-10-08

The audit's proof-size issue has been fixed, and the integer-range arc has
changed what this family accepts and how it sums. This pass brings the text
into line with both at `0a5b4ec6`.

| Issue | Fixed by | What changed here |
|---|---|---|
| #1035, trivial reason literals | #1055 | the bound pushes' reason leaves out a term at its declared bound when the term's bits imply that bound, when its boundary pin is already a unit, or, above `AssertionLevel::Links`, when it would have been pinned; the `pol`s leave out a bound the bits imply, no longer divide by the changed variable's coefficient, and are not emitted when no bound is added. The three things to know, Shared code, [Proof-time state](#proof-time-state), [Interval efficiency](#interval-efficiency) 2, the JP 3.15 departures, rules 1, 8 and 9, [Tests](#tests), [Benchmarks](#benchmarks-and-examples), [Proof performance](#proof-performance), [Known limitations](#known-limitations), Next step 1, [Prior art](#prior-art) and the [commentary](#developer-commentary) |
| — (the integer-range arc) | #1214, #1215, #1220 | inputs must lie in `±(2⁶⁰ − 1)`, and a coefficient or right-hand side outside it is refused at construction, as is a condition value past one above the top; the sweeps' running sums are exact 128-bit `WideSum`s, so there only a total that does not fit throws, but the reified inequality's undecided check still sums in `Integer`; the fold state is 24 bytes: [Robustness and limits](#robustness-and-limits), [Mutable state](#mutable-state-and-incrementality), [Tests](#tests), [Known limitations](#known-limitations), Next step 4 |
| — (#1200, #1206) | #1208 | 14 `…_view_mixed_late` lanes ([Tests](#tests)) |
| — (front-end integer range) | #1217 | four `lin_strict_*_edge` chain cases ([Cake conformity](#cake-conformity)) |

**Corrected from review**, not from a fix:

- recounting the first pass's own kept `Inferences` proofs, `le` has 173
  unhinted family assertions, not 174 (`ge`'s 203 and `le_iff`'s 733 stand);
- the propagator's overflow throw was already an `IntegerOverflow` (an
  `UnexpectedException` subclass) at `00797a97`, not a bare
  `UnexpectedException`.

**What was measured again.** At `0a5b4ec6`, Release, fataepyc-10 (boost off),
pinned with `taskset`, `GLIBC_TUNABLES` raising glibc's mmap and trim
thresholds: `2008_shortest_path` without proofs and at both assertion levels,
with VeriPB on both proofs; the `pol` and assertion statistics over the whole of
those proofs, and the same statistics over the whole of the first pass's kept
proofs (its figures were from the first 200 and 300 MB); the six test lanes'
proof lines at seed 1; `pattern-set-mining-k2` default against stateless, one
run each; rule 3's assertion; `2x − 2y = 1`'s proof lines; the overflow
shapes, including the partial-sum shape under every reified form and a
total past `2⁶³`; `generic_reason`'s literals on 0/1 variables; and the lane
count. **Not re-run**: the CPU table, the corpus share
survey, the rule counts, the caps, the strength brute force, the reified
equality's bounds-check experiment, and `2x − 2y + 3z = 1`. Those stay at
the commits they name.

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
  over a bit-sum encoding. So the cost of **one sweep** is proportional to the
  **number of terms**, never to domain width. That includes the proof: a bound
  push names every other term's bound except those already true at the top,
  because the bits imply them or the declared bound is pinned (above
  `AssertionLevel::Links`, would be) (#1055). Until then it named every term, which is how a 0.92 s
  `shortest_path` search wrote a 15 GB proof (#1035); it now writes 617 MB.
  **The number of sweeps is another matter**: an
  equality alternates two sweeps until one of them moves nothing, and on
  `2x − 2y = 1` over `0..N` that takes a number linear in `N`, inside one call
  (#1091). And with coefficients other than ±1 the equality's bounds are only
  `bounds(R)`: an endpoint can survive with no integer support.
- **The three wrong-answer bugs found here were all at the edges**, not in the
  propagator: an XCSP3 translation that predated `LinearNotEquals` (#1032), a
  constant-condition mapping that no front end reaches (#1033), and a Python
  binding that posted `≤` where its name says `≥` (#1036). All three are fixed.
- **The implementation choice matters more than any algorithm.** The stateless
  sweep and the incremental one find the same solutions in the same order, and
  each beats the other by up to 3× on some real model. The default, incremental
  from 8 terms up, loses 2.2× on one of them for a reason that is not linear's
  at all (#1034).

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
equality's take a full `innards::Literal`**, and a constant one is resolved per
form (`literal_to_reif`, since #1077; before that `If` and `NotIf` got it wrong,
#1033):

| Form | `TrueLiteral` | `FalseLiteral` |
|---|---|---|
| `EqualityIf` | `MustHold` | released |
| `NotEqualsIf` (stored as `NotIf`) | `MustNotHold` | released |
| `EqualityIff` | `MustHold` | `MustNotHold` |
| `NotEqualsIff` (stored as `Iff(¬c)`) | `MustNotHold` | `MustHold` |

The columns are the literal the **user** passed. `NotEqualsIff` negates it
before resolving, so its row is `Iff`'s with the columns swapped: a true
condition means the equality must *not* hold, as the name says.

`ReificationCondition` has no "no constraint" alternative, so a released form
is the same form over a condition that never holds, `0_c = 1`. It is written to
the `.scp` and the OPB as such, and its rows are vacuous. **No propagator is
installed under either arm**: `install_propagators` returns on a `Deactivated`
condition before it chooses between `BC` and `Tabulated` (#1108). So on
`x + y = 3` over `0..2`, both forms under both arms make zero propagations and
find all 9 assignments, and their proofs verify. The same early return covers
an `If`/`NotIf` whose condition literal is a variable's but already decided
false at install (for instance `c = 5` with `c ∈ 0..1`, or `c = 1` with `c`
fixed at 0): `test_reification_condition` reports it as `Deactivated` too,
so nothing is installed for it either (the `c ∈ 0..1` probe: 18 solutions,
zero propagators, proofs verify, both forms and arms). Measured at
`c9ceea25`. Until #1108 the `Tabulated` arm did not check, and built a table
over every tuple: 13 propagations on the same probe at `61112ed0`, with the
same answers, so wasted work rather than a bug (#1103).
`LinearNotEqualsIff(s, v, c)` is stored as `ReifiedLinearEquality` with
`Iff(¬c)` and a `flipped_cond` flag, which only changes its `.scp` spelling.

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
| `LinearNotEquals` | ✓ `int_lin_ne`; two-term becomes `NotEquals`[^mzntwo] | ✓ `sum` with `ne`, since #1074[^xne] | ? | ✓ `lin_not_equals` | |
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

[^xne]: `sum` with `ne` posts `LinearNotEquals` directly, with a variable
    operand moved onto the left as `Σ cᵢxᵢ − y ≠ 0`. Until #1074 it posted
    `sum + diff = bound` and `diff ≠ 0` over an auxiliary
    `diff ∈ [−range, range]`, a workaround from 2022 that predated
    `LinearNotEquals`. But `bound − sum` could exceed `range`, and a variable
    operand was not counted in `range` at all. So `x ∈ 0..5`, `x ≠ −3` found 3
    solutions of 6, and `x ∈ 0..2`, `x ≠ y` with `y ∈ 10..12` was reported
    `UNSATISFIABLE`, which the proof verified, since the mistranslation is
    upstream of the model the proof sees (#1032). Lanes
    `xcsp_sum_not_equals_negative` and `xcsp_sum_not_equals_var` cover both
    shapes now.

`gcspy` binds `LinearEquality`, `LinearNotEquals`, `LinearLessThanEqual`,
`LinearGreaterThanEqual`, `LinearEqualityIff`, `LinearLessThanEqualIff` and
`LinearGreaterThanEqualIff`. Until #1073 its `post_linear_greater_equal_iff`
posted `LinearLessThanEqualIff` (#1036), and `post_linear_less_equal_iff` had
no Python registration at all. `python/python_test.py` now tests all three
`_iff` bindings, but **no CI workflow runs that file**. CPMpy's upstream GCS
interface, checked 2026-09-23, calls none of the `_iff` bindings and posts
every linear constraint through the four plain ones.

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
`benchmarks/tabulated_linear_random` measures it. The header's comment on the
variant named a level where the variant has a tag until #1075; it now names
`consistency::Tabulated` and its cost. `BC` here is the tag: what the default
**achieves** is `bounds(R)` on an equality in general (rules 1 and 2).

`ReifiedLinearInequality` has no `with_consistency()`.

**The incremental threshold**, `with_incremental_threshold()` on the equality
and a constructor argument on the inequality, defaulting to
`GCS_LINEAR_INCREMENTAL_THRESHOLD` or 8. At or above it, a direction the
dispatcher can reach gets a backtrackable fold state and the incremental
propagator, which folds fixed terms out of the sum. Below it, the stateless
sweep runs. The two are designed to make identical inferences, so this picks
a strategy and never a model. What has been checked is weaker: identical
solution sequences on 23 corpus models ([CPU performance](#cpu-performance)). What it costs either way is under [CPU
performance](#cpu-performance) and #1034.

**Slack-based waking**, `GCS_LINEAR_SLACK_WATCH_THRESHOLD` (default: off) and
`GCS_LINEAR_SLACK_WATCH_COVER_PERCENT` (default 15). This is for an inequality
whose direction is decided at install, is long enough, and has a small
covering set. It wakes only when a covering term's contributing bound moves,
through refined watches, instead of on every bound. It is designed to make
identical inferences again, and the lanes that force it on pass and verify.
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
wrap the terms in views. Because the family's facts about its **terms** are all
bounds, it is outside #882's range-literal problem by construction. Its
**reification condition** is not: see [Reification](#reification).

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
corpus (#1042).

**A range-literal condition works without proofs and throws with them.** Both
classes accept an `in_range(b, lo, hi)` condition: an `IntegerVariableCondition`
for the inequality, and inside an `innards::Literal` for the equality. With
proofs off, `LinearEqualityIff(x + y, 2, in_range(b, 1, 3))` over
`x, y ∈ 0..2`, `b ∈ 0..4` enumerates the right 21 solutions, and
`LinearLessThanEqualIff` the right 24. With proofs on, both throw `range
literals during model writing are not yet supported` from
`NamesAndIDsTracker::need_invar` when the model is written (#310). Measured at
`61112ed0`. No front end posts one.

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
- `justify_linear_contrapositive` is used only by the gated stages. #1055's
  trimming reaches the stages through both helpers: their `pol`s leave out
  bounds the bits imply, and the sweep's reasons leave out bounds already at
  the top. `arithmetic.md` follows it.
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
| `lin_strict_{lt,gt}_edge_sat`, `lin_strict_lt_edge_unsat` (since #1217) | `strict` |
| `lin_equals_iff_sat`, `lin_less_equal_iff_sat`, `lin_strict_lt_edge_iff_sat` (since #1217) | `none` |

Fifteen of the eighteen are byte-for-byte label matches with cake. The three
reified cases are chain-only. The four `lin_strict_*_edge` cases are `.scp`
strict inequalities (`lin_less_than`, `lin_greater_than`, `lin_less_than_iff`)
at the ends of the bounded range, where the reader moves the integer step into
the sum as a constant (`verified_encodings/scp_cases/CMakeLists.txt:53-60`,
`:370`). No
lane covers `If`, `NotIf` or a reified not-equals.

### Proof-time state

- Everything the justifications cite is in the OPB. Nothing is emitted at the
  root, and every justification line is `ProofLevel::Temporary`.
- **Order literals are introduced lazily**, one per bound a justification or
  reason names, by the names-and-IDs tracker (the `red` lines in a proof). On a
  long sum that is every other term's current bound that its bits do not
  imply, at every bound push: a bound the bits imply, such as a 0/1
  variable's `≥ 0`, is named by neither the push's `pol` nor its reason, so
  the bound pushes never introduce it (#1055). Before #1055 they named every
  term's current bound (#1035). **The other rules were not trimmed**: the
  not-equals (rules 6 and 7, `propagate.cc:690`, `:704`) and the reified
  forms' undecided verdicts (rules 8–12, `linear_inequality.cc:305`,
  `linear_equality.cc:451`) use `generic_reason` over every variable, so on
  four 0/1 variables `LinearNotEquals` and `LinearEqualityIff` still
  introduce and cite `x ≥ 0` (measured at `0a5b4ec6`).
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
| `Tabulated` | `install_tabulation`'s | the extensional family's | 13 | `with_consistency(Tabulated{})`, unless the form is released (#1108) | as `table.md` | as `table.md` |

**Idempotence.** The stateless and incremental sweeps claim it, and the claim
is argued in `propagate_linear`. The forward sweep writes only upper bounds of
positive-coefficient terms and lower bounds of negative ones, and reads only
the other side. So reads and writes are disjoint per variable, and a single
pass is the `≤` fixpoint, even across a write that snaps past a hole. The
equality alternates the forward and inverse sweeps until one is clean, which
reaches its own fixpoint in one call, **however many sweeps that takes**: on
`2x − 2y = 1` it is a number linear in the width (#1091). The test harness
turns on `GCS_CHECK_IDEMPOTENT_CLAIMS`, which re-runs every honoured claim and
aborts if it infers anything. Since #1086 that holds in every harness binary.
Before it, 100 lanes ran with the checker silently off (#1056), but
`linear_test` was not among them. #1086's forced-on sweeps over the suite, 1,821
MiniZinc and 6,178 XCSP3 instances found no false claim. The slack-watched form
cannot claim it, since a coarse re-wake would defeat the watches.

**The two reified classes disagree about passing the claim on.** When the
condition is undecided at install, the shared dispatcher strips an enforced
sweep's `EnableButIdempotent`, because a re-run also re-tests the condition and
"nobody has audited that interplay yet". The equality's hand-written undecided
branch returns the sweep's claim unchanged once the condition is decided true.
The harness's re-run check has not caught a problem in the `eq_if` and
`eq_iff` lanes, but the two classes should agree (#1043, item 4); see [Next
steps](#next-steps).

**Holes affect.** Two arms observe holes. The undecided reified equality asks,
once one term is left, whether the value that would satisfy the equality is in
its domain (rule 11), and its `on_change` triggers are the truth. The
`Tabulated` arm is the extensional family's propagator, which is GAC and so
reads every value. The not-equals acts only on fixed values. The enforced
sweeps read only bounds and are triggered `on_bounds`, and the undecided
reified inequality decides its condition from the minimum and maximum sums
(rules 8 and 9), which are bounds too. So **an enforced inequality or `BC`
equality, and a reified inequality whether decided or not,** is never a reason
for another constraint's interior pruning to stay on, and nor is a
not-equals. An undecided reified
equality or a `Tabulated` one can be: an interior removal can decide the first's
condition, and can cost the second a support. The slack-watched form declares
its bounds-only reading explicitly, because `scope_only` would otherwise read as
"holes affect everything".

### Mutable state and incrementality

**Backtrackable**: `LinearIncrementalState {n_active, fixed_lower}`, one per
reachable direction at or above the threshold. The engine copies it at every
search node, as a heap allocation, because it exceeds `std::any`'s in-place
storage (#1034). It is 24 bytes since #1220 made `fixed_lower` an exact
128-bit `WideSum` (`propagate.hh:94-100`); it was 16.

**Not backtrackable, and sound**: the incremental propagator's `active`
permutation. A fold swaps a newly fixed term to the end of the active prefix
and decrements `n_active`. Swaps stay inside the current prefix, so every
earlier level's prefix keeps the same *set* of terms, in a different order.
Backtracking restores `n_active`, and the sweep does not depend on order. The
propagator keeps at least one term active, so a fully fixed, violated
assignment still reaches a check.

**Recomputed per call.** The stateless sweep re-reads every term's bounds into
a `small_vector` (inline up to 8 terms) and recomputes the minimum sum. That is
`O(n)` per **sweep**, and one sweep per call for an inequality. An equality's
call runs sweeps until one is clean. How many that usually is has not been
measured. It can be a number linear in the width (#1091), so its per-call cost
is `O(n)` times that.
The incremental sweep does the same over the active terms only, and has the
same loop. The slack form re-sorts the potentials after every clean wake, which is
`O(n log n)`. The design note records why an incremental cover does not help.

### Interior values and optional pruning

**What this family offers:** `None.` No class installs a pair, or accepts
`consistency::Auto`.

**What this family observes:** bounds, stated in those words, for the enforced
sweeps and the undecided reified inequality; fixed values only, for the
not-equals. The exceptions are the undecided reified equality, whose last-value
rule reads a hole, and the `Tabulated` arm, which reads every value. A variable
that appears only in enforced sweeps, reified inequalities and not-equals lets
any neighbour's optional interior pruning be dropped. One in an
undecided reified equality or a `Tabulated` equality does not.

### Robustness and limits

- **Unbounded domains**: no width limit, since everything is bounds and
  `BinEnc`. Since #1214 a declared domain must lie in `±(2⁶⁰ − 1)`
  (`Integer::max_bounded_value()`; it was about `2⁶¹`), and a view's values
  reach one bit further. That is the solver's rule, not the family's.
- **Inputs outside that range are refused at construction** (#1215):
  `require_bounded` checks every coefficient, the right-hand side and the
  condition's value (`linear_equality.cc:161-163`,
  `linear_inequality.cc:56-58`). A coefficient of `2⁶⁰` throws `IntegerOverflow`
  ("a coefficient of a linear constraint is 1152921504606846976, which is
  outside the supported range"), as does a right-hand side of `2⁶¹`.
- **Running sums are exact** since #1220: the lower and inverse sums, the
  incremental `fixed_lower`, `tidy_up_linear`'s constant, the not-equals and
  undecided-equality accumulators, `Tabulated`'s callbacks and the slack cover
  are 128-bit `WideSum`s, and there only a total that does not fit throws.
  Before it, nine terms at the top of the range and nine at the bottom, summed
  in that order, threw though their total was 0. **One sum was missed**: the
  reified inequality's undecided check still sums its minimum and maximum in
  plain `Integer` (`linear_inequality.cc:308-318`), though both are only
  compared with the right-hand side (`:321`, `:335`), so a 128-bit sum would
  decide without narrowing. #1220's own shape, nine terms fixed at the top
  and nine at the bottom with `z ∈ −2..2` and `sum ≤ 0`, has 3 solutions
  under `LinearLessThanEqual`, but with proofs off every reified inequality
  form throws: `LinearLessThanEqualIff`, `…If` and a `NotIf` with `Integer
  overflow: 9223372036854775800 += 1152921504606846975`, and
  `LinearGreaterThanEqualIff` and `…If` with the mirror. `LinearEqualityIff`
  on the same shape solves. The same accumulator throws on a maximum past
  `2⁶³` that only the comparison needs: `LinearLessThanEqualIff` with two
  terms of coefficient `2⁴⁰` over `0..2²²` throws `Integer overflow:
  4611686018427387904 += 4611686018427387904` (`:313`). All measured at
  `0a5b4ec6`. Under `integer-ranges.md` that is a bug: a throw on a value
  nothing needs. With proofs on, these reified forms throw the model writer's
  "cannot size the reification constant" first, which is allowed. Filed as
  #1298. Solving `c·x = r` uses
  `WideSum::divided_exactly_by`. The per-term remainder arithmetic is
  unchanged: saturating it would be unsound.
- **Overflow**: coefficient × bound products are checked `Integer` arithmetic
  and **throw** `IntegerOverflow` on overflow; they never wrap. Measured at
  `0a5b4ec6`: with coefficients of `2⁴⁰` and bounds of `2²⁹` to `2³⁰`, the
  forward sweep throws `Integer overflow: 1099511627776 * 536870912` (one
  term's least contribution is `2⁶⁹`); so do the reified inequality's
  undecided check (its maximum sum) and an equality with a negative
  coefficient, whose forward sweep multiplies it by an upper bound. With
  proofs on, the model writer refuses those rows first, before search, with an
  `IntegerOverflow` that says which quantities may be to blame (#852).
  **A total past `2⁶³` throws too**, even when every product fits: two terms
  of coefficient `2⁴⁰` over `[2²², 2²² + 1]` make the `≤` and the equality
  throw `a sum does not fit in an Integer` (`WideSum::narrow_or_throw`, from
  the lower sum, `propagate.cc:260`), and with proofs on that throw still
  comes from the propagator, not the writer. Over `0..2²²` the `≤` and the
  equality solve. **The propagator's throws name no constraint**, and a
  total's names no product either. A sweep's product or lower sum past `2⁶³`
  is a value the sweep needs, so under `integer-ranges.md` it is a limit an
  arithmetic constraint may have, not a bug; the reified inequality's
  undecided sums above are the exception.
- **Negative values and zero**: negative coefficients are first-class
  throughout, and the chain has negative-coefficient and sign-bit lanes. A
  zero coefficient is dropped by `tidy_up_linear`.
- **Degenerate shapes**: an empty sum is a constant check (rules 4 and 5).
  `linear_constant_test` posts empty equality and not-equals sums; the
  inequality's empty sum is one data row in `linear_test`. A single term is an ordinary sweep. A
  repeated variable is merged, so `x − x ≤ 3` is empty. A constant term moves
  to the right-hand side. A two-term `±1` constraint from MiniZinc never
  arrives here (it becomes `Equals`, `NotEquals` or `LessThanEqual`).
- **A constant condition** on the equality's reified forms: resolved per form
  since #1077 ([Semantics](#semantics)); before that, `If` and `NotIf` gave
  wrong answers (#1033).
- **A range-literal condition**: right without proofs, throws with them
  (#310; [Reification](#reification)).

### Interval efficiency

`Fine at any width` **per sweep**, on all four questions, for the default
arms, and fine per call for the inequality and the not-equals. **Not per call
for the equality**: its fixpoint loop can run a number of sweeps linear in the
width (#1091).

1. **Propagation.** The sweeps read and write bounds only. The not-equals asks
   `in_domain` for one value, once. The undecided equality asks `in_domain` for
   one value on its last unset term. Nothing in `propagate.cc`,
   `linear_equality.cc` or `linear_inequality.cc` walks a domain's values.
   That can be checked by reading. The `Tabulated` arm enumerates tuples, which
   is the product of the domain sizes and is what its tag means. **But width
   can still set the number of sweeps.** The equality alternates the forward
   and inverse sweeps until one is clean. On `2x − 2y = 1` over distinct
   `x, y ∈ 0..N`, each sweep moves each bound by one step, and the loop runs
   until a domain empties: one propagator call, one recursion, a number of
   sweeps linear in `N`, in both the stateless and incremental arms. The
   answer is right; the time is width's. What decides it is **the terms still
   unfixed when the call runs**, and their domains, not the constraint as
   posted. At `61112ed0`, proof lines grow tenfold from `N = 100` to
   `N = 1000`, each in one propagation, on:
   - `2x − 2y = 1`, `3x − 3y = 1`, `2x − 4y = 1` and `6x − 4y = 1`, over
     `x, y ∈ 0..N`;
   - `2x + 2y = 1` with `x ∈ 0..N` and `y ∈ −N..0`, so it is not about the
     signs of the coefficients either.

   It also happens partway through search, on a constraint whose gcd is fine
   at install. `2x − 2y + 3z = 1` with `z ∈ 0..1` has overall gcd 1. Branching
   on `z` first, the call after `z = 0` faces `2x − 2y = 1`: 2,473 lines at
   `N = 100` and 24,073 at `N = 1000`, to the first solution, in four
   propagations. Lines do not grow on `2x + 4y = 1` over `0..N`, where the
   first inverse sweep empties a domain. Nor do they grow to the **first
   solution** of `3x − 2y = 0` or `3x − 2y = 1`. A full enumeration of
   `3x − 2y = 0` grows 2,633 → 26,033 lines, but with 34 → 334 solutions, so
   that growth is the solutions', not the sweeps'. Normalising a call's unfixed
   terms by their gcd would settle every slow shape above. It would not show
   that every equality converges in a width-independent number of sweeps, and
   nobody has argued that one does.
2. **Reasons.** At most one bound literal per term, never per value, and
   assembly is guarded on `want_reasons()`, so plain search pays nothing.
   Since #1055 a bound push leaves out a term still at its declared bound
   when its bits imply that bound, when its boundary pin is already a unit, or,
   above `AssertionLevel::Links`, when it would have been pinned
   (`order_literal_holds_at_top`, `propagate.cc:65-106`). The not-equals and
   the reified forms' undecided verdicts still name every variable's domain
   (`generic_reason`). Before #1055, every
   term's bound went in, and the reasons' problem was that **triviality**,
   not width (#1035).
3. **Proofs.** Order literals over `BinEnc`, one `pol` per bound push with one
   term per variable. Width enters each push only through the logarithmic bit
   count, and there is no per-value form, so no width gate. **The number of
   pushes is where width gets in**, through the sweep count above: at
   `0a5b4ec6`, `2x − 2y = 1` writes 2,408 proof lines at `N = 100` and 24,008
   at `N = 1000` (2,420 and 24,020 at `61112ed0`, before #1055), in one
   propagation. The `N = 100` proof verifies
   (`veripb --force-checked-deletion`).
4. **The audit lane**: `LinearEquality`, `ReifiedLinearEquality` and
   `ReifiedLinearInequality` are all `Clean`, and there is no proof-size row.
   **Axes they do not vary**: coefficients other than ±1 (so no overflow and
   no rounding), holes (irrelevant to the sweeps, but rule 11 reads them), the
   not-equals, the `Tabulated` arm, and the incremental versus stateless
   choice. The `Tabulated` arm would trip, by design. **So would an equality
   whose unfixed terms' gcd does not divide what is left of `v`**, over wide
   variables, such as `2x − 2y = 1`, or `2x − 2y + 3z = 1` once `z` is fixed
   (#1091). No row has that shape, and it is the one that shows the sweep
   count growing with width.

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
lines: 173 of them in `linear_constraint_le`'s proofs at seed 1, and 203 in
`ge`'s. `hints::LinearInequality` exists, and is used only as the base of the
`cond` hint. **None of the five earlier family documents records an
unattributed assertion.** An external justifier has to find the row that licenses one by
searching the model's inequalities for one whose scope covers the clause's
variables and whose JP 3.15 step yields the clause. The row is in the model, so
this is a search, not missing information: the verdict is `search`, not
`solver-side`.

**What licenses them.** Rules 1–3 are **JP 3.15 (linear inequality
propagation)** and its infeasibility case, from McIlree's thesis. The rest are
single RUPs against the encoding, or ours, as each entry says. Our JP 3.15
departs from the thesis in four ways:

- it closes by RUP on the undivided sum, where the thesis closes by syntactic
  implication. Until #1055 it divided the summed line by the changed
  variable's coefficient first; once the other terms cancel, dividing buys
  unit propagation nothing, and with bits left in the sum, rounding them up
  would lose the RUP (`justify.cc:52-62`);
- **it leaves out a bound the term's own bits imply**, such as a 0/1
  variable's `≥ 0`, and leaves that term's bits in the line instead
  (`bit_sum_implies`, `justify.cc:45`). Left unassigned, they add as much to
  the line's maximum as to its degree, so the RUP's slack is never more than
  with the bound added. The thesis's procedure names every other term's bound,
  and so did ours until #1055 (#1035);
- deview mode substitutes each view's underlying variable's bits;
- the equality's inverse direction cites the `ge` row where the forward cites
  `le`.

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
- **Strength** — for an **inequality**, `GAC`: for `cⱼ > 0`, every value
  `w ≤ ubⱼ` left in `D(xⱼ)` has `cⱼw ≤ cⱼ·ubⱼ ≤ v − L₋ⱼ`, so it is supported by
  every other term taking its contributing bound, which is a value in its
  domain (the mirror for `cⱼ < 0`). For an **equality**, with
  rule 2, **`bounds(R)`** on every term, and `bounds(Z)` on a term whenever
  every *other* term's coefficient is ±1, since a sum of unit-coefficient
  integer intervals takes every integer in its range. That condition is
  sufficient, not necessary. With other coefficients an endpoint can have a
  real support and no integer one: `2x + 3y + 3z = 4` over `x ∈ 0..2`,
  `y, z ∈ 0..1` is a fixed point, and its one solution is `(2, 0, 0)`, so
  `x = 0`, `y = 1` and `z = 1` survive unsupported. Checked at `61112ed0` by
  brute force at the root fixpoint of random three-term instances, holes
  included: no value left in an inequality's domains lacked a support (38,881
  values at 3,644 root fixpoints). An equality's never lacked a `bounds(R)` one (1,972 with
  coefficients up to ±4, 2,164 all ±1), nor a `bounds(Z)` one when the other
  coefficients were ±1 (13,644 endpoints). Without holes, 491 of 1,290 general
  instances had an endpoint with no integer support.
- **Algorithm** — one pass: the minimum sum from each term's contributing
  bound, then each term's slack against it. `O(n)` in **terms**. The forward
  sweep's writes never touch what it reads, so one pass is its fixpoint. The
  incremental form does the same over the unfixed terms only. **An equality
  repeats** rules 1 and 2 until one sweep is clean, and the number of repeats
  can be linear in the domain width (#1091; see [Interval
  efficiency](#interval-efficiency)).
- **Why it is true** — the others contribute at least `L₋ⱼ` whatever they
  take, so `cⱼxⱼ ≤ v − L₋ⱼ`; divide, rounding towards the feasible side.
- **Proof technique** — `pol` then `RUP`, by **JP 3.15**, with the departures
  above. The row, plus `|cᵢ|` times each other term's bound literal
  (`add_for_literal`), skipping a bound the term's bits imply; no division
  since #1055, and no `pol` at all when nothing was added, because the RUP can
  use the row as it stands (`justify.cc:14-63`). Precondition: every bound the
  `pol` adds is the one the minimum sum used.
- **Reason** — every other term's contributing bound, and the reification
  condition for a reified form, except that a term still at its declared bound
  is left out when its bits imply the bound or its boundary pin is already a
  unit (#1055); above `AssertionLevel::Links`, where no pins are written, also
  when it would have been pinned (`names_and_ids_tracker.cc:791-830`). That is
  safe only because this RUP lists no antecedent lines and nothing cites its
  line
  (`propagate.cc:74-82`). Before #1055 every term went in
  (#1035). **Still not minimal**: a term whose bound has moved goes in
  whether or not the push needs it. At most one literal per term. Guarded on
  `want_reasons()`.
- **Assertion** — the new bound literal, `∨ ¬reason`.
- **Hint** — `hints::LinearEquality` for an equality, none for an inequality.
- **Offline reconstructibility** — `hinted` for an equality: the constraint id
  names the row, and the reason, with the declared bounds of the terms it
  leaves out, gives every bound JP 3.15 needs.
  **`search` for an inequality.** Nothing names the constraint, but the row is
  in the model. A reconstructor finds it by searching the inequalities whose
  scope covers the clause's variables, and runs JP 3.15 against each candidate
  until one yields the clause. It does not have to find the row the solver
  used: any row that licenses the clause will do. The cost is the candidates
  tried. A hint (Next step 3) would make it `hinted` and save that search. It
  would not supply anything that is missing.
- **Proof size** — at most one `pol`, over the row and up to `n − 1` bound
  definitions, one RUP, and a definition for each bound literal not yet
  introduced. In **terms**, never width, **per push**. The number of pushes an
  equality's call makes can grow with width (#1091). On `2008_shortest_path`,
  whose objective sum has about 215 terms, the `pol`s average 21.4 fields over
  the whole `Off` proof at `0a5b4ec6`, against 742.8 at `00797a97`, before
  #1055 (the first pass's 656 was its first 200 MB).
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: linear-inverse-bound

(Rule 2.)

- **Infers** — the mirror of rule 1 from the `≥` half of an equality.
- **Fires when** — an equality's inverse sweep, alternated with the forward one
  until either is clean.
- **Strength** — `bounds(R)` with rule 1, and `bounds(Z)` under rule 1's
  unit-coefficient condition.
- **Algorithm** — as rule 1, on the negated sum, alternated with it until one
  is clean: a number of rounds that can be linear in the width (#1091).
- **Why it is true** — as rule 1.
- **Proof technique** — as rule 1, citing the `ge` row.
- **Reason, Assertion, Hint, Proof size** — as rule 1. The hint is always
  `hints::LinearEquality`.
- **Offline reconstructibility** — `hinted`.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: linear-bound-conflict

(Rule 3.)

- **Infers** — rule 1's or rule 2's bound, when that bound is already false,
  so the domain would empty. Not an explicit `contradiction()`: an ordinary
  inference whose literal is already false.
- **Fires when** — the tracker's `_or_stop` inference fails. The propagator
  stops reading `state` and returns.
- **Strength** — as rules 1 and 2.
- **Algorithm** — none beyond rules 1 and 2.
- **Why it is true** — the other terms' minimum already exceeds what this
  term's remaining values allow: the thesis's infeasibility argument (JP 3.14).
- **Proof technique** — as rule 1: the same `pol`, and the same RUP of the
  attempted bound under the reason. The conflict itself is closed afterwards,
  by the backtrack's own line, and is not part of this rule.
- **Reason, Hint** — as rule 1. The reason names the *other* terms' bounds
  only, as rule 1's does, so on its own it does not contradict the constraint.
  The attempted bound is what meets the changed term's opposing bound.
- **Assertion** — `attempted bound ∨ ¬reason`, the same shape as rule 1's, **not**
  `¬reason`. With `x, y ∈ 0..10`, `x = 3` and `y = 1` posted by `Equals`, and
  `x + y = 3`, the assertion at `AssertionLevel::Inferences` is
  `a 1 ~i[x][ge3] 1 ~i[y][ge1] >= 1`, that is `x < 3 ∨ y < 1`, and a separate
  backtrack assertion follows (measured at `61112ed0`, and the same at
  `0a5b4ec6`; the `Off` proof verifies `UNSATISFIABLE`). Compare rules 4, 5
  and 7, which really do assert
  `¬reason`: rule 4 calls `contradiction()`, rule 7 `contradiction_or_stop()`,
  and rule 5 infers `FalseLiteral`.
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
  `v + modifier ≠ 0`, or `MustNotHold` with `v + modifier = 0`. A form released
  by a false constant condition (#1077) is neither, and never reaches it.
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
  row plus every term's contributing bound, except one the term's bits imply,
  and no `pol` when nothing is added (#1055; `linear_inequality.cc:68-93`). It
  is JP 3.15's shape with the condition left over. It reads `state`. `If` reaches this rule as well as
  `Iff` (`linear_constraint_le_if` does 22 times at seed 1), and it licenses
  `¬c` (`set_not_cond_if_must_not_hold`), citing its own row. The comment
  above the verdict said otherwise until #1075 corrected it; the code was
  always right.
- **Reason** — `generic_reason` over the scope, built once at install.
- **Assertion** — `¬c ∨ ¬reason`.
- **Hint** — `hints::LinearInequalityCond`: `originator`, plus the sanitised
  terms, the rows and a pointer to `state` for the emitter. Wire:
  `(constraint_id N) (subhint cond)`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — at most one `pol`, over the row and up to `n` bound
  definitions, and one RUP.
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
  and changed no solution. `l2p`, which finishes, searched 119,187 nodes
  either way.
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
- **Fires when** — `with_consistency(consistency::Tabulated{})` on an equality,
  unless the form is released (#1108).
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
| `linear_constraint_{eq,ne,le,ge,le_not}` × `{incremental,stateless}` and their `_if`/`_iff`/`_notif` forms | `linear_test`, random instances of three terms, enumeration against brute force. Consistency is checked only for single-constraint instances: `bounds(Z)` on each term for the inequalities, weaker than the `GAC` they reach (`GAC` for not-equals), **never for `LinearEquality`**, whose `bounds(R)` would not pass a `bounds(Z)` check, and never for the reified equality and not-equals forms; `GAC` for the `Tabulated` rows. Since #1220, also a partial-sum case for `eq` (and its `Tabulated` arm), `ne`, `le` and `ge`, at the default threshold and at 0: nine terms fixed at the top of the range and nine at the bottom, then one free over `−2..2`, so a running sum in term order passes `2⁶³` though the total is small (`linear_test.cc:335-400`); with proofs, except for `ne`, whose half-reified rows cannot hold nine such coefficients |
| `linear_constraint_*_view_mixed` (14) | the same with the terms wrapped in views |
| `linear_constraint_*_view_mixed_late` (14) | the same, with every view registered by a constraint posted after the one under test (#1208) |
| `linear_constraint_*_slack` (8) | the inequality forms with slack waking forced on at any length and any cover |
| `linear_constant_constraint_{incremental,stateless}` | constant and empty sums, and since #1077 every equality form (`If`, `Iff`, `NotEqualsIf`, `NotEqualsIff`) with a `TrueLiteral` and a `FalseLiteral` condition, checking the exact solution set under `BC` and `Tabulated`, with proofs; and since #1108, for a `FalseLiteral` condition only and without proofs, that a released `If`/`NotIf` installs no propagator and makes no propagations under either arm (9 solutions, by `Stats`) |
| `xcsp_sum_not_equals`, `…_negative`, `…_var` | XCSP3 `<sum>` with `ne`, the last two added by #1074 for a negative bound and a variable operand |
| `mini_linear_constraint` | a private refined-watch test harness (`MiniLinearGreaterEqual`); posts nothing from this family |
| `linear_utils_test` | `tidy_up_linear` |
| `scp_chain_lin_*` (18) | see [Cake conformity](#cake-conformity) |
| `minizinc-two-term-lin-{eq,ne,le,le-difference-logic}` | the two-term recovery |
| `rcpsp_deadline`, `rcpsp_mm_deadline` | linear rows as makespan deadlines |

VeriPB runs in every data-driven lane when it is on the path. Every lane is
seeded. The incremental/stateless split is by `GCS_LINEAR_INCREMENTAL_THRESHOLD`
in the lane's environment, and the slack lanes set
`GCS_LINEAR_SLACK_WATCH_THRESHOLD=0` and `…_COVER_PERCENT=100`. All 74 pass at
`00797a97`. At `0a5b4ec6` the list above is 95 lanes, counted from the build's
CTest files; they were not run as a suite for that re-audit.

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

- **The equality's strength.** Nothing checks what it achieves, so nothing
  would notice a change in either direction. The counterexample under rule 1
  (`2x + 3y + 3z = 4`, `x ∈ 0..2`, `y, z ∈ 0..1`, a fixed point with one
  solution) would pin `bounds(R)` as a regression row. Unfiled.
- **An equality whose unfixed terms' gcd does not divide what is left of
  `v`**, on wide domains, where the sweep count grows with width (#1091),
  including one that reaches that state only after a branch fixes a term.
- **A range-literal reification condition**, which throws with proofs on
  (#310). No lane posts one.
- **The `gcspy` linear `_iff` bindings in CI.** `python/python_test.py` tests
  all three since #1073, but no workflow runs it, and its `add_test` in
  `python/CMakeLists.txt` is commented out.
- (No longer uncovered: a constant condition, since #1077, and an XCSP3 `<sum>`
  with `ne` that escapes the old auxiliary's range, since #1074.)
- **Coefficients other than small ones**: every random instance uses
  coefficients within a few units, and the partial-sum case uses unit ones, so
  nothing exercises a coefficient-times-bound overflow, the rounding of rule
  1's division by a large coefficient, or rule 12's divisibility.
- **Partial sums in the reified forms.** #1220's partial-sum case covers
  `eq`, `ne`, `le` and `ge`, but no `If`, `NotIf` or `Iff` form, which is why nothing
  caught the reified inequality's undecided check still summing in `Integer`
  (#1298; [Robustness and limits](#robustness-and-limits)).
- **Long sums.** Every random `linear_test` instance has three terms; the
  partial-sum case has nineteen, all but one fixed from the start. So the
  incremental propagator's folding is exercised on three terms at threshold 0,
  and the slack path only by forcing it. Every random instance's reason is
  short, which is why nothing in the suite noticed #1035. #1055's mutations
  show that the suite does exercise the trimming (dropping every reason
  literal fails 164 tests, every `pol` bound 99, per its body), but **nothing
  pins its pin condition**: a mutation that drops a declared-bound literal
  without a pin also passed the whole suite.
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
  by 1.9–3× or loses by 2.2× (at `00797a97`; the loss was 2.3× at
  `0a5b4ec6`), and they give the same solution sequences under
  every configuration. `shortest_path` 2008 finishes in under a second.
- **For proofs**: `shortest_path` 2008 is the smallest linear-dominated model
  that finishes. Since #1055 its `Off` proof is 617 MB and VeriPB verifies it
  in 261 s. At `00797a97` it was 15 GB; the first pass stopped VeriPB at 707 s,
  and #1055's run verified it in about 880 s (indicative: 48 checks in
  parallel). #1055's body also has larger linear-heavy models at fixed work,
  among them `vrp` 2011 (2,953.5 → 1,021.1 MB) and `unit-commitment` 2023
  (2,880.9 → 1,005.0 MB), every proof verifying, five of them only at a
  smaller K after hitting its 3600 s VeriPB cap in both arms.

### CPU performance

All at `00797a97`, Release, GCC 15.2.0, fataepyc-09 (EPYC 7643, boost off),
pinned, 2026-09-23, one run each unless stated.

**Where the family is the cost.** Share of propagation time over the whole
corpus (10 s each, `GCS_PROPAGATOR_STATS=time`): linear appears in 250 models,
with a median share of 8.4%, and at least 50% in 44 of them.

**The implementation, measured.** Nodes in 30 s under four configurations.
Solution sequences are identical in every row, and the one model that finishes
under all four (`shortest_path` 2008) searches 42,437 nodes in each. The trees
were not compared node by node.

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
  long `Iff` inequalities gets two (#1034). **Re-checked at `0a5b4ec6`**,
  after #1113's epoch reuse and #1220's wider fold state, one run each:
  stateless finishes 440,699 nodes in 25.6 s, and the default reaches 225,101
  in 30 s with the same 38 solutions in the same order, about 2.3× slower per
  node. The `perf` profile was not re-taken.
- **Slack waking at 128 terms changes nothing** measurable on any model: the
  corpus has almost no constraint that long and loose. That is consistent with
  it shipping off.

**The reified equality's missing bounds check**: a local experiment adding it
fired 13.9 million times on `grid-colouring` 2011 and 5.7 million on
`diameterc-mst`, and changed no solution anywhere. `l2p` searched 119,187 nodes
either way. So its absence costs nothing measurable here.

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
`0..6,778` whose defining equality has about 215 terms; all solutions, 42,437
nodes, 3 solutions, and conclusion `BOUNDS 88 88` in both proof rows. At `0a5b4ec6`,
fataepyc-10, pinned, one run each; VeriPB 3.0.2 with
`--force-checked-deletion`, serially on one core:

| | solve | proof | VeriPB |
|---|---|---|---|
| proofs off | 0.78 s | — | — |
| `AssertionLevel::Off` | 13.6 s | 7,340,846 lines, 617 MB | 261 s, `VERIFIED` |
| `AssertionLevel::Inferences` | 6.9 s | 1,960,330 lines, 474 MB | 8.9 s, `UNDER ASSERTIONS` |

At `00797a97`, before #1055, on fataepyc-09: 0.92 s without proofs; `Off`
106.2 s, 7,343,416 lines, 14.97 GB, VeriPB not finished after 707 s;
`Inferences` 44.1 s, 1,960,330 lines, 9.76 GB, VeriPB 191 s. So #1055 left the
line counts almost unchanged and cut the bytes 24× at `Off` and 21× at
`Inferences`: each `pol` and each assertion got shorter, and there are as many
of them. (#1055's own body measured the same 617 MB, at fixed work against
`00797a97`.)

**Own against shared.** The OPB is 348 constraint rows. The proof is almost all this
family's bound pushes, about one `pol` per push. Over the whole proofs, at
`0a5b4ec6` against the first pass's kept proofs at `00797a97`:

| | `0a5b4ec6` | `00797a97` |
|---|---|---|
| `Off`: `pol`s, fields per `pol` | 1,802,943, 21.4 | 1,803,379, 742.8 |
| `Off`: `rup`s, `del`s | 1,844,222, 3,645,645 | 1,844,505, 3,645,645 |
| `Inferences`: `linear_equality` assertions, literals each | 1,801,633, 6.5 | 1,801,633, 187.3 |
| share of those literals that are `~x[ge0]` | 0.03% | 96.5% |

A `~x[ge0]` literal is the clause form of a reason literal `x ≥ 0` on a 0/1
variable, true before search started; #1055 removed almost all of them. The
first pass sampled only the first 200 MB of the `Off` proof (656 fields per
`pol`) and the first 300 MB of the `Inferences` proof (167 literals over all
62,507 assertions there, backtracks included; its 59,583 `linear_equality`
assertions average 171.8; 95.6%).
So the proof's size was set by how many terms each assertion named, not by how
many assertions there were, and it still is: the count is the same, and the
size fell with the names.

**The test lanes at both assertion levels**, `linear_test <mode> --seed=1` at
the default threshold, every proof kept, at `0a5b4ec6`. The lines leave out
#1220's partial-sum instances, which did not exist at `00797a97`; the `Off`
column at `00797a97` is in brackets, and the other two columns are unchanged:

| Lane | lines, `Off` | lines, `Inferences` | family assertions |
|---|---|---|---|
| `eq` | 8,277 (8,429) | 1,365 | 368 `linear_equality` |
| `eq_iff` | 689,081 (689,317) | 383,321 | 1,317 `linear_equality`, 388 `linear_not_equals` |
| `ne` | 337,791 (337,791) | 190,608 | 192 `linear_not_equals`, 189 `linear_equality` |
| `le` | 32,960 (33,014) | 22,333 | **173 unhinted** |
| `le_iff` | 84,647 (84,893) | 56,555 | **733 unhinted**, 48 `linear_inequality … cond` |
| `ge` | 12,248 (12,338) | 7,119 | **203 unhinted** |

#1055 barely moves these: their terms range over a few values either side of
zero, so few bounds are ones the bits imply. All twelve runs pass, VeriPB on
the `PATH`.

The rest of each proof is search (`backtrack`, `solx_block`). The core's own
final `a >= 1;` for an unsatisfiable instance is also unhinted, in these
lanes, and is not this family's.

## Status, gaps, and next steps

### Proof-logging gaps

**One attribution gap**: the inequality's bound pushes (rules 1, 3 and 4 for an
inequality) carry no hint, so in hints-only mode nothing names the constraint
that licenses them. That costs a reconstructor a search over the model's
inequalities (verdict `search`), not information it cannot get. Every
inference is justified, nothing is asserted, and no propagator changes
strength when proofs are on. **One model-writing gap**: a range-literal
reification condition cannot be written at all (#310).

### Known limitations

- **An equality can take a number of sweeps linear in the width** to reach its
  fixpoint, in time and in proof lines (#1091). See [Interval
  efficiency](#interval-efficiency) for the shapes tried.
- **The equality is `bounds(R)`, not `bounds(Z)`**, with coefficients other
  than ±1: an endpoint can survive with no integer support. That is the
  standard behaviour of interval reasoning on a linear equality, not a bug;
  `Tabulated` is the way to get more.
- **A range-literal reification condition throws with proofs on** (#310,
  #1225). It propagates correctly without them.
- **Proofs on long sums are large.** Since #1055 a bound push no longer names
  the bounds that hold trivially, but its reason still names every other term
  whose bound has moved, and proof logging multiplies `shortest_path`'s solve time
  17× at `Off` (13.6 s against 0.78 s) for a 617 MB proof. Before #1055 every
  term was named, and the same search wrote 15 GB (#1035).
- **The default incremental threshold can be slower than stateless** by 2.2×
  on a model with many long reified inequalities (#1034; at `00797a97`, and
  2.3× per node at `0a5b4ec6`). It was 1.6–3× faster where there are a few
  long sums, at `00797a97`.
- **A coefficient times a bound, or a sum of them, past `2⁶³` throws**
  `IntegerOverflow` from inside propagation, naming no constraint (a product's
  message names the product; a total's names nothing). With proofs on, the
  model writer refuses a row whose products are too large first; a total
  past `2⁶³` in the `≤` or the equality still throws from the propagator,
  while for a reified inequality the writer refuses first. Inputs outside
  `±(2⁶⁰ − 1)` are refused at construction (#1215).
- **The reified inequality's undecided check sums in plain `Integer`**
  (`linear_inequality.cc:308-318`), so every reified inequality form throws,
  with proofs off, on a partial sum that leaves the range though the total
  fits, where the unreified forms solve since #1220, and on a maximum past
  `2⁶³` that only a comparison needs (see [Robustness and
  limits](#robustness-and-limits)). Filed as #1298.
- **A reified equality waits for its last unfixed term** before deciding its
  condition, even when its bounds already exclude the value. This costs nothing
  measurable on the corpus (#1042).
- **No `If` forms from MiniZinc**, since `mznlib` declares no `*_imp`.

### Next steps

Ranked by what they buy for what they cost. The audit's first three (#1032,
#1036, #1033) are done; see [Re-audit](#re-audit-2026-09-25).

1. **#1035** — **Done by #1055**, both halves and for this family only: the
   reason leaves out a declared bound that the bits imply, that a pin already
   states, or, above `AssertionLevel::Links`, that would have been pinned, and the `pol` leaves out a bound the bits imply and no longer
   divides. Both halves went to proofs consultants. On `shortest_path` it was
   24× in bytes, more than the order of magnitude this item guessed. Doing it
   centrally, for every constraint's rendered reasons, broke 41 tests. The
   same filter restricted to the lines `ProofLogger::infer` writes passed all
   925, and sits on a local branch: #1055's body leaves it as Ciaran's call,
   since it makes each such RUP depend on pins if it is ever hinted. It also
   leaves the same shape in `Knapsack`, `BinPacking`, `GlobalCardinality` and
   difference logic as follow-ups. Not done either: this family's
   `generic_reason` rules (the not-equals and the undecided verdicts) still
   name every variable ([Proof-time state](#proof-time-state)).
2. **#1091** — an equality whose unfixed terms' gcd does not divide what is
   left of `v` takes a number of sweeps linear in the width, at the root or
   after a branch. Checking that gcd per call, before the loop and with its
   proof, would settle those shapes; a check at install would not catch the
   ones that arise in search. It would not settle
   the general question of how many sweeps an equality can take, which wants
   its own look.
3. **Hint the inequality's bound pushes** with `hints::LinearInequality{owner}`,
   which already exists. It would turn rule 1's `search` into `hinted` for an
   inequality, saving the reconstructor a row search; it supplies nothing that
   is missing. Deliberately not filed (Ciaran, 2026-09-23): whether it is worth
   carrying will show up when the justifier work reaches it.
4. **#1034** — make the fold state fit in `std::any` (harder since #1220 made
   it 24 bytes), make slot copies cheap engine-wide, or allocate an `Iff`'s
   second direction lazily. Then re-measure `pattern-set-mining-k2`,
   `unit-commitment` and `vrp` together.
5. **Tests**, unfiled:
   - long sums, tens of terms, so folding and reasons have something to do;
   - large coefficients;
   - a strength regression row for the equality: the `2x + 3y + 3z = 4`
     fixed point, asserting it stays `bounds(R)`, so that the description
     cannot drift back to `bounds(Z)` unnoticed;
   - a #1091-shaped equality at several widths, in both arms, with proofs on
     and off.
6. **Tidying**, the rest of #1043 (#1075 did items 1–3):
   - decide whether the equality's undecided branch should strip the sweep's
     idempotence claim, as the dispatcher does for the inequality (item 4);
   - fold `linear-slack-waking.md` into this document's commentary (item 5).
     That also means updating the comment in `propagate.cc` that cites it, so
     it waits for a non-docs change.
7. **#1042 — a bounds check in the undecided reified equality.** Cheap, and it
   would remove the one-failure probe case, but the corpus shows no benefit.
8. **#310**, for the range-literal condition. It is the solver-wide gap, not
   this family's.
9. **#868** — cross-solver, against Gecode's `linear` on the linear-only corpus
   models, which is the family's natural benchmark.

## Prior art

Bounds propagation for linear constraints is folklore; Harvey and Schimpf
(*Bounds consistency techniques for long linear constraints*, 2002) is the
usual reference for doing it in one pass, and for the incremental folding of
fixed terms. Slack-based watching is the pseudo-Boolean "watch enough to cover
the slack" scheme. `Tabulated` is GAC by enumeration, which is exact and
exponential. The proof side is JP 3.14 and 3.15 of McIlree's thesis, which
also sketches them from Gocht et al.'s earlier proof-logging work. What is new
here is small: the incremental propagator's fold, the deview mode, and closing
by RUP over the undivided sum with the bounds the bits imply left out (#1055;
until then it divided by the changed variable's coefficient to close by RUP).

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
and heavily tuned, and the audit found no wrong answer in it. It found three
in the code around it: a translation that predated the constraint it should
have used, a constant-literal mapping nobody posts, and a binding nobody
calls. Each survived because the tests post exactly the shapes the propagator
expects: variable conditions, small bounds, three terms. A family this central
is worth auditing at its edges more than at its core. All three were fixed the
next day.

**But the audit's own description of the core was wrong twice**, and review
caught both. It called the equality `bounds(Z)` because the algorithm is a
bounds algorithm, and it called every cost width-independent because one sweep
is. A brute-force check of small instances refutes the first in seconds, and
a two-term equality refutes the second. So check a strength claim against
enumeration, and state a cost per call, not only per pass.

**Equal solution sequences are a cheap check, and a weaker one than it
looks.** The stateless, incremental and slack-watched forms are all
documented as making the same inferences. Running them side by side on 23
corpus models gave identical solution sequences in every row, and on the one
model that finished under all four configurations (`shortest_path` 2008), the
same 42,437 nodes. That is what was checked. It rules out a different set or
order of solutions, but not a different tree: two searches can fail in
different subtrees and still produce the same sequence, and the trees were not
compared node by node. So the CPU table compares configurations known to
produce the same solutions, not ones known to search the same tree.

**The proof cost of a long linear constraint was its reasons.** At
`AssertionLevel::Inferences` there is no justification at all, and at
`00797a97` `shortest_path`'s proof was still 9.8 GB, because each
`linear_equality` assertion restated 187 bound literals on average, nearly
all of them trivially true. Trimming justifications would not have touched
that; trimming reasons did both. #1055 did it: those assertions now average
6.5 literals, and that proof is 474 MB.
