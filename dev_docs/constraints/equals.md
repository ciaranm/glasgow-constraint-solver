# `Equals`: two operands are (or are not) the same value

> **Maturity** production ·
> **Audited** 2026-09-07 at `7d014207` ·
> **Open issues** none open specific to this family; see [Next
> steps](#next-steps) for the three this audit would file

Six posted classes over one implementation: an equality between two operands,
optionally reified, optionally negated. It is the smallest interesting
constraint in the solver and one of the busiest — 71% of all propagator calls
on `ortho_latin --all 6`, and 44% of the assertions in its proof — so its cost
per call and its trigger set matter more than its algorithm does.

## What it is

### Semantics

`Equals(v1, v2)` holds iff `v1 = v2`. `NotEquals(v1, v2)` holds iff `v1 ≠ v2`.
The four reified forms take an `IntegerVariableCondition` `cond`:

| Class | Semantics |
|---|---|
| `Equals(v1, v2)` | `v1 = v2` |
| `NotEquals(v1, v2)` | `v1 ≠ v2` |
| `EqualsIf(v1, v2, cond)` | `cond → v1 = v2` |
| `EqualsIff(v1, v2, cond)` | `cond ↔ v1 = v2` |
| `NotEqualsIf(v1, v2, cond)` | `cond → v1 ≠ v2` |
| `NotEqualsIff(v1, v2, cond)` | `cond ↔ v1 ≠ v2` |

All six are the one class `ReifiedEquals`, distinguished only by the
`ReificationCondition` its constructor passes down. The `NotEquals*` variants
do **not** flip any propagation logic; they negate the condition at
construction, so `NotEqualsIff(v1, v2, c)` is stored as `Iff{¬c}` and reaches
the same equality-enforcing code. Read the concrete variant's constructor to
see what a given class actually installs; the `_neq` member is not the place to
look (see [Known limitations](#known-limitations)).

Degenerate cases:

- **Aliased operands.** `NotEquals(x, x)` on a non-constant `x` throws
  `InvalidProblemDefinitionException` at construction. The other five accept
  aliasing; `EqualsIff(x, x, c)` correctly forces `c`, and `NotEqualsIf(x, x,
  c)` correctly forces `¬c`, via the alias check in the undecided pass.
- **Constant operands.** Two constants are a valid model, including two equal
  constants under `NotEquals` — trivially infeasible, but a model, so it is not
  rejected. Only genuine variable aliasing is.
- **Views.** Accepted in either position, at a cost — see [Variable kinds and
  views](#variable-kinds-and-views).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Equals` | ✓ `int_eq`, `bool2int`, `bool_eq`; also `decompose`[^lin] | ✓ `intension` eq (n-ary, chained pairwise), `instantiation`, top-level `iff` | ? | ✓ `equals` | |
| `NotEquals` | ✓ `int_ne`, `bool_not`; also `decompose`[^lin] | ✓ `intension` ne | ? | ✓ `not_equals` | |
| `EqualsIf` | frontend gap — no FlatZinc predicate maps to a half-reified equality | ✓ `ifThenElse` arms | ? | ✓ `equals_if` | |
| `EqualsIff` | ✓ `int_eq_reif`, `bool_eq_reif`, `int_ne_reif`[^neg] | ✓ `intension` reified EQ, `iff` | ? | ✓ `equals_iff` | |
| `NotEqualsIf` | frontend gap — as `EqualsIf` | unsupported | ? | ✓ `not_equals_if` | |
| `NotEqualsIff` | ✓ via `EqualsIff` with a negated condition | ✓ `intension` reified NE | ? | ✓ — but writes as `equals_iff`[^flip] | |

[^lin]: MiniZinc rewrites `x = y` and `x != y` between two variables into a
    two-term `int_lin_eq` / `int_lin_ne`, emitting `int_eq` / `int_ne` only for
    reified forms. Across 75 sampled challenge instances: 13,605 two-term
    unit-coefficient `int_lin_eq` in 37 of them and 24,636 `int_lin_ne` in 6,
    against **zero** `int_eq` and 125 `int_ne`. `fzn_glasgow.cc` therefore
    recovers the two-variable shape from any two unit coefficients and posts
    `Equals` / `NotEquals` instead of `LinearEquality` / `LinearNotEquals`.
    Without that recovery this family would be almost unreachable from
    MiniZinc. For `_eq` the recovery is a strength gain as well as a speed one:
    the generic linear equality is bounds(Z) and cannot carry a hole across,
    where `Equals` intersects the domains. For `_ne` both are GAC, so it is
    purely the cheaper propagator.

[^neg]: `int_ne_reif` posts `EqualsIff{v1, v2, reif != 1}` — the negation goes
    into the condition rather than into a different class.

[^flip]: The `not_equals_iff` keyword exists in the reader and in
    `verified_encodings/scp_cases/not_equals_iff_sat.scp`, but the writer never
    emits it. See [Known limitations](#known-limitations).

### Options

`None.` The family has no tunables: no consistency-level knob, no algorithm
selection, no incrementality threshold. Everything the six classes differ by is
a constructor argument, not an option.

This is worth stating rather than omitting, because the neighbouring linear
family does have `with_consistency` and `with_incremental_threshold`, and a
reader coming from there will look for the equivalent here.

### Variable kinds and views

Both operands are `IntegerVariableID`, so plain variables, constants and views
are all accepted, and the propagator is instantiated over the `visit` of both
operand kinds.

Views are where the proof and the propagator diverge:

- **Propagation** treats a view like anything else; the inferences go through
  the same `infer_*` calls and the view layer translates them.
- **Proof.** One rule — the interval-wise symmetric difference — is only
  available when *both* operands are a bare `SimpleIntegerVariableID`. It is
  guarded on exactly that (`both_simple`), and a view or constant in either
  position falls back to a per-value rule that is correct but emits one
  inference and one proof line per removed *value* instead of per removed
  *interval*. The reason is a proof-layer limitation, not a propagation one: the
  bridge lemmas that carry a range literal across the equality need a plain
  variable on the far side.

The view sweep in the test binary exercises both positions
(`add_view_tests(equals_constraint equals_test 2)`), so the fallback path is
covered; it is not free, and a model built entirely out of views pays the
per-value cost.

### Reification

All four reified forms are first-class here rather than bolted on: the class
*is* `ReifiedEquals` and `Equals` / `NotEquals` are the degenerate
`MustHold` / `MustNotHold` cases. The machinery is
`install_reified_dispatcher` (see `dev_docs/reification.md`), which installs a
single propagator and dispatches on the condition's current state.

Two things are specific to this family:

- The condition's own literal is passed into every pass and appears in every
  reason. The propagator never consults the reification *policy* — which
  literal to infer for which verdict is the dispatcher's decision, driven by
  `evaluated_reif::Undecided`'s three flags.
- When the condition is already decided at install time, the dispatcher installs
  a propagator that runs one enforce pass directly, with no per-call
  `test_reification_condition`. That is the path `Equals` and `NotEquals`
  always take, and it is also what a FlatZinc-generated constraint with an
  already-fixed reification literal takes.

### Relation to other families

**Decomposes into this family.** The not-equals clique encoding of an
all-different — one `NotEquals` per pair — is the source of essentially all the
call volume in [CPU performance](#cpu-performance). Note that this is the
*model's* choice, not `AllDifferent`'s: `ortho_latin --all-different
not-equals` posts the clique itself in a double loop, and `AllDifferent` has no
such mode. `gcs::AllEqual` likewise has its own propagator and does not
decompose here.

What does land here: XCSP3's `instantiation` (one `Equals` to a constant per
variable), its n-ary `intension` eq (chained pairwise), its `intension` ne and
reified eq/ne, its `ifThenElse` arms and top-level `iff`; FlatZinc's `int_eq` /
`int_ne` / `bool2int` / `bool_eq` / `bool_not` and the two reified forms; and
the two-term linear recovery in `fzn_glasgow.cc`, which is where almost all of
the MiniZinc traffic arrives.

**Posts as children.** Nothing. `ReifiedEquals::prepare` allocates nothing and
posts nothing.

**Shares code with.** `enforce_equality` is exported from `gcs::innards` and
called by `Element` (`element.cc:699`) to tie a result variable to a selected
array entry. Any change to its inference set or its return value is an
`Element` change too — this is the one cross-family coupling in the file.

**Presolvers.** None rewrite or target this family. `DifferenceLogic` scans for
`x - y ≤ d` shapes and does not recognise an `Equals`.

**Nearly, but not, the same family.** `gcs/constraints/comparison/` is a
parallel hierarchy of twelve classes over `ReifiedCompareLessThanOrMaybeEqual`,
with the same reified-dispatcher shape and the same cosmetic-negation-flag
design — but a separate encoding, separate propagator and separate `hints.hh`.
The template's family list flags `comparison`+`equals` as a candidate merge;
**this audit says keep them separate.** They share a pattern, not code, and
merging the documents would bury two distinct OPB encodings in one section.

## The proof model

### OPB encoding

The operands are compared through their **bit** (binary) encodings, not their
order literals. Writing `⟦v⟧` for the bit sum of `v`:

```
MustHold      (Equals)          ⟦v1⟧ - ⟦v2⟧ = 0
                                  split into two rows, le and ge

MustNotHold   (NotEquals)       ne                     ->  ⟦v1⟧ - ⟦v2⟧ >= 1
                                ¬ne                    ->  ⟦v1⟧ - ⟦v2⟧ <= -1
                                  with one fresh flag ne per constraint

If            (EqualsIf)        cond                   ->  ⟦v1⟧ - ⟦v2⟧ = 0
                                  split into le and ge, each half-reified

NotIf         (NotEqualsIf)     gt                     ->  ⟦v1⟧ - ⟦v2⟧ >= 1
                                ¬gt                    ->  ⟦v1⟧ - ⟦v2⟧ <= 0
                                lt                     ->  ⟦v1⟧ - ⟦v2⟧ <= -1
                                ¬lt                    ->  ⟦v1⟧ - ⟦v2⟧ >= 0
                                lt + gt + ¬cond        >=  1

Iff           (EqualsIff,       cond                   ->  ⟦v1⟧ - ⟦v2⟧ = 0
               NotEqualsIff)      split into le and ge, each half-reified
                                gt                     ->  ⟦v1⟧ - ⟦v2⟧ >= 1
                                lt                     ->  ⟦v1⟧ - ⟦v2⟧ <= -1
                                lt + gt + cond         >=  1
```

The encoding is **definitional**: every row states part of what the constraint
means, and no row is a consequence. There is no scaffolding, no auxiliary
integer variable, and no per-value row — so the encoding is **logarithmic in
domain size**, which is why this family is one of the few that is comfortable
at a domain width of 10⁹.

Two details that only show up in the emitted file. The half-reification
coefficient is the worst-case violation, so it scales with the domain width
(`8 ~b[_1][ne]` for a width-4 domain); this is the reification layer's
choice, not the constraint's, but it means the OPB's *coefficients* grow with
domain size even though its *row count* does not. And `NotIf` reifies its two
selectors **fully** (both `[r]` and `[f]` halves) where `Iff` reifies them only
forward (`[r]`), because in the `Iff` case the `le`/`ge` rows already supply the
other direction.

An `Equals` between two operands of a width-4 domain is two rows:

```
@c[_1][le] -1 i[x][b0] -2 i[x][b1] -4 i[x][b2] 1 i[y][b0] 2 i[y][b1] 4 i[y][b2] >= 0;
@c[_1][ge]  1 i[x][b0]  2 i[x][b1]  4 i[x][b2] -1 i[y][b0] -2 i[y][b1] -4 i[y][b2] >= 0;
```

### Labels

Every row is labelled, and every label is load-bearing — the whole point of the
labelling here is to match what `cake_pb_cp` assigns, so that a proof citing a
row parses against cake's re-derived model.

| Label | Row | Used by |
|---|---|---|
| `@c[id][le]`, `@c[id][ge]` | the two halves of the equality | `MustHold`, `If`, `Iff` |
| `@c[id][gt]`, `@c[id][lt]` | the two strict comparisons | `MustNotHold` |
| `@b[id][gt][r]`, `@b[id][gt][f]` | forward/reverse halves of the `gt` selector | `NotIf` (both), `Iff` (`[r]` only) |
| `@b[id][lt][r]`, `@b[id][lt][f]` | ditto for `lt` | `NotIf` (both), `Iff` (`[r]` only) |
| `@c[id][al1]` | the at-least-one tying `lt`, `gt` and the condition | `NotIf`, `Iff` |

The selector-flag rows are labelled with the flag's own name plus a role suffix
(`pb_file_string_for(flag) + "[r]"`), not with `@c[id][...]`, because that is
what cake does. Getting this wrong is not a soundness bug but a hard parse
failure: a proof citing a label cake never assigns will not load.

### Cake conformity

Conformant, and the best-covered family in the SCP chain suite: all six
variants have a case, five of them `_sat` and three `_unsat`.

```
equals_sat  equals_unsat  equals_if_sat  equals_iff_sat  binary_equals_unsat
not_equals_sat  not_equals_unsat  not_equals_if_sat  not_equals_iff_sat
```

Each comment in `define_proof_model` names the cake function it conforms to
(`encode_equal`, `cencode_equal_1`, the `nev` / `gtv` / `ltv` selectors).

One divergence, benign but worth naming: the writer's own output for
`NotEqualsIff` is an `equals_iff` s-expression with a negated condition rather
than a `not_equals_iff` one. Both describe the same constraint — verified by
round-tripping all six variants through `read_scp` and getting identical
solution counts (8/24/20/16/28/16) — but it means the `not_equals_iff` reader
path is exercised only by the hand-written case file, never by writer output.
See [Known limitations](#known-limitations).

### Proof-time state

**Nothing at the root, nothing lazily, nothing deleted.** This family creates
no scaffolding at all. `install_initialiser` is not used; `define_proof_model`
emits between two and five rows and stops.

The only proof-time objects are the selector flags — `b[id][ne]` for
`MustNotHold`, `b[id][gt]` and `b[id][lt]` for `NotIf` and `Iff` — and they are
**in the OPB**, created by `model.create_proof_flag` at definition time and
fully reified there. So:

- an external justifier locates everything this family refers to from the OPB
  alone, by the labels in the table above, plus the constraint id in the hint;
- there is no proof-only auxiliary, hence no question of whether unit
  propagation determines it on `solx`;
- there is no proof-only vector to index, hence none of the dangling-index
  hazard that proof-only state carries;
- the `del` lines that appear near this family's inferences belong to the
  shared range-literal and order-literal layers, not to it.

The temporary lemmas two of the rules emit (`ProofLevel::Temporary`) are the
one exception to "nothing deleted", and they are deleted by the level
machinery rather than by anything here.

## The implementation

### Initialisation and global data

`prepare()` evaluates the reification condition against the initial state once
and stores the result; that is all. No auxiliary variables, no backtrackable
state, no precomputation, and no root cost worth measuring.

Argument validation is in the *constructors*, not in `prepare`: only
`NotEquals` validates anything, rejecting genuine variable aliasing. That
placement means a bad model throws at `post` rather than at solve.

### Propagator inventory

One propagator, whichever variant is posted. The trigger set is what differs,
and it is the only tuned thing in the family.

| Propagator | Triggers | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|
| dispatcher, decided must-hold | `on_change` both operands | 1–4 | `Equals`, and `If`/`Iff` fixed true at install | never claims | yes, once an operand is fixed |
| dispatcher, decided must-not-hold | `on_instantiated` both operands | 5 | `NotEquals`, and `NotIf`/`Iff` fixed false at install | never claims | yes, once it has acted |
| dispatcher, undecided | `on_change` both operands **and** the condition | 1–9 | the four reified forms while `cond` is open | claims stripped | yes, on any verdict |

**The narrow trigger is the one design decision here** (issue #819). An
unconditional `NotEquals` only ever runs rule 5, which reads nothing but
`optional_single_value` and disables itself until backtrack once it has acted —
so `on_instantiated` cannot miss a wake, and the wakes it drops are the
expensive ones. Fixing a vertex removes one value from each of its *d*
neighbours, and under `on_change` every one of those interior removals woke
every other not-equals on that neighbour only to find neither end fixed. On
`ortho_latin --all 6` this is 321.7M calls against 55.4M.

The cost is not free and the accounting is subtle: narrowing a trigger *delays*
an inference by a round whenever the dropped wake would have caught it early,
which fragments the changes a co-registered propagator sees into more, smaller
instalments — and an O(n·d) propagator pays per *run*, not per change. So
`ortho_latin` gained 16.5% while `colour` lost 3.6–5.2% on two of three
instances, at an identical search tree. Both were measured before the change
landed; see [CPU performance](#cpu-performance).

**Idempotence.** No pass ever returns `EnableButIdempotent`, so no claim is
made. Note that the runtime-dispatch path would not forward such a claim even
if one were made, because a re-run of the dispatcher also re-tests the
reification condition and that interplay has not been audited. The two
install-time-decided paths do forward claims, since there the run is exactly
the enforce call.

**Self-disabling.** Rules 1, 2 and 5 return `DisableUntilBacktrack` — once an
operand is fixed, an equality has nothing left to say at this node or below.
Any verdict from the undecided pass also disables. This is a large part of why
the per-call cost is so low.

### Mutable state and incrementality

`None.` Nothing persists between calls: no `add_constraint_state`, no watch
scratch, no cached bounds. Every call re-reads the operands' state.

That is the right answer for this family rather than an omission. The most
expensive pass materialises two `IntervalSet`s and merge-walks them; there is
nothing worth carrying across a call that would not cost more to keep valid
than to recompute. The one thing a reader might expect — remembering that the
domains were already equal — is subsumed by `DisableUntilBacktrack`.

### Robustness and limits

**Large domains.** The bounds rule is fine and the encoding is logarithmic:
`Equals` over two operands of width 10⁹ solves in 0 ms and emits two OPB rows.
The symmetric-difference rule is interval-based, so it too is insensitive to
width.

**One rule is not.** The reified no-overlap rule (rule 9) walks *every integer
between v1's bounds*, building one reason literal per value:

| v1 bounds width | wall time, proofs **off** |
|---|---|
| 10⁴ | 0 ms |
| 10⁶ | 29 ms |
| 10⁷ | 350 ms |
| 10⁹ | `std::bad_alloc` after 2.6 GB |

Linear in domain width, in both time and memory, and paid even when proofs are
off — see [Proof-logging gaps](#proof-logging-gaps) for why that last part is a
bug rather than an inherent cost. Measured with `EqualsIff{x, y, b == 1}`,
`x ∈ [0, w/2]`, `y ∈ [w/2+1, w]`, so that the rule fires once at the root.

**Unbounded domains.** Not separately probed. The bounds and
symmetric-difference rules have no per-value work and should be unaffected;
rule 9 will not terminate in any useful time, by the scaling above.

**Negative values and zero.** Fine, and covered: the test data includes
`[-10, 10]` ranges, negative constants, and the `{-2,-2}`/`{-3,-3}` fixtures.

**Overflow.** Checked, not merely unlikely. `Integer` arithmetic throws
`IntegerOverflow` rather than wrapping — `operator+` goes through
`add_overflows`, and `operator++`/`--` guard the extremes — so the
`bounds.second + 1_i` pattern in rule 4 would throw a diagnosable exception if
an operand's upper bound were `Integer::max_value()`, not silently wrap.
Verified UBSan-clean with both operands at `LLONG_MAX/2`.

**Per-value costs.** Two rules are per-value rather than per-interval: rule 3
(the view/constant fallback) and rule 9. Everything else is per-interval or
constant.

## Inference catalogue

Nine rules. The first four are the must-hold pass (`enforce_equality`), the
fifth is the must-not-hold pass, and the last four are the reified verdicts of
the undecided pass.

Two facts hold for all nine and are not repeated in each entry. Every one is
attributed to the hint type `hints::Equals`, whose wire form is
`(constraint_id <id>)` and which carries **no operand data** — everything an
external justifier needs must be recoverable from the asserted literal, the
reason, and the OPB rows. And no rule reads `state` from inside a
justification; rule 9's emitter is the sole holder of a `State *`, and it is
valid only because the verdict is consumed synchronously (see [Next
steps](#next-steps)).

### Rule: equal-to-fixed-operand

- **Infers** — `other = v`, where one operand is fixed to `v`.
- **Fires when** — either operand becomes a singleton, in the must-hold pass.
- **Strength** — `GAC` on its own, for two distinct operands.
- **Algorithm** — two `optional_single_value` reads. O(1).
- **Why it is true** — immediate from `v1 = v2`.
- **Proof technique** — `RUP`.
- **Reason** — the base reason (the condition literal) plus `v1 = *val1`.
  Minimal.
- **Assertion** — the clause `other = v ∨ ¬(v1 = v) ∨ ¬cond`, e.g.
  `a 1 i[y][eq1] 1 ~i[x][eq1] >= 1`.
- **Hint** — `hints::Equals{owner}`.
- **Offline reconstructibility** — `offline`. One RUP against `@c[id][le]` and
  `@c[id][ge]`; the asserted clause names both literals.
- **Proof size** — one line.
- **Gaps** — `None.`

### Rule: symmetric-difference-intervals

- **Infers** — `pruned ∉ [lo, hi]` for each contiguous interval of the
  symmetric difference of the two domains, in both directions.
- **Fires when** — either domain has a hole, neither operand is fixed, and
  **both** operands are bare `SimpleIntegerVariableID`.
- **Strength** — `GAC` for two distinct operands: the two domains end up equal
  to their intersection.
- **Algorithm** — materialise both domains (`copy_of_values`), then merge-walk
  via `each_interval_minus`. O(intervals(v1) + intervals(v2) + |output|) — in
  *intervals*, not values, which is the whole point of the rule.
- **Why it is true** — if `v1 = v2` then any value in neither domain is in
  neither variable's support.
- **Proof technique** — `RUP+hints` — two bound lemmas, then the conclusion.
- **Reason** — the base reason plus `not_in_range(other, lo, hi)`. A fresh
  snapshot per interval, so the justification's repeated materialisations do
  not see an accumulating literal. Minimal.
- **Assertion** — `¬(pruned ∈ [lo,hi]) ∨ (other ∈ [lo,hi])`, e.g.
  `a 1 ~i[y][in4_6] 1 i[x][in4_6] >= 1`.
- **Hint** — `hints::Equals{owner}`. **Indistinguishable on the wire from
  rule 1**, despite needing a two-lemma bridge rather than a bare RUP; the
  discriminator is that the asserted literal is a range literal. See [Next
  steps](#next-steps).
- **Offline reconstructibility** — `hinted`, with a caveat. The two bridge
  lemmas
  ```
  rup ¬(pruned ≥ lo) ∨ (other ≥ lo) ∨ <reason>
  rup ¬(other ≥ hi+1) ∨ (pruned ≥ hi+1) ∨ <reason>
  ```
  are determined by the asserted range literal's endpoints, so a justifier can
  rebuild them — but only if it knows to, which today means recognising the
  literal shape rather than reading a subhint.
- **Proof size** — three lines per removed interval, plus the shared
  range-literal definitions and linking clauses (which belong to the
  range-literal layer, not here).
- **Gaps** — `None.` The rule is skipped, not weakened, when an operand is not
  simple; rule 3 covers that case at a worse cost.

Why the bridge is needed at all: a range literal asserts only *order* atoms,
never bits, and the equality rows are a *bit*-sum equality — so
`¬(y ∈ [4,6])` is not RUP from `¬(x ∈ [4,6])` on its own. Each bridge lemma is
RUP because its negation supplies a pair of opposing bounds that contradict the
equality at the bit level. The lemmas mention no range literal, so any literal
sharing those endpoints can reuse them. The pairing assumes a **same-sign**
link; a sign-flipped link, as `Abs` has, needs the mirrored pairing.

### Rule: symmetric-difference-values

- **Infers** — `pruned ≠ val`, one value at a time.
- **Fires when** — as rule 2, but at least one operand is a view or a constant.
- **Strength** — `GAC`. Same fixpoint as rule 2, reached one value at a time.
- **Algorithm** — the same merge-walk, then a per-value loop over each removed
  interval. O(removed **values**).
- **Why it is true** — as rule 2.
- **Proof technique** — `RUP`.
- **Reason** — the base reason plus `other ≠ val`, rebuilt per value. Minimal.
- **Assertion** — `pruned ≠ val ∨ ¬(other ≠ val) ∨ ¬cond`.
- **Hint** — `hints::Equals{owner}`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per removed value.
- **Gaps** — `None.`, in the sense that the inference is fully justified. It is
  a proof-*size* regression against rule 2, not a proof-strength one.

### Rule: bounds-intersection

- **Infers** — up to four bounds: each operand's lower bound raised to the
  other's, each upper bound lowered to the other's.
- **Fires when** — neither domain has a hole, neither operand is fixed, and the
  two bound pairs differ.
- **Strength** — `GAC`, because with no holes the bounds intersection *is* the
  domain intersection.
- **Algorithm** — two `bounds` reads, four `infer_*` calls. O(1).
- **Why it is true** — immediate from `v1 = v2`.
- **Proof technique** — `RUP`.
- **Reason** — the base reason plus the one bound literal being carried across.
  Minimal.
- **Assertion** — e.g. `v2 ≥ lb1 ∨ ¬(v1 ≥ lb1) ∨ ¬cond`.
- **Hint** — `hints::Equals{owner}`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per bound moved, so at most four.
- **Gaps** — `None.`

Note the four inferences are emitted unconditionally once the bound pairs
differ at all, so up to three of them can be no-ops. This is deliberate:
`Inference::NoChange` costs less than four comparisons would.

### Rule: not-equal-to-fixed-operand

- **Infers** — `other ≠ v`, where one operand is fixed to `v`.
- **Fires when** — either operand becomes a singleton, in the must-not-hold
  pass. This is the `on_instantiated`-triggered rule of issue #819.
- **Strength** — `GAC`. For a binary disequality, pruning only when one side is
  fixed *is* GAC.
- **Algorithm** — two `optional_single_value` reads. O(1). This is the busiest
  rule in the solver on clique-encoded models.
- **Why it is true** — immediate from `v1 ≠ v2`.
- **Proof technique** — `RUP`.
- **Reason** — stated outright as `{cond, v1 = *value1}` rather than deferred,
  since the value is already in hand and both literals sit inline. Guarded on
  `want_reasons()`, so it costs nothing when nothing will read it. Minimal.
- **Assertion** — `other ≠ v ∨ ¬(v1 = v) ∨ ¬cond`.
- **Hint** — `hints::Equals{owner}`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`

Uses the non-throwing `infer_not_equal_or_stop`, returning `Enable` on
contradiction so the propagate loop sees `tracker.contradicted()` instead of
paying for a throw.

### Rule: reified-alias

- **Infers** — the constraint must hold, hence the condition literal the
  reification kind licenses.
- **Fires when** — the two operands are the same non-constant variable handle,
  in the undecided pass. Fires at the root.
- **Strength** — `GAC` on the condition.
- **Algorithm** — one handle comparison. O(1).
- **Why it is true** — `x = x`.
- **Proof technique** — `RUP`.
- **Reason** — `NoReason{}`; the fact is unconditional.
- **Assertion** — the condition literal alone.
- **Hint** — `hints::Equals{owner}`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`

Without this rule the verdict would wait until search fixed the variable, and
`NotEqualsIf(x, x, c)` would leave `c` unpruned — the "propagator silent on
alias" bug the dup tests were added for.

### Rule: reified-both-fixed

- **Infers** — must-hold if the two fixed values are equal, must-not-hold
  otherwise.
- **Fires when** — both operands are singletons, in the undecided pass.
- **Strength** — `GAC` on the condition.
- **Algorithm** — two `optional_single_value` reads and a comparison. O(1).
- **Why it is true** — the constraint is decided by the assignment.
- **Proof technique** — `RUP`.
- **Reason** — `{v1 = *value1, v2 = *value2}`. Minimal.
- **Assertion** — the condition literal, plus the negations of the two
  equalities.
- **Hint** — `hints::Equals{owner}`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`

### Rule: reified-one-fixed-unsupported

- **Infers** — must-not-hold.
- **Fires when** — exactly one operand is a singleton and its value is absent
  from the other's domain.
- **Strength** — `GAC` on the condition.
- **Algorithm** — one `optional_single_value` and one `in_domain`. O(1) or
  O(log intervals) depending on the domain representation.
- **Why it is true** — the fixed value has no partner.
- **Reason** — `{v1 = *value1, v2 ≠ *value1}`. Minimal.
- **Proof technique** — `RUP`.
- **Assertion** — `¬cond ∨ ¬(v1 = v) ∨ ¬(v2 ≠ v)`.
- **Hint** — `hints::Equals{owner}`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`

### Rule: reified-no-overlap

- **Infers** — must-not-hold, from the two domains being disjoint.
- **Fires when** — neither operand is fixed, the condition is undecided, and
  `domains_intersect` is false.
- **Strength** — `GAC` on the condition.
- **Algorithm** — one `domains_intersect`, then a walk over **every integer
  between v1's bounds**. O(width of v1's bounds range), in values. This is the
  family's only super-logarithmic cost and its only large-domain failure; see
  [Robustness and limits](#robustness-and-limits).
- **Why it is true** — no value is in both domains, so no assignment satisfies
  the equality. The witness is per-value: for each `val` in v1's bounds range,
  either `val ∉ dom(v1)` or (since the domains are disjoint) `val ∉ dom(v2)`.
- **Proof technique** — `RUP+hints` — one per-value lemma each, then the
  conclusion.
- **Reason** — v1's two bound literals, then one literal per value in the
  range: `v2 ≠ val` when `val ∈ dom(v1)`, and `v1 ≠ val` when it is not. So
  `2 + width` literals. **Not** minimal in any useful sense, and not guarded on
  `want_reasons()`.
- **Assertion** — the conclusion clause, e.g. for `x ∈ [1,3]`, `y ∈ [7,9]`:
  ```
  a 1 ~i[b][b0] 1 ~i[x][ge1] 1 i[x][ge4] 1 i[y][eq1] 1 i[y][eq2] 1 i[y][eq3] >= 1
      ::equals:((constraint_id _1) (subhint no_overlap));
  ```
- **Hint** — `hints::EqualsNoOverlap`, wire form
  `(constraint_id <id>) (subhint no_overlap)`. The struct additionally holds a
  `State *`, both operands, v1's bounds and the condition literal, but **none of
  that reaches the wire** — it is held for the internal emitter only.
- **Offline reconstructibility** — `hinted`. The subhint says which shape to
  build, and the asserted clause carries everything needed to build it: the two
  bound literals give the range, and each per-value literal's *variable* says
  which branch that value took (`y = val` for a value in v1's domain, `x = val`
  for one outside it). So the emitter's `State *` is a convenience, not
  information the justifier lacks. This is the one rule in the family where the
  verdict is worth checking rather than assuming.
- **Proof size** — `width + 1` lines: one lemma per value in v1's bounds range,
  plus the conclusion. Emitted at `ProofLevel::Temporary`, so the lemmas are
  deleted.
- **Gaps** — the inference is fully justified. The *cost* is a bug: see
  [Proof-logging gaps](#proof-logging-gaps).

## Evidence

### Tests

Two binaries. `gcs/constraints/equals/equals_test.cc` is the enumeration
suite, plus a view sweep (`add_view_tests(equals_constraint equals_test 2)`).
`gcs/innards/proofs/range_infer_test.cc` is a dedicated single-purpose proof
test for rule 2: a plain `Equals` where each side carries a contiguous hole, so
each loses one interval to the other, run under `run_test_and_verify.bash`. Its
hole on `x` is deliberately wide (`[10..30]` out of `[0..40]`) so that the
inference's *width-independence* is exercised on a non-trivial interval — it is
the evidence that an interval of `infer_not_equal` really does collapse into one
`infer_not_in_range` without re-encoding `Equals`.

- **Enumeration with per-node GAC assertion.** `solve_for_tests_checking_gac`
  for the main matrix, so every value left in a domain at every node is
  asserted to be supported by some solution. The no-overlap fixture uses
  `solve_for_tests_checking_consistency` instead, marking `c` as `None`:
  `c = 1` is unsupported only by a deduction across all thirteen posted
  constraints, which no individual propagator can make. That distinction is
  spelled out in the test rather than fudged.
- **VeriPB really runs**, for every case, gated on `can_run_veripb()`. A seeded
  run is 284 proofs, all verifying, in 1.26 s.
- **SCP round-trip** on every proving case, via
  `check_scp_writer_reader_symmetry` — but see below for what it does not
  check.
- **Seeded.** `establish_and_announce_seed`, reproducible with `--seed=N`.
- **Coverage of the awkward cases**: all-constant operands in both directions
  (issue #254), aliasing for all six variants, negative domains, disjoint
  domains, singleton domains, and the `NotEquals(x, x)` rejection.
- **No runtime caps.** Nothing here is slow enough to need one.

What the tests do **not** cover:

- **No large-domain case.** Every domain in `equals_test.cc` is inside
  `[-10, 10]`, and `range_infer_test`, though it checks that one rule's proof is
  independent of *interval* width, works inside `[0, 40]`. Nothing in either
  suite would have caught the rule-9 blow-up, which needs a domain wide enough
  to be worth walking. This is the gap that matters most.
- **The SCP symmetry check is a readability check, not a semantic one.** It
  asserts that `read_scp` can parse whatever the writer emitted; it does not
  check that what was parsed means the same thing. The `NotEqualsIff` keyword
  flip passes it. A semantic round-trip is available —
  `cake_probe_chain` — but only under `GCS_TEST_CAKE`.
- **No mutation evidence recorded.** Nothing in the file or in this document
  demonstrates that VeriPB *refuses* a mangled equals derivation, so the
  derivations are not known to be tight.

### Benchmarks and examples

In-repo examples posting this family: `ortho_latin`, `colour`, `sudoku`,
`skyscrapers`, `talent`, `hitori`, `seat_moving`, `n_fractions`,
`circuit_random`, `skeleton_puzzle`. From the frontends, any MiniZinc model
with a two-variable `=` or `!=` reaches it via the two-term linear recovery.

- **For CPU benchmarking: `ortho_latin --all 6`** with the default
  `--all-different not-equals`. Already curated in `dev_docs/benchmarking.md`
  as `ortho_latin_6_all`. It is dominated by this family (71% of calls) and has
  a fixed, deterministic search tree, so a before/after is meaningful.
  Secondary: `colour`, which is where a trigger change shows its downside — its
  single `ArrayMax` was measured under #819 at 82% of its propagation time, so
  anything that makes `ArrayMax` run more often costs there.
- **For proof benchmarking: `ortho_latin --all 5`.** Size 6 must be capped
  (`dev_docs/proof-benchmarks.md`); size 5 is 5.7 MB and there is nothing in
  between.
- **Do not** pin `circuit_random` results without `--seed=N`; it defaults to a
  random seed.

### CPU performance

*Measured 2026-09-07 at `7d014207`, Release + `GCS_WERROR=ON`, g++ 15.2.0,
AMD Ryzen 9 9950X3D, 30 GB. Min of three.*

| Benchmark | Time | Recursions | Propagator calls | Busiest type |
|---|---|---|---|---|
| `ortho_latin --all 6` | 20.49 s | 1,339,912 | 77,784,903 | `not_equals`, 55,435,743 (71%) |

Under `GCS_PROPAGATOR_STATS=time`, `not_equals` takes **18% of 19.06 s** of
propagation while making 71% of the calls — about 57 ns a call. That ratio is
the family's whole performance story: the algorithm is already as cheap as a
propagator gets, so the only lever left is *how often it is woken*, which is
what issue #819 addressed. A timed run's own wall clock (23.29 s here) is not
comparable with an uninstrumented one.

**Cross-solver comparison: `Not measured.`** Doing it properly needs an
identical-search-tree harness against Gecode, Choco and ACE on a
clique-encoded model, and a note on the fact that those solvers would normally
use a specialised all-different rather than a disequality clique — which makes
"the same benchmark" the hard part, not the timing. Flagged in [Next
steps](#next-steps).

**Historical A/B, measured elsewhere (issue #819, pre-merge):**
`ortho_latin --all 6` 24.29 s → 20.28 s (−16.5%), 321.7M → 55.4M
`not_equals` calls; `colour` +3.6% and +5.2% on two instances and neutral on a
third; identical search trees throughout. Those figures are from the issue, not
from this machine on this date, and the two sets should not be mixed in one
table.

### Proof performance

*Same build and machine. `ortho_latin --all 5`: 607 recursions, 18 solutions,
0.044 s to solve and write.*

| Assertion level | Proof size | Assertions | VeriPB | Verdict |
|---|---|---|---|---|
| `Off` (justify everything) | 5.66 MB | 0 | 2.30 s | `VERIFIED COMPLETE ENUMERATION` |
| `Links` | 3.33 MB | 31,069 | — | — |
| `Inferences` | 3.15 MB | 30,064 | 0.04 s | `UNDER ASSERTIONS` |

Verification is **52× the solve time** fully justified. Asserting inferences
cuts the proof by 44% and, since `a` is an oracle rather than a checked rule,
the "verification" becomes free — which is exactly the input an external
justifier is meant to consume, and exactly why its output has to be checked
again afterwards.

Of the 30,064 assertions at `Inferences` level, **13,323 (44%) carry the
`equals` hint** — more than any other family in that proof
(`modulus` 8,280, `linear_equality` 4,032, `divide` 3,804). All 13,323 are the
bare `((constraint_id _N))` form; the `no_overlap` subhint does not arise in
`ortho_latin`, since disjoint domains do not occur there.

Per-rule proof sizes are in the catalogue. The family's own contribution is one
to three lines per inference; a fully-justified proof of an equals-heavy model
is dominated by the *shared* order-literal and equality-literal definitions
that the variable-encoding layer emits on demand, not by this constraint.

## Status, gaps, and next steps

### Proof-logging gaps

**Nothing is left unjustified, and no rule is weakened when proofs are
enabled.** There is no `a`-oracle use, no unlogged inference, and no
strength difference between a proving and a non-proving run.

There is one cost gap in the other direction, which is a genuine bug:

**Rule 9 pays its proof cost when proofs are off.**
`no_overlap_justification` builds a reason of `2 + width` literals
unconditionally, and `SimpleInferenceTracker::materialises_reasons` is
`false`, so with proofs off that vector is built and thrown away. The
`InferenceTracker` header states the rule this breaks — "a propagator whose
reason is expensive to assemble (a `ConcatReason` allocation, **a long
extra-literal walk**) should guard that assembly on this query" — and the
must-not-hold pass in the *same file* does guard, added by commit `fea9508d`
("equals: guard the reified must-not-hold reason on want_reasons"). This site
was missed. It is what turns a wide-domain `EqualsIff` into a `std::bad_alloc`.

Guarding it does not remove the O(width) cost when proofs *are* on — that is
inherent to the per-value witness — but it does confine it to proving runs, and
it is a one-line change with the pattern already in the file's history.

### Known limitations

**`ReifiedEquals::clone()` drops `_neq`, which silently disables a deliberate
fix.** The clone is `make_unique<ReifiedEquals>(_v1, _v2, _cond)` — no fourth
argument — so `_neq` defaults to `false`. `Problem::post` clones, and
`create_propagators` clones again, so by the time anything reads `_neq` it is
always `false`. Consequences, all verified by running the six variants:

1. The `cond_to_write` un-negation in `s_expr()` is **unreachable**. Its guard
   is `_neq && holds_alternative<reif::Iff>`, and `_neq` is never true.
2. `NotEqualsIff{x, y, b == 1}` therefore writes `(_1 equals_iff (b != 1) x y)`
   where the code comment intends `(_1 not_equals_iff (b = 1) x y)`.
3. The OPB provenance comment for a `NotEqualsIff` reads
   `* constraint equals _1`.

None of this is a correctness bug **because the two errors cancel exactly**:
`¬c ↔ x = y` and `c ↔ x ≠ y` are the same constraint, and all six variants
round-trip through `read_scp` to identical solution counts. The comparison is
instructive: `ReifiedLinearEquality::clone()` *does* pass its equivalent flag
(`_flipped_cond`) through, which is why the same commit's fix was load-bearing
there — `linear_test` `ne_iff` went 0/68 to 68/68 — while `equals_test` showed
no change at all. That silence was the only signal that the fix had not taken.

The danger is a partial repair. Fixing `clone()` alone flips the emitted
keyword and the condition together, and stays correct. Fixing either half on
its own emits the *opposite* constraint, and the SCP symmetry check will not
catch it, because it only checks that the keyword parses.

**Two derivations share one wire hint.** Rules 1 and 2 both emit
`equals:((constraint_id N))`, but rule 1 is a bare RUP and rule 2 needs two
bridge lemmas first. An external justifier has to discriminate on whether the
asserted literal is a range literal, rather than on the hint. The mechanism for
saying so already exists and is already used by rule 9 — a subhint.

**Aliased operands are not GAC**, deliberately: a GAC algorithm for distinct
variables does not generally give GAC under aliasing, and the dup tests check
the solution set and the proof only. Documented rather than fixed.

**The view/constant fallback costs one proof line per value.** Documented
above; it is a proof-size limitation of the range-literal bridge, which needs
a plain variable on the far side.

### Next steps

Ranked. None of these are filed yet; the first three are what this audit would
open.

1. **Guard `no_overlap_justification` on `want_reasons()`.** One line, removes
   a `std::bad_alloc` on wide domains with proofs off, and follows a pattern
   already applied to the neighbouring pass in `fea9508d`. Add a wide-domain
   case to the test file at the same time — the current suite tops out at
   `[-10, 10]` and cannot see this.
2. **Fix `clone()` to pass `_neq`, and check the emitted `.scp` changes as
   expected.** Small, but it must be done as one change: it flips both the
   keyword and the condition, and half of it is silently wrong. Worth pairing
   with a semantic round-trip assertion (solve the re-read model, compare
   solution counts) so the symmetry check stops passing on an equivalent-but-
   unintended description. Also makes the `not_equals_iff` reader path reachable
   from the writer.
3. **Give the not-in-range bridge its own subhint.** Removes the one place in
   this family where an external justifier must key off literal shape instead
   of the hint. Cheap, and the pattern is already there in
   `EqualsNoOverlap`.
4. **Consider an interval-wise no-overlap witness.** Rule 9's per-value walk is
   the only super-logarithmic thing here. Whether an interval-wise certificate
   exists is a real question, not a refactor: the witness genuinely is
   per-value, since it says *for each value* which side excludes it. A cheaper
   alternative may be to bound the rule and fall back to leaving the verdict
   undecided when the range is wide — a strength loss, but a bounded one.
5. **Measure against Gecode, Choco and ACE.** Needs an identical-search-tree
   harness and a defensible choice of model, since those solvers would not
   normally encode an all-different as a disequality clique.
6. **Record a mutation.** Show that VeriPB refuses a mangled equals
   derivation, so the derivations are known to be tight rather than merely
   accepted.
7. **Drop the `State *` from `EqualsNoOverlap`.** The reconstructibility
   analysis above shows the asserted clause already carries what the emitter
   reads it for. Removing it would make the family's justifications uniformly
   free of `state` access, which is the invariant everywhere else.

## Prior art

There is none to speak of, and that is the point worth making in a survey: a
binary (dis)equality is not a constraint anyone publishes a propagation
algorithm for, and the interesting content here is entirely on the proof side.
Two things are worth citing:

- The bit-level bound-opposition argument the bridge lemmas rely on is what
  the code calls the "Theorem 2.9 / Justification Procedure 3.2" configuration;
  the range-literal layer that needs it is specified in
  `dev_docs/range_literals_spec.md`, and `range_infer_test.cc` is the worked
  single-inference demonstration.
- The trigger-narrowing result (issue #819) is an ordinary engineering
  measurement, but the *shape* of it — that an avoided no-op wake is worth
  ~15 ns while a delayed inference costs a co-registered O(n·d) propagator a
  whole extra run — is the transferable finding, and it generalises to every
  cheap binary constraint in the solver.

## Further reading

- `dev_docs/constraints.md` — the generic three-phase structure, the inference
  and justification APIs, and the OPB building blocks this family uses without
  extending.
- `dev_docs/reification.md` — `ReificationCondition`,
  `EvaluatedReificationCondition` and `install_reified_dispatcher`, which
  carry all four reified forms here.
- `dev_docs/range_literals_spec.md` — the interval-literal proof layer, and why
  a range literal cannot cross a bit-sum equality without the bridge.
- `dev_docs/variable-encodings.md` — the in-OPB versus in-proof axis this
  family sits entirely on the OPB side of.
- `dev_docs/refined-triggers.md` — the per-literal watch mechanism. Not used
  here, and the contrast is informative: this family's trigger win came from
  coarsening `on_change` to `on_instantiated`, not from watching literals.
- `dev_docs/infer-redesign.md` — the typed assertion hints in
  `gcs::innards::hints` and the `JustifyExplicitly` / `JustifyUsingRUP` split.
- `dev_docs/benchmarking.md`, `dev_docs/proof-benchmarks.md` — where
  `ortho_latin` sits in the curated sets, and the size cap on the size-6 proof.

## Developer commentary

`None.` The family predates the practice of writing design notes, and the
inline comments in `equals.cc` are unusually thorough — the cake conformity
notes in `define_proof_model`, the `#819` trigger rationale, and the bridge
explanation in `enforce_equality` are all worth reading in place. This document
does not duplicate them.
