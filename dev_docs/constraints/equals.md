# `Equals`: two operands are (or are not) the same value

> **Maturity** production ·
> **Audited** 2026-09-07 at `7d014207`; re-audited 2026-09-08 at `76bfd836` ·
> **Open issues** #882 (views have no range literal) and #895 (the
> refined-watch scan) reach into this family without being about it; #868 is
> an audit-wide prerequisite, now half done. The first pass filed #864–#870
> and six of those seven are fixed. Tracked under #871.

Six posted classes over one implementation: an equality between two operands,
optionally reified, optionally negated. It is the smallest interesting
constraint in the solver and one of the busiest — 71% of all propagator calls
on `ortho_latin --all 6`, and 44% of the assertions in its proof — so its cost
per call and its trigger set matter more than its algorithm does.

**What the second pass changed.** The first audit filed seven issues and this
document was the argument for them; six are now closed. One more fix arrived
from outside the audit (#889), and it lands in the same place the audit's
findings did — the trigger set. Between them they changed what this document
*says*, not only what the code does:

| Fixed | What it changed here |
|---|---|
| #864 → #873 | the no-overlap reason is guarded on `want_reasons()`, so it is not assembled and thrown away with proofs off |
| #865 → #883 | `clone()` carries `_neq`, so all six variants write their own `.scp` keyword |
| #866 → #884 | the interval bridge carries its own subhint, so the family's wire inventory is three forms, not two |
| #867 → #881 | the no-overlap certificate is **interval-wise**: two lines plus the conclusion at any domain width, against `width + 1` |
| #869 → #886 | five mutation lanes and a control, so the derivations are known to be tight rather than merely accepted |
| #870 → #885 | no justification in the family reads `state`, which was the last exception to an invariant the rest of the solver keeps |
| #889 → #894 | a constant-operand reified equals wakes on a refined watch, not `on_change` |

Two of those are worth reading before the rest of this document, because they
are the load-bearing changes rather than tidying. The interval-wise witness
removed the family's only large-domain failure and its only super-logarithmic
cost, which is most of what [Robustness and limits](#robustness-and-limits)
used to be about. And the trigger change is the second instance of the
family's one real performance lever — how often the propagator wakes — this
time in the opposite direction from #819: *narrower* than any coarse trigger
can express, rather than coarser.

Every figure below was measured again at `76bfd836` on an idle machine, except
the cross-solver table, which is `238c7836` and labelled as such. Where a
number moved, it says so.

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
see what a given class actually installs. The `_neq` member reaches no
propagation at all: it picks the keyword the constraint describes itself by in
the `.scp` and nothing else — and until #883 it did not reach that either,
because `clone()` dropped it (see [Cake conformity](#cake-conformity)).

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
| `NotEqualsIff` | ✓ via `EqualsIff` with a negated condition | ✓ `intension` reified NE | ? | ✓ `not_equals_iff`[^flip] | |

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

[^flip]: Until #883 the writer emitted `equals_iff` over a *negated* condition
    for this class, so the `not_equals_iff` keyword existed in the reader and in
    `verified_encodings/scp_cases/not_equals_iff_sat.scp` but was never reached
    by writer output. Both halves were negated, so the two errors cancelled and
    nothing failed. See [Cake conformity](#cake-conformity).

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
- **Proof.** Two rules degrade, for the same underlying reason: **a view has
  no range literal** (#882), so nothing interval-shaped can be said about one.

  The interval-wise symmetric difference (rule 2) is guarded on both operands
  being a bare `SimpleIntegerVariableID` (`both_simple`) and falls back
  wholesale to a per-value rule when either is not — correct, but one
  inference and one proof line per removed *value* rather than per removed
  interval. The bridge lemmas that carry a range literal across the equality
  need a plain variable on the far side.

  The no-overlap witness (rule 9) degrades more narrowly, and deliberately so:
  it spells out only the *runs whose variable is a view*, value by value,
  leaving the rest of the walk alone. So a view there pays for its own holes
  and not for the width of anything. That is the granularity the general fix
  wants, and it is the difference between the eighth view detour in the solver
  and the seventh — both are `equals.cc`, and #882 counts them separately for
  exactly this reason.

The view sweep in the test binary exercises both positions
(`add_view_tests(equals_constraint equals_test 2)`), so the fallback path is
covered, and `run_holey_no_overlap_view_equals_test` covers the one shape
whose witness is not spelled entirely in intervals. Neither is free, and a
model built entirely out of views pays rule 2's per-value cost.

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

**No divergences**, since #883. There was one: a `NotEqualsIff` described
itself as an `equals_iff` over a negated condition, because
`ReifiedEquals::clone()` omitted `_neq` and both `Problem::post` and
`Problem::create_propagators` clone, so the flag was always `false` by the
time `s_expr()` read it. That is the same constraint said backwards — all six
variants still round-tripped through `read_scp` to identical solution counts
(8/24/20/16/28/16) — and the un-negation written for this case was therefore
unreachable. All six now write their own keyword, `not_equals_iff` included,
and the OPB provenance comment for one says `not_equals` rather than `equals`.

What pins it is two checks per variant, because the old bug was invisible to
the obvious one. The description is read out of the `.scp` and matched, which
catches a flag that stops reaching `s_expr()`; then it is read back with
`read_scp`, re-solved, and its solution **set** compared with the posted
model's, which catches a keyword and a condition that no longer agree.
`check_scp_writer_reader_symmetry` asks only whether the reader has a *case*
for the keyword it was handed. Repairing either half of the old bug alone
emits the opposite constraint — with the same number of solutions — which is
why the comparison is of sets and not of counts.

### Proof-time state

**Nothing at the root, nothing lazily, nothing deleted.** This family creates
no scaffolding at all. `install_initialiser` is not used; `define_proof_model`
emits between two and five rows and stops.

The only proof-time objects are the selector flags — `b[id][ne]` for
`MustNotHold`, `b[id][gt]` and `b[id][lt]` for `NotIf` and `Iff` — and they are
**in the OPB**, created by `model.create_proof_flag` at definition time and
fully reified there. So:

- an external justifier locates everything this family refers to from the OPB
  alone, by the labels in the table above, plus the constraint id and subhint
  in the annotation;
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
| — with **one constant operand** | `on_instantiated` both **and** a refined watch on `other != c`, plus the condition | 1, 5, 7, 8 | any variant with exactly one constant operand | as above | as above |

**The trigger set is the only tuned thing in the family, and it has now been
tuned twice in opposite directions.** Both times the lever was how often the
propagator wakes, never what it does when it does; see [CPU
performance](#cpu-performance) for both sets of figures.

*Coarser, for the unconditional disequality* (#819). `NotEquals` only ever
runs rule 5, which reads nothing but `optional_single_value` and disables
itself until backtrack once it has acted — so `on_instantiated` cannot miss a
wake, and the wakes it drops are the expensive ones. Fixing a vertex removes
one value from each of its *d* neighbours, and under `on_change` every one of
those interior removals woke every other not-equals on that neighbour only to
find neither end fixed. On `ortho_latin --all 6` this is 321.7M calls against
55.4M.

The cost is not free and the accounting is subtle: narrowing a trigger
*delays* an inference by a round whenever the dropped wake would have caught
it early, which fragments the changes a co-registered propagator sees into
more, smaller instalments — and an O(n·d) propagator pays per *run*, not per
change. So `ortho_latin` gained 16.5% while `colour` lost 3.6–5.2% on two of
three instances, at an identical search tree.

*Finer than any coarse trigger can express, for a constant operand* (#889).
With `v2` pinned at `c`, everything the propagator reads collapses: the
undecided pass never reaches its `domains_intersect` arm, and reports MustHold
exactly when `v1` is instantiated to `c` and MustNotHold exactly when `c`
leaves `v1`'s domain. So the propagator turns on two facts — is the other
operand instantiated, and is `c` still in it. `on_instantiated` states the
first. The second is a *literal*, and `on_change` is the finest coarse
granularity there is but is still per *variable*, so it woke the propagator
for every removal from `v1`. A model posting one such propagator per
(variable, value) pair — FlatZinc's `int_eq_reif` against a constant, which is
what `x == sum(bool2int(xs[i] == v))` flattens to — then wakes *d* of them per
removal and *d* − 1 find nothing. A refined watch on `other != c` wakes only
the one whose value went.

Two constants need no special case: `on_change` registers no wake for a
constant either, and every pass decides outright on the one call every
propagator gets when search starts.

**Idempotence.** No pass ever returns `EnableButIdempotent`, so no claim is
made. Note that the runtime-dispatch path would not forward such a claim even
if one were made, because a re-run of the dispatcher also re-tests the
reification condition and that interplay has not been audited. The two
install-time-decided paths do forward claims, since there the run is exactly
the enforce call.

That the family makes no claim of its own is why the engine bug #894 fixed
alongside the watch survived so long: the round-boundary replay fired refined
watches from `requeue` but not from `requeue_unless_already_seen`, the variant
taken when *some* propagator in the round claims — so in any round with a
claimant every watch fire was dropped, and dropped for good, since each
inference is replayed exactly once. A dropped wake costs pruning and not
soundness, so nothing failed; what showed it was the learned-nogood store,
also a refined-watch client, exploring a different tree on the refined path
than on the scan oracle.

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

**Large domains: no rule is width-sensitive any more.** The bounds rule is
O(1) and the encoding is logarithmic; the symmetric-difference rule is
interval-based; and since #881 so is the reified no-overlap rule, which was
the one exception. `Equals` over two operands of width 10⁹ solves in 0 ms and
emits two OPB rows.

Rule 9 was the family's only large-domain failure. It walked *every integer
between v1's bounds*, building one reason literal per value. Two changes
closed it, and they are separate:

- #873 guarded the reason's assembly on `want_reasons()`, which confines the
  cost to proving runs. That is the pattern the file's neighbouring pass had
  already been given in `fea9508d`, and it is not the whole fix — it leaves
  the proof's own per-value cost, which is genuine.
- #881 replaced the certificate. Disjointness is a statement about **runs**,
  so the witness is a walk that carries one invariant (`v1 ≥ p`) up the number
  line, one move per maximal run `v1` cannot occupy. See [rule
  9](#rule-reified-no-overlap) for the six moves and what each costs.

*What it cost before, measured elsewhere and not to be put in a table beside
the figures below.* At `7d014207`, this audit's first pass, proofs **off**: 29
ms at width 10⁶, 350 ms at 10⁷, and `std::bad_alloc` after 2.6 GB at 10⁹.
Proofs **on**, from #881's own pre-merge table: 6,525 proof lines at width
10³, 65,025 at 10⁴ taking veripb 8.2 s, and 650,025 at 10⁵ which veripb did
not finish inside 900 s. Both sets are from different runs on different
commits, and #873's audit-lane figures (160 s and 78 GB at 10⁹) are from a 2
TB node, which is why the same shape died at 2.6 GB where it was reported — a
`bad_alloc` is a fact about the machine.

*Measured 2026-09-08 at `76bfd836`, Release + `GCS_WERROR=ON`, g++ 15.2.0, AMD
Ryzen 9 9950X3D, otherwise idle, `taskset -c 4`, `ulimit -v 4000000`. One
`EqualsIff{x, y, b == 1}` with `x ∈ [0, w/2]` and `y ∈ [w/2+1, w]`, so the
rule fires once at the root; root propagation only.*

| width | proofs off | proof lines | proof size | VeriPB |
|---|---|---|---|---|
| 10³ | 0 ms | 13 | 965 B | verified |
| 10⁴ | 0 ms | 13 | 1.2 KB | verified |
| 10⁶ | 0 ms | 13 | 1.7 KB | verified |
| 10⁹ | 0 ms | 13 | 2.6 KB | verified |

Thirteen lines at every width, of which **two are the witness** — one lemma
and the conclusion — six define the two order literals they mention, and five
are proof preamble. The bounds-disjoint case is not special-cased; it falls
out, because nothing anchors on `v1`'s lower bound when `v2` starts above it,
so the reason is `{v2 ≥ lb2, v1 ≤ ub1}`. That is also a strictly more general
nogood than the per-value reason it replaces.

The guard is still load-bearing, and `equals.cc`'s no-overlap reason still
carries a `LargeDomainIterationCounter` (one of three such sites in the
solver, alongside `element.cc` and `all_equal.cc`) — because what it counts is
now *moves of an interval walk* rather than values, and a domain can have as
many runs as it has values. See `dev_docs/large-domains.md`, which records the
audit row and the two things that generalise: that a `Clean` row nothing
instruments is only as strong as the box it ran on, and that a **reason** is a
place a search for pruning loops will not reach.

**Unbounded domains.** Not separately probed, and no longer expected to
matter: every rule is now per-interval or O(1) except rule 3, whose cost is
the number of values actually removed rather than the domain's width.

**Negative values and zero.** Fine, and covered: the test data includes
`[-10, 10]` ranges, negative constants, and the `{-2,-2}`/`{-3,-3}` fixtures.

**Overflow.** Checked, not merely unlikely. `Integer` arithmetic throws
`IntegerOverflow` rather than wrapping — `operator+` goes through
`add_overflows`, and `operator++`/`--` guard the extremes — so the
`bounds.second + 1_i` pattern in rule 4 would throw a diagnosable exception if
an operand's upper bound were `Integer::max_value()`, not silently wrap.
Verified UBSan-clean with both operands at `LLONG_MAX/2`.

**Per-value costs.** One rule is, and only because of views: rule 3, the
view/constant fallback for the symmetric difference. Rule 9 spells out the
runs of a *view* operand value by value for the same reason (#882) and nothing
else. Both are proof-layer limitations, not propagation ones.

## Inference catalogue

Nine rules. The first four are the must-hold pass (`enforce_equality`), the
fifth is the must-not-hold pass, and the last four are the reified verdicts of
the undecided pass.

Three facts hold for all nine and are not repeated in each entry.

**No hint carries operand data.** All three hint types in the family derive
from `hints::Equals`, whose wire form is `(constraint_id <id>)`, and nothing
beyond the constraint id and an optional subhint reaches the wire — everything
an external justifier needs must be recoverable from the asserted literal, the
reason and the OPB rows. Two of the three hold extra fields for the internal
emitter's use only.

**The wire inventory is a closed list of three forms**, and this is what
distinguishes derivations of different length:

| Wire form | Hint type | Means | Rules |
|---|---|---|---|
| `equals:((constraint_id N))` | `hints::Equals` | one RUP against the equality rows | 1, 3, 4, 5, 6, 7, 8 |
| `equals:((constraint_id N) (subhint not_in_range))` | `hints::EqualsNotInRange` | two bound lemmas, then the conclusion | 2 |
| `equals:((constraint_id N) (subhint no_overlap))` | `hints::EqualsNoOverlap` | the disjointness walk, then the conclusion | 9 |

Before #884 rule 2 wore the bare form, and the only way to tell its three-line
derivation from a one-line pruning was to notice that the asserted literal was
spelled as a range — keying off literal spelling, which is exactly what a hint
vocabulary exists to avoid. `run_hint_inventory_equals_test` reads the
inventory off real proofs at `AssertionLevel::Inferences` and fails on a
subhint outside this table, so a fourth form has to be added here as well as
there.

**No rule reads `state` from inside a justification.** Since #885 this is
uniform: rule 9's emitter re-walks the reason's own literals rather than the
domains, and holds no `State *`. It was the family's only exception, and it
was on the wrong side of an invariant the rest of the solver keeps — a
justification does not run at the moment its inference was decided, so a
domain read there can be narrower than the one the reason was built from, at
which point the lemmas stop lining up with the literals they exist to let unit
propagation see through. Reading the reason cannot go stale, because the
reason is what the conclusion is asserted under.

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
- **Tightness** — shown. The `fixed_operand_reason` mutation lane drops the
  fixed operand's value from the reason, so the pruning claims to follow from
  the reification condition alone, and VeriPB rejects it. That is the reason's
  minimality in the sense that matters here: the equality rows say the two
  operands agree, not what either of them is.

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
- **Hint** — `hints::EqualsNotInRange`, wire form `(constraint_id <id>)
  (subhint not_in_range)`. Nothing beyond the subhint: the emission is a
  lambda at the call site rather than an `emit_justification`, and the
  interval and the operands come out of the asserted literal and the reason.
- **Offline reconstructibility** — `hinted`. The two bridge lemmas
  ```
  rup ¬(pruned ≥ lo) ∨ (other ≥ lo) ∨ <reason>
  rup ¬(other ≥ hi+1) ∨ (pruned ≥ hi+1) ∨ <reason>
  ```
  are determined by the asserted range literal's endpoints, and since #884 the
  subhint says which shape to build, so a justifier no longer has to recognise
  that the asserted literal is spelled as a range in order to know that two
  lemmas are missing from what it can see. At `AssertionLevel::Inferences`
  those two lines are not in the proof at all, which is why the annotation and
  not the proof has to carry the distinction.
- **Proof size** — three lines per removed interval, plus the shared
  range-literal definitions and linking clauses (which belong to the
  range-literal layer, not here).
- **Gaps** — `None.` The rule is skipped, not weakened, when an operand is not
  simple; rule 3 covers that case at a worse cost.
- **Tightness** — shown, and it is the mutation that tests a *design* claim
  rather than an arithmetic step. The `bridge_lemmas` lane emits the
  conclusion with no bound lemmas before it, so it claims to be RUP across the
  equality unaided; VeriPB rejects it. If it did not,
  `justify_not_in_range_across_equality` would be unnecessary here.

  Worth knowing before writing a fixture for this: over `{0..w}` with the
  middle third removed, VeriPB **accepts** the lemma-free proof at w = 5 and w
  = 11 and rejects it at 6, 7, 8, 9, 10, 12, 14, 16, 20, 100 and 1000. Both
  exceptions put an interval endpoint on a bit boundary, where the bound is
  one literal rather than a sum and unit propagation crosses the equality
  unaided. The lemmas are load-bearing in general, and a narrow fixture would
  have reported that they are not.

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
- **Tightness** — `Not shown.` The `fixed_operand_reason` corruption would
  apply in principle (this reason is also the base reason plus one literal),
  but the lane exercises rule 1's site, not this one.

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
- **Tightness** — `Not shown.` No lane corrupts a bound push. It is the shape
  most similar to rule 1's, which is shown, and the reason is one literal, so
  there is little room between minimal and empty.

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
- **Tightness** — `Not shown.`, and this is the one worth caring about: it is
  the busiest rule in the solver on clique-encoded models and 13,309 of the
  13,323 equals-hinted assertions in `ortho_latin --all 5`'s proof. The
  corruption exists — it is `fixed_operand_reason`'s, dropping the fixed
  operand's value — but `with_proof_mutation` reaches `enforce_equality` and
  this rule lives in the must-not-hold pass, which the mutation is not
  threaded through. Cheap to add, and it should be.

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
- **Tightness** — `Not shown.`, and there is nothing to show: the reason is
  `NoReason{}` and the assertion is a single literal, so the only available
  corruption is to assert something else.

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
- **Tightness** — `Not shown.` Dropping either of the two equality literals
  from the reason is the obvious corruption and no lane does it.

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
- **Tightness** — `Not shown.` As rule 7.

### Rule: reified-no-overlap

- **Infers** — must-not-hold, from the two domains being disjoint.
- **Fires when** — neither operand is fixed, the condition is undecided, and
  `domains_intersect` is false.
- **Strength** — `GAC` on the condition.
- **Algorithm** — one `domains_intersect`, then `walk_no_overlap` over the two
  materialised domains. One move per interval of either domain, so
  O(intervals(v1) + intervals(v2)) — in *intervals*, since #881. It was
  O(width of v1's bounds range) in values, which was the family's only
  super-logarithmic cost and its only large-domain failure.
- **Why it is true** — disjointness is a statement about **runs**, and the
  walk is what states it. It carries one invariant up the number line: at each
  point `p`, the facts stated so far — together with the reification
  condition, which makes the two operands equal — force `v1 ≥ p`. Each move
  pushes `p` past one maximal run `v1` cannot occupy, either because `v1` has
  nothing there or because *`v2`* has nothing there and under `cond` `v1` must
  be wherever `v2` is. `p` strictly increases, so the walk stops after at most
  one move per interval, and it stops by running `p` off the top of one of the
  two domains, which is the contradiction the conclusion needs. The six moves,
  and what each costs:

  | Move | Reason literal | Lemmas |
  |---|---|---|
  | start at v1's lower bound | `v1 ≥ lb1` | — |
  | v2 starts higher, jump to it | `v2 ≥ lb2` | 1 |
  | a hole of v1 | `¬[v1 ∈ lo..hi]` | — |
  | a run where v2 is empty | `¬[v2 ∈ lo..hi]` | 2 |
  | p ran off the top of v1 | `v1 ≤ ub1` | — |
  | p ran off the top of v2 | `v2 ≤ ub2` | 1 |

  A hole of `v1` is free: the range literal's own reverse reification steps
  `p` over it. A run where `v2` is empty costs the two bound-crossing lemmas.
- **Proof technique** — `RUP+hints` — at most two lemmas per run, then the
  conclusion.
- **Reason** — one literal per move of the walk, so one per run rather than
  one per value. For the common shape — two hole-free domains on opposite
  sides of a point — that is `{v2 ≥ lb2, v1 ≤ ub1}`, **two literals at any
  width**, and a strictly more general nogood than the per-value reason it
  replaces. Guarded on `want_reasons()` since #873, and carrying a
  `LargeDomainIterationCounter` because a domain can have as many runs as
  values.
- **Assertion** — the conclusion clause: the condition literal negated, then
  one literal per move. For `x ∈ [1,3]`, `y ∈ [7,9]` the walk is one jump and
  one stop, so it is two:
  ```
  a 1 ~i[b][b0] 1 ~i[y][ge7] 1 i[x][ge4] >= 1
      ::equals:((constraint_id _1) (subhint no_overlap));
  ```
  For interleaved domains it is one literal per run, alternating between the
  operands, ending in the stop:
  ```
  rup 1 ~i[_3][b0] 1 ~i[_2][ge1] 1 i[_1][eq1] 1 i[_2][eq2] 1 i[_1][eq3]
      ... 1 i[_1][ge15] >= 1;
  ```
- **Hint** — `hints::EqualsNoOverlap`, wire form `(constraint_id <id>)
  (subhint no_overlap)`. The struct additionally holds the two operands and
  the condition literal — which is what the lemmas are *about* — and, in a
  testing-only build, a mutation selector. **None of that reaches the wire**,
  nothing in it describes the domains, and since #885 it holds no `State *`.
- **Offline reconstructibility** — `hinted`, and this is the one rule in the
  family where the verdict is *exercised* rather than argued. The subhint says
  which shape to build and the asserted clause carries everything needed to
  build it, so the emitter reads the walk back out of the reason's literals —
  from exactly the literals an external justifier is handed. A `GreaterEqual`
  literal is an anchor or a jump, a `NotInRange` (or a maximal run of
  consecutive `NotEqual`s, which is what a view's run degrades to) is a run,
  and a `Less` is the stop; whose variable it names says whether lemmas are
  owed.
- **Proof size** — two lines per run where the run belongs to `v2`, none where
  it belongs to `v1`, plus one conclusion. Emitted at `ProofLevel::Temporary`,
  so the lemmas are deleted.

  *Measured 2026-09-08 at `76bfd836`, same machine and build as [Robustness
  and limits](#robustness-and-limits). `v1` the even values of `[0, 2n)`, `v2`
  the odd ones, so every run is one value long and every second run costs
  lemmas — the walk's worst case.*

  | runs (n) | total proof lines | the witness's own | the shared literal layers |
  |---|---|---|---|
  | 2 | 25 | 4 | 21 |
  | 8 | 97 | 16 | 81 |
  | 32 | 385 | 64 | 321 |
  | 128 | 1,537 | 256 | 1,281 |

  Exactly `2n` lines of witness against `10n + 1` of shared order- and
  equality-literal definitions, so **five sixths of the proof is not this
  rule** even in the shape that costs it most. In the bounds-disjoint shape
  the witness is two lines at any width, out of thirteen.
- **Gaps** — `None.` The inference is fully justified and, since #881, at a
  cost that is independent of domain width. The one residual is that a run
  belonging to a *view* is spelled value by value, because a view has no range
  literal (#882) — one run, not the rule.
- **Tightness** — shown, by three of the five mutation lanes, which between
  them cover the rule's whole proof surface. `no_overlap_stop` drops the
  walk's last reason literal, so the reason climbs to a position and never
  says the position is impossible. `no_overlap_lemmas` emits no lemmas at all,
  which is the control for the rule: it says whether the walk is load-bearing
  before asking whether any particular move of it is. `no_overlap_selector`
  states the lemmas under `cond` rather than `¬cond` — the one-character
  version of the mistake that is easiest to make in a reified derivation and
  hardest to see by reading, since the lemmas are still about the right
  operands, bounds and direction, and every one of them is false. VeriPB
  rejects all three.

  The lane's instance had to be built with care, and the reason generalises:
  see [Tests](#tests).

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
- **VeriPB really runs**, for every case, gated on `can_run_veripb()`. A
  seeded run is **296 proofs, all verifying, in 1.13 s** (`--seed=1` at
  `76bfd836`; 284 in 1.26 s at `7d014207`).
- **SCP round-trip** on every proving case, via
  `check_scp_writer_reader_symmetry`, plus the two-check description pinning
  described under [Cake conformity](#cake-conformity) for each of the six
  variants.
- **Seeded.** `establish_and_announce_seed`, reproducible with `--seed=N`.
- **Coverage of the awkward cases**: all-constant operands in both directions
  (issue #254), aliasing for all six variants, negative domains, disjoint
  domains, singleton domains, and the `NotEquals(x, x)` rejection.
- **No runtime caps.** Nothing here is slow enough to need one.

Six lanes were added by the fixes, and each covers a shape the original suite
structurally could not reach. They are worth listing individually, because
five of the six exist for a reason that will recur in the next family:

| Lane | What it covers, and why nothing else could |
|---|---|
| `run_wide_no_overlap_equals_test` | width 10⁹, proofs off. Every other domain in the file is inside `[-10, 10]`; `range_infer_test` works inside `[0, 40]`. It pins the **answer**, not the cost — it would have passed before #873 too, slowly — and says so. |
| `run_wide_proved_no_overlap_equals_test` | the same shape at 10⁶, **proved**, asserting the proof is under a thousand lines before handing it to veripb. This is the lane that pins the cost. The bound is deliberately loose and not a pinned figure: most of a proof this small is fixed overhead, and any threshold separates a constant from a million lines. 10⁶ rather than 10⁹ so that a regression fails rather than filling the disk. |
| `run_holey_no_overlap_equals_test`, both orders | interleaved disjoint domains, which is the only shape reaching the two moves that carry a range literal. Both orders, because the walk climbs `v1`'s domain and so is not symmetric; between them they reach all six moves. |
| `run_holey_no_overlap_view_equals_test` | one operand a **view**, the only shape whose witness is not spelled entirely in intervals. Checked by diffing proof bytes, not by a lane going red: leaving the run in pieces still verifies, at exactly nine more lines at every seed tried. |
| `run_value_indicator_equals_test` | the `nmseq` shape in miniature — one reified equality per (variable, value) — with a **driver** that punches a value out of the interior on its own. Every other lane posts a single constraint over its operands, so nothing removes an interior value and a trigger that sees only instantiations passes. Checked as consistency at every node, since a missed wake loses no solutions. |
| `run_hint_inventory_equals_test` | the wire inventory, read off two real proofs at `AssertionLevel::Inferences`, failing on a subhint outside the family's closed list. |

**The derivations are known to be tight** (#886). `EqualsProofMutation` is
five corruptions behind a testing-only `with_proof_mutation()`, each changing
the proof and nothing else, registered as `equals_mutation_*` ctest lanes that
pass only if veripb *refuses* the result. Two corrupt reasons and three
corrupt emitted lemmas, which between them are the family's whole proof
surface — every step here is a RUP, so there is nowhere else for a mistake to
live. A sixth lane is the **control**: the same instances, uncorrupted,
verified. Without it a lane could be green because its instance does not
verify either.

This matters more here than in most families and not less: almost every
inference is a single RUP against a two-row encoding, "veripb accepted a
one-line RUP" is the weakest evidence in the suite because an over-broad
conclusion can be RUP for a reason unrelated to the rule that drew it, and a
corrupted *proof* changes no answers — so neither the solution checks nor
veripb had anything to say about it before.

Two findings about the *instances*, which cost more work than the corruptions
and are recorded in `equals_mutations.hh` and generalised in
`dev_docs/constraints.md`:

- **Dropping a reason literal is only a corruption when that literal traces to
  a search decision.** Anything a propagator derived is written to the proof
  as a clause of its own, so the checker has it whether or not the reason
  repeats it, and a root-firing rule's reason merely restates the database.
  Two of the obvious no-overlap instances accept the mutation for exactly that
  reason before the third bites; the lane's instance puts the bound push
  behind a decision, with a fixed branching order so it is taken first.
- **A narrow fixture would have said the bridge lemmas are unnecessary.** See
  [rule 2](#rule-symmetric-difference-intervals) for the two widths at which
  VeriPB accepts the lemma-free proof.

Of the issue's original mutation candidates, one has no site: "cite the wrong
half of the equality" cannot be done, because no step in this family cites a
proof line by label at all.

What the tests do **not** cover:

- **No `cake_probe_chain` semantic round-trip by default.** The two-check
  `.scp` pinning described under [Cake conformity](#cake-conformity) compares
  solution *sets* through `read_scp`, which is the check
  `check_scp_writer_reader_symmetry` is not; but the full chain against cake's
  own re-derived model runs only under `GCS_TEST_CAKE`.
- **The view coverage is a byte-diff, not a lane.** Leaving a view's run in
  pieces still produces a proof that verifies, so nothing goes red if the
  regrouping regresses — only a nine-line proof-size difference, which is
  checked by hand against a parent commit rather than by the suite.
- **No lane holds the `no_overlap` walk's *reason length* down.** The
  proof-line budget in `run_wide_proved_no_overlap_equals_test` catches a
  per-value witness in a proving run; with proofs off, the guard added in #873
  means the reason is not built at all, so a regression to a per-value reason
  would be caught by the large-domain audit lane rather than by this file.
- **`ortho_latin`, the family's own benchmark, exercises two of the nine
  rules.** See [Proof performance](#proof-performance) — worth knowing before
  reading any conclusion off it.

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
  between. Know what it does *not* cover before reading a per-inference cost
  off it: two of the family's nine rules, and neither subhint — see [Proof
  performance](#proof-performance).
- **For the reified arm: `magic_series 300`** (in `minicp_benchmarks/`, and
  the size is positional — it takes no `--size` and no `--stats`).
  `ortho_latin` is all unreified `NotEquals`, so it says nothing about the
  four reified forms. `magic_series` posts `EqualsIff{series[j],
  constant_variable(i), ...}` per (position, value) pair, which is the
  constant-operand shape exactly, and it has a fixed search tree — 1,193
  recursions, 1,181 failures. It is what #889's C++ half was measured on.
- **For a cross-solver comparison**, neither of the above: take the model from
  `minizinc-benchmarks` — `queens/queens.mzn` for the unreified arm and
  `nmseq/nmseq.mzn` for the reified one, the latter pinning its own
  `int_search`. See `dev_docs/cross-solver-benchmarking.md` for why posting
  our own clique would not do.
- **Do not** pin `circuit_random` results without `--seed=N`; it defaults to a
  random seed.

### CPU performance

*Measured 2026-09-08 at `76bfd836`, Release + `GCS_WERROR=ON`, g++ 15.2.0, AMD
Ryzen 9 9950X3D, 30 GB, otherwise idle, `taskset -c 4`. Min of three.*

| Benchmark | Time | Recursions | Propagator calls | Busiest type |
|---|---|---|---|---|
| `ortho_latin --all 6` | 20.64 s | 1,339,912 | 77,784,903 | `not_equals`, 55,435,743 (71%) |

Under `GCS_PROPAGATOR_STATS=time`, `not_equals` takes **18% of 17.88 s** of
propagation while making 71% of the calls — about 58 ns a call. That ratio is
the family's whole performance story: the algorithm is already as cheap as a
propagator gets, so the only lever left is *how often it is woken*, which is
what both trigger changes did. A timed run's own wall clock (23.55 s here) is
not comparable with an uninstrumented one.

The search shape is identical to the first audit's, to the digit, and the time
is 0.7% higher — 20.49 s at `7d014207`. That is not noise and it is accounted
for: #894 put the watch-index test on the inference replay path, which its own
`perf stat` measured at +0.69% of `ortho_latin`'s instructions. The index is
empty for this model, so it is pure overhead here; hoisting it out is #895.

**Cross-solver comparison.** Measured for this family, which it was not at the
first audit — the harness #868 asked for now exists, in the `gcs-benchmarks`
repo, with the method written up in `dev_docs/cross-solver-benchmarking.md`.
Both models come from `minizinc-benchmarks` rather than being posted here,
which matters: the natural gcs benchmark for this family is a disequality
clique, and no other solver would be given one.

*Measured elsewhere — gcs `238c7836` against Gecode 6.3.0 via the MiniZinc
2.9.7 bundle, 2026-09-07, on this machine but not in this table's build.
`gcs-benchmarks` holds the authoritative tables. Identical trees throughout,
verified on `nodes`.*

| Model | Arm | Instance | nodes (both) | gcs / gecode |
|---|---|---|---|---|
| `queens --all` | unreified `!=` | n=12 | 292,203 | 0.93x |
| `queens --all` | unreified `!=` | n=14 | 8,396,439 | 0.97x |
| `nmseq` | reified `==` | n=100 | 767 | 6.20x |
| `nmseq` | reified `==` | n=200 | 1,567 | 6.40x |

The unreified arm is level with Gecode, marginally ahead. The reified arm was
6.3x behind for the reason this family's whole performance story predicts —
82% of propagation time in `Equals`, at 130,756 calls per node of which 4.4%
were effectful, at a per-call cost (52 ns) that was already fine. #894 took
that to **2.6x at both sizes**; see below. Choco and ACE are still unmeasured,
which is what keeps #868 open.

**Historical A/B, measured elsewhere.** Two, and neither should be put in a
table beside the figures above.

*Issue #819, pre-merge:* `ortho_latin --all 6` 24.29 s → 20.28 s (−16.5%),
321.7M → 55.4M `not_equals` calls; `colour` +3.6% and +5.2% on two instances
and neutral on a third; identical search trees throughout.

*Issue #889, in PR #894:* upstream `nmseq`, same binary, same tree, min of
three — `Equals` calls 100.3M → 4.43M at n=100 (22.6x) and 1.594G → 35.4M at
n=200 (45.0x), effectful share 4.4% → 98.6% and 2.2% → 99.3%, `solveTime`
4.455 s → 2.097 s and 80.881 s → 32.847 s. `magic_series 300` from
`minicp_benchmarks/` is the same shape in C++: identical search, propagations
41.9M → 15.9M, 10.5% fewer instructions. The rest of the `benchmarking.md` set
is unchanged by it.

### Proof performance

*Same build and machine. `ortho_latin --all 5`: 607 recursions, 33,258
propagations, 18 solutions; 0.010 s to solve, 0.040 s to solve and write the
fully-justified proof. VeriPB 3.0.2, min of three.*

| Assertion level | Proof size | Assertions | VeriPB | Verdict |
|---|---|---|---|---|
| `Off` (justify everything) | 5.66 MB | 0 | 1.83 s | `VERIFIED COMPLETE ENUMERATION` |
| `Links` | 3.33 MB | 31,069 | — | — |
| `Inferences` | 3.15 MB | 30,064 | 0.04 s | `UNDER ASSERTIONS` |

Byte-for-byte the same proof as at the first audit at all three levels, and
the same assertion counts: none of the six fixes touched what this model
emits. Verification is **46× the solve time** fully justified. (It was 52× at
the first audit — 2.30 s against the 1.83 s measured here for an identical
proof. Which of the two runs was the anomalous one is not established; only
this one was taken `taskset`-pinned on a verified-idle machine, so it is the
one quoted.) Asserting inferences cuts the proof by 44% and, since `a` is an
oracle rather than a checked rule, the "verification" becomes free — which is
exactly the input an external justifier is meant to consume, and exactly why
its output has to be checked again afterwards.

Of the 30,064 assertions at `Inferences` level, **13,323 (44%) carry the
`equals` hint** — more than any other family in that proof (`modulus` 8,280,
`linear_equality` 4,032, `divide` 3,804).

**All 13,323 are the bare `((constraint_id _N))` form, and this is a fact
about the benchmark rather than about the family.** Neither subhint arises
here. Reading the asserted clauses back: every literal in all 13,323 is an
`eq` atom, 13,309 of them a two-literal clause with both literals negated at
the same value and 14 of them a single positive literal. That is **rule 5**
(13,309, the not-equal-to-fixed-operand pruning of the clique) and **rule 1
against a constant** (14, the puzzle's fixed cells), and nothing else.
`ortho_latin` exercises two of the family's nine rules in its proof — no bound
push, no interval bridge, no disjointness walk — so the interesting
derivations are covered by `equals_test` and the hint-inventory lane, not by
the family's own proof benchmark. Anyone reading a per-inference cost off this
table should know which two inferences it is an average over.

Per-rule proof sizes are in the catalogue. **The family's own contribution is
a minority of the proof even where it is most expensive.** For the
disjointness walk over interleaved domains, measured above, it is `2n` lines
against `10n + 1` of shared order- and equality-literal definitions that the
variable-encoding layer emits on demand — one sixth. For the bounds-disjoint
shape it is two lines out of thirteen. A fully-justified proof of an
equals-heavy model is dominated by those shared layers, not by this
constraint.

## Status, gaps, and next steps

### Proof-logging gaps

**Nothing is left unjustified, and no rule is weakened when proofs are
enabled.** There is no `a`-oracle use, no unlogged inference, and no strength
difference between a proving and a non-proving run. Since #886 the derivations
are also known to be **tight**: five corruptions of them are rejected by
VeriPB, against a control that shows the same instances verify uncorrupted.

`None.` on cost gaps, too, which was not true at the first audit. The one that
was — rule 9 assembling a `2 + width` reason unconditionally, so that with
proofs off it was built, never read and thrown away — is fixed twice over: #873
guarded the assembly on `want_reasons()`, and #881 made the witness
interval-wise so the width does not enter even when proofs are on.

The one thing left in this direction is not this family's: **a view has no
range literal** (#882), so rule 2 falls back wholesale to per-value pruning
when either operand is a view, and rule 9 spells a view's runs out value by
value. Both are proof-size costs on a correct proof, and #882 prices them
alongside the solver's other six such detours. Recording it here rather than
working around it again is deliberate — the family already carries the
smallest workaround available, which is degrading a run rather than a rule.

### Known limitations

**Aliased operands are not GAC**, deliberately: a GAC algorithm for distinct
variables does not generally give GAC under aliasing, and the dup tests check
the solution set and the proof only. Documented rather than fixed.

**The view/constant fallback costs one proof line per value.** Rule 2 is
skipped wholesale when either operand is not a bare `SimpleIntegerVariableID`,
and rule 3 covers the case one value at a time. It is a proof-size limitation
of the range-literal bridge, which needs a plain variable on the far side, and
the general form of it is #882 — where this family holds two of the eight view
detours in the solver.

**A constant-operand propagator's refined watch is scanned, not indexed**
(#895). The engine tests every watch armed on a variable against each
inference on it, so the scan is as long as the coarse trigger list was and
only the per-item body got cheaper — a `test_literal` instead of a full
propagator call. That is still where the `nmseq` shape's remaining `Equals`
cost is after #894. Indexing watches by value would need the inference replay
to carry the value, which is an engine change rather than a constraint one.

**A model of nothing but reified equalities against constants pays a second
`Equals` it does not need.** FlatZinc's `int_eq_reif(s[j], c, b)` plus
`bool2int(b, x)` is two propagators where one would do, which #889 raised. It
is a frontend question rather than a propagator one, and after #894 it is not
where that model spends itself.

*Three limitations recorded at the first audit are gone rather than
outstanding*: the `clone()` gap that dropped `_neq` (#865, fixed in #883 — and
the sweep behind it stands, since it was the **only** `clone()` under
`gcs/constraints/` or `gcs/presolvers/` dropping a constructor argument), the
shared wire hint between rules 1 and 2 (#866, fixed in #884), and rule 9's
per-value cost (#864 and #867, fixed in #873 and #881).

### Next steps

Ranked. **No propagation or proof bug in this family is outstanding**: the
seven the first audit filed are #864–#870, and only #868 is still open. The
first three items below are a shared mechanism, an engine cost and a
benchmark, all reached through this family rather than owned by it; the fourth
is a hole in its own test coverage that writing the per-rule tightness field
surfaced.

1. **#882 — Give views a range literal.** The largest remaining item, and this
   family is where the price is most visible: rule 2 is skipped wholesale for
   a view operand and rule 3 covers it one value at a time, which is a domain
   width rather than a constant now that the interval vocabulary is the
   ordinary one. Two candidate designs, and #881 sharpened the case for the
   second of them — define range literals over a registered view's own bits
   and let the two order *cuts* cross the view's defining equality, since the
   no-overlap walk showed that a range literal never crosses an equality, only
   its cuts do, one bound at a time. That is a hand UP analysis, so it is a
   reason to test the design and not to adopt it.
2. **#895 — Hoist the refined-watch empty-index test, and index watches by
   value.** Two costs, both measured while doing #889. The first is 1.7% of
   `tsp`'s instructions and 0.69% of `ortho_latin`'s, all of it paid by models
   that arm no watches at all, and it is a template parameter away from
   compiling out. The second is what is left of this family's cost in the
   `nmseq` shape. Both are engine work, and the first is worth doing carefully
   rather than quickly: the invariant it needs is about the hottest loop in
   the solver, and what it would protect against getting wrong is exactly the
   silent wake loss #894 fixed.
3. **#868 — Measure against Choco and ACE.** Half done: the harness exists,
   the method is written up, and Gecode is measured on both arms of this
   family (`dev_docs/cross-solver-benchmarking.md`). What is missing is the
   other two solvers. The hard part is settled and worth reusing — the model
   has to come from an external suite, because the natural gcs benchmark for
   this family is a disequality clique and no other solver would be given one.
4. **Thread the proof mutation through the must-not-hold pass.** Not filed as
   an issue yet, and small. `with_proof_mutation` reaches `enforce_equality`, so
   `fixed_operand_reason` corrupts rule 1's reason but not rule 5's — and rule
   5 is the busiest rule in the solver and 13,309 of the 13,323 equals-hinted
   assertions in the family's own proof benchmark. The corruption already
   exists; only the lambda's capture list and one lane registration are
   missing. Worth doing before the next family's mutation lane is written,
   since "the corruption exists but does not reach the rule I care about" is
   the shape of mistake it demonstrates.

**Not to do, having been considered:** bounding rule 9 and leaving the verdict
undecided when the range is wide. That was the fallback the first audit
proposed in case an interval-wise certificate did not exist. It does exist
(#881), so a deliberate strength loss buys nothing.

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
- The **interval-wise disjointness certificate** (#867/#881) is, as far as
  this audit found, novel — and it is the one thing in this family that is a
  proof technique rather than an application of one. "These two domains do not
  overlap" has an obvious per-value witness and no obvious interval-wise one,
  because the fact really is stated value by value. Restating it as a *walk* —
  an invariant `v1 ≥ p` carried up the number line, one move per maximal run
  `v1` cannot occupy, ending by pushing `p` off the top of one domain — makes
  it cost one literal per run and at most two lines per run, at any domain
  width. Two things in it generalise past this constraint: that the witness
  and the reason must come out of the *same* walk in the same order, since the
  lemmas exist precisely to let unit propagation see that reason's literals
  through, and that the moves which cost nothing are the ones stepping over a
  run *inside* one variable, where the variable's own reverse reification does
  the work. `dev_docs/range_literals_spec.md` records it as the range-literal
  layer's second consumer.

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
- `dev_docs/refined-triggers.md` — the per-literal watch mechanism, which this
  family uses for its constant-operand arm (#889) and which the first audit
  recorded as unused here. Also the place the one-shot-subscription rule and
  the claim-path replay invariant are written down, both of which #894
  established.
- `dev_docs/propagator-performance.md` — where the "when every coarse trigger
  is too coarse, watch the literal" case is generalised, with this family's
  figures as the worked example, and the caveat that a watch scan is as long
  as the trigger list was.
- `dev_docs/cross-solver-benchmarking.md` — how to compare gcs against another
  solver at an identical search tree, and the two `minizinc-benchmarks` models
  this family's arms are measured on. Written for #868; read it before quoting
  any cross-solver ratio.
- `dev_docs/large-domains.md` — the `GCS_LARGE_DOMAIN_GUARD` audit lane, this
  family's row in it, and the two generalisable findings the rule-9 blow-up
  produced: that a `Clean` row nothing instruments is only as strong as the
  box it ran on, and that a *reason* is a place a search for pruning loops
  will not reach.
- `dev_docs/infer-redesign.md` — the typed assertion hints in
  `gcs::innards::hints` and the `JustifyExplicitly` / `JustifyUsingRUP` split.
- `dev_docs/benchmarking.md`, `dev_docs/proof-benchmarks.md` — where
  `ortho_latin` sits in the curated sets, and the size cap on the size-6 proof.

## Developer commentary

`None.` The family predates the practice of writing design notes, and the
inline comments in `equals.cc` are unusually thorough — the cake conformity
notes in `define_proof_model`, the trigger rationale for both #819 and #889,
the bridge explanation in `enforce_equality`, and `walk_no_overlap`'s
statement of the invariant it carries are all worth reading in place. This
document does not duplicate them.
`gcs/constraints/innards/equals_mutations.hh` is the other one to read: it
argues why this family needs a mutation lane more than most rather than less,
and records what its instances cost to build.

**What the second pass changed in the template**, on the evidence of having
re-audited a family rather than written one. All four are things this rewrite
wanted and could not find, which is the same test the first pass applied.

- **A re-audit is a distinct event, and the status line carries both dates**
  plus an `issue → PR → what it changed here` table. A reader needs to know
  which commit each figure was taken at, and which sections moved.
- **A rule entry gains a `Tightness` field.** The template asked under Tests
  "whether the derivation has been shown to be tight", which is the right
  question at the wrong altitude: a mutation lane corrupts *one rule's* step,
  so the evidence is per-rule and belongs beside that rule's proof size.
  Putting it there is what surfaced the gap now ranked fourth in [Next
  steps](#next-steps) — six of nine rules answer `Not shown.`, and one of
  those six is the busiest rule in the solver. Under the old shape this family
  could answer "yes, tight" and stop.
- **Say what the family's own benchmark does not exercise.** `ortho_latin`
  reaches two of nine rules. That was true at the first audit too and went
  unsaid; it is the sort of thing a cross-family pivot over these documents
  would silently average over. Read it off the proof's assertions rather than
  guessing — it took one `awk` over the polarity of 13,323 clauses.
- **The own-versus-shared proof-size split wants a measurement, not an
  estimate.** The first pass asserted that the shared layers dominate; the
  second varied the run count and measured `2n` against `10n + 1`. The
  template already demanded the separation, and now demands a number.

**And one thing the re-audit did not change.** The first pass's structural bet
— that the repeated unit is the inference *rule* and not the family — held up
under a rewrite driven by code changes rather than by reading, though not as
cleanly as it might have. Three of the seven fixes (#866, #867, #870) are
changes to one rule's derivation, and each landed in that rule's entry plus at
most one section of shared context; the rule catalogue is where a
proof-technique change goes, and it took the weight. The other four cut across
it, and two of those cut widely: `clone()` (#865) touched the semantics, the
frontend table, cake conformity and the limitations, because a flag that
decides how a constraint *describes itself* is not a property of any rule; and
the mutation lanes (#869) touched every rule entry at once, which is exactly
why the evidence now has a field there. That is the honest version — a
rule-shaped change is cheap to document, and the audit's findings are not all
rule-shaped.
