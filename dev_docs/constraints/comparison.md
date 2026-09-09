# `Comparison`: one operand is ordered against another

> **Maturity** production ·
> **Audited** 2026-09-08 at `76bfd836` ·
> **Open issues** #907 (every reason built unguarded) and #908 (`MustNotHold`
> and `NotIf` throw from `s_expr()`), both filed by this audit. #868 is the
> audit-wide cross-solver prerequisite; #598 would close a deliberate presolver
> gap that is half about this family. Tracked under #871.

Twelve posted classes over one implementation and one propagator: an
inequality between two operands, optionally reified, in either direction, with
or without equality. It is the second-simplest constraint in the solver after
[`equals`](equals.md), and unlike `equals` it is **almost unreachable from the
frontends** — both of them turn a binary ordering into a two-term linear
inequality instead — so its main consumer is the difference-logic presolver,
which reads it back and lifts it into a global propagator.

Two things to know before touching it. Its facts are **single order literals**
and nothing else: no value removals, no intervals, no proof flags, no
scaffolding, one wire hint. That is why it is the one family so far with no
exposure to #882 at all. And its propagator assembles a reason on every call
without asking whether anything will read it, which this audit measured at
**43% of the cycles** on a family-dominated benchmark.

## What it is

### Semantics

The family enforces `v1 <op> v2` for `<op>` one of `<`, `<=`, `>`, `>=`,
optionally under an `IntegerVariableCondition` `cond`:

| Class | Semantics |
|---|---|
| `LessThan(v1, v2)` | `v1 < v2` |
| `LessThanEqual(v1, v2)` | `v1 ≤ v2` |
| `GreaterThan(v1, v2)` | `v1 > v2` |
| `GreaterThanEqual(v1, v2)` | `v1 ≥ v2` |
| `LessThanIf(v1, v2, cond)` | `cond → v1 < v2` |
| `LessThanEqualIf(v1, v2, cond)` | `cond → v1 ≤ v2` |
| `GreaterThanIf(v1, v2, cond)` | `cond → v1 > v2` |
| `GreaterThanEqualIf(v1, v2, cond)` | `cond → v1 ≥ v2` |
| `LessThanIff(v1, v2, cond)` | `cond ↔ v1 < v2` |
| `LessThanEqualIff(v1, v2, cond)` | `cond ↔ v1 ≤ v2` |
| `GreaterThanIff(v1, v2, cond)` | `cond ↔ v1 > v2` |
| `GreaterThanEqualIff(v1, v2, cond)` | `cond ↔ v1 ≥ v2` |

All twelve are the one class `ReifiedCompareLessThanOrMaybeEqual`, which stores
a **normalised** form: `left <` or `left <=` `right`, plus the reification
condition. The four `Greater*` classes are the corresponding `Less*` with the
operands exchanged at construction, and a `_vars_swapped` flag remembering
which way round they were posted — used only for the `.scp` spelling, since
nothing else can tell the difference. So `GreaterThan(a, b)` is stored as
`left = b, right = a, or_equal = false`.

That normalisation is why the base class, not the derived type, is what a
presolver enumerating a `Problem` sees: `clone()` returns a
`ReifiedCompareLessThanOrMaybeEqual` whatever was posted, so
`reification_condition()` and `or_equal()` are what distinguish `LessThan` from
`LessThanEqualIff`, not the C++ type. See [Relation to other
families](#relation-to-other-families).

Degenerate cases:

- **Aliased operands.** `LessThan(x, x)` and `GreaterThan(x, x)` on a
  non-constant `x` throw `InvalidProblemDefinitionException` at construction —
  they are unsatisfiable. The `<=` and `>=` forms accept aliasing, because
  `x ≤ x` holds, and the reified forms accept it in all four directions: the
  undecided pass's alias check resolves the verdict at the root rather than
  waiting for search to narrow the bounds.
- **Constant operands.** Two constants are a valid model, including a pair that
  makes the comparison false. That case installs no propagator at all, only an
  initialiser — see [Propagator
  inventory](#propagator-inventory).
- **Views.** Accepted in either position at no cost anywhere, which is unusual
  and is the point of [Variable kinds and views](#variable-kinds-and-views).

**Two reification kinds no class posts.** `ReificationCondition` also admits
`reif::MustNotHold` and `reif::NotIf`, and the base class is public, so both
are reachable — `ReifiedCompareLessThanOrMaybeEqual{x, y, reif::MustNotHold{},
true}` compiles and propagates. They are not a dead branch: the propagator has
a must-not-hold pass, `define_proof_model` emits the negated row, and
`constraint_row_test.cc` posts a `NotIf` deliberately. What they do **not**
have is an `.scp` spelling, and `s_expr()` throws on both. See [Known
limitations](#known-limitations).

### Concrete constraints and frontend coverage

Twelve classes, four cells each; the pattern is uniform enough to table by
shape rather than by class. The CPMpy cells are `?` except for the
half-reified forms, which `frontend-support-matrix.md` already tracks as a
CPMpy gap under #61 — that row and the matrix's "binary comparison" row are the
two this table replaces.

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `LessThan` | ✓ `int_lt`, `bool_lt` — but see[^lin] | ✓ `intension` lt, `decompose`[^intaff] | ? | ✓ `less_than` | |
| `LessThanEqual` | ✓ `int_le`, `bool_le` — but see[^lin] | ✓ `intension` le, `decompose`[^intaff]; also `ordered` arms | ? | ✓ `less_equal` | |
| `GreaterThan` | `decompose` — flattened to `int_lt` with the operands exchanged | ✓ `intension` gt | ? | ✓ `greater_than` | |
| `GreaterThanEqual` | as `GreaterThan` | ✓ `intension` ge; also `circuit`'s tour-size bound | ? | ✓ `greater_equal` | |
| `LessThanIff`, `LessThanEqualIff` | ✓ `int_lt_reif` / `int_le_reif` and the `bool_` forms | ✓ reified `intension` lt/le | ? | ✓ `less_than_iff`, `less_equal_iff` | |
| `GreaterThanIff`, `GreaterThanEqualIff` | `decompose` — as the unreified `Greater*` | ✓ reified `intension` gt/ge | ? | ✓ `greater_*_iff` | |
| the four `*If` forms | frontend gap — no FlatZinc predicate half-reifies[^imp] | unsupported — a top-level `imp` becomes an `Or` over a fully-reified control | frontend gap (#61) | ✓ `less_than_if` etc. | the presolver's most valuable donor shape, and nothing produces it |

[^lin]: **This family is nearly unreachable from MiniZinc, deliberately.**
    MiniZinc 2.10's flattener emits `int_lin_le([1,-1],[x,y],d)` even for a bare
    `x <= y`, so `int_le` and `int_lt` are bound but hardly ever produced. Note
    the contrast with `equals`: there, `fzn_glasgow.cc` *recovers* the
    two-variable shape from a two-term `int_lin_eq` and posts `Equals` instead,
    because `Equals` intersects domains where a linear equality is only
    bounds-consistent. No such recovery exists here and none is wanted — a
    two-term linear inequality and a `LessThanEqual` are both bounds-consistent,
    so the strength argument that justifies the `equals` recovery has no
    analogue. This audit adds a second reason: on `difference_chain` the
    comparison spelling is **2.7x slower** than the two-term linear one at an
    identical search tree. See [CPU performance](#cpu-performance).

[^intaff]: XCSP3's `post_intension_top_level` tries an affine peephole first for
    `le`, `lt`, `ge` and `gt`, folding operands built from variables, integers,
    `add`, `sub` and `neg` into a single `LinearLessThanEqual`; anything else
    falls back to the ordinary walk and reaches this family. `eq` is excluded
    from that peephole for the strength reason in [^lin]. Details and the
    measured OPB/proof saving are in
    [`frontend-support-matrix.md`](../frontend-support-matrix.md).

[^imp]: `minizinc/mznlib/` declares no `*_imp` predicates, so MiniZinc's
    flattener never half-reifies. That matters more than it looks: the
    difference-logic presolver lifts a half-reified donor, which is where the
    paper's scheduling wins come from, and neither frontend produces one.

### Options

`None.` No tunables: no consistency-level knob, no algorithm selection, no
incrementality threshold. The twelve classes differ only by constructor
arguments.

Worth stating rather than omitting for the same reason as in `equals`: the
neighbouring linear family has `with_consistency` and
`with_incremental_threshold`, and a reader arriving from there will look for
the equivalent.

### Variable kinds and views

Both operands are `IntegerVariableID`, so plain variables, constants and views
are all accepted — and, uniquely among the families audited so far, **a view
costs nothing anywhere**. There is no `both_simple` guard, no per-value
fallback, no degradation of any kind, and no entry in #882's inventory of view
detours.

The reason is structural and worth generalising: **this family never says
anything interval-shaped.** Every fact it states is a single order literal
(`v1 ≥ k`, `v1 < k`) or a reification condition, and a view has order literals.
It is a range literal a view lacks, which is what forces the eight detours
#882 counts — two of them in `equals`. A family whose whole vocabulary is
bounds is immune by construction.

In the proof this shows up as the view getting a proof-only variable and being
cited like anything else. From a real `difference_chain` assertion, where the
right operand is `y[0] + -1`:

```
a 1 ~i[x[40]][ge80] 1 p[39_view_of_y[0]_plus_-1][ge80] >= 1
    ::comparison:((constraint_id _901));
```

Constants are handled a step earlier still: two of them are recognised in
`prepare()` and the constraint installs an initialiser instead of a propagator.

### Reification

All four reified forms are first-class rather than bolted on, via
`install_reified_dispatcher` (see `dev_docs/reification.md`), which installs a
single propagator and dispatches on the condition's current state. Three things
are specific to this family:

- **The `Iff` form needs no auxiliary flag.** This is the substantive
  difference from `equals`, and the reason this audit keeps the two documents
  apart. The negation of `v1 ≤ v2` is `v2 ≤ v1 − 1` — still a *single*
  inequality — so `Iff` is two half-reified rows and nothing else. The negation
  of `v1 = v2` is a disjunction, which is why `equals` has to introduce `ne`,
  `gt` and `lt` proof flags and reify them. See [OPB
  encoding](#opb-encoding).
- **The condition literal appears in every reason** of the two enforce passes,
  and the propagator never consults the reification *policy*: which literal to
  infer for which verdict is the dispatcher's decision.
- **A condition already decided at install time** takes a propagator that runs
  one enforce pass directly, with no per-call `test_reification_condition`.
  That is the path all four unconditional classes always take.

### Relation to other families

**Decomposes into this family.** Nothing. No constraint in `gcs/` posts a
comparison as a child — verified by grepping every constructor call under
`gcs/constraints/` and `gcs/presolvers/`, where the only hits are the family's
own two out-of-line constructors. Contrast `equals`, whose `enforce_equality`
is called from `Element`.

**Posts as children.** Nothing. `prepare()` allocates nothing and posts
nothing.

**Shares code with.** Nothing.

**Read by a presolver — and this is the family's one real coupling.**
`DifferenceLogic` enumerates every posted
`ReifiedCompareLessThanOrMaybeEqual` and lifts it into a global
difference-constraint propagator, because `x ≤ y + d` *is* a difference
constraint: `x ≤ y` states `x − y ≤ 0` and `x < y` states `x − y ≤ −1`. It
reads the family through a published API kept deliberately narrow —
`left_variable()`, `right_variable()`, `or_equal()`,
`reification_condition()`, and
`ConstraintProofModelData<ReifiedCompareLessThanOrMaybeEqual>::primary_row_role()`
— and counts what it lifts as `DifferenceLogicStats::comparison_edges_lifted`,
separately from the linear family's edges.

This is a *read* coupling through a documented interface rather than a shared
function, and the interface is load-bearing in a way that is easy to
underestimate: the presolver builds VeriPB `pol` steps citing the row
`primary_row_role` names, and `cake_pb_cp` re-derives the same labels at the
other end. Renaming a role is a cross-tool break, not an internal one.

Two things about that API are worth reading before changing it. It exposes the
constructor's arguments and nothing else — no `prepare()`-time snapshot —
because a presolver runs with a `State` and can ask that for current bounds
itself. And `primary_row_role` is a *second* visit over the same
`ReificationCondition` that `define_proof_model` visits, rather than a field
the latter sets, because `define_proof_model` does not run when proofs are off
and a presolver must get the same answer either way. `constraint_row_test.cc`
keeps the two honest by posting each kind and checking that a published role
resolves to a label the `.opb` actually contains.

**Presolvers that rewrite it.** None. `AutoTable` tabulates it like anything
else.

**Nearly, but not, the same family.** Three neighbours:

- `gcs/constraints/equals/` — the same reified-dispatcher pattern and the same
  twelve-classes-over-one shape, but a separate encoding (see
  [Reification](#reification)), a separate propagator and a separate
  `hints.hh`. The template's family list flags them as a candidate merge and
  the `equals` audit settled it: **keep them separate.**
- `gcs/constraints/linear/` — a two-term `LinearLessThanEqual` expresses
  exactly what this family does, emits the same labelled OPB row, and is lifted
  by the same presolver. Which one a model gets is a question of size and speed
  rather than reach; [^lin] and [CPU performance](#cpu-performance) are about
  precisely that.
- `gcs/constraints/lex/` — `LexCompareGreaterThanOrMaybeEqual` is the
  lexicographic analogue over two *arrays*, with the same
  swapped/or-equal/reification flag design. Separate family.

## The proof model

### OPB encoding

One inequality over the operands' **bit** encodings. Writing `BinEnc(v)` for
the bit-sum encoding of `v` --- the notation
[`justification-techniques.md`](../justification-techniques.md) and the thesis
both use --- and `d` for `0` in the `<=` form and `−1` in the `<` form:

```
MustHold      BinEnc(left) - BinEnc(right) <= d

MustNotHold   BinEnc(right) - BinEnc(left) <= -d-1        the integer negation

If            cond  ->  BinEnc(left) - BinEnc(right) <= d

NotIf         cond  ->  BinEnc(right) - BinEnc(left) <= -d-1

Iff           cond  ->  BinEnc(left) - BinEnc(right) <= d          role r
              ¬cond ->  BinEnc(right) - BinEnc(left) <= -d-1       role f
```

The encoding is **definitional** and as small as an encoding gets: **one row**
for four of the five reification kinds, **two** for `Iff`, and — the fact worth
carrying away — **zero proof flags, zero auxiliary variables, zero
scaffolding.** It is logarithmic in domain size, so the family is comfortable
at a width of 10⁹.

Measured, one constraint of each of the twelve classes over `x, y ∈ [0,3]`:

```
lt      @c[_1]    -1 i[x][b0] -2 i[x][b1] 1 i[y][b0] 2 i[y][b1] >= 1;
le      @c[_1]    -1 i[x][b0] -2 i[x][b1] 1 i[y][b0] 2 i[y][b1] >= 0;
gt      @c[_1]    -1 i[y][b0] -2 i[y][b1] 1 i[x][b0] 2 i[x][b1] >= 1;
ge      @c[_1]    -1 i[y][b0] -2 i[y][b1] 1 i[x][b0] 2 i[x][b1] >= 0;
le_if   @c[_1]    -1 i[x][b0] -2 i[x][b1] 1 i[y][b0] 2 i[y][b1] 3 ~i[b][b0] >= 0;
le_iff  @c[_1][r] -1 i[x][b0] -2 i[x][b1] 1 i[y][b0] 2 i[y][b1] 3 ~i[b][b0] >= 0;
        @c[_1][f] -1 i[y][b0] -2 i[y][b1] 1 i[x][b0] 2 i[x][b1] 4 i[b][b0] >= 1;
```

Two details that only show up in the emitted file. The `greater_*` forms need no
extra row: the operands are simply the other way round, which is the
normalisation of [Semantics](#semantics) reaching the OPB. And the
half-reification coefficient is the worst-case violation, so it scales with the
domain width (`3` and `4` above for a width-4 domain) — the reification layer's
choice rather than the constraint's, but it means the *coefficients* grow with
domain size even though the row count does not.

### Labels

Every row is labelled, and every label is public API — more so here than
anywhere else audited, because the difference-logic presolver cites these rows
in `pol` steps and `cake_pb_cp` re-derives the same names.

| Label | Row | Used by |
|---|---|---|
| `@c[id]` | the single inequality | `MustHold`, `If` — and, stating something else, `MustNotHold`, `NotIf` |
| `@c[id][r]` | the `cond →` half | `Iff` |
| `@c[id][f]` | the `¬cond →` half | `Iff` |

A comparison is one inequality, so there is no half to name and the role is
empty for the unreified and half-reified forms. The trap is that
**`MustNotHold` and `NotIf` share the bare `@c[id]` label while stating the
*negated* inequality with the operands exchanged**, so anything citing
`@c[id]` must look at the reification condition to know which inequality it
got. That is exactly why `primary_row_role` returns `nullopt` for those two
kinds and for `Iff`: none of the three is the row a citer asking for
`left ≤ right` means, and naming a row that says something else would be worse
than naming none.

### Cake conformity

Conformant, and verified against `cake_pb_cp` at both ends: the label roles
above are what cake re-derives, and `constraint_type()` emits cake's own names
(`less_than`, `less_equal`, `greater_than`, `greater_equal`) with the `_if` and
`_iff` suffixes appended.

**Ten SCP chain cases, and all ten are unconditional:**

```
less_than_sat  less_than_unsat  less_equal_sat  less_equal_unsat
binary_less_equal_sat  greater_than_unsat
greater_equal_sat  greater_equal_unsat  greater_equal_neg_unsat
multi_comparison_unsat
```

So **four of the twelve variants have a chain case** and the eight reified ones
have none, even though the writer emits their keywords and `scp_reader.cc`
parses them. That is a coverage gap rather than a conformity one; see
[Tests](#tests) for what does cover them and [Next steps](#next-steps).

The reader is generic over the whole family: it parses the swapped / or-equal /
reification flags straight out of the keyword and hands them to the base
constructor, so it reconstructs exactly the object the writer serialised rather
than dispatching over twelve cases. `read_comparison` in `scp_reader.cc` is
about thirty lines for all twelve.

### Proof-time state

**Nothing at the root, nothing lazily, nothing deleted, and no flags.**
`install_initialiser` is used for propagation in the both-constant case but
creates no proof objects; `define_proof_model` emits one or two rows and stops.
This is the emptiest proof-time state of any family audited, `equals` included
— `equals` at least has its three selector flags, and this has none. So:

- an external justifier locates everything this family refers to from the OPB
  alone, by the three labels above plus the constraint id in the hint;
- there is no proof-only auxiliary, hence no question of whether unit
  propagation determines it on `solx`;
- there is no proof-only vector to index, hence none of the dangling-index
  hazard;
- nothing is emitted at `ProofLevel::Temporary`, because no rule emits a lemma
  at all — every one is a bare RUP;
- the `del` lines near this family's inferences belong to the shared
  order-literal layer, not to it. On the `difference_chain` refutation measured
  below there are 5,743 of them against 5,742 of the family's own inferences,
  which is a fair summary of where a comparison's proof cost actually lives.

## The implementation

### Initialisation and global data

`prepare()` reads three things and stores them: whether each operand is a
constant (`optional_single_value`), and the reification condition evaluated
against the initial state. No auxiliary variables, no backtrackable state, no
precomputation, no root cost worth measuring.

Argument validation is in the *constructors*, not in `prepare()`: `LessThan`
and `GreaterThan` reject genuine variable aliasing, and nothing else validates
anything. So a bad model throws at `post` rather than at solve.

### Propagator inventory

**Two entirely different shapes, chosen in `install_propagators` on whether
both operands are constants.**

| Propagator | Triggers | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|
| initialiser, both operands constant | — (runs once at root) | 6, 7 | any variant over two constants, where there is something to say | n/a | n/a — one shot |
| dispatcher, decided must-hold | `on_bounds` both operands | 1 | the four unconditional `Less*`/`Greater*`, and `If`/`Iff` fixed true at install | never claims | yes, once the bounds are separated |
| dispatcher, decided must-not-hold | `on_bounds` both operands | 2 | `NotIf`/`Iff` fixed false at install | never claims | yes, likewise |
| dispatcher, undecided | `on_bounds` both operands **and** the condition | 1–5 | the four reified forms while `cond` is open | claims stripped | yes, on any verdict |

**`on_bounds` is the whole trigger story, and it is the right answer rather
than a compromise.** Every pass reads `state.bounds()` and nothing else — no
`in_domain`, no `optional_single_value`, no domain materialisation — so a hole
appearing in either operand cannot change any verdict this family reaches, and
a wake on it would be wasted. Contrast `equals`, whose trigger set has been
tuned twice (#819, #889) because its passes read finer things.

The interesting consequence is that this family has **no trigger work left to
do**: it is already on the coarsest trigger that can see everything it reads.
Whatever is slow here is per-call cost, not wake count — the opposite of
`equals`, where the algorithm was already as cheap as it gets and only the wake
count could move. [CPU performance](#cpu-performance) is where that lands.

**The both-constant arm is worth knowing about** because it is the only place
in either binary family that skips the propagator machinery entirely. With both
operands fixed, the comparison is decided at model-build time, so there is at
most one inference to make ever: force the condition, or contradict. That is an
initialiser, and when there is nothing to say — a `MustHold` that holds — the
constraint installs **nothing at all**. A `Deactivated` condition likewise
installs nothing.

**Idempotence.** No pass ever returns `EnableButIdempotent`, so no claim is
made anywhere in the family.

**Self-disabling.** Every pass returns `DisableUntilBacktrack` once the bounds
are separated by the required margin, and any verdict from the undecided pass
disables. Together with `on_bounds` that keeps the wake count honest; it is the
per-call cost that is not.

### Mutable state and incrementality

`None.` Nothing persists between calls: no `add_constraint_state`, no watch
scratch, no cached bounds. Every call re-reads both operands' bounds.

That is the right answer rather than an omission — a pass is two `bounds()`
reads and two `infer_*` calls, and there is nothing to cache that would not
cost more to keep valid than to recompute. Note that the three `prepare()`-time
members are constraint-level and immutable, not backtrackable state.

### Robustness and limits

**Large domains: nothing here is width-sensitive, and unusually this can be
established by inspection rather than by measurement.** `comparison.cc`
contains **no loop of any kind** — no `for`, no `each()`, no
`copy_of_values()`, no `IntervalSet` — so there is no candidate for
width-proportional work to find. Every pass is two bounds reads and at most two
inferences.

The `GCS_LARGE_DOMAIN_GUARD` audit lane carries three rows for the family
(`LessThan`, `GreaterThan`, and `ReifiedCompareLessThanOrMaybeEqual` as a
`LessThanIf`), all `Clean` over a `0..10⁹` domain. The `equals` audit's warning
about `Clean` rows applies here and comes out the other way: there, a row was
`Clean` because its probe never reached the hazard, and the lesson was that a
`Clean` row nothing instruments is only as strong as the box it ran on. Here
there is no hazard to reach, and the three rows between them cover both enforce
passes and the undecided verdict. This is the rare family where `Clean` is a
theorem.

**Unbounded domains.** Not separately probed, and not expected to matter, for
the same reason.

**Negative values and zero.** Fine, and covered: the test matrix includes
`[-2, 2]`-style ranges in both operand positions, and
`greater_equal_neg_unsat.scp` covers a negative chain case.

**Overflow.** The `+ 1_i` in every pass (`v2_bounds.second + (or_equal ? 1_i :
0_i)` and its three siblings) goes through `Integer::operator+`, which throws
`IntegerOverflow` rather than wrapping, so an operand bounded at
`Integer::max_value()` gives a diagnosable exception. Not separately probed
here; the mechanism is the same one `equals` verified UBSan-clean.

**Per-value costs.** `None.`

**One real cost, and it is not about domains.** The reason literals for all
nine inference sites are constructed unconditionally, without asking
`inference.want_reasons()`. On a family-dominated benchmark that is 43% of the
cycles. See [CPU performance](#cpu-performance) and [Next
steps](#next-steps).

## Inference catalogue

Seven rules. Two are the enforce passes, three are the undecided pass's
verdicts, and two belong to the both-constant initialiser.

Three facts hold for all seven and are not repeated in each entry.

**Every rule is a bare RUP.** The family contains no `JustifyExplicitly`, emits
no lemma, and writes nothing at `ProofLevel::Temporary`. So the **Proof size**
is one line for all seven, and the **Offline reconstructibility** verdict is
`offline` for all seven — the assertion alone determines the derivation,
against one or two rows whose labels the OPB carries. Each rule's **Proof
technique** field says `RUP` and then which procedure licenses it, which is
where the seven differ.

**And every rule is licensed by the same published procedure.** The four bound
transfers are instances of **JP 3.2 (comparison)**, whose correctness proof is
**Theorem 2.9**: the negated conclusion supplies a lower bound on one operand,
this family's single row, and an upper bound on the other, which is exactly
2.9's contradictory triple. The three condition rules reduce to the same thing
or to nothing, and every one of the seven carries its reification condition by
**Theorem 2.6**.
[`justification-techniques.md`](../justification-techniques.md) states the
facts; nothing in this family departs from a published procedure, which is
worth saying because [`equals.md`](equals.md) has one rule that does.

**The precondition is `B ∈ {0,1}`, and this family is exactly it.** Theorem 2.9
requires the middle row's degree to be 0 or 1, and **Example 2.15** is the
counterexample to relaxing that — a middle row of degree 3 over which unit
propagation stalls. `left ≤ right` is `right − left ≥ 0` and `left < right` is
`right − left ≥ 1`, so the family's two spellings *are* the theorem's two
admissible degrees and there is nothing else it can emit. That is a stronger
guarantee than most families get, and it is worth knowing which way round the
dependency runs: the encoding is inside the theorem because a comparison has
only these two forms, not because anything checks.

It is also the sharpest available answer to why a two-term
`LinearLessThanEqual` is *not* interchangeable with this family on the proof
side, whatever [CPU performance](#cpu-performance) says about speed: a linear
row with a constant outside `{0,1}` is outside Theorem 2.9 and needs JP 3.15
instead.

JP 3.2's correctness proof also handles a case this family hits, and takes
care over it: if either operand is **not** two's-complement encoded the three
constraints are not literally Theorem 2.9's, but they are in the state 2.9's
own proof reaches after propagating the most significant bit, so the argument
still applies. Both encodings occur here, since a non-negative operand is
plain binary.

**There is one wire form.** `hints::Comparison`, wire form
`(constraint_id <id>)`, with no subhint and no payload beyond the owning
constraint. Measured across four proofs covering every rule: 13 annotations,
all of them that form. This is the simplest hint inventory of any family, and
it is simple for a reason worth stating — a subhint exists to distinguish
derivations of different *length*, and here they are all length one.

**No justification reads `state`.** There is nothing to read: no rule holds a
`State *` and no rule needs one.

### Rule: bounds-from-must-hold

- **Infers** — two bounds: `left < ub(right) + [or_equal]`, and
  `right ≥ lb(left) + [strict]`. Emitted as one rule because they are the same
  fact read from either end.
- **Fires when** — either operand's bounds move, in the must-hold pass.
- **Strength** — `GAC`. For a binary comparison the bounds pruning *is* domain
  consistency: a value `k` of `left` is supported iff some value of `right`
  exceeds it (or equals it), and whether one does depends only on `ub(right)`.
  Holes in either domain cannot remove support. The thesis states the same
  thing, and states it as the reason this family's justification is simple —
  *"Because bounds-consistency and domain-consistency are equivalent for this
  constraint, the only kind of inference we need to be able to justify is
  `y≥v ∧ x≥u ⇒ 0 ≥ 1`."* It is also checked rather than only argued:
  `comparison_test` runs the whole matrix under
  `solve_for_tests_checking_gac`, so every value left in a domain at every node
  is checked against the solution set.
- **Algorithm** — two `bounds()` reads, two `infer_*_or_stop` calls. O(1).
- **Why it is true** — immediate from `left ≤ right`.
- **Proof technique** — `RUP`, by **JP 3.2 (comparison)**, licensed by
  **Theorem 2.9** with `B ∈ {0,1}` as above. The negated conclusion gives
  `left ≥ k` and `right ≤ k − 1 + [or_equal]`, which with this family's single
  row is 2.9's triple.
- **Reason** — the base reason (the condition literal) plus the one bound
  literal being carried across: `{cond, right ≤ ub(right)}` for the first
  inference and `{cond, left ≥ lb(left)}` for the second. Minimal. **Not**
  guarded on `want_reasons()`, which is the family's one performance defect.
- **Assertion** — `left < k ∨ ¬(right ≤ k−1+[or_equal]) ∨ ¬cond`. Measured, on
  a `difference_chain` edge whose right operand is a view:
  ```
  a 1 ~i[x[40]][ge80] 1 p[39_view_of_y[0]_plus_-1][ge80] >= 1
      ::comparison:((constraint_id _901));
  ```
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No mutation lane exists for this family. Per the
  policy in [`TEMPLATE.md`](TEMPLATE.md), that is an ordinary answer and not
  outstanding work; it is worth adding if this rule's derivation is ever
  changed, and the shape to corrupt is obvious — drop the bound literal from
  the reason, so the push claims to follow from the condition alone.

Uses the non-throwing `infer_less_than_or_stop` /
`infer_greater_than_or_equal_or_stop`, returning `Enable` on contradiction so
the propagate loop sees `tracker.contradicted()` instead of paying for a throw.

### Rule: bounds-from-must-not-hold

- **Infers** — the mirrored pair: `right < ub(left) + [strict]`, and
  `left ≥ lb(right) + [or_equal]`.
- **Fires when** — either operand's bounds move, in the must-not-hold pass —
  which is reached only by an `Iff` whose condition is false, or by the
  `MustNotHold` / `NotIf` kinds nothing posts.
- **Strength** — `GAC`, by the same argument: the negation of a comparison is a
  comparison.
- **Algorithm** — as rule 1. O(1).
- **Why it is true** — `¬(left ≤ right)` is `right ≤ left − 1`.
- **Proof technique** — `RUP`, by **JP 3.2** against the negated row, which
  `define_proof_model` emits with the operands exchanged and the margin
  flipped. Degree 0 or 1 either way, so the licence is the same; that the
  *negation* of a comparison is a comparison is what keeps this family inside
  one theorem.
- **Reason** — `{cond, left ≤ ub(left)}` and `{cond, right ≥ lb(right)}`.
  Minimal, and likewise unguarded.
- **Assertion** — as rule 1 with the operands exchanged and the margin flipped.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`, as rule 1.

### Rule: condition-must-hold-from-bounds

- **Infers** — the constraint must hold, hence the condition literal the
  reification kind licenses.
- **Fires when** — in the undecided pass, when the bounds already separate the
  operands the required way: `ub(left) ≤ lb(right)` for `<=`, strictly less for
  `<`.
- **Strength** — `GAC` on the condition.
- **Algorithm** — two `bounds()` reads and one comparison. O(1).
- **Why it is true** — every remaining assignment satisfies the comparison.
- **Proof technique** — `RUP`. **Theorem 2.6** is doing the work: the asserted
  literal is the condition, so the step is the reified form of "the negated row
  is contradicted", and 2.6 reduces it to that unreified question — which is
  JP 3.2 against the negated row under the two bound literals in the reason.
- **Reason** — `{left ≤ ub(left), right ≥ lb(right)}`. Minimal — exactly the
  two bounds that make the argument, and no condition literal, since the
  condition is what is being inferred.
- **Assertion** — the condition literal, plus the negations of the two bound
  literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: condition-must-not-hold-from-bounds

- **Infers** — the constraint cannot hold, hence the opposite condition
  literal.
- **Fires when** — the mirrored test: `lb(left) > ub(right)` for `<=`, `≥` for
  `<`.
- **Strength** — `GAC` on the condition.
- **Algorithm** — as rule 3. O(1).
- **Why it is true** — no remaining assignment satisfies the comparison.
- **Proof technique** — `RUP`, the mirror of rule 3: **Theorem 2.6** over
  JP 3.2 against the `cond ->` row.
- **Reason** — `{left ≥ lb(left), right ≤ ub(right)}`. Minimal.
- **Assertion** — the negated condition literal plus the two bound negations.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: condition-from-aliased-operands

- **Infers** — must-hold for the `<=` form, must-not-hold for the `<` form,
  hence the corresponding condition literal.
- **Fires when** — the two operands are the same non-constant variable handle,
  in the undecided pass. Fires at the root.
- **Strength** — `GAC` on the condition.
- **Algorithm** — one handle comparison. O(1).
- **Why it is true** — `x ≤ x`, and never `x < x`.
- **Proof technique** — `RUP`, and no procedure applies because there is
  nothing to cross: with both operands the same handle the row reads
  `BinEnc(x) − BinEnc(x) ≤ d`, whose left side is identically zero, so it is
  either trivially true (`d = 0`) or trivially false (`d = −1`) and the
  condition follows by **Theorem 2.6** alone.
- **Reason** — `NoReason{}`; the fact is unconditional.
- **Assertion** — the condition literal alone. Measured, for
  `LessThanIff{x, x, b == 1}`:
  ```
  a 1 ~i[b][b0] >= 1::comparison:((constraint_id _1));
  ```
- **Gaps** — `None.`
- **Tightness** — `Not shown.`, and there is nothing much to show: the reason
  is empty and the assertion is a single literal, so the only corruption
  available is to assert something else.

Without this rule the verdict would wait for search to narrow the bounds, and
for the `<=` form it would never come at all — `ub(x) ≤ lb(x)` only once `x` is
fixed. The dup tests in `comparison_test` cover all eight reified forms under
aliasing for exactly this reason.

### Rule: condition-from-constant-operands

- **Infers** — the condition literal, decided by comparing the two constants.
- **Fires when** — both operands are constants and the condition is undecided;
  once, from an initialiser, at the root.
- **Strength** — `GAC` on the condition.
- **Algorithm** — one comparison of two `Integer`s, done in `prepare()`. O(1).
- **Why it is true** — the constraint is decided by the model.
- **Proof technique** — `RUP`. As rule 5: the two constants make the row's left
  side a known integer, so no bit-sum reasoning is needed and **Theorem 2.6**
  gives the condition. This is why the assertion below is a unit — the two
  constant literals are root-level facts and resolve away.
- **Reason** — `{left = c1, right = c2}`. Minimal, and both literals are
  root-level facts.
- **Assertion** — the condition literal, plus the negations of the two
  equalities. Measured, for `LessThanIff{5, 3, b == 1}`:
  ```
  a 1 ~i[b][b0] >= 1::comparison:((constraint_id _1));
  ```
  — the two constant literals resolve away, so what reaches the file is a unit.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: contradiction-from-constant-operands

- **Infers** — a contradiction.
- **Fires when** — both operands are constants, the condition is *decided*, and
  the constants disagree with it; once, from an initialiser, at the root.
- **Strength** — n/a; the model is infeasible.
- **Algorithm** — as rule 6. O(1).
- **Why it is true** — the model asserts a false statement about two constants.
- **Proof technique** — `RUP`, as rule 6, with the condition already decided so
  the conclusion is the empty clause rather than a literal.
- **Reason** — `{cond, left = c1, right = c2}`. Minimal.
- **Assertion** — the empty clause. Measured, for
  `LessThan{5, 3}`, which is the whole proof:
  ```
  pseudo-Boolean proof version 3.0
  a >= 1::comparison:((constraint_id _1));
  % asserting contradiction
  a >= 1;
  output NONE;
  conclusion UNSAT : -1;
  end pseudo-Boolean proof;
  ```
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

One binary, `gcs/constraints/comparison/comparison_test.cc`, run as **twelve
ctest lanes** — one per variant, selected by an argv mode
(`ge ge_if ge_iff gt gt_if gt_iff le le_if le_iff lt lt_if lt_iff`) — plus
twelve view-sweep lanes, for 24 of the 27 lanes matching `comparison`. The
other three are `scp_chain_multi_comparison_unsat` and the two
`difference_chain-presolved-comparison-*` lanes.

- **Enumeration with per-node GAC assertion.** `solve_for_tests_checking_gac`
  for the whole matrix, in both the unreified and reified helpers. This is the
  evidence behind every rule's `GAC` claim: bounds pruning achieving domain
  consistency is a *property* of a binary comparison rather than an obvious
  fact, and it is checked at every node rather than argued.
- **VeriPB really runs**, for every case. Seeded, all twelve modes:
  **1,356 proofs, all verifying, in 3.35 s total** — 51 for each of `ge` and
  `le`, 47 for each of `gt` and `lt`, and 145 for each of the eight reified
  modes.
- **A view sweep in both positions**, `add_view_tests(comparison_constraint_
  ${mode} comparison_test 2 ${mode})`, one per mode.
- **Aliasing for all eight reified forms plus the two `<=`/`>=` unreified
  ones**, via the dup helpers, with the expected verdict pinned per form
  (`c == 0` for the strict forms, `c == 1` for the or-equal ones).
- **Both operand orders** for every mode, via `build_expected`.
- **Seeded**, reproducible with `--seed=N`.
- **`.scp` round-trip**, in `scp_reader_test.cc`: three variants
  (`LessThanEqual`, `GreaterThan` — which is the one that exchanges its
  operands on write — and `LessThanEqualIff`) are written, read back with
  `read_scp`, written again, and the two descriptions compared byte for byte.
- **The published row role**, in `constraint_row_test.cc`: five constraints
  covering `MustHold` twice, `If`, `Iff` and `NotIf`, checking that each
  published role resolves to a label the `.opb` really contains, and that the
  three kinds which publish `nullopt` do so.
- **No runtime caps.** Nothing here is slow enough to need one.

What the tests do **not** cover:

- **No large-domain case in the test file.** Every domain in
  `comparison_test.cc` is small. Unlike `equals`, this is not the gap that
  matters — there is no width-proportional work for one to find, and the
  `GCS_LARGE_DOMAIN_GUARD` lane carries three rows for the family. Worth
  stating so that the absence reads as considered.
- **Eight of the twelve variants have no cake chain case**, and the four `*If`
  forms are round-tripped nowhere: `scp_reader_test` covers `_iff` but not
  `_if`. The keywords are written and parsed, so this is untested rather than
  broken.
- **The `.scp` round-trip is a write→read→write fixpoint, not a semantic
  check.** It catches a reader that loses information, which is the failure the
  `equals` audit's `_neq` bug was; it would not catch a writer and reader
  agreeing on the wrong meaning. Nothing in this family currently has the
  asymmetry that made that bug possible, since the reader parses the flags
  straight out of the keyword.
- **No mutation lane.** See the per-rule `Tightness` fields and the policy note
  in [`TEMPLATE.md`](TEMPLATE.md): partial coverage is the expected state, and
  this family has none. Its derivations are accepted but not known to be tight.
- **`MustNotHold` and `NotIf` are covered for propagation and for their OPB row
  but not for anything that writes an `.scp`** — `constraint_row_test.cc`
  disables the `.scp` deliberately. See [Known
  limitations](#known-limitations).
- **`difference_chain`, the family's own benchmark, exercises one of the seven
  rules.** See [Proof performance](#proof-performance).

### Benchmarks and examples

In-repo examples posting this family: `difference_chain`, `table_layout`,
`talent`, `magic_square`, plus the XCSP3 and FlatZinc paths — though [^lin] is
the caveat that matters for anything arriving from MiniZinc.

- **For CPU benchmarking: `difference_chain --variant=decomposed
  --donor=comparison -n 500`.** Purpose-built for this family and the one to
  use. It is Example 8 of Kletzander et al. (see [Prior
  art](#prior-art)) — a system of difference constraints whose fixpoint costs
  Θ(n³) with one propagator per constraint — so it is propagation-bound by
  construction, and `--donor` selects between spelling each edge as a
  comparison or as a two-term linear inequality **over an identical search
  tree**. At n=500 that is 63.0M propagator calls of which
  **99% of propagation time is this family**, which is far more
  family-dominated than `ortho_latin` is for `equals` (71% of calls, 18% of
  time).
- **For proof benchmarking: `difference_chain --mode=refute
  --donor=comparison -n 40`.** The refutation closes a negative cycle at the
  root, so the whole proof is propagation with no search in it — 1 recursion.
  n=40 verifies in 0.86 s; n=80 takes 13.41 s, and is the right size only if a
  bigger proof is the point.
- **Do not** read a comparison-versus-linear ratio off any other example: the
  point of `--donor` is that it holds the model and the tree fixed, and no
  other benchmark does.
- `magic_square` and `talent` reach the family too, but both are dominated by
  other constraints.

### CPU performance

*Measured 2026-09-08 at `76bfd836`, Release + `GCS_WERROR=ON`, g++ 15.2.0, AMD
Ryzen 9 9950X3D, 30 GB, otherwise idle, `taskset -c 4`. Min of three.*

| Benchmark | Time | Recursions | Propagator calls | Busiest type |
|---|---|---|---|---|
| `difference_chain --donor=comparison -n 500` | 4.01 s | 503 | 63,004,752 | `less_equal`, 63,004,750 (99.99%) |
| `difference_chain --donor=linear -n 500` | 1.48 s | 503 | 63,253,752 | `lin_less_equal`, 63,253,752 (100%) |

Under `GCS_PROPAGATOR_STATS=time`, `less_equal` takes **99% of 4,993 ms** of
propagation — about **78 ns a call**. A timed run's own wall clock (6.41 s) is
not comparable with an uninstrumented one.

**The two donor arms are the finding.** Same model, same OPB row, same
presolver treatment, and the same search: 503 recursions and 126,251
propagators in both, with propagation counts 0.4% apart (63,004,752 against
63,253,752) and effectful counts 0.13% apart. So this is a per-call cost
comparison and nothing else — and **the comparison spelling costs 2.7x the
two-term linear spelling.** The example was built to ask this question; as far
as this audit can tell, nobody had answered it.

*Instruction and cycle counts, `perf stat`, deterministic, n=300:*

| Arm | Instructions | Cycles | IPC |
|---|---|---|---|
| `--donor=comparison` | 9.984 G | 4.893 G | 2.04 |
| `--donor=comparison`, reasons guarded | 7.642 G | 2.796 G | 2.73 |
| `--donor=linear` | 7.082 G | 1.665 G | 4.25 |

**Most of it is a reason nothing reads.** A `perf record` profile of the
comparison arm puts 51% of cycles in the enforce lambda, and **30% of all
cycles in one `memcpy`** — the `small_vector` construction inside
`ExplicitReason{ReasonLiterals{...}}`. `ReasonLiterals` holds a nested variant,
so each element is large, and each call builds two of them. Every reason
construction in `comparison.cc` — nine of them — is unconditional, where
`gcs/constraints/linear/propagate.cc` routes all of its through
`inference.want_reasons()`. `SimpleInferenceTracker::materialises_reasons` is
`false`, so with proofs off the whole thing is built, never read, and thrown
away. `InferenceTracker`'s own header states the rule: *"A propagator whose
reason is expensive to assemble (a `ConcatReason` allocation, a long
extra-literal walk) should guard that assembly on this query, so it optimises
away whenever nothing will read it."*

Guarding the four reasons on the two enforce passes — the hot ones — was tried
and measured:

| | n=500 time | Recursions | Propagations | Effectful |
|---|---|---|---|---|
| as it is today | 4.01 s | 503 | 63,004,752 | 375,751 |
| four reasons guarded | **2.30 s** | 503 | 63,004,752 | 375,751 |

**1.74x, at a byte-identical search tree**, with 63 of 63 `comparison` and
`difference` ctest lanes green. The guard cannot affect proofs, because reasons
are materialised whenever one is being written.

That is not the whole gap. Guarded, the arm is still 1.55x the linear one, and
the residual is IPC-shaped rather than instruction-shaped (2.73 against 4.25),
which is consistent with the offset view's indirection on every bounds read —
`--donor=comparison` spells each edge `LessThanEqual{x, y + d}`. This audit did
**not** isolate that, and says so rather than guessing: the honest claim is
that the reason accounts for 43% of the cycles and the rest is unattributed.

**Cross-solver comparison: `Not measured.`** #868's harness exists and the
method is written up in `dev_docs/cross-solver-benchmarking.md`, but it has
been pointed at `equals` only. The model question is easier here than it was
there — a system of difference constraints is a model every solver would be
given, and `difference_chain` pins its own search — so this family is a good
second target.

### Proof performance

*Same build and machine. `difference_chain --mode=refute --donor=comparison
-n 40`: 1 recursion, 71,646 propagations, 0.028 s to solve and write the
fully-justified proof. VeriPB 3.0.2.*

| Assertion level | Proof size | Lines | Assertions | VeriPB | Verdict |
|---|---|---|---|---|---|
| `Off` (justify everything) | 4.64 MB | 48,680 | 0 | 0.86 s | `VERIFIED UNSATISFIABLE` |
| `Links` | 1.95 MB | 32,305 | 26,556 | — | — |
| `Inferences` | **0.44 MB** | 5,752 | 5,745 | — | — |

Verification is **30x the solve time** fully justified. At n=80 the same
instance is 20.2 MB and 193,320 lines, verifying in 13.41 s against a 0.132 s
solve — **102x**, and the ratio grows because the proof does.

Asserting inferences cuts the proof by **10.5x**, which is far more than the
44% the same switch buys on `equals`'s benchmark. The reason is the substance
of this section:

**The family's own contribution is one line per inference — 11.8% of the
proof.** Every rule is a bare RUP, so the family writes exactly one `rup` line
per inference and never anything else. Breaking the fully-justified proof down
by line kind:

| Line kind | Count | Whose |
|---|---|---|
| `red` | 16,332 | the shared bit/order-literal definition layer |
| `pol` | 16,127 | the same layer, chaining the order encoding |
| `rup` | 10,472 | **5,742 this family's**, the rest the literal layer proving bounds |
| `del` | 5,743 | the shared layer's temporaries |

5,742 of 48,680 lines, against 42,938 the shared layer emits *around* them —
**8.5 full-proof lines per inference, of which one is ours.** A comparison's
proof cost is almost entirely the cost of defining the order literals it
mentions, which is exactly why dropping to `Inferences` level collapses it: the
`a` line is all that is left.

Of the 5,745 assertions at `Inferences` level, **5,742 (99.9%) carry the
`comparison` hint** — the highest concentration of any family so far, and all
of them the one bare wire form.

**And, as with `equals`, the benchmark exercises a minority of the rules.**
Reading the assertions back: every literal in all 5,742 is a `ge` atom, 5,661
of them a two-literal clause with one literal negated and 81 a single negated
literal (where the reason literal was a root-level unit and resolved away).
That is **rule 1 alone** — no must-not-hold pass, no reified verdict, no
constant pair. `difference_chain` posts `LessThanEqual`, so it reaches one of
the family's seven rules. Anyone quoting a per-inference proof cost from this
table should know it is an average over one rule, and the other six are covered
by `comparison_test`'s 1,356 proofs instead.

## Status, gaps, and next steps

### Proof-logging gaps

**Nothing is left unjustified, and no rule is weakened when proofs are
enabled.** There is no `a`-oracle use, no unlogged inference, and no strength
difference between a proving and a non-proving run. Every one of the seven
rules is a bare RUP against a row the OPB carries under a label the presolver
and cake both agree on.

`None.` on cost gaps in the proof direction, too: the family emits one line per
inference and no lemmas, and there is no view detour or interval degradation
anywhere ([Variable kinds and views](#variable-kinds-and-views)).

The cost gap runs the other way — the propagator pays a *proof-shaped* cost
when proofs are off, by assembling reasons nothing will read. That is a
propagation defect rather than a proof-logging one, and it is in [CPU
performance](#cpu-performance) and [Next steps](#next-steps).

**One sharp edge rather than a gap:** two of the five reification kinds have no
`.scp` spelling and throw from `s_expr()`. Details below.

### Known limitations

**`MustNotHold` and `NotIf` throw when an `.scp` is written, and leave a
truncated file behind** (#908). Both kinds propagate correctly — verified against
brute force, `¬(x ≤ y)` giving exactly the 6 pairs of `x > y` and `¬(x < y)`
the 10 of `x ≥ y` over `[0,3]²` — and both have a correct, labelled OPB row.
What they do not have is a cake spelling, so `s_expr()` throws
`UnexpectedException{"Unexpected reification type in s_expr"}`. Measured:
posting one from the public base class with proofs on writes the `.opb`, a
33-byte `.pbp` and an **88-byte `.scp` cut off mid-`(constraints`**, then
throws.

This is known and worked around where it has to be:
`constraint_row_test.cc` sets `names.s_expr_file = nullopt` with a comment
saying exactly why, and it is the one test that needs those forms. The
limitation is worth recording rather than fixing on sight for two reasons —
nothing in `gcs` posts either kind, and the *linear* family has the identical
gap, so a fix belongs to both at once. But two things make it sharper than the
code comments suggest. The base class is public, so "there is no user-facing
class for them" is true of the twelve named classes and not of the family. And
the failure is not clean: a partial `.scp` on disk is worse than none.

The spelling itself is mechanical, which is what makes this a small piece of
work rather than a design question: `MustNotHold` with `or_equal` emits exactly
the row `LessThan{right, left}` emits, so it *is* `(id less_than right left)`.
`constraint_type()` would need the same swap-and-flip.

**Half-reified forms are unreachable from every frontend.** The four `*If`
classes exist, propagate, and are the difference-logic presolver's most
valuable donor shape — a half-reified edge is where the paper's scheduling wins
come from — and neither frontend produces one. MiniZinc's flattener never
half-reifies because `minizinc/mznlib/` declares no `*_imp` predicates; the
XCSP3 binding turns a top-level `imp(b, le(...))` into an `Or` over a fully
reified control. Declaring `int_lin_le_imp` is the obvious step and changes
flattening for every model, so it wants measuring on its own.

**The negated forms are a deliberate presolver gap (#598).** `DifferenceLogic`
lifts `MustHold` and `If` donors and counts `MustNotHold` / `NotIf` under
`skipped_reified`, even though those rows are now perfectly citable. Both this
family and the linear family are skipped the same way, and the issue's argument
for closing them together rather than one at a time is the right one. Note the
strictness flip is the risk there: an off-by-one inverting an edge is
*unsound*, not merely incomplete.

**Aliased operands under a strict comparison throw at construction rather than
being reported as infeasible.** `LessThan(x, x)` is a modelling error and
`InvalidProblemDefinitionException` says so, but a model generator that can
emit one has to catch it rather than getting an unsatisfiable problem. The
reified forms behave the other way — `LessThanIff(x, x, c)` cheerfully forces
`¬c`. Deliberate, and worth knowing.

### Next steps

Ranked. Two are findings of this audit and neither is filed yet; the third is
the audit-wide prerequisite.

1. **#907 — guard the reason assembly on `want_reasons()`.** Nine reason
   constructions in `comparison.cc`, none guarded; the four on the enforce
   passes are the hot ones and guarding just those is **1.74x on
   `difference_chain -n 500`** (4.01 s to 2.30 s) at a byte-identical search
   tree, with 63 of 63 relevant ctest lanes green. The pattern is
   `gcs/constraints/linear/propagate.cc`'s, which routes every reason through
   the same query, and `equals`'s #864 was the same defect in a more dramatic
   form. This is the largest single win the audit found and it is a handful of
   lines; the remaining five sites belong to the reified verdicts and the
   both-constant initialiser, which are not hot but should go the same way for
   uniformity. A working patch is preserved at
   `~/claude/tmp/famdocs-findings/`.
2. **Find out what the rest of the comparison-versus-linear gap is.** Not
   filed. Guarded, the comparison spelling is still 1.55x the two-term linear
   one on an identical tree, and the difference is IPC-shaped rather than
   instruction-shaped — consistent with the offset view's indirection on every
   bounds read, but not isolated. It matters beyond this family: if a view
   costs that much on a bounds read, it is a fact about the view layer, not
   about comparisons, and every family that accepts views inherits it. The
   experiment is small — the same chain with and without a zero-offset view —
   but it needs a propagation-bound harness, and the obvious two-line probe is
   not one (tried; search dominated it).
3. **#868 — point the cross-solver harness at this family.** The harness and
   method exist and have been used for `equals` only. This family is an easier
   target than that one was: a system of difference constraints is a model any
   solver would be given, and `difference_chain` pins its own search, so the
   "which model is defensible" question that dominated #868 for `equals`
   answers itself.

**Not to do, having been considered.**

*Recovering a two-variable `Comparison` from a two-term linear inequality in
`fzn_glasgow.cc`,* the way that file recovers `Equals` from a two-term
`int_lin_eq`. The `equals` recovery is a strength gain — `Equals` intersects
domains where a linear equality is bounds-consistent — and there is no
analogous gain here, since both spellings are bounds-consistent. The measured
per-call costs say the recovery would be a 2.7x **loss** today, and 1.55x after
item 1.

*Tuning the trigger set.* `on_bounds` is already the coarsest trigger that can
see everything any pass reads, and every pass self-disables once the bounds
separate. There is nothing here of the kind #819 and #889 found in `equals`.

## Prior art

- **Kletzander, Dekker, Schutt and Stuckey, "Global Difference Constraint
  Propagation for Constraint Programming".** The reason this family has a
  purpose-built benchmark: their Example 8 is a system of difference
  constraints whose fixpoint costs Θ(n³) to reach with one propagator per
  constraint and Θ(n²) with a global one, and `examples/difference_chain/` is
  it. The paper is about the global propagator; what it makes measurable here
  is the *decomposed* case, which is this family.
- **The justification is entirely published, and there is nothing novel on the
  proof side.** Every rule is JP 3.2 or a Theorem 2.6 reduction to it, from
  McIlree's thesis (2026) — which also states the strength claim below, as the
  reason a comparison's justification is simple: *"Because bounds-consistency
  and domain-consistency are equivalent for this constraint, the only kind of
  inference we need to be able to justify is `y≥v ∧ x≥u ⇒ 0 ≥ 1`."* This is the
  first family in the arc with a completely empty novelty column, and that is a
  useful thing for the paper to be able to say about something.
- **The propagation algorithm has no literature and does not need one.** A
  binary inequality is two bound pushes; nobody publishes that. As with
  `equals`, the interesting content is on the proof side — and here it is
  interesting for being *absent*: one definitional row, no flags, no
  scaffolding, one RUP per inference. If the proof-logging-for-CP paper wants a
  baseline against which to measure what a hard constraint's certificate costs,
  this family is it.
- **The one non-obvious claim in the family is a strength claim**, and it is
  folklore rather than published: bounds pruning on a binary comparison
  achieves domain consistency, because support for a value of one operand
  depends only on the other's extreme value. It is asserted at every search
  node by `solve_for_tests_checking_gac` rather than argued, which is the right
  way round.

## Further reading

- [`dev_docs/justification-techniques.md`](../justification-techniques.md) —
  what licenses the `RUP` in all seven rules. For this family it is one
  procedure (JP 3.2) and one theorem (2.9), and the theorem's `B ∈ {0,1}`
  precondition happens to be exactly the family's two row shapes, so this is
  the cheapest family in the arc to read alongside it.
- `dev_docs/constraints.md` — the generic three-phase structure, the inference
  and justification APIs, and the OPB building blocks this family uses without
  extending.
- `dev_docs/reification.md` — `ReificationCondition`,
  `EvaluatedReificationCondition` and `install_reified_dispatcher`, which carry
  all eight reified forms here.
- `dev_docs/difference-logic.md` — the presolver that consumes this family, the
  global propagator it lifts into, and its proof logging. The `pol` steps there
  cite the rows [Labels](#labels) describes, so the two documents share an
  interface.
- `dev_docs/variable-encodings.md` — the in-OPB versus in-proof axis this
  family sits entirely on the OPB side of, and the order-literal layer that
  turns out to be 88% of its proof.
- `dev_docs/propagator-performance.md` — where the trigger-granularity results
  for the neighbouring families live, and the `GCS_PROPAGATOR_STATS` caveats
  used above.
- `dev_docs/cross-solver-benchmarking.md` — the identical-tree method, for
  whoever picks up item 3.
- `dev_docs/large-domains.md` — the audit lane carrying this family's three
  `Clean` rows, and why a `Clean` row usually needs more scepticism than it
  does here.
- [`equals.md`](equals.md) — the sibling family, and the document to read
  beside this one. The two are the same shape and differ in exactly the places
  worth noticing: `equals` needs proof flags and this does not, `equals` has
  two view detours and this has none, `equals` had its trigger set tuned twice
  and this has nothing to tune.

## Developer commentary

`None.` The family predates the practice of writing design notes. Its inline
comments are unusually good on the two things a reader will get wrong — the
label-role contract in `define_proof_model` and `primary_row_role`, and the
operand normalisation in `s_expr()` and the `\name Posted arguments` block of
the header — and this document does not duplicate them.

**What this family changed in the template.** `None.` The skeleton fitted
without modification, which is the first time that has happened; the pilot
reshaped it and the pilot's re-audit added four fields. Two things are worth
recording as evidence *for* the current shape rather than against it. The
per-rule `Tightness` field, added by the re-audit, answers `Not shown.` seven
times here, and reads as a fact about the family rather than a to-do list —
which is what the policy note in [`TEMPLATE.md`](TEMPLATE.md) intended. And the
"say what the benchmark does not exercise" requirement, also from the
re-audit, caught the same shape of thing it caught for `equals`: one rule of
seven, found by the same `awk` over assertion polarities.

The one place the template's shape did real work was [Relation to other
families](#relation-to-other-families). Its fifth direction, **shared code**,
was added by the pilot for `enforce_equality`; this family shares no code with
anything, and what it has instead is a *published read interface* that a
presolver depends on. That is a sixth direction, and rather than add it on one
example, this document says so in prose and leaves the vocabulary alone — the
next family that consumes or is consumed by a presolver should settle it.
