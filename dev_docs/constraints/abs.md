# Abs: one variable is the absolute value of another

> **Maturity** production ·
> **Audited** 2026-09-23 at `f28fdef8` ·
> **Open issues** filed by this audit: #1058 (a constant `v2` removes `v1`'s
> values one at a time, in time and proof lines linear in the constant),
> #1057 (the propagator reaches its own fixpoint but does not claim
> idempotence; claiming it is 18–20% on `celar`). Found here but not this
> family's: #1056 (the test harness's idempotence-claim checker is silently
> off in 100 of the 317 lanes that use it, `abs_constraint` among them).
> Already open and touching this family: #868 (cross-solver). Tracked under
> #871.

`Abs(v1, v2)` says `v2 = |v1|`. It is one class, with one initialiser and one
propagator, and the propagator is generalised arc consistent: bounds both ways,
then the values of `v2` with no preimage and the values of `v1` whose absolute
value `v2` has lost. Its bound and range proofs resolve the model's two
half-reified rows by `pol`, because unit propagation can neither split on
`v1`'s sign nor cross the negative branch's row, which is a sum rather than a
difference. Its single-value removals are plain RUP.

Three things to know before touching it.

- **It is generalised arc consistent in a single call, and does not say so.**
  Removing a value from one side never removes a support on the other, so one
  call reaches the fixpoint. It returns `PropagatorState::Enable`, so the engine
  requeues it after its own inferences. Returning `EnableButIdempotent` instead
  passes 212 runs with the claim checked, over every view wrap, and cuts
  `celar`'s time by 18–20% at the same node count (#1057).
- **A constant `v2` falls off the interval path.** The range justifications
  resolve against order atoms of both operands, and a constant has none. So with
  `v2` a constant `c`, `v1`'s interior `[−c + 1, c − 1]` is removed one value at
  a time, about 13 proof lines each: 3.1 s at `c = 10⁷`, and 260,030 lines at
  `c = 10⁴`, where a one-value **variable** takes 0.1 ms and 137 lines at any
  `c`. MiniZinc's `celar` reaches it, and pays 30% of its proof lines and 43% of
  its checking time for it (#1058).
- **It is most of the propagation on `celar`, where we are about five times
  slower than Gecode.** `Abs` is 55–64% of propagation time on both `celar`
  instances. The whole solver takes 4.8 and 5.6 times as long as Gecode to the
  same solution, at node counts within 4% either way. How much of that gap is
  `Abs`'s was not isolated.

## What it is

### Semantics

`Abs(v1, v2)`: `v2 = |v1|`. Degenerate shapes:

- **Constants**: `abs(c1) == c2` is decided at the root. #254's six rows cover
  both outcomes; two more post one-value variables, and two mix a constant with
  a one-value variable.
- **`Abs(x, x)`**: `x = |x|`, so `x ≥ 0`. Five rows of `run_dup_abs_test`.
- **A negative constant `v2`**: unsatisfiable, and caught by the bounds rules
  (3 and 4), which pull `v1` above and below zero at once.
- **Two views of one variable**, such as `Abs(x, −x)` or `Abs(x + 2, x)`: legal,
  and not in the tests; see [Variable kinds and views](#variable-kinds-and-views).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Abs` | ✓ `int_abs` | ✓ `abs` and `dist` inside `intension`[^xabs] | ✓ `abs(x) == y`, through `gcspy`'s `post_abs` | ✓ `abs` | |

[^xabs]: The intension walker gives `abs(e)` an auxiliary result `absresult`
    whose domain is the image of `e`'s bounds, and posts `Abs{e, r}`. `dist(a,
    b)` becomes a difference variable `a − b` by a linear equality, then `Abs`
    on it. `frontend-support-matrix.md` has no row for either; they sit under
    its `intension` row.

CPMpy's upstream GCS interface, checked 2026-09-23, posts `abs(x) == y` as
`post_abs(x, y)`, asserting that `abs` has one argument; its comment adds
that the argument must not be a nested expression.

### Options

`None.` There is no `with_consistency()`, and nothing else to set.

### Variable kinds and views

Any `IntegerVariableID` in either position. The proof handles views, as it has
since the representation-consistency work that `view-proof-logging.md`
describes. Abs and `AllDifferent` were the two hard cases there, and both now
verify under every wrap. `abs_constraint_view_mixed` wraps both positions, and
the hole rows run under the wrap too.

**A constant is the one kind the proof treats differently.** The range
justifications (rules 6 and 8) resolve against an order atom of each operand,
and a constant has none, so a constant operand sends both interior loops down
their per-value arm. With `v1` constant that costs nothing, because the bounds
rules fix `v2` first. With `v2` constant it is the hazard in [Interval
efficiency](#interval-efficiency).

**Aliased views** are not in the tests. This audit's differential posted
`Abs(a₁·x + c₁, a₂·x + c₂)` for `a` in `{1, −1}`, `c₁` in `{−3, 0, 2}`, `c₂` in
`{−2, 0, 3}` and four ranges of `x`: 144 instances, every one matching brute
force, every proof verified.

### Reification

`None.` MiniZinc has no reified `int_abs`; a reified use flattens to `int_abs`
over an auxiliary and a reified comparison. Nothing asks for one.

### Relation to other families

**Into this family.** MiniZinc's `int_abs`; XCSP3's `abs` and `dist`; CPMpy's
`abs`; the `.scp` reader. `examples/crystal_maze --abs` posts it instead of three
`NotEquals` per edge.

**Posts as children.** Nothing.

**Shares code.** Nothing. `abs/justify.{hh,cc}` is used by `abs.cc` alone.
`arithmetic-proofs.md` says `product_justify` is written "in the style of"
it, which is a family resemblance, not shared code.

**Presolvers.** None reads or rewrites `Abs`.

**Reached only through a decomposition?** No.

**The candidate merge, settled: not merged into `arithmetic`.** The family list
kept `abs` separate "for now because of the view-proof gap". That gap is
closed, so the stated reason no longer holds, but the answer stands on others.
`Abs` has its own directory, its own encoding (Encoding Procedure 3.3, which is
`cake_pb_cp`'s), and its own justification helpers. The arithmetic family's
products are built on sign-magnitude channels and a bit-product grid, and share
none of it. This is the same answer `comparison` gave `equals`: similar in
shape, no shared code, separate encodings, so separate documents.

## The proof model

### OPB encoding

Definitional, and exactly Encoding Procedure 3.3 of McIlree's thesis:

```
v1 ≥ 0  ⇒  v2 − v1 = 0          ≤ half labelled posge, ≥ half posle
v1 < 0  ⇒  v2 + v1 = 0          ≤ half labelled negge, ≥ half negle
```

Two half-reified equalities, each written as two inequalities, so four rows,
gated on `v1`'s sign atom. That `v2 ≥ 0` follows is a consequence, and is
derived, not stated (rule 1). The size is independent of both domains: four rows
over `BinEnc(v1)` and `BinEnc(v2)`.

### Labels

The labels are `cake_pb_cp`'s, which names them by the direction of the slack,
so the half that says `v2 ≥ v1` is `posle`:

| Row | Label | Captured as | Used by |
|---|---|---|---|
| `v1 ≥ 0 ⇒ v2 ≤ v1` | `posge` | `_abs_nonneg_lines.first` | rules 2, 6, 8 |
| `v1 ≥ 0 ⇒ v2 ≥ v1` | `posle` | `_abs_nonneg_lines.second` | rules 1, 3, 5, 6, 8 |
| `v1 < 0 ⇒ v2 ≤ −v1` | `negge` | `_abs_neg_lines.first` | rules 2, 6, 8 |
| `v1 < 0 ⇒ v2 ≥ −v1` | `negle` | `_abs_neg_lines.second` | rules 4, 5, 6, 8 |

The propagator reaches them by line number, captured in `define_proof_model`.

### Cake conformity

| Case | Chain | `opbdiff` |
|---|---|---|
| `scp_chain_abs_sat` (`x ∈ −3..3`, `y ∈ 0..3`, enumerate) | full workflow 2 | `strict` |
| `scp_chain_abs_unsat` (`y ∈ 4..7`) | full workflow 2 | `strict` |

Both report `OK: full workflow-2 chain passed` at `f28fdef8`, with
`cake_pb_cp` and `opbdiff` on the path, so the OPB matches cake's label for
label. Neither case starts with a hole, a view or a constant. Search makes
holes, so the chain does see the preimage rules: `abs_sat`'s proof has rule 9's
single-value RUPs and a rule 8 `pol` triple. The image rules (6 and 7) were
not looked for in it.

### Proof-time state

- **No proof flags and no proof-only variables.** Every derivation resolves the
  four model rows against order-literal definitions, which the names-and-IDs
  tracker introduces on demand (`need_pol_item_defining_literal`). An external
  tool finds the rows by label and the literals by name.
- **At the root**, the initialiser emits its four bounds (rules 1–4) with their
  `pol`s at `ProofLevel::Temporary` and the conclusions at the root.
- **Lazily**, each propagator inference emits its lemmas at `Temporary`.
  Nothing is cached and nothing outlives its inference.
- **Constant `v1`**: the five bound helpers return at once, and the inference
  is a plain RUP, because the relevant half is then unreified in `v1` and closes
  by itself. The range helpers are never reached with a constant operand.
- **The captured line numbers are optional**, and empty with proofs off, because
  `define_proof_model` does not run then. Every capture dereferences inside the
  justification, which does not run either; a comment at the range rule says so.

## The implementation

### Initialisation and global data

Nothing at construction. `install_propagators` adds one initialiser, at
`InitialiserPriority::SimpleDefinition`, that infers rules 1–4 once at the root,
with no reason, and returns at once when `v2` is a constant. Two of its bounds
are skipped when `v2`'s upper bound is below zero, or at most zero, to avoid
naming an atom that coincides with the sign atom. The propagator detects that
case directly.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| consequence-bound initialiser | initialiser | — | 1–4 | always, unless `v2` is a constant | n/a | one shot |
| the `Abs` propagator | `on_change`: `v1`, `v2` | derived: both, truthfully | 2–9 | always | **is, and does not claim it** (#1057) | never |

**Idempotence.** One call reaches the propagator's fixpoint when `v1` and `v2`
are different variables. A value of `v2` is supported by `±w` in `v1`, and a
value of `v1` by `|u|` in `v2`. A value removed from either side has no support
on the other, so it never was a support, and removing it cannot remove support
from anything left. The bound rules remove only values outside the image or
preimage. So a second call infers nothing. The propagator returns `Enable`
anyway.

This audit checked the claim by making it, behind a local switch, and forcing
the checker on: 25 seeds bare and 25 mixed-view, and all 18 view wraps at every
position choice (both, `v1` only, `v2` only) over three seeds, 212 runs with no
failure. A control confirms the checker would catch it: a variant that
skips the interior loops on a call where a bound rule fired, while claiming
idempotence, is rejected with "claimed idempotence, but re-running it did more".
The engine ignores a claim when positions alias (`positions_alias`), so
`Abs(x, x)` and the aliased views stay requeued. The measured effect is under
[CPU performance](#cpu-performance).

**It never disables itself**, even with both operands fixed.

**Holes affect**: both operands, and the triggers tell the truth. A hole in `v2`
removes `v1`'s values on both sides of zero, and a hole in `v1` removes values
from `v2`, through the two interior loops.

### Mutable state and incrementality

**Nothing persists between calls.** Each call copies both domains
(`copy_of_values`), builds the image of `v1` and the preimage of `v2` as vectors
of pieces, sorts and merges each into an `IntervalSet`, and walks
`each_interval_minus` against them. That is proportional to the domains'
interval counts, not their widths, but it allocates every call.

**What maintaining it would buy.** On `celar` 2013, the propagator's own code is
12.5% of the profile. The interval generators, `pieces_to_set` and
`copy_of_values` are at least another 15.1%, most of it presumably `Abs`'s,
though the generators are shared and callers were not separated. Allocation,
shared with everything else, is another 10%. So no saving is claimed. The
cheaper win is not recomputing at all: #1057's claim removes about 3.0
million of `Abs`'s 6.8 million calls on `celar` 2013, 44%, which is 19% of all
propagator calls there.

### Interior values and optional pruning

**What this family offers:** `None.` There is one level, `GAC`, and no
`consistency::Auto`.

**What this family observes:** holes in both operands, as the inventory says.
`celar`'s frequency domains are sparse, so the interior rules have work there.
Whether that is why our search differs from Gecode's bounds-consistent `abs`
was not isolated: on one instance we explore 4% fewer nodes, and on the other
2% more.

### Robustness and limits

- **Unbounded domains.** The bound rules and both range rules are constant work
  and constant proof per inference. A probe removing `k` runs of width `w − 1`
  wrote proofs with identical line counts at `w = 10`, `10³` and `10⁶`; the
  bytes grow with the numbers' digits. The exception is a
  constant `v2`; see [Interval efficiency](#interval-efficiency).
- **Negative values and zero.** A run of `v1` that straddles zero is split
  there before the preimage rule proves it, because its negation would decide
  nothing about `v1`'s sign. An image piece that straddles zero is `[0,
  max(−a, b)]`. The `preimage_far` hole row reaches the first, whose removed run
  straddles zero, and `image_gap` the second, through `v1`'s piece `[−1, 1]`.
- **Degenerate shapes**: see [Semantics](#semantics).
- **Overflow.** The arithmetic is `-v1_lb`, `-v2_ub`, the image and preimage
  endpoints, and `abs(val)`, all on `Integer`, which throws on overflow rather
  than wrapping. Only a domain at the edge of the 64-bit range could reach it.

### Interval efficiency

1. **Propagation.** `State`'s per-value iterators are used nowhere. The bounds
   are `O(1)`. The image and preimage are built from `each_interval`, and the
   removals found by `each_interval_minus`, so the work is in intervals. Two
   hand-written per-value loops remain, one per direction, each counted by a
   `LargeDomainIterationCounter`. They run over a removal of width 1, which is
   one step, and over **any** removal when an operand is a constant. With `v1`
   constant that is nothing, because `v2` is already fixed. **With `v2`
   constant it is `2c − 1` steps**, which is the #1058 hazard: 0.033 s at
   `c = 10⁵`, 0.33 s at `10⁶`, 3.1 s at `10⁷`, against 0.1 ms for a one-value
   variable at every `c`.
2. **Reasons.** One or two literals per inference, each a range or a bound:
   `{v1 ∉ [lo, hi], v1 ∉ [−hi, −lo]}` for an image removal, and for a preimage
   one `{v2 ∉ [lo, hi]}` when the piece is non-negative, `{v2 ∉ [−hi, −lo]}` when
   it is negative. Built unconditionally, but constant-sized, so an
   unguarded build costs nothing that matters.
3. **Proofs.** Per run, not per value, and the form is chosen by width: a run of
   two or more values takes the range rule, a single value the value rule. **And
   by kind**: a constant operand takes the value rule for every value. That is
   the shape #924 fixed in `Element` and #931 fixed for views here (the choice
   depending on the kind of a variable rather than on width). For a constant it
   is a real limitation of the helper, not an oversight: the range lemmas name
   order atoms of both operands.
   A constant `v2` costs about 13 lines per removed value, so 260,030 lines at
   `c = 10⁴` against 137 for a one-value variable. #1058 suggests the range
   derivation with the constant folded into the row, which needs no atom of
   `v2`.
4. **The audit lane.** Five rows, all `Clean`: `Abs` (two wide variables, which
   reach neither interior loop), `Abs/hole` and `Abs/hole-preimage` (one per
   loop), and `Abs/view-hole` and `Abs/view-hole-preimage` (the same with one
   operand wrapped, which tripped before #931). **None has a constant operand**,
   so the one path that still walks values is unprobed, though the comment on
   `Abs/view-hole` names it: "the one genuine exemption left is a constant".
   There is no `Abs` row in the pinned `"Large domain proof sizes"` case. The
   unpinned survey in `large-domains.md` has `Abs/hole` flat at 30 OPB rows and
   78 proof steps from `10³` to `10⁴`, and `Abs/hole-preimage` at 26 and 113.

## Inference catalogue

Nine rules. Rules 1–4 are consequence bounds that the initialiser infers at the
root with no reason; rules 2–4 are also inferred by the propagator, under a
reason, with the same derivation. Rule 5 is the propagator's lower bound on
`v2`. Rules 6–9 are the interior removals, one range rule and one value rule per
direction.

Four facts hold across them.

**The wire inventory is one form.**

| Wire form | Hint type | Rules |
|---|---|---|
| `abs:((constraint_id N))` | `hints::Abs` | 1–9 |

`hints::Abs` carries `originator` (`ConstraintID`) and no subhint. The nine
rules are nonetheless told apart by the assertion's shape once the `.scp` says
which operand is `v1`: an upper bound on `v2` is rule 2, a lower bound on it
rule 1 or 5, bounds on `v1` rules 3 and 4, and a range or a value removed from
either operand one of rules 6–9. Rules 1 and 5 share a shape, and are told
apart by the bound: rule 1's is always 0, rule 5's always at least 1.

**What licenses them.** The thesis gives the encoding (Encoding Procedure 3.3)
and no justification procedure, so every derivation here is **ours**. Rules
1–6 and 8 share one shape: a `pol` that adds a model row to the defining items
of the order atoms whose arithmetic it uses, and saturates. The operands' bit
sums cancel, and what is left is a clause over order atoms, conditioned on
`v1`'s sign; then the conclusion is RUP. Rules 7 and 9 are plain RUP, because a
single value pins every bit. Two reasons keep the others off RUP. For the bound
rules, `abs.cc` says that RUP cannot case-split on `v1 ≥ 0 ∨ v1 < 0`. For the
range rule 6, `large-domains.md` records why the two-lemma RUP shape of
**Theorem 2.9** fails. The non-negative row is a difference and would take it.
The negative row is a sum, whose negation gives two lower bounds rather than a
lower and an upper, and on `abs_test`'s own `v1 ∈ [−6, 8]`, `v2 ∈ [0, 15]`,
nothing propagates (Proposition 2.1). `pol` does not care, and is used on both
branches so that there is one shape.

**Justifications do not read `state`.** Every helper takes the reason, the
operands and the captured row numbers, and the bounds it needs are passed in
from the propagator. The one exception in spirit is that the propagator passes
bounds it read from `state` as the inference's own parameters, which is the
normal pattern.

**Tightness.** No mutation lane. For rules 6 and 8, #875's work removed each
proof line in turn and then each justification whole: the whole justification
is rejected, but eight of twelve lines are individually droppable, because
VeriPB's unit propagation has more than one route. `large-domains.md` records
it as the reason to sabotage whole justifications rather than lines.

### Rule: v2-nonneg

(Rule 1.)

- **Infers** — `v2 ≥ 0`.
- **Fires when** — the initialiser, once, at the root; it changes something when
  `v2`'s declared lower bound is negative. Skipped when `v2` is a constant.
- **Strength** — `partial`: part of `bounds(Z)` on `v2`.
- **Algorithm** — `O(1)`.
- **Why it is true** — an absolute value is never negative.
- **Proof technique** — `pol` then `RUP`, ours: the `posle` row (`v2 ≥ v1` under
  `v1 ≥ 0`) plus the definitions of `v1 ≥ 0` and `v2 < 0`, saturated. With `v1`
  a constant, plain `RUP`.
- **Reason** — none.
- **Assertion** — `v2 ≥ 0`.
- **Hint** — `hints::Abs`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`: the derivation cites this
  constraint's `posle` row, which the hint's constraint id and the label find.
- **Proof size** — one `pol`, one RUP.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: v2-upper

(Rule 2.)

- **Infers** — `v2 ≤ M`, where `M = max(ub(v1), −lb(v1))`.
- **Fires when** — the initialiser; and the propagator, when `M < ub(v2)`
  (skipped when `v2` is a constant).
- **Strength** — `partial`: part of `bounds(Z)` on `v2`.
- **Algorithm** — `O(1)`.
- **Why it is true** — `|v1|` is at most the larger magnitude of `v1`'s bounds.
- **Proof technique** — `RUP sequence` and `pol`, ours. Two lemmas state `v1`'s
  bounds under the reason, in the view's own encoding so that they cancel
  against the model rows. Then two `pol`s, `posge` with the upper lemma and
  `negge` with the lower one, each against the definition of `v2 > M`, and a
  RUP.
- **Reason** — `{v1 ≥ lb, v1 ≤ ub}` in the propagator; none at the root.
- **Assertion** — `v2 ≤ M ∨ ¬reason`.
- **Hint** — `hints::Abs`.
- **Offline reconstructibility** — `hinted`, as rule 1.
- **Proof size** — two RUP lemmas, two `pol`s, one RUP.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: v1-upper

(Rule 3.)

- **Infers** — `v1 ≤ ub(v2)`.
- **Fires when** — the initialiser, unless `ub(v2) < 0` or `v2` is a constant;
  and the propagator, when `ub(v2) < ub(v1)`.
- **Strength** — `partial`: part of `bounds(Z)` on `v1`.
- **Algorithm** — `O(1)`.
- **Why it is true** — `v1 ≤ |v1| = v2`.
- **Proof technique** — `RUP sequence` and `pol`, ours: a lemma for `v2 ≤ ub`
  under the reason, then `posle` with it and the definition of `v1 > ub`, then
  that definition against the one for `v1 < 0`, then RUP.
- **Reason** — `{v2 ≤ ub}`; none at the root.
- **Assertion** — `v1 ≤ ub(v2) ∨ ¬reason`.
- **Hint** — `hints::Abs`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — one lemma, two `pol`s, one RUP.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: v1-lower

(Rule 4.)

- **Infers** — `v1 ≥ −ub(v2)`.
- **Fires when** — the initialiser, unless `ub(v2) ≤ 0` or `v2` is a constant;
  and the propagator, when `−ub(v2) > lb(v1)`.
- **Strength** — `partial`, as rule 3.
- **Algorithm** — `O(1)`.
- **Why it is true** — `−v1 ≤ |v1| = v2`.
- **Proof technique** — as rule 3, mirrored through `negle` and the definition of
  `v1 ≥ 0`.
- **Reason** — `{v2 ≤ ub}`; none at the root.
- **Assertion** — `v1 ≥ −ub(v2) ∨ ¬reason`.
- **Hint** — `hints::Abs`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — as rule 3.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: v2-lower-by-sign

(Rule 5.)

- **Infers** — `v2 ≥ lb(v1)` when `v1 ≥ 1`, or `v2 ≥ −ub(v1)` when `v1 ≤ −1`.
- **Fires when** — the propagator, when `v1` is on one side of zero and the
  bound exceeds `lb(v2)`. Skipped when `v2` is a constant.
- **Strength** — `partial`: with rules 1 and 2, `bounds(Z)` on `v2`.
- **Algorithm** — `O(1)`.
- **Why it is true** — on one side of zero, `|v1|` is at least the magnitude of
  the bound nearer zero.
- **Proof technique** — `RUP sequence` and `pol`, ours: a lemma for `v1`'s bound
  under the reason, then `posle` (or `negle`) with it and the definition of
  `v2 < bound`, then RUP. The other sign branch is closed by the reason.
- **Reason** — `{v1 ≥ lb}` or `{v1 ≤ ub}`.
- **Assertion** — `v2 ≥ bound ∨ ¬reason`.
- **Hint** — `hints::Abs`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — one lemma, one `pol`, one RUP.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: image-range

(Rule 6.)

- **Infers** — `v2 ∉ [lo, hi]`, for a run of `v2` of two or more values that
  neither `lo..hi` nor `−hi..−lo` meets in `v1`.
- **Fires when** — the propagator's image loop, after the bound rules, when
  neither operand is a constant. `each_interval_minus` of `v2` against `v1`'s
  image, clipped to `v2`'s new bounds.
- **Strength** — `partial`; with rule 7, `GAC` on `v2`.
- **Algorithm** — the image of `v1` is built from its intervals: a piece at or
  above zero maps to itself, one below zero to its mirror, one straddling zero
  to `[0, max(−a, b)]`. Then one `each_interval_minus`. In **intervals**.
- **Why it is true** — `v2 = w` needs `w` or `−w` in `v1`.
- **Proof technique** — `pol` and `RUP sequence`, ours. Four `pol`s, one per
  model row, each the row plus two atom definitions: on the non-negative branch
  `v2 ≥ lo` carries to `v1 ≥ lo` and `v2 ≤ hi` to `v1 ≤ hi`, and on the negative
  branch to `v1 ≤ −lo` and `v1 ≥ −hi`. Then two RUP lemmas under the reason,
  one per sign, each leaving only the sign atom. The two signs are a literal and
  its negation, so the conclusion is RUP. The lemmas are spelled with two order
  atoms rather than the range literal, so no range flag is needed.
- **Reason** — `{v1 ∉ [lo, hi], v1 ∉ [−hi, −lo]}`: two range literals. Minimal.
- **Assertion** — `v2 ∉ [lo, hi] ∨ ¬reason`.
- **Hint** — `hints::Abs`.
- **Offline reconstructibility** — `hinted`: the run is the assertion's, the
  rows are this constraint's.
- **Proof size** — four `pol`s, two lemmas and a RUP per run, **independent of
  its width**: measured identical at run widths 9, 999 and 999,999.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` by a lane; see the catalogue preamble for #875's
  check.

### Rule: image-value

(Rule 7.)

- **Infers** — `v2 ≠ w`.
- **Fires when** — the image loop, for a run of one value, and for every value
  of any run when either operand is a constant. With a constant `v2` that is at
  most its one value; with a constant `v1`, `v2` is already fixed. So this rule
  is never wide.
- **Strength** — `partial`; see rule 6.
- **Algorithm** — one `in_domain` per value of the run.
- **Why it is true** — as rule 6.
- **Proof technique** — `RUP sequence`, ours: two lemmas under the reason,
  `v1 < 0 ∨ v1 = w ∨ v2 ≠ w` and `v1 ≥ 0 ∨ v1 ≠ −w ∨ v2 ≠ w`, then RUP. A
  single value pins every bit of `v2`, and through the active row every bit of
  `v1`, so RUP works here where a range needs rule 6's `pol`s. **The second
  lemma does nothing.** The reason contains `v1 ≠ −w`, so the lemma holds under
  it trivially. The comment above it describes a different line,
  `(v2 = w ∧ v1 < 0) → v1 = −w`. Removing the lemma leaves `abs_test` verifying
  at ten of ten seeds, and so does writing it as the comment says. Removing both
  lemmas fails at nine of ten, which is the control that the mutation was
  built in.
- **Reason** — `{v1 ≠ w, v1 ≠ −w}`.
- **Assertion** — `v2 ≠ w ∨ ¬reason`.
- **Hint** — `hints::Abs`.
- **Offline reconstructibility** — `offline`: each lemma is a RUP whichever rows
  it goes through.
- **Proof size** — three lines.
- **Gaps** — `None.`
- **Tightness** — shown by hand for the pair, not the lemmas: without both
  lemmas VeriPB rejects the conclusion, at nine seeds of ten.

### Rule: preimage-range

(Rule 8.)

- **Infers** — `v1 ∉ [lo, hi]`, for a run of `v1` on one side of zero, of two
  or more values, whose absolute values are not in `v2`.
- **Fires when** — the propagator's preimage loop, when neither operand is a
  constant. `each_interval_minus` of `v1` against `v2`'s preimage, clipped to
  `v1`'s new bounds, and split at zero.
- **Strength** — `partial`; with rule 9, `GAC` on `v1`.
- **Algorithm** — the preimage of each interval of `v2` is its mirror and
  itself, merged. In **intervals**.
- **Why it is true** — `v1 = u` needs `|u|` in `v2`.
- **Proof technique** — `pol`, then `RUP`, ours. The run lies on one side of
  zero, so the conclusion's own negation decides `v1`'s sign, and only the
  active row is needed. Three `pol`s: the sign (`v1 ≥ lo` against `v1 < 0`, or
  the mirror), and the two bounds the row licenses on `v2`. None is stated under
  the reason: all three are consequences of the model alone. Then RUP.
- **Reason** — `{v2 ∉ [lo, hi]}` for a non-negative piece, `{v2 ∉ [−hi, −lo]}`
  for a negative one: one range literal. Minimal.
- **Assertion** — `v1 ∉ [lo, hi] ∨ ¬reason`.
- **Hint** — `hints::Abs`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — three `pol`s and a RUP per piece, independent of width.
  Cheaper than rule 6, because there is no sign case to close.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` by a lane; see the catalogue preamble.

### Rule: preimage-value

(Rule 9.)

- **Infers** — `v1 ≠ u`.
- **Fires when** — the preimage loop, for a piece of one value, and **for every
  value of every run when either operand is a constant**. With `v2` a constant
  `c` that is every value of `[−c + 1, c − 1]`, once, at the root.
- **Strength** — `partial`; see rule 8.
- **Algorithm** — one `in_domain` per value, counted by the large-domain guard.
  Linear in `c` in the constant case (#1058).
- **Why it is true** — as rule 8.
- **Proof technique** — `RUP`: `v1 = u` pins `v1`'s bits, and the active row
  pins `v2`'s to `|u|`, which the reason excludes.
- **Reason** — `{v2 ≠ |u|}`. With `v2` a constant, empty, and the assertion is
  a unit.
- **Assertion** — `v1 ≠ u ∨ ¬reason`.
- **Hint** — `hints::Abs`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line, plus the literal definitions it needs: about 13
  lines per value in total, measured over the constant case.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

| Lane | What it checks |
|---|---|
| `abs_constraint` | `abs_test`: 26 fixed rows (ranges, #446's tight domains, #254's constants, one-value variables) and 30 random ones (both operands ranges, `v1` constant, `v2` constant), each with and without proofs, under `solve_for_tests_checking_gac`, so `GAC` at every node; four hole rows, three for the image loop and one for the preimage loop; five `Abs(x, x)` rows under plain enumeration; nine initialiser-only proof checks (its `bound1` to `bound4` are rules 1, 3, 4 and 2 here) and five over wider domains |
| `abs_constraint_view_mixed` | the same with positions wrapped in views, minus the initialiser and dup rows |
| `scp_chain_abs_sat`, `scp_chain_abs_unsat` | see [Cake conformity](#cake-conformity) |
| `xcsp_intension_arithmetic`, `xcsp_intension_basic` | `eq(abs(x), y)` and `eq(dist(x, y), 1)` |
| `minizinc-abs` | `int_abs` against MiniZinc's default solver |
| `crystal_maze-abs`, `crystal_maze-abs-gac` | the example with `--abs`, proof verified |
| `large_domain_audit_test` | five `Clean` rows; registered only in a build with `GCS_LARGE_DOMAIN_GUARD=ON` |

The nine lanes above that post `Abs` pass at `f28fdef8`, caps off, with
MiniZinc 2.9.7, `cake_pb_cp` and `opbdiff` on the path.
`large_domain_audit_test` was not re-run: this audit's builds have the guard
off, and its rows' outcomes are the ones pinned in the source. At `--seed=1`,
`abs_test` verifies 74 proofs. The data-driven lanes are seeded, and reproduce
with `--seed=N`.

**Runtime caps.** No lane sets or clears one, and **the defaults never fire
here**: three unseeded runs of each data-driven lane with the 300-solution and
1,500-node caps passed in the environment printed no truncation from a
local-only print; a two-solution control fires 44 times. The largest domain in
the random rows is 16 values, so the capped run checks completeness too.

**The idempotence-claim checker is off in `abs_constraint`** (#1056). The
engine reads `GCS_CHECK_IDEMPOTENT_CLAIMS` once, at the first propagation in the
process, and the harness sets it in `solve_for_tests_with_callbacks`. With
VeriPB on the path, `abs_test` runs its initialiser checks first, through
`check_initialisation_only_for_tests`, which propagates before that. So the
checker does not run in the bare lane. `abs_constraint_view_mixed` skips the
initialiser checks and has the checker on, so a claim would be checked there,
over every data and hole row with both positions wrapped. It does not matter
today, since `Abs` claims nothing. Across the suite the checker is off in 100 of
the 317 lanes whose binary uses the harness, over 17 binaries. Every lane tried
with it forced on passes: the 86 lanes whose names match `abs`, `circuit`,
`subcircuit`, `smart_table`, `knapsack_upfront`, `nogoods` or `equals`, and 21
non-mutation scheduling, `dag`, `reachable` and control lanes. Most of the 69
mutation lanes among the 100 were not tried (#1056).

**Rules the tests reach**, from local counters at `--seed=1`: all nine, both
branches of rule 5, and the constant arm of rule 7. **The constant arm of rule
9 is not reached at seed 1**, where all ten constant-`v2` rows are
unsatisfiable: nine fail on the bounds, and one in rule 7's constant arm. Over
seeds 1 to 20 it is reached at 18, 8 to 50 times each, and not at seeds 1 and
19.

**What the tests do not cover:**

- **A constant `v2` of any size.** The random constants are in `[−10, 10]`, so
  the per-value arm is at most 19 values, and no row, lane or audit-lane probe
  pins its cost (#1058).
- **Aliased views.** Only `Abs(x, x)`, whose consistency is not checked. This
  audit's 144-case differential is not in the tree.
- **A claimed idempotence**, because nothing claims one; and in the bare lane
  the checker would not see one anyway.
- **A chain case that starts with a hole, a view or a constant**, as [Cake
  conformity](#cake-conformity) says.

### Benchmarks and examples

- **In-repo**: `examples/crystal_maze --abs`, where `Abs` replaces three
  `NotEquals` per edge (`≠ 0`, `≠ 1`, `≠ −1`). Tiny: its lanes finish in a
  third of a second.
- **The corpus.** `int_abs` appears 1,459 times in 14 of the 297 MiniZinc
  Challenge models flattened for the throw survey (2026-09-05, one instance
  each). Constant operands appear in three: `celar` 2013 and 2016 post 16
  constraints each with a constant `v2` (`|f[x] − f[y]| = 238`, with the
  difference declared within `[−776, 776]`), and `harmony` 2024 posts 31 with a
  constant
  `v1`, which is harmless.
- **Where it is the cost** (share of propagation time, 10 s each,
  `GCS_PROPAGATOR_STATS=time`, at `00797a97`, from `linear.md`'s survey; `abs/`
  is unchanged since): `celar` 2013 63.8%, 2016 55.0%; `roster-sickness` 14.3%;
  `on-call-rostering` 2013 9.3%, `city-position` 8.7%, `fast-food` 8.1% and
  6.4%, `on-call-rostering` 2018 5.8%, `cable_tree_wiring` 5.1%, and under 3% in
  the other five. 0.5–0.9 µs per call, and 2.1 µs on `roster-sickness`.
- **For CPU**: `celar` 2013 (`CELAR6-SUB2`) to its 200th solution, 5.6 s;
  `celar` 2016 (`CELAR6-SUB0`) to its 300th, 0.2 s.
- **For proofs**: `celar` 2013 to its 20th solution, 163 nodes, a 318,150-line
  proof that checks in 29 s.

### CPU performance

All at `f28fdef8`, Release, GCC 15.2.0, fataepyc-09 (EPYC 7643, boost off),
pinned with `numactl --cpunodebind=0 --membind=0 taskset -c 8 setarch -R`,
2026-09-23, on an unmodified build except where a switch is named.

**Against Gecode 6.3.0**, each flattened with its own library and run by its own
FlatZinc binary with `-n N`, three runs each. `celar` writes plain `abs`, so
Gecode posts its bounds-consistent `AbsBnd`; ours is `GAC`, so the two searches
are not the same, and differ by a few per cent in nodes.

| instance | N | GCS nodes | GCS s | Gecode nodes | Gecode s | ratio |
|---|---|---|---|---|---|---|
| `celar` 2013 | 200 | 68,754 | 5.573 / 5.577 / 5.629 | 71,696 | 1.172 / 1.173 / 1.175 | 4.8× |
| `celar` 2016 | 300 | 3,075 | 0.214 / 0.214 / 0.215 | 3,005 | 0.038 / 0.038 / 0.038 | 5.6× |

Both reach the same objective at the Nth solution (15,071 and 21,036). In 30 s
each, the two find the same sequence of objectives, ours a prefix of Gecode's:
284 against 285 solutions on 2013, while exploring 378,167 and 1,896,517 nodes
in that time.

**Where the time goes**, `perf` on 2013 to the 200th solution, by symbol: the
`Abs` propagator's own code 12.5%, `each_interval_minus` 6.4%, `each_interval`
5.6% over two symbols, `pieces_to_set` 2.4%, `copy_of_values` 2.0% and the
generators' `begin` 1.1%; the linear propagators about 13%;
`Propagators::propagate` 7.1% and `new_epoch` 4.2%; allocation and copying
about 10%.

**The idempotence claim** (#1057), as a local switch in an otherwise
unmodified build, with the counters compiled out:

| instance | N | nodes (both) | propagations | as today | claiming | unmodified build |
|---|---|---|---|---|---|---|
| `celar` 2013 | 200 | 68,754 | 15,759,399 → 12,756,238 | 5.661 / 5.655 / 5.692 s | 4.539 / 4.526 / 4.518 s | 5.588 / 5.584 / 5.589 s |
| `celar` 2016 | 300 | 3,075 | 685,521 → 580,205 | 0.218 / 0.216 / 0.216 s | 0.178 / 0.176 / 0.177 s | 0.215 / 0.215 / 0.213 s |

The same nodes, 19% and 15% fewer propagator calls, and 20% and 18% faster. The
switch build without the claim is within 1.5% of the unmodified one, which is
the null control.

**What these benchmarks exercise**, from local counters to the 200th solution
of 2013: rules 2 and 5 dominate (2.08 million upper and 2.14 million lower
bounds on `v2`, over 6.8 million calls); rule 8 fires 43,925 times, rule 9
7,383 times, plus 7,600 on the constant arm at the root; rules 3 and 4 16 times
each, all at the root. **Rules 6 and 7, the image direction, never fire**, and
neither does rule 1, since every `v2` is declared non-negative. So a
per-inference cost quoted from `celar` is a cost of bounds and preimage
removals.

### Proof performance

**`celar` 2013 to its 20th solution** (163 nodes; the 20 objectives are the same
in every row):

| | solve | proof | VeriPB |
|---|---|---|---|
| `AssertionLevel::Off` | 0.511 s | 318,150 lines, 35 MB | 28.7 s, `VERIFIED BOUNDS` |
| `Off`, the 16 constants replaced by one-value variables | 0.385 s | 221,752 lines, 26 MB | 16.4 s, `VERIFIED BOUNDS` |
| `AssertionLevel::Inferences` | 0.300 s | 33,322 lines, 11 MB | 0.35 s, `UNDER ASSERTIONS` |

Checking the justified proof takes 82 times as long as the asserted one. **The
constant path is 30% of its lines and 43% of its checking time**, as the second
row shows: the same search, with rule 8's range form in place of rule 9's
per-value one.

**Assertions at `Inferences`**, 32,935 in all: `abs` 16,675 (51%),
`linear_equality` 10,025, `comparison` 3,275, `equals` 2,727, `or` 99, and the
solver's own `backtrack` 114 and `soli_improve` 20. Of the `abs` ones, 7,600
are rule 9's unit removals at the root: 16 constraints times 475 values.

**Own against shared**, by the number of runs removed at the root: a probe with
`v1 ∈ {0, w, 2w, …, kw}` and `v2 ∈ [0, kw]` (image direction: `k` runs, `k + 1`
solutions), or `v1 ∈ [−kw, kw]` and `v2 ∈ {0, w, …, kw}` (preimage direction:
`2k` runs, `2k + 1` solutions), enumerating every solution with proofs, all
verified.

| k | image: proof lines | image: `pol` / `rup` / `red` | preimage: proof lines | preimage: `pol` / `rup` / `red` |
|---|---|---|---|---|
| 1 | 111 | 14 / 19 / 20 | 158 | 21 / 26 / 26 |
| 2 | 210 | 29 / 35 / 40 | 300 | 41 / 51 / 52 |
| 4 | 408 | 59 / 67 / 80 | 590 | 81 / 107 / 104 |
| 8 | 804 | 119 / 131 / 160 | 1,194 | 161 / 243 / 208 |

Identical at `w = 10`, `10³` and `10⁶`, which is the width independence.
The growth in `k` mixes this family's lines with the enumeration of the extra
solutions, so it is an upper bound on the per-run cost: about 99 lines per image
run, and 148 per step of `k` in the preimage direction, which is two runs. The
`red` lines, the literal definitions, are 20 and 26 of those.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified, and nothing is asserted at
`AssertionLevel::Off`. The propagator is the same with proofs on and off.

### Known limitations

- **A constant `v2` is slow and proof-heavy in proportion to its value**
  (#1058). Posting it as a one-value variable is the workaround, and front
  ends do not do it.
- **Slower than Gecode** by about five times where `Abs` dominates, at node
  counts within 4% either way.
- **No reified form.**

### Next steps

Ranked by what they buy for what they cost.

1. **#1057** — return `EnableButIdempotent`. One line, 18–20% on `celar`,
   at the same node counts (only nodes and propagation counts were compared).
   #1056 first is better, so that the bare lane checks the claim as well as
   the view lane.
2. **#1058** — give the range rules a form for a constant `v2`: the row with
   the constant folded in needs no atom of `v2`, so the preimage derivation
   should survive with that resolution dropped. Then add a constant-operand row
   to the audit lane, and a wide constant to `abs_test`. Small; 30% of `celar`'s
   proof.
3. **#1056** — set `GCS_CHECK_IDEMPOTENT_CLAIMS` where every data-driven test
   starts, for example in `establish_and_announce_seed`, not in the first
   harness solve. Not this family's, but found here.
4. **Rule 7's second lemma**, which its own reason implies: drop it, or write
   it as its comment says. Either verifies; the comment and the code should at
   least agree. In #1057's issue, as a while-there item.
5. **Per-call allocation.** Two domain copies, two piece vectors and two
   `IntervalSet`s per call. Worth measuring after #1057, which removes 44% of
   `Abs`'s calls on `celar` anyway. Unfiled.
6. **Tests.** The aliased-view differential as a lane; a chain case with a
   hole. Unfiled.

## Prior art

The encoding is Encoding Procedure 3.3 of McIlree's thesis, and `cake_pb_cp`'s.
The thesis gives no justification procedure for `Abs`; the ones here are ours:
one `pol` shape over the two half-reified rows for the bounds and ranges, and
plain RUP for single values. Why the obvious alternative,
Theorem 2.9's two-lemma RUP, does not work on the negative branch is in
`large-domains.md`. Gecode has bounds and domain consistent `abs`
propagators (`AbsBnd`, `AbsDom`) and picks by the propagation level, bounds by
default. Whether any other certifying solver covers `abs` was not surveyed.

## Further reading

- [`large-domains.md`](../large-domains.md): the Theorem 2.9 section, which uses
  `Abs` as the example of where the two-lemma shape stops holding, and the
  #875 section on sabotaging proof lines one at a time.
- [`view-proof-logging.md`](../view-proof-logging.md): the representation
  invariants that `justify_abs_v2_le_big_m` was the historical counterexample
  to, and why its operand bounds are emitted in view form.
- [`arithmetic-proofs.md`](../arithmetic-proofs.md): the product family's
  justification layer, which follows `abs/justify.cc`'s style.

## Developer commentary

**A constant is a kind of variable that the width policy did not reach.**
#931 removed every "is this a view?" test from the choice between a range and a
value proof, and left the constant, correctly, because a constant has no order
atom to resolve against. But the per-value arm it left is proportional to the
constant, not to anything the policy measures, and no audit-lane row posts a
constant operand. A real model found it: `celar` pays 30% of its proof for 16
constraints of the form `|a − b| = 238`.

**A lane can run with a checker that was never switched on.** The harness turns
the idempotence checker on in the solve helper, and the engine reads the switch
once. So a test that propagates before its first solve helper runs without the
checker, and says nothing. The way to find this was to make a false claim on
purpose and see what caught it: the per-node consistency check did, and the
claim checker did not.
