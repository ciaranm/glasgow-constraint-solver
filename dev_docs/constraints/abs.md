# Abs: one variable is the absolute value of another

> **Maturity** production ·
> **Audited** 2026-09-23 at `f28fdef8`; re-audited 2026-09-25 at `61112ed0` ·
> **Open issues** filed by this audit: none left open. #1057, #1058 and #1056
> are fixed; see [Re-audit, 2026-09-25](#re-audit-2026-09-25). Already open and
> touching this family: #868 (cross-solver). One finding is unfiled: with a
> constant operand, either one, our four rows are not `cake_pb_cp`'s, so the
> strict `opbdiff` oracle fails although cake verifies the proof ([Cake
> conformity](#cake-conformity)). Tracked under #871.

## Re-audit, 2026-09-25

All three issues the first pass filed were fixed and merged on 2026-09-24.

| issue | PR | what it changed here |
|---|---|---|
| #1057 | #1076 | The propagator returns `EnableButIdempotent`, with the argument in a comment at the `return`. `justify_abs_hole` (rule 7) lost its second lemma, which its own reason implied. Changes the inventory, the idempotence text, rule 7, and the CPU figures. |
| #1058 | #1080 | With a constant `v2`, the preimage loop removes each run of `v1` at once, by plain RUP, rather than a value at a time. The loop's range arm is now gated on `v1` alone being a variable. New `abs_test` rows (one hole row, four wide-constant rows), and an `Abs/constant` audit-lane row. Changes rules 8 and 9, interval efficiency, the proof figures, and the limitations. |
| #1056 | #1086 | Not this family's code. The test harness now switches the idempotence-claim checker on before anything propagates, and throws if it is off. So both `abs_constraint` lanes now check the claim that #1076 makes. Changes Tests. |

**Re-measured at `61112ed0`**, on the same machine and pinned the same way
(on core 20, where the first pass used core 8), alongside a re-run of the
`f28fdef8` build in the same sitting:

- the `celar` CPU runs;
- the Gecode baseline;
- the `celar` proof runs at both assertion levels, with VeriPB;
- the constant-`v2` probe;
- the hole-run probe;
- the `celar` propagation share;
- the nine lanes.

**Not re-measured**, and still `f28fdef8`'s: the `perf` profile, the per-rule
firing counters, the runtime-cap check, and the aliased-view differential. The
counters came from local instrumentation that is not in any build now.
Everything below that is not marked otherwise was re-checked against the code
at `61112ed0`. A figure from the first pass is labelled with its commit.

`Abs(v1, v2)` says `v2 = |v1|`. It is one class, with one initialiser and one
propagator, and the propagator is generalised arc consistent: bounds both ways,
then the values of `v2` with no preimage and the values of `v1` whose absolute
value `v2` has lost. Its bound and range proofs resolve the model's two
half-reified rows by `pol`, because unit propagation can neither split on
`v1`'s sign nor cross the negative branch's row, which is a sum rather than a
difference. Its single-value removals are RUP: plain for `v1`'s, and after one
lemma for `v2`'s. Its range removals against a constant `v2` are plain RUP.

Three things to know before touching it.

- **It is generalised arc consistent in a single call, and says so.** Removing
  a value from one side never removes a support on the other, so one call
  reaches the fixpoint, and since #1076 the propagator returns
  `EnableButIdempotent`. On `celar` that is 19% and 15% fewer propagator calls
  at the same node counts, and 21% and 18% less time. Re-measured at
  `61112ed0`: 5.61–5.66 s → 4.43–4.46 s on 2013, and 0.215 → 0.177 s on 2016.
- **A constant `v2` is the one operand the range proofs cannot name, and it
  needs none.** A constant has no order atom, so rule 8's `pol` derivation does
  not apply. But with the constant folded into the model's rows, each half is
  a bound on `v1` alone, and a run on one side of zero is plain RUP (#1080).
  Before that, `v1`'s interior `[−c + 1, c − 1]` went a value at a time, at
  about 13 lines each. That took 3.1 s at `c = 10⁷`, and 260,030 lines at
  `c = 10⁴` (`f28fdef8`). Now it is 86 lines and under 0.2 ms at every `c` up
  to `10⁹`. On `celar` it had been 30% of the proof's lines.
- **It is the largest share of the propagation on `celar`, where we are about
  four times slower than Gecode.** `Abs` is 51% and 45% of propagation time on the two
  `celar` instances over 10 s. The whole solver takes 3.8 and 4.6 times as long
  as Gecode to the same solution, at node counts within 4% either way. Before
  #1076 those figures were 63% and 55%, and 4.8 and 5.6 times. How much of the
  gap is `Abs`'s was not isolated.

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
and a constant has none. What happens instead depends on which operand it is:

- **A constant `v1`** is one value. The bounds rules fix `v2` first, so each
  interior loop has at most that one value to consider.
- **A constant `v2`**, in the image loop, is also one value.
- **A constant `v2`**, in the preimage loop, takes rule 8's second form. With
  the constant folded into the model's rows, a run of `v1` on one side of zero
  is removed by plain RUP (#1080). Before #1080 it took the per-value arm, which
  was the hazard the first pass reported in [Interval
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

Both report `OK: full workflow-2 chain passed` at `f28fdef8`, and again at
`61112ed0`, with `cake_pb_cp` and `opbdiff` on the path. So the OPB matches
cake's label for label. Neither case starts with a hole, a view or a constant.
Search makes holes, so the chain does see the preimage rules: `abs_sat`'s proof
has rule 9's single-value RUPs and a rule 8 `pol` triple. The image rules (6
and 7) were not looked for in it.

**A constant operand is not label-for-label cake's, in two different ways.**
The re-audit checked two uncommitted cases with `run_scp_chain.bash` in
`strict` mode. Each one verifies through cake and then fails the `opbdiff`
oracle, so the script exits 1.

- **A constant `v2`**: `(X −50 50) (Y −3 3)`, `abs X 45`, `abs Y 2`,
  enumerated. `s VERIFIED COMPLETE ENUMERATION OF 4 SOLUTIONS`. The oracle
  differs on all four `posle`/`negle` rows, in the big-M coefficient on the
  sign atom's literal: for `X`'s `posle`, ours is 63 and cake's 18. Why the two
  differ was not traced. Posting the constant as a one-value variable makes
  that constraint's rows match.
- **A constant `v1`**: `(Y 0 50)`, `abs −45 Y`, enumerated. `s VERIFIED
  COMPLETE ENUMERATION OF 1 SOLUTIONS`. The oracle differs on **all four**
  rows, `posge` and `negge` too. We write each half folded and unreified, with
  no guard literal: our `negle` is `… >= 45`. Cake keeps a guard,
  `… 45 n[-45][ge0] >= 45`, and adds two rows of its own that define that
  fixed atom.

Cake accepts our proof against its own rows in both cases. The `f28fdef8`
build gives the same differences in both, so neither is new; #1080's
description first noted the constant-`v2` one. Both are unfiled, and no
`scp_cases` case posts a constant. See [Next steps](#next-steps).

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
- **Constant `v2`**: the preimage range removal (rule 8's second form) calls no
  helper and is a plain RUP. Its reason is a range literal on the constant,
  which is true by construction, so the logged line is an unconditional unit:
  `a 1 ~i[v1][in-4_-1] >= 1::abs:…` at `AssertionLevel::Inferences`, for
  `v1 ∈ [−10, 10]`, `v2 = 5`.
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
| the `Abs` propagator | `on_change`: `v1`, `v2` | derived: both, truthfully | 2–9 | always | **yes, claimed** (`EnableButIdempotent`, #1076) | never |

**Idempotence.** One call reaches the propagator's fixpoint when `v1` and `v2`
are different variables. A value of `v2` is supported by `±w` in `v1`, and a
value of `v1` by `|u|` in `v2`. A value removed from either side has no support
on the other, so it never was a support, and removing it cannot remove support
from anything left. The bound rules remove only values outside the image or
preimage. So a second call infers nothing. Since #1076 the propagator returns
`EnableButIdempotent`, and the argument is a comment at the `return`. At
`f28fdef8` it returned `Enable`.

The first pass checked the claim by making it, behind a local switch, and
forcing the checker on. That was 212 runs with no failure:

- 25 seeds bare and 25 mixed-view;
- all 18 view wraps at every position choice (both, `v1` only, `v2` only),
  over three seeds.

Then #1076 repeated that with the claim committed, over 221 runs, and #1080 did
so over 471 after its own change. A control confirms the checker would catch a
false claim: a variant that skips the interior loops on a call where a bound
rule fired, while claiming idempotence, is rejected with "claimed
idempotence, but re-running it did more". The engine ignores a claim when
positions alias (`positions_alias`), so `Abs(x, x)` and the aliased views stay
requeued. Since #1086 both `abs_constraint` lanes run with the checker on, so
the ordinary suite checks the claim too. The measured effect is under [CPU
performance](#cpu-performance).

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

**What maintaining it would buy.** On `celar` 2013 at `f28fdef8`, the
propagator's own code was 12.5% of the profile. The interval generators,
`pieces_to_set` and `copy_of_values` were at least another 15.1%, most of it
presumably `Abs`'s, though the generators are shared and callers were not
separated. Allocation, shared with everything else, was another 10%. So no
saving is claimed. The cheaper win was not recomputing at all, and it has been
taken. The first pass's counters estimated that #1057's claim would remove
about 3.0 million of `Abs`'s 6.8 million calls on `celar` 2013, 44%. With #1076
merged, the whole run's propagator calls fall by exactly 3,003,161, from
15,759,399 to 12,756,238. The profile was not re-taken at `61112ed0`.

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
  wrote proofs with identical line counts at `w = 10`, `10³` and `10⁶`, and
  again at `61112ed0`; the bytes grow with the numbers' digits. At `f28fdef8`,
  a constant `v2` was the exception. Since #1080 it is not; see [Interval
  efficiency](#interval-efficiency).
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

`Fine at any width` since #1080, on all four questions. At `f28fdef8` a constant
`v2` was the exception, on propagation and proofs both.

1. **Propagation.** `State`'s per-value iterators are used nowhere. The bounds
   are `O(1)`. The image and preimage are built from `each_interval`, and the
   removals found by `each_interval_minus`, so the work is in intervals. Two
   hand-written per-value loops remain, one per direction, each counted by a
   `LargeDomainIterationCounter`. Each now only ever walks **one value**:
   - a removal of width 1;
   - in the image loop, a run in a constant `v2`, which is one value; under a
     constant `v1` the bound rules have already fixed `v2`, and the clip to its
     new bounds leaves nothing;
   - in the preimage loop, a constant `v1`'s one value.

   A constant `v2`'s preimage runs go by rule 8's plain-RUP form, one inference
   per run. Re-measured at `61112ed0` with the first pass's probe (`v1 ∈ [−c,
   c]`, `v2 = c` a constant): 0.06–0.14 ms at every `c` from `10²` to `10⁹`. At
   `f28fdef8` the same probe walked `2c − 1` values: 0.033 s at `c = 10⁵`, 0.33 s
   at `10⁶`, 3.1 s at `10⁷` (#1058).
2. **Reasons.** One or two literals per inference, each a range or a bound:
   `{v1 ∉ [lo, hi], v1 ∉ [−hi, −lo]}` for an image removal, and for a preimage
   one `{v2 ∉ [lo, hi]}` when the piece is non-negative, `{v2 ∉ [−hi, −lo]}` when
   it is negative. Built unconditionally, but constant-sized, so an
   unguarded build costs nothing that matters.
3. **Proofs.** Per run, not per value, and the form is chosen by width: a run of
   two or more values takes a range rule, a single value a value rule. The
   **kind** of an operand still matters in two places, and neither makes a
   proof per value. In the preimage loop, two variables take rule 8's `pol`
   derivation, and a constant `v2` takes its plain RUP form, because the `pol`
   names an order atom of `v2` and a constant has none. The image loop keeps
   its range rule for two variables, and a constant operand sends it to the
   value rule. That is at most one value there: a constant `v2` is one value,
   and under a constant `v1` the bound rules have already fixed `v2`. At `f28fdef8` a constant operand took the value
   rule for every value, the shape #924 fixed in `Element` and #931 fixed for
   views here: 13 lines per removed value, so 260,030 lines at `c = 10⁴`,
   against 137 for a one-value variable. Re-measured at `61112ed0` on the same
   probe, the constant gives **86 lines at every `c`**, all verified with
   `--force-checked-deletion`. The one-value variable still gives 137, so the
   constant is now the cheaper spelling.
4. **The audit lane.** Six rows, all `Clean`:
   - `Abs`: two wide variables, which reach neither interior loop;
   - `Abs/hole` and `Abs/hole-preimage`: one per loop;
   - `Abs/view-hole` and `Abs/view-hole-preimage`: the same with one operand
     wrapped, which tripped before #931;
   - `Abs/constant` (#1080): `v1 ∈ [−10⁹, 10⁹]`, `v2 = 10⁹` a constant.

   #1080 reports that `Abs/constant` trips with the old gate put back, so it
   discriminates. That was not re-run here, since this build has the guard off.
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
1–6, and rule 8 over two variables, share one shape. It is a `pol` that adds a
model row to the defining items of the order atoms whose arithmetic it uses,
and saturates. The operands' bit sums cancel, and what is left is a clause over
order atoms, conditioned on `v1`'s sign; then the conclusion is RUP. Rules 7
and 9 are RUP, rule 7 after one lemma, because a single value pins every bit.
So is rule 8 against a constant `v2`, whose rows are then bounds on `v1` alone
(Theorem 2.7 via Lemma 3.2). Two reasons keep the others off RUP. For the bound
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
- **Proof technique** — `RUP sequence`, ours: one lemma under the reason,
  `v1 < 0 ∨ v1 = w ∨ v2 ≠ w`, then RUP. From `v2 = w` the lemma and the
  reason's `v1 ≠ w` give `v1 < 0`, which activates the negative row, and that
  pins `v1` to `−w` against the reason's `v1 ≠ −w`. A single value pins every
  bit of `v2`, and through the active row every bit of `v1`, so RUP works here
  where a range needs rule 6's `pol`s. **At `f28fdef8` there was a second
  lemma**, `v1 ≥ 0 ∨ v1 ≠ −w ∨ v2 ≠ w`, which the reason implied, and whose
  comment described a different line. The first pass showed it droppable at ten
  seeds of ten, and #1076 dropped it.
- **Reason** — `{v1 ≠ w, v1 ≠ −w}`.
- **Assertion** — `v2 ≠ w ∨ ¬reason`.
- **Hint** — `hints::Abs`.
- **Offline reconstructibility** — `offline`: the lemma and the conclusion are
  each a RUP, whichever rows they go through.
- **Proof size** — two lines, the lemma and the conclusion; three at
  `f28fdef8`.
- **Gaps** — `None.`
- **Tightness** — shown by hand, not by a lane. Without the remaining lemma,
  VeriPB rejects the proof at nine of seeds 1–10. That was measured at
  `f28fdef8` with both lemmas dropped, and by #1076 with its one lemma dropped;
  it was not re-run here.

### Rule: preimage-range

(Rule 8.)

- **Infers** — `v1 ∉ [lo, hi]`, for a run of `v1` on one side of zero, of two
  or more values, whose absolute values are not in `v2`.
- **Fires when** — the propagator's preimage loop, when `v1` is not a constant:
  `each_interval_minus` of `v1` against `v2`'s preimage, clipped to `v1`'s new
  bounds, and split at zero. **Two forms**, picked by whether `v2` is a
  constant. The gate was "neither is a constant" at `f28fdef8`, which sent a
  constant `v2` to rule 9 (#1058, fixed by #1080). A constant `v1` is one value
  and never forms a run.
- **Strength** — `partial`; with rule 9, `GAC` on `v1`.
- **Algorithm** — the preimage of each interval of `v2` is its mirror and
  itself, merged. In **intervals**.
- **Why it is true** — `v1 = u` needs `|u|` in `v2`.
- **Proof technique** — two forms.
  - **Variable `v2`**: `pol`, then `RUP`, ours. The run lies on one side of
    zero, so the conclusion's own negation decides `v1`'s sign, and only the
    active row is needed. Three `pol`s: the sign (`v1 ≥ lo` against `v1 < 0`,
    or the mirror), and the two bounds the row licenses on `v2`. None is stated
    under the reason: all three are consequences of the model alone. Then RUP.
  - **Constant `v2 = c`**: `RUP`, ours, licensed by **Theorem 2.7 via Lemma
    3.2** (#1080). With `c` folded in, each half is a bound on `v1` alone:
    `v1 ≥ c` under `v1 ≥ 0`, and `v1 ≤ −c` under `v1 < 0`. The negated
    conclusion gives `v1 ≥ lo` and `v1 < hi + 1`. The run is on one side of
    zero, so one of those atoms' definitions fixes `v1`'s sign bit by unit
    propagation. The halves are guarded on the atom `v1 ≥ 0`, not on the bit,
    so it takes one more step: the order chain, or that atom's own definition,
    then sets `v1 ≥ 0` one way or the other. That enables one half. The half is a bound on `v1`'s own bits that contradicts
    the run's, and contradictory bounds on one binary sum unit propagate.
    **The split at zero is load-bearing.** #1080's mutation, which removes a
    run straddling zero in one go, is rejected by VeriPB.
- **Reason** — `{v2 ∉ [lo, hi]}` for a non-negative piece, `{v2 ∉ [−hi, −lo]}`
  for a negative one: one range literal. Minimal. With `v2` a constant, it is
  true by construction.
- **Assertion** — `v1 ∉ [lo, hi] ∨ ¬reason`. With `v2` a constant, the
  reason's literal is true and drops out, so the assertion is the unit
  `v1 ∉ [lo, hi]`. Checked on an `a` line at `AssertionLevel::Inferences`.
- **Hint** — `hints::Abs`.
- **Offline reconstructibility** — `hinted` for the `pol` form: the hint's
  constraint id finds the rows. `offline` for the constant form: it is one RUP
  against the database, so there is nothing to choose, as for rule 9.
- **Proof size** — independent of width in both forms. The `pol` form is three
  `pol`s and a RUP per piece, cheaper than rule 6 because there is no sign case
  to close. The constant form is one RUP per piece, plus the atom definitions it
  needs.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` by a lane; see the catalogue preamble.

### Rule: preimage-value

(Rule 9.)

- **Infers** — `v1 ≠ u`.
- **Fires when** — the preimage loop, for a piece of one value, including
  under a constant `v2`, and for a constant `v1`'s one value. At `f28fdef8` it
  also took **every value of every run when either operand was a constant**.
  With `v2` a constant `c` that was every value of `[−c + 1, c − 1]`, once, at
  the root (#1058). Since #1080 those runs go to rule 8.
- **Strength** — `partial`; see rule 8.
- **Algorithm** — one `in_domain`, counted by the large-domain guard.
- **Why it is true** — as rule 8.
- **Proof technique** — `RUP`: `v1 = u` pins `v1`'s bits, and the active row
  pins `v2`'s to `|u|`, which the reason excludes.
- **Reason** — `{v2 ≠ |u|}`. With `v2` a constant, true by construction, so
  the assertion is a unit.
- **Assertion** — `v1 ≠ u ∨ ¬reason`.
- **Hint** — `hints::Abs`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line, plus the literal definitions it needs: about 13
  lines per value in total, measured over the constant case at `f28fdef8`,
  when that case still came here.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

| Lane | What it checks |
|---|---|
| `abs_constraint` | `abs_test`: 30 fixed rows (ranges, #446's tight domains, #254's constants, one-value variables, and since #1080 four with a wide constant `v2 = 45`) and 30 random ones (both operands ranges, `v1` constant, `v2` constant), each with and without proofs, under `solve_for_tests_checking_gac`, so `GAC` at every node; five hole rows, three for the image loop and two for the preimage loop (`preimage_far_constant`, from #1080, has a constant `v2` and runs away from zero); five `Abs(x, x)` rows under plain enumeration; nine initialiser-only proof checks: four (`bound1` to `bound4`, which are rules 1, 3, 4 and 2 here) and five over wider domains, nine in all |
| `abs_constraint_view_mixed` | the same with positions wrapped in views, minus the initialiser and dup rows |
| `scp_chain_abs_sat`, `scp_chain_abs_unsat` | see [Cake conformity](#cake-conformity) |
| `xcsp_intension_arithmetic`, `xcsp_intension_basic` | `eq(abs(x), y)` and `eq(dist(x, y), 1)` |
| `minizinc-abs` | `int_abs` against MiniZinc's default solver |
| `crystal_maze-abs`, `crystal_maze-abs-gac` | the example with `--abs`, proof verified |
| `large_domain_audit_test` | six `Clean` rows, `Abs/constant` among them; registered only in a build with `GCS_LARGE_DOMAIN_GUARD=ON` |

The nine lanes above that post `Abs` pass at `f28fdef8`, caps off, and again
at `61112ed0` with the default caps, with MiniZinc 2.9.7, `cake_pb_cp` and
`opbdiff` on the path. `large_domain_audit_test` was not re-run: neither
audit's build has the guard on, and its rows' outcomes are the ones pinned in
the source. At `--seed=1`, `abs_test` verifies 74 proofs at `f28fdef8` and 79
at `61112ed0`, where the new rows account for the difference. The data-driven
lanes are seeded, and reproduce with `--seed=N`.

**Runtime caps.** No lane sets or clears one, and at `f28fdef8` **the
defaults never fired here**. Three unseeded runs of each data-driven lane, with
the 300-solution and 1,500-node caps passed in the environment, printed no
truncation from a local-only print, and a two-solution control fired 44 times.
The largest domain in the random rows is 16 values, so the capped run checks
completeness too. Not re-measured at `61112ed0`. #1080's new rows have at most
121 values in `v1` and a constant `v2`, so a handful of solutions each.

**The idempotence-claim checker is on in both lanes, since #1086.** It checks
the claim #1076 makes. `establish_and_announce_seed`, which every test main
calls first, switches the checker on and reads it back, and it throws if an
earlier propagation had already fixed it off.
`solve_for_tests_with_callbacks` throws if it is off. So a passing lane is one
that ran with it on.

At `f28fdef8` it was **off** in the bare `abs_constraint` lane (#1056). The
engine reads `GCS_CHECK_IDEMPOTENT_CLAIMS` once, at the first propagation in the
process, and the harness set it in `solve_for_tests_with_callbacks`. `abs_test`
runs its initialiser checks first, through
`check_initialisation_only_for_tests`, which propagated before that. Across
the suite the checker was off in 100 of the 317 lanes whose binary uses the
harness, over 17 binaries. #1086's sweeps, with the checker forced on
everywhere, found no false claim.

**Rules the tests reach**, from local counters at `--seed=1` at `f28fdef8`:
all nine, both branches of rule 5, and the constant arm of rule 7. At the time
**the constant arm of rule 9 was not reached at seed 1**, where all ten
constant-`v2` rows are unsatisfiable: nine fail on the bounds, and one in rule
7's constant arm. Over seeds 1 to 20 it was reached at 18, 8 to 50 times each,
and not at seeds 1 and 19. The counters were not re-run at `61112ed0`.

Rule 8's constant form is reached by construction, at every seed, by #1080's
fixed rows. On `{−60..60}` with `v2 = 45`, for example, the bound rules leave
`[−45, 45]`, and then `[−44, −1]` and `[0, 44]` go as one run each. The
`preimage_far_constant` row is there so that both its runs, `[30, 44]` and
`[−44, −30]`, lie away from zero.

**What the tests do not cover:**

- **Aliased views.** Only `Abs(x, x)`, whose consistency is not checked. This
  audit's 144-case differential is not in the tree.
- **A chain case that starts with a hole, a view or a constant**, as [Cake
  conformity](#cake-conformity) says. A constant would currently fail the
  strict oracle.
- **The cost of a constant `v2`** is pinned only by the guarded
  `Abs/constant` row, which no default build registers. The first pass's gap
  here, that no row had a constant wider than 10, is closed by #1080's rows.

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
  `GCS_PROPAGATOR_STATS=time`, at `00797a97`, from `linear.md`'s survey). That
  was before #1076, #1080 and `87c88f2e` changed `abs/`, and only `celar` has
  been re-run since: `celar` 2013 63.8%, 2016 55.0%; `roster-sickness` 14.3%;
  `on-call-rostering` 2013 9.3%, `city-position` 8.7%, `fast-food` 8.1% and
  6.4%, `on-call-rostering` 2018 5.8%, `cable_tree_wiring` 5.1%, and under 3% in
  the other five. 0.5–0.9 µs per call, and 2.1 µs on `roster-sickness`.
  **Re-measured for `celar` only**, the same way (10 s, all solutions, pinned),
  in one sitting. The `f28fdef8` build gives 63.0% and 54.6% of propagation
  time, and 42.2% and 28.6% of calls. The `61112ed0` build gives **50.9% and
  45.1%** of time, and 27.5% and 19.3% of calls, at 0.51–0.52 µs per call. The
  other models were not re-run.
- **For CPU**: `celar` 2013 (`CELAR6-SUB2`) to its 200th solution, 5.6 s at
  `f28fdef8`, 4.4 s at `61112ed0`; `celar` 2016 (`CELAR6-SUB0`) to its 300th,
  0.2 s.
- **For proofs**: `celar` 2013 to its 20th solution, 163 nodes. At `f28fdef8`
  the proof is 318,150 lines and checks in 29 s; at `61112ed0` it is 216,100
  lines and checks in 19 s.

### CPU performance

**Re-measured at `61112ed0`**, 2026-09-25, on the same machine and FlatZinc
files, pinned the same way, on core 20 where the first pass used core 8. The
`f28fdef8` build was re-run in
the same sitting. There were four runs per build, interleaved, and the first is
dropped as warm-up. Gecode is the same binary and files, re-run alongside.

| instance | N | nodes | propagations | `f28fdef8` s | `61112ed0` s | Gecode s | ratio to Gecode |
|---|---|---|---|---|---|---|---|
| `celar` 2013 | 200 | 68,754 both | 15,759,399 → 12,756,238 | 5.655 / 5.639 / 5.609 | 4.462 / 4.425 / 4.452 | 1.169 / 1.179 / 1.180 | 4.8× → **3.8×** |
| `celar` 2016 | 300 | 3,075 both | 685,521 → 580,205 | 0.215 / 0.215 / 0.216 | 0.177 / 0.176 / 0.177 | 0.0387 / 0.0383 / 0.0382 | 5.6× → **4.6×** |

Same last objectives as before (15,071 and 21,036). The two builds differ by
every commit on `main` in between, not only #1076 and #1080. But the change in
propagator calls is exactly the one the first pass measured for #1057's claim
behind a switch, at the same node counts. That is the evidence that the saving
is the claim's. #1080's change runs only at the root on these instances, where
the constants' interior is removed once.

The rest of this section is the first pass's. All of it is at `f28fdef8`,
Release, GCC 15.2.0, fataepyc-09 (EPYC 7643, boost off), pinned with
`numactl --cpunodebind=0 --membind=0 taskset -c 8 setarch -R`, 2026-09-23, on
an unmodified build except where a switch is named.

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
unmodified build, with the counters compiled out. This is what #1076 then
merged, and the re-measurement above reproduces its counts exactly:

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
removals. Since #1080 the 7,600 root removals are 32 of rule 8's constant form,
two per constraint. That count is from the `61112ed0` proof's `a` lines, at
`AssertionLevel::Inferences`: 7,600 unit value removals before, and 32 unit
range removals and no value removals after. The counters were not re-run.

### Proof performance

**Re-measured at `61112ed0`.** `celar` 2013 to its 20th solution, both builds
in one sitting, pinned. MB here is 10⁶ bytes. The four VeriPB 3.0.2 runs were concurrent, on separate
cores, with `--force-checked-deletion`. Same 163 nodes and last objective 33,692
throughout.

| | `f28fdef8` | `61112ed0` |
|---|---|---|
| `Off`: solve | 0.459 s | 0.348 s |
| `Off`: proof | 318,150 lines, 36.6 MB | **216,100 lines, 26.6 MB** (−32%) |
| `Off`: VeriPB | 30.4 s, `VERIFIED BOUNDS` | **18.6 s**, `VERIFIED BOUNDS` (−39%) |
| `Inferences`: proof | 33,322 lines, 11.0 MB | 24,945 lines, 10.4 MB |
| `Inferences`: VeriPB | 0.42 s, `UNDER ASSERTIONS` | 0.31 s, `UNDER ASSERTIONS` |

The line counts are exact and match the first pass, and #1080's own figure
(216,100). The checking time falls by about as much as the first pass's
one-value-variable workaround saved, and the constant's proof is now
**smaller** than that workaround's 221,752 lines. At `Inferences`, `abs`'s
assertions fall from 16,675 to 8,664. The difference is the 7,600 unit
removals becoming 32 range removals, plus 443 fewer elsewhere in `Abs`. Of all
24,558 assertions, 10,027 are `linear_equality`, 2,936 `comparison`, 2,698
`equals`, 114 `backtrack`, 99 `or` and 20 `soli_improve`. Where the other 443
went was not traced; the search is the same.

**The first pass's figures, at `f28fdef8`.** `celar` 2013 to its 20th solution
(163 nodes; the 20 objectives are the same in every row):

| | solve | proof | VeriPB |
|---|---|---|---|
| `AssertionLevel::Off` | 0.511 s | 318,150 lines, 35 MB | 28.7 s, `VERIFIED BOUNDS` |
| `Off`, the 16 constants replaced by one-value variables | 0.385 s | 221,752 lines, 26 MB | 16.4 s, `VERIFIED BOUNDS` |
| `AssertionLevel::Inferences` | 0.300 s | 33,322 lines, 11 MB | 0.35 s, `UNDER ASSERTIONS` |

The sizes in this table are rounded and do not share one unit. The `Off`
proof is 36,587,380 bytes, which is the "35 MB" above in MiB, and 36.6 MB in
the re-measured table. The `Inferences` proof is 10,956,305 bytes.

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
**Re-measured at `61112ed0`: every cell is unchanged**, and every proof
verifies. Rule 7's dropped lemma does not reach this probe, whose runs are all
at least nine values wide.
The growth in `k` mixes this family's lines with the enumeration of the extra
solutions, so it is an upper bound on the per-run cost: about 99 lines per image
run, and 148 per step of `k` in the preimage direction, which is two runs. The
`red` lines, the literal definitions, are 20 and 26 of those.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified, and nothing is asserted at
`AssertionLevel::Off`. The propagator is the same with proofs on and off.

### Known limitations

- **Slower than Gecode**, by 3.8 and 4.6 times on the two `celar` instances,
  where `Abs` is the largest share of propagation, at node counts within 4% either way. It was 4.8 and 5.6
  times before #1076.
- **A constant operand fails the strict `opbdiff` oracle**, although cake
  verifies the proof. For a constant `v2`, the `posle` and `negle` rows' big-M
  differs. For a constant `v1`, we write all four rows folded and unguarded,
  where cake keeps a guard on a fixed atom. Unfiled; see [Cake
  conformity](#cake-conformity).
- **No reified form.**

A constant `v2` was slow and proof-heavy in proportion to its value at
`f28fdef8` (#1058). It is no longer, since #1080.

### Next steps

Ranked by what they buy for what they cost.

**Done since the first pass**, all merged 2026-09-24:

- **#1057 → #1076.** Claim idempotence. Rule 7's second lemma was dropped as a
  while-there item.
- **#1058 → #1080.** A constant `v2`'s preimage runs, by plain RUP. It needed
  no lemma at all, where the issue expected a folded-row derivation.
- **#1056 → #1086.** The checker is on before anything propagates.

What is left:

1. **Constant operands against cake's encoding.** There are two shapes. For a
   constant `v2`, find out why our `posle`/`negle` big-M differs from cake's.
   For a constant `v1`, we fold and drop the guard, where cake keeps a guard
   and defines the fixed atom. Then either match cake, or document the
   differences and use a non-strict oracle mode. Then add a chain case for
   each. Unfiled. (#1080 recorded the constant-`v2` difference and left it.)
2. **Per-call allocation.** Two domain copies, two piece vectors and two
   `IntervalSet`s per call. `Abs` is still 51% and 45% of `celar`'s propagation
   time with the claim in place, at about 0.5 µs a call, so this is now the
   lever. Profile first; the `f28fdef8` profile predates the claim. Unfiled.
3. **Tests.** The aliased-view differential as a lane; a chain case with a
   hole. Unfiled.

## Prior art

The encoding is Encoding Procedure 3.3 of McIlree's thesis, and `cake_pb_cp`'s.
The thesis gives no justification procedure for `Abs`; the ones here are ours:
one `pol` shape over the two half-reified rows for the bounds and ranges, and
RUP for single values and for a constant `v2`'s ranges. Why the obvious alternative,
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
constant, not to anything the policy measures, and no audit-lane row posted a
constant operand. A real model found it: `celar` paid 30% of its proof for 16
constraints of the form `|a − b| = 238`.

**The fix needed less than the issue asked for.** #1058 proposed a range
derivation with the constant folded into the row. Building one, #1080 found
that no lemma at all was needed: with the constant folded in, each half is a
bound on `v1` alone, and plain RUP closes the run. It found this because
mutations dropping each line still verified. The same trap, a derivation that
verifies with parts missing, is what #875 recorded for rules 6 and 8. It is
worth expecting whenever a constant turns a two-variable row into a
one-variable one.

**A lane can run with a checker that was never switched on.** The harness turns
the idempotence checker on in the solve helper, and the engine reads the switch
once. So a test that propagates before its first solve helper runs without the
checker, and says nothing. The way to find this was to make a false claim on
purpose and see what caught it: the per-node consistency check did, and the
claim checker did not.
