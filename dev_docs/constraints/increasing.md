# `Increasing`: a sequence is monotone, strictly or not, up or down

> **Maturity** production ·
> **Audited** 2026-09-29 at `c9ceea25` ·
> **Open issues** none filed by this audit yet; see [Next steps](#next-steps)
> for what it would file. Already open and touching this family: #833 (the
> large-domain policy, which the impossible repeated pair below falls
> outside), #868 (cross-solver comparisons; this document gives one, by hand).
> Tracked under #871.

Four posted classes, `Increasing`, `StrictlyIncreasing`, `Decreasing` and
`StrictlyDecreasing`, over one class, `IncreasingChain`, and one propagator. A
descending chain is reversed at install, so everything below the constructor is
one ascending sweep. The encoding is the chain of `n − 1` comparisons, and the
propagator is a forward sweep of lower bounds and a backward sweep of upper
bounds.

Four things to know before touching it.

- **It is generalised arc consistent, and cheap, on distinct variables.** A
  chain of comparisons at its bounds fixpoint supports every value in every
  domain, holes or not, and the propagator reads nothing but bounds. So **holes
  affect nothing here**, the same answer [`comparison`](comparison.md) gives.
  GCS takes 2.5 to 2.7 times Gecode's time on an identical search tree, and
  one chain takes about 10% less time than the `n − 1` `LessThan`s it replaces.
- **A repeated variable weakens it, and an impossible repeated pair costs the
  width of its domain.** `StrictlyIncreasing{x, x}`, and equally the
  non-strict `Increasing{x + 1, x}`, are unsatisfiable, but the propagator never
  sees that. Each call pushes both of `x`'s bounds by one, and it fails after up
  to W/2 calls on a domain of width W: 50,001 propagations at W = 10⁵.
  `LessThan(x, x)` has contradicted at once since #1088; this family has no
  such check. A repeat with the same sign stays sound and `bounds(D)`; one
  through an opposite-sign view (`x` and `c − x`) is not even `bounds(Z)`.
- **MiniZinc's int `decreasing` never reaches it.** The standard library has no
  plain `var int` overload of `decreasing`, so an int array goes to the
  optional-variable overload and on to a pairwise decomposition; the solver's
  own `fzn_decreasing_int` is dead code. See [the frontend
  table](#concrete-constraints-and-frontend-coverage).
- **No front end can reach a reified form, and no presolver reads it.** The
  chain's rows are difference constraints, but the difference-logic presolver
  recognises only `Comparison` and two-term linear donors, so a model that
  posts `increasing` rather than pairwise `<=` hides its edges from it.

## What it is

### Semantics

`IncreasingChain(vars, strict, descending)` holds exactly when every adjacent
pair satisfies the comparison: `vars[i] ≤ vars[i + 1]` for `Increasing`, `<`
for `StrictlyIncreasing`, and `≥` and `>` for the two descending classes. The
four user-facing classes are thin constructors fixing the two flags.

- **Empty array, or one variable:** trivially true. `prepare()` returns false,
  so nothing is installed and no OPB row is written.
- **All constants:** a true/false check, handled by the ordinary propagator
  (#254 made sure it does not crash). `{1, 2, 3}` satisfies both ascending
  classes; `{2, 2, 3}` only the non-strict one.
- **A repeated variable** is accepted in every class. `Increasing{x, y, x}`
  forces `x = y`; `StrictlyIncreasing{x, x}` is unsatisfiable. See [Robustness
  and limits](#robustness-and-limits) for what that costs.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Increasing` | ✓ `fzn_increasing_int`, `fzn_increasing_bool` | ✓ `ordered` with `le` | ?[^gcspy] | ✓ `increasing` | |
| `StrictlyIncreasing` | ✓ `fzn_strictly_increasing_int` | ✓ `ordered` with `lt` | ?[^gcspy] | ✓ `strictly_increasing` | |
| `Decreasing` | int: `frontend gap`, pairwise `int_lin_le`[^mznrev]; bool: ✓ as `Increasing` over the reversed array | ✓ `ordered` with `ge` | ?[^gcspy] | ✓ `decreasing` | |
| `StrictlyDecreasing` | `frontend gap`, pairwise `int_lin_le`[^mznrev] | ✓ `ordered` with `gt` | ?[^gcspy] | ✓ `strictly_decreasing` | |
| any reified form | `decompose`: the stdlib's `fzn_*_reif` | n/a | — | — | no class exists |
| `ordered` with `lengths` | n/a | `decompose`: one two-term linear inequality per pair[^xlen] | — | — | not this family |

[^gcspy]: `gcspy` binds none of the four, so CPMpy can reach this family only
    through a decomposition of its own, if at all. Not checked.

[^mznrev]: `minizinc/mznlib/fzn_decreasing_int.mzn` is
    `glasgow_increasing_int(reverse(x))`, and likewise
    `fzn_decreasing_bool.mzn` and `fzn_strictly_decreasing_int.mzn`, **but for
    int arrays nothing selects them.** The standard library's `decreasing` has
    overloads for `var bool`, `var opt float`, `var opt $$E` and sets, and
    none for plain `var int`. So an int array takes the `var opt` overload,
    which calls `increasing(reverse(...))` typed as optional, which goes to the
    stdlib's `fzn_increasing_int_opt` decomposition and comes out as pairwise
    `int_lin_le`. Flattening `minizinc/tests/decreasing.mzn` and
    `strictlydecreasing.mzn` with `build/glasgow.msc` on 2.9.7 and 2.10.1 gives
    two `int_lin_le` each and no `glasgow_*` call (`tmp/fd-ordering/mzn/`).
    A bool `decreasing` does reach `glasgow_increasing_bool`, through the
    stdlib's own `reverse`, not through `fzn_decreasing_bool`. All three
    `fzn_*decreasing*` files are dead, for different reasons.
    `fzn_decreasing_int` is reachable only through the deprecated
    `decreasing_int.mzn`, which does not resolve through `globals.mzn`, and
    included by name fails to compile on either version (`Cannot open file
    'fzn_decreasing_int_reif.mzn'`). `fzn_decreasing_bool` is reachable only
    through `decreasing_bool.mzn`, which fails the same way
    (`fzn_decreasing_bool_reif.mzn`). `fzn_strictly_decreasing_int` is
    referenced nowhere in either standard library. So the `Decreasing` classes
    are reached only from XCSP3, the `.scp` reader and the C++ API. [Next
    steps](#next-steps) has a tested fix.

[^xlen]: `buildConstraintOrdered` with `lengths` posts
    `vars[i] + lengths[i] (op) vars[i + 1]` as a `WeightedSum` inequality per
    pair, which is XCSP3's semantics for the form.

Positions are all that matter here: no value is an index, so an array indexed
from something other than 1 cannot be mistranslated the way #987's were.

### Options

`None.` There is no consistency tag and no algorithm switch.

### Variable kinds and views

Plain variables, constants and views of either sign are all accepted, and the
propagator is the same for all of them: it reads `bounds()` and infers bounds.

**The proof handles views too.** A view is given its own bit-sum proof variable
with `viewle`/`viewge` channel rows (see
[`view-proof-logging.md`](../view-proof-logging.md)), and the chain row is
written over that variable. So the row's constant stays the chain's step, 0 or
1, whatever the view's offset or sign, and the argument in the [Inference
catalogue](#inference-catalogue) applies unchanged. Checked: `Increasing{x0,
x1 + 1, −x2 + 5, x3}` over `0..4` enumerates its 55 solutions with a verifying
proof (`tmp/fd-ordering/probes/fam.cc`, mode `inc_views`), and the test's
`view_mixed` lane runs every shape with views mixed in.

### Reification

`None.` MiniZinc's `increasing_int_reif` and its siblings reach the solver as
the standard library's decomposition into reified comparisons, before
flattening, so a flattened model cannot show whether one was written. There is
no case for a class of its own yet.

### Relation to other families

- **Decomposes into it:** nothing.
- **Child constraints:** none. The chain is its own rows and its own
  propagator.
- **Shares code:** none. `increasing.cc` includes no helper from another
  family.
- **Presolvers:** none reads it. The difference-logic presolver lifts
  `Comparison` and two-term `LinearInequality` donors, found by
  `dynamic_cast`, and needs a labelled row to cite. An `IncreasingChain` is
  `n − 1` difference edges with unlabelled rows, so it is invisible to it. See
  [Next steps](#next-steps).
- **The merge question with `comparison`:** separate. The encoding is the same
  row, and the proof argument is the same theorem, but the classes share no
  code, and the chain's sweep is the reason it exists. Posting the `n − 1`
  comparisons instead reaches the same fixpoint, a propagation at a time.

## The proof model

### OPB encoding

For the ordered array `v` (reversed first for a descending class), and
`step` = 1 for the strict classes and 0 otherwise:

```
for i in 0 .. n-2:    v[i] − v[i+1] ≤ −step
```

That is the whole encoding. **It is definitional**: the rows are the
constraint's meaning and nothing more. It is `n − 1` rows over bit sums, so it
is logarithmic in domain width.

### Labels

`None.` The rows are written unlabelled, and no rule cites a row: every
inference is a plain RUP, so unit propagation finds the row it needs.

### Cake conformity

`cake_pb_cp` encodes the family as the same chain of comparisons, labelled
`@c[id][i]`. The ascending chain cases (`increasing_sat`, `increasing_unsat`,
`strictly_increasing_sat`, `strictly_increasing_unsat`) and the two-variable
`decreasing_sat` are `strict`: `opbdiff` matches every row, by position,
because the solver's rows carry no label. `strictly_decreasing_unsat` is
`none`: the solver reverses a descending chain before writing it, so its rows
come out in the opposite order to cake's, which defeats the positional
fallback. It still chain-verifies, since the proof never cites a row.

The divergence is benign, but it is the solver's to fix: labelling the rows
`@c[id][i]` in the user's order would make all six cases `strict`.

### Proof-time state

Nothing is emitted at the root, and there is no proof-only auxiliary. The
family writes no scaffolding and deletes nothing itself; its inference lines
are written at the current search level, and the shared backtrack machinery
deletes them when search leaves that level. The `W = 200` root-unsatisfiable
proof of `StrictlyIncreasing{x, x}` ends with 200 `del` lines after its final
backtrack, 199 `del id` and one `del range -3 -1`, which between them delete
its 201 inference RUPs; the final `rup >= 1` is kept. Nothing a later step
needs is deleted. The only things the proof mentions besides the chain rows
are the variables' order literals, which the shared literal layer introduces
lazily the first time an inference names them.

## The implementation

### Initialisation and global data

`prepare()` moves the variables into `_ordered_vars`, reversing them for a
descending class, and declines to install anything for fewer than two. There is
no initialiser. Nothing is computed once but the order.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| the chain sweep | `on_bounds`, every variable | derived: **nothing** | 1, 2 | always, for two or more variables | never claims, and is not over holes | yes, once every adjacent pair is separated by the step |

**`on_bounds` is the whole trigger story, and it is exact.** The sweep reads
`state.bounds()` and nothing else, so no hole can change what it infers.
Nothing sets `Triggers::holes_affect_propagation`.

**Idempotence.** Not claimed, and a claim would be wrong over holes. The
forward sweep carries the bound it *asked for* to the next variable, not the one
the domain landed on: with `x0 ∈ 1..5`, `x1 ∈ {0, 3, 4, 5}` and `x2 ∈ 0..5`,
the first call pushes `x1 ≥ 1`, which lands on 3, and carries 1 on to `x2`. The
second call finishes the job. Measured: five propagations, three effectful, to
reach `x1 ≥ 3, x2 ≥ 3` at the root (`probes/incidem.cc`). Over interval domains
and distinct variables one call is a fixpoint. Carrying `state.lower_bound()`
after each push would make it one over holes too, still on distinct variables:
a repeated variable (`StrictlyIncreasing{x, x}`) takes W/2 calls whatever is
carried. An idempotence claim would nonetheless be safe, since the
propagator machinery ignores claims when positions alias (`propagators.cc`,
around lines 113–120 and 780). See [Next steps](#next-steps).

**Self-disabling.** The pass ends by checking every adjacent pair for
`ub(v[i]) + step ≤ lb(v[i+1])`, and disables until backtrack when all of them
hold.

### Mutable state and incrementality

`None.` Nothing persists between calls. Every call is two sweeps and an
entailment check, each `O(n)` bounds reads, and there is nothing to cache that
would cost less to keep valid.

### Interior values and optional pruning

**Offers.** `None.` Every rule moves a bound, and at its fixpoint the sweep is
already generalised arc consistent on distinct variables, so there is no
stronger interior pruning to make optional.

**Observes.** **Nothing, on any variable.** The family's whole vocabulary is
bounds, which is the case that makes the mechanism pay: an `Increasing` in a
model is never a reason for anybody else's interior pruning to stay on. The
same argument [`comparison.md`](comparison.md) makes for a single comparison
applies to a chain of them.

### Robustness and limits

**Unbounded domains.** Fine on distinct variables: every call is `O(n)` bounds
reads whatever the width. An impossible repeated pair, strict or not, is the
exception, below.

**Negative values and zero.** Tested: `increasing_test` runs `[−2, 1]`,
`[−1, 2]` and `[0, 3]`, and its random shapes reach from −3 to 7.

**Degenerate shapes.**

- *Empty, singleton, all constant:* covered by the test, per #254.
- *A repeated non-strict variable* is sound but not generalised arc consistent.
  `Increasing{x, y, x}` forces `x = y`, and the sweep brings their bounds
  together, but leaves a value of `x` whose partner is missing from `y`'s
  domain. The root probe below finds `bounds(D)` on every one of 3,000 random
  aliased instances, and GAC failing on 579 of them (seed 2; 596 at seed 1).
  That holds for plain repeats and same-sign views only.
- ***A repeat through an opposite-sign view*** is not even `bounds(Z)`, and an
  unsatisfiable one is not always failed at the root; it stays sound.
  `StrictlyIncreasing{x, 2 − x}` with `x ∈ {−2, 1, 3}` leaves the root unchanged,
  though 1 and 3 have no support; `Increasing{x, −x}` over `−3..6` stops at
  `x ≤ 3`, though 1 to 3 have none (`probes/incneg.cc`). The fact-check's sweep
  over 3,000 aliased instances with `±1` views, seed 1, finds `bounds(Z)`
  failing on 129, 70, 120 and 74 (`Increasing`, strict, `Decreasing`, strict)
  and 11, 5, 10 and 0 unsatisfiable instances not failed at the root. The
  alias mode of this audit's own `ordcheck.cc` has no views, which is why it
  missed this.
- ***An impossible repeated pair costs its width.*** `StrictlyIncreasing{x,
  x}`, `StrictlyIncreasing{x, y, x}` and the non-strict `Increasing{x + 1, x}`
  are unsatisfiable, but no pass notices. The forward sweep pushes `lb(x)` up,
  the backward sweep pushes `ub(x)` down, and the propagator is woken again by
  its own change until the domain empties. For a repeated pair at positions
  `i < j` with offsets `b_i` and `b_j`, each call closes the domain by about
  `2d`, where `d = step·(j − i) + b_i − b_j` is how far the pair falls short,
  so it takes about W / (2d) calls: W/2 for `{x, x}` strict and for
  `Increasing{x + 1, x}` or `Increasing{x + 1, y, x}`, W/4 for
  `StrictlyIncreasing{x, y, x}`, and W/6 for `StrictlyIncreasing{x, y, z, x}`.
  Measured, with proofs off, on the Release build of `c9ceea25` on
  fataepyc-10, 2026-09-29 (`probes/aliaswide.cc`; the last two rows from
  `tmp/fd-ordering/factcheck2/increasing/cyc.cc`, 2026-09-30); the sub-20 ms
  times are single runs that do not reproduce closely, and the propagation
  counts are the meaningful column:

  | Shape | W | Propagations | Time |
  |---|---|---|---|
  | `StrictlyIncreasing{x, x}` | 10³ | 501 | — |
  | `StrictlyIncreasing{x, x}` | 10⁵ | 50,001 | 0.017 s |
  | `StrictlyIncreasing{x, y, x}` | 10⁵ | 25,001 | 0.015 s |
  | `Increasing{x + 1, x}` | 10⁵ | 50,001 | 0.017 s |
  | `Increasing{x + 1, y, x}` | 10⁵ | 50,001 | — |
  | `StrictlyIncreasing{x, y, z, x}` | 10⁵ | 16,667 | — |

  The proof is sound: at W = 200 `StrictlyIncreasing{x, x}` takes 101
  propagations and 201 inferences (101 forward, 100 backward), and its proof is
  2,019 lines and verifies as unsatisfiable. It is width-proportional, about one
  inference per unit of width. The per-call large-domain guard does not see it,
  because no single call walks anything: a guard build of `c9ceea25`
  (`tmp/fd-table/build-guard`) runs W = 2·10⁵ to its 100,001 propagations
  without tripping, while a `LexSmartTable` control over the same width, built
  the same way, trips it (`probes/guardctl.cc`). `LessThan(x, x)` contradicts on
  its first call since #1088, and the same check belongs here.
- *A satisfiable repeat through a same-sign view* is harmless:
  `StrictlyIncreasing{x, x + 1}` holds for every `x` and takes two propagations
  at W = 10⁵. What stalls is a same-sign repeat whose offsets make the pair
  impossible, strict or not. (An opposite-sign repeat is weak in a different
  way, above.)

**Overflow.** `prev_lb + step` and `prev_ub − step` go through
`Integer::operator+` and `operator−`, which throw `IntegerOverflow` rather than
wrap. A bound at `±2⁶¹` plus one is still in range.

### Interval efficiency

**Fine at any width on distinct variables**, by inspection. There is no loop
over values anywhere in `increasing.cc`.

1. **The propagation side.** Two `O(n)` sweeps and an `O(n)` entailment check,
   all bounds reads. No `each_value`, no `in_domain`, no `IntervalSet`. The
   exception is not a walk but a call count: the impossible repeated pair above
   makes about W / (2d) calls of `O(n)` each, W/2 at worst.
2. **The reason side.** One order literal per inference, never per value. It
   is built as an `ExplicitReason` at the inference site, so only when an
   inference is made, and it is not guarded on `want_reasons()`. Its one
   literal is stored inline (`ReasonLiterals` is a `small_vector` with inline
   capacity 2), so there is no heap allocation, per inference or per call.
3. **The proof side.** One RUP line per inference, with no lemma and no second
   form, so there is nothing for a width gate to choose.
4. **The audit lane.** One row, `IncreasingChain`, pinned `Clean`:
   `Increasing{wide(p, 4)}`, four distinct plain variables over `0..10⁹`. It
   does not vary strictness, direction, repetition, holes or views. The one
   width hazard this family has is a repeated strict variable, and a row posting
   `StrictlyIncreasing{x, x}` would still pass, since the guard counts values
   walked per call and this hazard walks none. The lane has no instrument for
   it.

## Inference catalogue

Two rules, one per sweep. A conflict is not a third rule: it arises when a sweep
pushes a bound past the other bound, and the tracker asserts the attempted
literal with its reason, exactly as for a successful push.

Three facts hold for both rules.

**Each is a bare RUP, licensed by JP 3.2 (comparison) and Theorem 2.9.** The
negated conclusion bounds one variable, the reason bounds its neighbour, and
the row between them is `v[i+1] − v[i] ≥ step` with `step ∈ {0, 1}`, which is
Theorem 2.9's precondition exactly. See
[`justification-techniques.md`](../justification-techniques.md). Views keep
the step in range because the row is written over the view's own proof
variable, as [above](#variable-kinds-and-views). So **Proof size** is one line
for both rules, and **Offline reconstructibility** is `offline` for both: a
plain RUP against the database needs nothing chosen. (A *hinted* RUP would
have to name the row, which carries no label, so it would first have to find
the row over the clause's two variables. Labelling the rows, as cake does,
removes that.)

**There is one wire form.** `hints::Increasing`, `(constraint_id <id>)`, no
subhint and no payload. Measured on the probe enumerations: 121 annotations
for `Increasing` over five variables in `0..4`, 73 for the strict class over
`0..7`, every one that form.

**No justification reads `state`,** and there is no `JustifyExplicitly` in the
family.

### Rule: lower-bound-forward

- **Infers** — `v[i] ≥ lb(v[i−1]) + step`, for `i` from 1 up, where the
  `lb(v[i−1])` carried is the bound the previous push asked for, when there was
  one.
- **Fires when** — any variable's bounds move, in the chain sweep's forward
  pass.
- **Strength** — `GAC` on distinct variables, together with rule 2. At the
  fixpoint of both sweeps, `lb(v[i]) + step ≤ lb(v[i+1])` and
  `ub(v[i]) + step ≤ ub(v[i+1])` for every `i`. A value `a` of `v[k]` is then
  supported by taking every earlier variable at its lower bound and every later
  one at its upper bound: `lb(v[k−1]) ≤ lb(v[k]) − step ≤ a − step`, and
  `ub(v[k+1]) ≥ ub(v[k]) + step ≥ a + step`, and each of those is a domain
  value. Holes cannot remove this support, since it uses only bounds. On a
  **repeated** variable it is `bounds(D)`, not `GAC`, for plain and same-sign
  repeats, and not even `bounds(Z)` through an opposite-sign view (see
  [Robustness](#robustness-and-limits)). Checked by brute force at the root
  over random domains with holes (`tmp/fd-ordering/ordcheck.cc`, 3,000
  instances per class): no GAC failure on distinct variables in any of the four
  classes (seed 1), and on plain repeated variables GAC failing on 579 of 3,000
  (`Increasing`, seed 2) with `bounds(D)` holding on all of them.
  `increasing_test` also checks GAC at every node, on interval domains.
- **Algorithm** — one pass over `v`, `O(n)` bounds reads. Carrying the asked-for
  bound rather than the landed one is why the pass is not a fixpoint over holes
  (see [Propagator inventory](#propagator-inventory)).
- **Why it is true** — `v[i−1] ≥ L` and `v[i−1] + step ≤ v[i]` give
  `v[i] ≥ L + step`.
- **Proof technique** — `RUP`, by **JP 3.2**, licensed by **Theorem 2.9** with
  `B = step ∈ {0, 1}`: the negated conclusion `v[i] < L + step`, the reason
  `v[i−1] ≥ L`, and the row between them are 2.9's triple.
- **Reason** — `{v[i−1] ≥ L}`, one literal. Minimal. Not guarded on
  `want_reasons()`, but built only when the push is made.
- **Assertion** — `v[i] ≥ L + step ∨ ¬(v[i−1] ≥ L)`. On a view, measured at
  `Inferences`:
  ```
  a 1 ~i[x[0]][ge2] 1 p[0_view_of_x[1]_plus_1][ge2] >= 1::increasing:((constraint_id _1));
  ```
  A failed push asserts the same shape; the conflict is closed by the backtrack.
- **Hint** — `hints::Increasing`: `originator`, the `ConstraintID`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per inference, whatever the width.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No mutation lane exists for this family, which
  is an ordinary answer per [`TEMPLATE.md`](TEMPLATE.md). The corruption to try
  is the obvious one: drop the reason literal.

### Rule: upper-bound-backward

- **Infers** — `v[i] ≤ ub(v[i+1]) − step`, for `i` from `n − 2` down, carrying
  the asked-for bound as rule 1 does.
- **Fires when** — any variable's bounds move, in the backward pass, after the
  forward pass.
- **Strength** — `GAC` on distinct variables, with rule 1; see there.
- **Algorithm** — one pass over `v` in reverse, `O(n)` bounds reads.
- **Why it is true** — `v[i+1] ≤ U` and `v[i] + step ≤ v[i+1]` give
  `v[i] ≤ U − step`.
- **Proof technique** — `RUP`, by **JP 3.2**, licensed by **Theorem 2.9**, as
  rule 1 with the roles of the two bounds exchanged.
- **Reason** — `{v[i+1] ≤ U}`, one literal. Minimal.
- **Assertion** — `v[i] < U − step + 1 ∨ ¬(v[i+1] ≤ U)`. Measured at
  `Inferences`:
  ```
  a 1 ~p[1_neg_view_of_x[2]_plus_5][ge5] 1 i[x[3]][ge5] >= 1::increasing:((constraint_id _1));
  ```
- **Hint** — `hints::Increasing`: `originator`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per inference.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

- **`increasing_test`** (`increasing_constraint`, plus
  `increasing_constraint_view_mixed`): for each of the four classes, a fixed
  list of shapes (trivial, pairs, triples, a negative range, tight strict
  chains, length five, constants mid-chain, all-constant chains per #254) and
  five random shapes of two to five variables, each a range whose lower bound is
  in `−3..3` and which is two to four wider, or a constant in `−3..7`. Each runs with and
  without proofs under `solve_for_tests_checking_gac`, so every value left in a
  domain at every node is checked against the solution set. VeriPB runs when it
  is on the path. Seeded (`--seed`).
- **Duplicate-variable runs**, bare lanes only: `{x, x}`, `{x, x, y}` and
  `{x, y, x}` over `1..5` and `1..4`, under plain `solve_for_tests`, so full
  enumeration and the proof but no consistency check.
- **`scp_chain_{increasing,strictly_increasing}_{sat,unsat}`,
  `scp_chain_decreasing_sat`, `scp_chain_strictly_decreasing_unsat`:** see
  [Cake conformity](#cake-conformity).
- **MiniZinc:** `increasing.mzn` and `strictlyincreasing.mzn`, compared
  against the reference solver. `decreasing.mzn` and `strictlydecreasing.mzn`
  run too, but flatten to pairwise `int_lin_le` and never reach this family
  (see the frontend table).
- **XCSP3:** `ordered_strict.xml`. (`ordered_lengths.xml` exercises the linear
  decomposition, not this family.)
- **Audit lane:** the `IncreasingChain` row; see [Interval
  efficiency](#interval-efficiency).

**Runtime caps.** No lane sets or clears one, and the default caps **never
fire** on this family: 184 runs in the bare lane and 168 in `view_mixed`, all
complete (`GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500
increasing_test --seed=1`, and the same with `--view-position=mixed`, at
`c9ceea25`). So the capped and uncapped runs check the same thing here.

**Tightness:** no mutation lane, and no refusal shown by hand.

**What the tests do not cover.**

- **Holes.** Every tested domain is an interval, so the per-node GAC check
  never sees a hole. The root probe above covers holes; nothing checks them per
  node.
- **A repeated variable over a wide domain, or behind a view.** The duplicate
  runs use `1..5` and plain variables, so the width-proportional cost of an
  impossible repeated pair, and the opposite-sign weakness, are invisible to
  the suite.
- **MiniZinc's int `decreasing`,** whose tests exercise the stdlib
  decomposition instead.
- **The consistency of the repeated shapes**, deliberately: the duplicate runs
  check no level.
- **Real instances:** none ported.

### Benchmarks and examples

- **In the repository:** no example or benchmark posts this family.
- **Corpus:** 23 `increasing_int` and 5 `increasing_bool` posts across 11 of
  the 285 flattened MiniZinc Challenge models (one instance each;
  `tmp/fd-ordering/scan_corpus.py`), none of them strict. An int `decreasing`
  arrives as pairwise `int_lin_le`, so the flattened models cannot say how many
  were written that way, or count them here. A bool `decreasing` arrives as
  `increasing_bool` over the reversed array, so the 5 `increasing_bool` posts
  may include decreasing ones. Chains are 2 to 17
  variables for `int`, up to 65 for `bool`. One more model is missing from that
  corpus because its data are JSON: `gt-sort` 2025, whose 7-element instance
  posts three `strictly_increasing` chains (flattened by hand,
  `tmp/fd-ordering/mzn/gtsort.fzn`). The family is never a meaningful share of
  a solve: on `yumi-static` 2022, its busiest user, it takes about 8,100 calls
  and 1 ms of a 10 s run (8,093 and 8,088 in two runs;
  `GCS_PROPAGATOR_STATS=time`).
- **For CPU:** the strictly increasing enumeration below, which reaches both
  rules and nothing else, and has a known solution count, `C(D, n)`.
- **For proof verification:** the same enumeration at `n = 4`, with `D` from 8
  to 32 (below). It grows with the solution count, so pick `D` by the budget.

### CPU performance

*Release build of `c9ceea25` (GCC 15.2.0, `-O3 -march=native`); Gecode 6.3.0,
built locally; fataepyc-10, boost off, pinned with `taskset -c 4`,
`GLIBC_TUNABLES` fixing the malloc thresholds; median of five runs; wall time
of the whole solve, proofs off; 2026-09-29.*

Enumerating every strictly increasing sequence of length `n` over `0..D−1`,
branching in input order on the smallest value (`inc_gcs.cc`,
`inc_gecode.cc` in `tmp/fd-ordering/bench/`). Every model here is generalised
arc consistent, so the three searches explore the same assignments in the same
order: the same solutions, and no failures in any of them. The node counts
still differ, because GCS's `smallest_first` gives a variable one child per
value, where Gecode's `INT_VAL_MIN` branches in two (`x = min`, `x ≠ min`).

| n | D | Solutions | GCS `StrictlyIncreasing` | GCS, `n − 1` `LessThan` | Gecode `rel(x, IRT_LE)` |
|---|---|---|---|---|---|
| 10 | 20 | 184,756 | 0.212 s | 0.238 s | 0.084 s |
| 12 | 22 | 646,646 | 0.827 s | 0.924 s | 0.307 s |

| n | D | GCS recursions | GCS propagations, chain | GCS propagations, pairs | Gecode nodes | Gecode propagations |
|---|---|---|---|---|---|---|
| 10 | 20 | 277,134 | 160,446 | 379,712 | 369,511 | 245,352 |
| 12 | 22 | 999,362 | 629,850 | 1,595,673 | 1,293,291 | 861,852 |

- **GCS is 2.5 to 2.7 times Gecode's time on an identical tree.** This is a
  whole-solve comparison on a benchmark with no failures, so it measures the
  search loop and the solution callback as much as the propagator. It is the
  kind of comparison #868 asks for, done by hand with an API-level Gecode
  driver rather than through the harness in
  [`cross-solver-benchmarking.md`](../cross-solver-benchmarking.md).
- **The chain takes 10.9% and 10.5% less time than the pairs** (the pairs take
  11 to 12% longer; the fact-check's re-run gives 9.9% and 10.0% less), with
  2.4 to 2.5 times fewer propagations: one call sweeps what the pairs pass
  along one propagation at a time. That is the case for the class existing at
  all. Gecode's column is a chain too: `rel(x, IRT_LE)` posts one n-ary
  `NaryLqLe` propagator (`gecode/int/rel.cpp`), so the comparison is chain
  against chain.
- **What the benchmark does not exercise:** conflicts (there are none), the
  descending classes (which are the same code reversed), repetition, views and
  holes.

### Proof performance

*Same build and machine. `inc_gcs chain 4 D p`: `StrictlyIncreasing` over four
variables in `0..D−1`, all `C(D, 4)` solutions, VeriPB 3.0.2 with
`--force-checked-deletion`.*

| D | Solutions | Lines, `Off` | Bytes, `Off` | This family's lines | Share | VeriPB, `Off` | Lines, `Inferences` |
|---|---|---|---|---|---|---|---|
| 8 | 70 | 972 | 28.7 KB | 58 | 6.0% | 0.01 s | 622 |
| 16 | 1,820 | 16,134 | 452 KB | 562 | 3.5% | 0.27 s | 13,306 |
| 32 | 35,960 | 280,138 | 7.88 MB | 4,962 | 1.8% | 11.8 s | 238,706 |

"This family's lines" is the count of `a` lines carrying the `increasing` hint
at `Inferences`, which is one-for-one with the rule firings, since each is one
RUP at `Off`. **The family writes one line per inference, and almost nothing
else is its.** At `D = 32` the fully justified proof is 80,482 `del`, 76,415
comment, 45,420 `rup` (of which 4,962 are the family's and the rest
backtracking), 41,157 `core`, 35,960 `solx`, 472 `red` and 228 `pol` lines.
The proof is an enumeration proof: its size tracks the solution count, and the
chain is a rounding error in it.

**Assertion levels.** At `Off` every probe proof verifies, for all four classes
and the view shape (`probes/fam.cc`, `probes/runfam.sh`). At `Definitions` and
`Inferences` VeriPB accepts each proof with `s UNDER ASSERTIONS`, not
`VERIFIED`: every one of this family's inferences is an `a` line there (121 of
121 at `Definitions` for `Increasing` over `0..4`), so only `Off` checks the
family. At `Links` none is accepted: each fails at a `solx` step, which is
generic rather than this family's, since other families' probes fail at `Links`
the same way. Of the `Inferences` assertions, 121 of 443 (`Increasing`, `0..4`)
and 73 of 220 (strict, `0..7`) carry this family's hint; the rest are the
search's own.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified at `Off`, and the propagator is the same
with proofs on or off.

### Known limitations

- **A chain that repeats a variable in an impossible order takes time
  proportional to that variable's domain to fail.** `StrictlyIncreasing{x, x}`
  or `Increasing{x + 1, x}` over a domain of width W makes W/2 propagator
  calls before it empties the domain, and other repeated pairs about W / (2d)
  (see [Robustness](#robustness-and-limits)). The answer is right, the proof
  verifies, and the proof is about W inferences long, two per call.
- **A non-strict chain that repeats a variable is only bounds consistent** on
  it: `Increasing{x, y, x}` forces `x = y` but does not remove the values of
  one that the other lacks. Through an opposite-sign view (`x` and `c − x`) it
  is weaker still, and can miss that the chain is unsatisfiable.
- **MiniZinc's int `decreasing` and `strictly_decreasing`** are decomposed
  pairwise by the standard library and never use this propagator.
- **A reified `increasing` from MiniZinc** is decomposed into reified
  comparisons by the standard library.
- **An `increasing` in a model is invisible to `--difference-logic`,** though
  its rows are exactly difference constraints.

### Next steps

1. **Decide a repeated variable at install.** The cheapest fix, and the one
   #1088 made for `LessThan(x, x)`: two same-sign positions `i < j` over one
   underlying variable fix the difference between them, so compare the
   offsets once, against the step accumulated between them, `step·(j − i)`,
   not a single pair's step (with one step, `StrictlyIncreasing{x, y, x + 1}`
   is missed, and takes 100,001 propagations over `±10⁵`). If the pair cannot
   hold, the constraint is unsatisfiable, so contradict at once. A satisfiable
   repeat forces what lies between the two occurrences, which could be posted
   as equalities, or simply accepted as `bounds(D)`. An opposite-sign pair,
   `a·x + b_i` and `−a·x + b_j`, does not fix a difference: it bounds `x` to
   one side, `2a·x ≤ b_j − b_i − step·(j − i)`, a unary constraint to post at
   install. The accumulated step matters here too: with only the pair's step,
   strict chains still fail `bounds(Z)`, for example
   `StrictlyIncreasing{2 − u1, u0 − 1, u1 − 1}` with `u1 ∈ {2, 4}`. With it,
   the fact-check's sweep (`chk2.cc`, all four classes, seeds 1 to 3, lengths
   up to 6) finds no `bounds(Z)` failure and every unsatisfiable instance
   failed at the root, and `Increasing{x, 10 − x, x}` over `±10⁵` goes from
   199,992 recursions to one propagation. **What it leaves:** two variables
   repeated in interleaved opposite-sign positions still cost the width, since
   no pair on its own is impossible: `Increasing{x, y, 10 − x, 9 − y}` over
   `±10⁵` takes 100,001 propagations, and 50,003 with the unary bounds. So
   the fix restores `bounds(Z)`, not failure in a constant number of calls.
   Gecode already does the same-view half: `NaryLqLe::post`
   (`gecode/int/rel/lq-le.hpp`, lines 208–235 in 6.3.0) fails a strict chain
   with a repeated view outright, and for a non-strict one posts `NaryEqBnd`
   over the positions between. Filed as #1144. Small; it buys robustness on
   a shape MiniZinc can produce after aliasing, and it should come with a
   wide-domain row in the audit lane.
2. **Route MiniZinc's `decreasing` to the family.** Append to
   `minizinc/mznlib/redefinitions.mzn`:
   ```
   include "increasing.mzn"; include "strictly_increasing.mzn";
   predicate decreasing(array [$X] of var $$E: xs) = increasing(reverse(array1d(xs)));
   predicate strictly_decreasing(array [$X] of var $$E: xs) = strictly_increasing(reverse(array1d(xs)));
   ```
   Tested in scratch, not in the repository
   (`tmp/fd-ordering/factcheck2/increasing/ovl/mznlib_E`): on 2.9.7 and
   2.10.1, with no warnings, int, enum and expression arrays reach the family;
   bool and opt arrays flatten as before; reified forms still decompose; and
   the four repository tests give their 10 solutions each. The parameter name
   `xs` is load-bearing: named `x`, the overloads disagree with the standard
   library's on the parameter name, and 2.10.1 warns about it. Plain `var int`
   overloads calling the `glasgow_*` builtins directly are not enough: they
   break `r <-> decreasing(x)`, which then fails to flatten on both versions.
   Then delete the three dead `fzn_*decreasing*` files, and consider renaming
   `minizinc/tests/increasing.mzn` and `decreasing.mzn`, whose file names
   shadow the standard library's, with a warning on both versions. Small.
   Filed as #1146.
3. **Carry the landed bound, not the asked-for one.** Reading `lower_bound()`
   after each push makes one call a fixpoint over holes, which saves the
   re-run the probe shows. Trivial; not worth an issue on its own, but it
   should come with the idempotence claim it would then support.
4. **Label the rows `@c[id][i]`, in the user's order.** That makes all six
   cake cases `strict`, and lets a hinted RUP name its row. Small.
5. **Let the difference-logic presolver lift a chain.** Its donor enumeration
   is by class, and needs a labelled row per edge, which step 4 provides.
   Whether it would ever help is empirical: no corpus model where the chain
   matters has been found. Not worth an issue yet.

## Prior art

Nobody publishes a propagation algorithm for a monotone chain as such: it is the
conjunction of binary comparisons, and a solver either posts it that way (the
MiniZinc standard library does) or propagates the chain as one, as here.
Gecode's `rel(home, x, IRT_LE)` on an array posts one n-ary chain propagator,
`Rel::NaryLqLe` (`gecode/int/rel.cpp`, `rel.hh`), reversing the array for `>`
and `≥`. The proof side is the comparison's, JP 3.2 in Matthew McIlree's
thesis, and there is nothing new in it.

## Further reading

- [`comparison.md`](comparison.md): the binary case, the same theorem, and the
  `#1088` check this family lacks.
- [`justification-techniques.md`](../justification-techniques.md): JP 3.2 and
  Theorem 2.9's `B ∈ {0,1}` boundary.
- [`view-proof-logging.md`](../view-proof-logging.md): why a view's offset does
  not move a row's constant.
