# `Element`: a result equals the array entry an index selects

> **Maturity** production ·
> **Audited** 2026-09-08 at `76bfd836` plus #897, since merged as `977532a6` ·
> **Open issues** #900 (the index-support rule's per-value proof), #901
> (nothing can select the consistency level) and #902 (the general form of
> #901), all filed by this audit. #878 is
> closed by #897, which this branch carries. #868 is the audit-wide cross-solver
> prerequisite. Tracked under #871.

Four posted classes over one templated implementation and **four** propagators:
`result = array[index]`, in one or two dimensions, over an array of variables or
of constants. It is the first family in the arc that is not binary, and almost
everything interesting about it follows from that.

Three things to know before touching it. Its OPB encoding is **one half-reified
equality per array cell**, so unlike [`equals`](equals.md) and
[`comparison`](comparison.md) it is *linear in the array* rather than
logarithmic in anything — and the slowest proof to verify in the curated
benchmark set is an `Element` one. It is the first family with a real **option**
(`with_consistency`), the first that **claims idempotence**, and the first whose
propagators are not all GAC. And it is the only family so far whose dominant
wire hint belongs to **another family**: 93% of the assertions it is responsible
for on its own benchmark arrive labelled `equals`, because it reuses
`enforce_equality`.

## What it is

### Semantics

`NDimensionalElement<EntryType_, dimensions_>` enforces
`result = array[index₁ - start₁]…[index_d - start_d]`. Four concrete classes:

| Class | Array | Dims | Default consistency |
|---|---|---|---|
| `Element(result, index, array)` | variables | 1 | `GAC` |
| `Element2D(result, index₁, index₂, array)` | variables | 2 | `GAC` |
| `ElementConstantArray(result, index, array)` | constants | 1 | `BC` |
| `Element2DConstantArray(result, index₁, index₂, array)` | constants | 2 | `BC` |

Each index is given either bare (0-based) or as a `pair{var, start}`, where
`start` is subtracted before indexing. That offset exists for the frontends:
FlatZinc's `array_int_element` is 1-based, and XCSP3 carries an explicit
`startIndex` per dimension.

The index variables' bounds are **narrowed at `prepare()` time** to
`[start, start + size - 1]` via `define_bound`, so an out-of-range index is
removed before search rather than propagated away.

Degenerate cases:

- **A zero-length dimension.** No assignment can satisfy the constraint. This
  is a valid model, not a rejected one: `prepare()` records the flag,
  `define_proof_model` emits a trivially-false `0 ≥ 1` row so the OPB stays
  self-describing, and `install_propagators` installs a contradiction
  initialiser rather than a propagator. The index-bound definitions are skipped
  for that dimension, because `[start, start - 1]` would label an empty
  interval as if it were an ordinary trim.
- **A constant-valued array of variables.** Accepted, and detected:
  `_array_has_nonconstants` is computed in `prepare()`, and when every entry is
  already fixed the array is not watched and the equality propagator is not
  installed at all.
- **Aliasing anywhere in the scope** — result also an index, an index repeated,
  or result or an index appearing inside the array. Accepted, and it has one
  consequence that is easy to miss: it turns off every idempotence claim in the
  family. See [Propagator inventory](#propagator-inventory).
- **Views.** Accepted everywhere, at a cost in one rule; see [Variable kinds
  and views](#variable-kinds-and-views).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Element` | ✓ `array_var_int_element`, `array_var_bool_element` (1-based) | ✓ `element` over a variable list, and the value-form with a constant result | ? | ✓ `element` | |
| `ElementConstantArray` | ✓ `array_int_element`, `array_bool_element` (1-based) | ✓ `element` over an int list | ? | ✓ `element`[^same] | the arm MiniZinc reaches most |
| `Element2D` | frontend gap — no FlatZinc builtin for a 2-D element | ✓ `element` matrix form, both variable-result and constant-result | ? | ✓ `element_2d` | |
| `Element2DConstantArray` | frontend gap — as `Element2D` | ✓ `element` matrix form over an int matrix | ? | ✓ `element_2d`[^same] | |

[^same]: `constraint_type()` returns `element` or `element_2d` and nothing else,
    so the constant-array forms describe themselves exactly as the variable
    forms do, and `read_scp` rebuilds them as the variable form over
    singleton-domain variables. That is semantically the same constraint and a
    deliberate consequence of the `.scp` recording the *model* rather than the
    solving strategy — see [Options](#options).

**The consistency default differs by arm, and no frontend overrides it.**
`ElementConstantArray` is bounds-consistent by default, which is what MiniZinc's
`array_int_element` gets. Nothing in the frontends, the examples or the
benchmarks calls `with_consistency` on this family, so the constant-array GAC
arm is reached only by `element_test`'s `constgac` lane — which exists for
exactly that reason.

### Options

**`with_consistency(consistency::GAC{} | consistency::BC{})`** — the first real
option in the arc, and the only thing this family is tunable by.

It selects **propagation strength only and never changes the OPB encoding**,
which is the property that makes it an option rather than a model choice: the
proof model is the same either way, so a proof written under one setting is a
proof of the same problem as a proof written under the other. That is also why
the `.scp` does not record it, and why that is correct rather than a gap — the
`.scp` describes the constraint, not the strategy used to propagate it.

What it changes is which of the two result propagators is installed:

- `GAC` installs the union propagator: `result` keeps only values some live
  array entry can take.
- `BC` installs the range propagator: `result`'s *bounds* are narrowed to the
  range spanned by live entries, and interior values with no support survive.

**The index side is `GAC` either way.** `_bounds_only` is only ever read when
choosing between the two result propagators; the index propagator watches full
domains and tests against `result`'s whole domain, so an interior hole in
`result` still removes a now-unsupported index. That asymmetry is deliberate and
is stated in the code.

### Variable kinds and views

Result, indices and array entries are all `IntegerVariableID`, so plain
variables, constants and views are accepted throughout, and the test binary
sweeps views over **six** positions in the variable-array mode
(`add_view_tests(element_constraint_var element_test 6 var)`).

One rule degrades, and it is the same underlying cause as in
[`equals`](equals.md): **a view has no range literal** (#882). The GAC union
propagator's interval path is guarded on `result` *and* every array entry it
considered being a bare `SimpleIntegerVariableID`; if any is a view, the whole
propagation falls back to removing one value at a time. The guard is not about
propagation — the values removed are identical — but about the proof: the range
conclusion has to carry an order atom from `result` across the model's
half-reified equality to the entry, and a view's atoms are spelled through the
view, so that crossing has not been shown to bridge one.

The code names its two neighbours on this point, which is worth repeating
because it is the clearest statement anywhere of what the view problem actually
costs: `min_max.cc`'s range path carries the same restriction for the same
reason, and **`Among`'s does not**, because Among's lines stay within one
variable and never cross an equality at all. That is the distinction #882 turns
on.

There is a second, quieter view cost. The per-value fallback is also the path
that carries this family's `LargeDomainIterationCounter`, so a view operand
moves the family from "provably width-independent" to "width-proportional and
instrumented". See [Robustness and limits](#robustness-and-limits).

### Reification

`None.` The family has no reified form and no `ReificationCondition`. It is the
first family in the arc without one, which removes a whole layer the two binary
families spend a section on: no dispatcher, no verdict rules, no half-reified
selector flags of its own, and no `Theorem 2.6` step at the constraint's own
level.

Half-reification does appear in the encoding — every cell's equality is guarded
by the index literals — but that is the *encoding's* structure rather than a
user-visible reification. Nothing chooses it.

### Relation to other families

**Shares code with `equals`, and this is the family's defining coupling.**
`innards::enforce_equality` is exported from `gcs/constraints/equals/equals.hh`
and called from `element.cc` once the index is fully determined, to tie
`result` to the selected entry. Three consequences, in increasing order of how
surprising they are:

1. `equals`'s rules 1–4 *are* this family's rule 5. Their strength, their
   reasons, their proof techniques and their view degradations are inherited
   wholesale, and a change to any of them is an `Element` change.
2. The inferences arrive in the proof under the **`equals` hint**, carrying
   `Element`'s constraint id.
3. On the family's own benchmark that is **93% of the assertions it is
   responsible for**. See [Proof performance](#proof-performance), which is
   where this stops being a curiosity.

**Decomposes into this family.** Nothing internal. `Element` is posted by
models and frontends, not by other constraints.

**Posts as children.** Nothing.

**Presolvers.** `AutoTable` tabulates it like anything else. No presolver
recognises or rewrites it, and it publishes no citable row for one to use —
see [Labels](#labels).

**Nearly, but not, the same family.** `gcs/constraints/min_max/` shares the
range-path view restriction and the "support across a selection" shape;
`gcs/constraints/table/` is what an `Element` becomes under `AutoTable`. Both
are separate families.

## The proof model

### OPB encoding

**One half-reified equality per array cell**, guarded by the conjunction of
index literals that selects it:

```
for each cell (x₁, …, x_d):
    (index₁ = x₁ + start₁) ∧ … ∧ (index_d = x_d + start_d)
        ->  BinEnc(result) - BinEnc(array[x₁]…[x_d]) = 0
              split into two rows, le and ge, each half-reified

if any dimension has length zero:
    0 >= 1
```

The encoding is **definitional** — every row states part of what the constraint
means — and it is the first in the arc that is **linear in the size of the
model object** rather than logarithmic. Measured, one `Element` over an array of
`n` variables, counting the rows in the constraint's own OPB block:

| | |
|---|---|
| 1-D, `n` cells | `2n` rows of the constraint's own, plus `4n + 2` of index-literal definitions |
| 2-D, `n × n` cells | `2n²` of its own, on the same pattern |
| domain width | **no effect on the row count** — 50 rows at width 7, 15, 31 and 63 |

So the family's own contribution is exactly two rows per cell, and the block it
sits in is about three times that, because each cell's guard mentions an index
`eq` literal that pulls in its own definition (`@i[i][geK][r/f]` and
`@i[i][eqK][r/f]`) the first time it is used. Those belong to the
variable-encoding layer, not here.

An `Element` over a 3-cell array of width-7 variables, showing one cell:

```
@i[i][eq0][r] 1 i[i][ge0] 1 ~i[i][ge1] 2 ~i[i][eq0] >= 2;
@i[i][eq0][f] 1 ~i[i][ge0] 1 i[i][ge1] 1 i[i][eq0] >= 1;
-1 i[r][b0] -2 i[r][b1] -4 i[r][b2] 1 i[_1][b0] 2 i[_1][b1] 4 i[_1][b2] 7 ~i[i][eq0] >= 0;
 1 i[r][b0]  2 i[r][b1]  4 i[r][b2] -1 i[_1][b0] -2 i[_1][b1] -4 i[_1][b2] 7 ~i[i][eq0] >= 0;
```

The half-reification coefficient (`7` here) is the worst-case violation, so it
scales with the domain width even though the row count does not.

### Labels

**`None.` This family labels nothing**, and it is the only one audited so far
that does not. `define_proof_model` calls `add_constraint` twice and
`add_labelled_constraint` never, and there is no
`ConstraintProofModelData<NDimensionalElement>` specialisation. Verified against
a real `.opb`: of the 50 rows in a 3-cell instance's element block, the 34
labelled ones are all `@i[…]` variable-literal definitions and the 16 unlabelled
ones are the constraint's.

Two consequences worth separating, because only one of them is a problem:

- **Nothing can cite an `Element` row**, so this family cannot be a presolver
  donor the way `comparison` is for `DifferenceLogic`. That is a
  non-consequence today: no presolver wants to.
- **An external justifier cannot *name* the row it is RUPing against.** Its
  derivations are all RUP, which needs no labels — but a tool reconstructing one
  has to identify "the half-reified equality for the cell this reason's index
  literals select" positionally rather than by label. That is derivable, and it
  is the reason the reconstructibility verdicts below are `hinted` rather than
  `offline`.

### Cake conformity

Conformant. `constraint_type()` emits cake's names (`element`, `element_2d`) and
`s_expr()` writes the array as a bare list — position is implicit, no per-entry
index — each index as a `(variable offset)` pair, then the result:
`(X0 … Xn-1) (Y0 off0) … Z`, with `element_2d`'s array as a list of rows. The
offset convention matches: both sides subtract it.

**Four SCP chain cases**, covering both dimensionalities in both directions:

```
element_sat  element_unsat  element_2d_sat  element_2d_unsat
```

The constant-array classes have no case of their own and need none: they write
the same keyword and the reader rebuilds them as the variable form over
singleton variables, per [^same].

`scp_reader_test.cc` round-trips one `Element` and one `Element2D` through
write → read → write and compares the descriptions byte for byte.

### Proof-time state

**Root-level index bounds, and nothing else.** `prepare()` calls
`propagators.define_bound` on each index variable for both bounds, which emits
the labelled `@i[name][lb]` / `[ub]` rows — so unlike the two binary families,
this one *does* put something in the OPB at root beyond its own constraint rows.
It is the index range, it is two rows per dimension, and it is what makes an
out-of-range index a modelling impossibility rather than a propagation
obligation.

Beyond that:

- no proof flags, no auxiliary variables, no scaffolding;
- **nothing created lazily and nothing deleted by this family** — but every rule
  emits intermediate lines at `ProofLevel::Temporary`, and those the level
  machinery deletes. On `langford --size=8` there are 16,319 `del` lines against
  71,243 total, which is a fair measure of how much of an `Element` proof is
  scratch;
- there is no proof-only auxiliary, hence no question of whether unit
  propagation determines it on `solx`;
- there is no proof-only vector to index, hence none of the dangling-index
  hazard.

## The implementation

### Initialisation and global data

`prepare()` does three things and is the only place any of them happen: it
checks every dimension for zero length (returning early if it finds one, with
the flag set), narrows each index variable's bounds to the array's extent, and
records whether any array entry is a non-constant.

`install_propagators` then dispatches on the index variables' concrete type via
`as_homogeneous`, so an all-`Simple`, all-`View` or all-constant index vector
gets a propagator specialised at install time and the hot per-cell iteration
skips the variant deview. A mixed scope falls back to the general
`IntegerVariableID` path. This is an install-time specialisation, not a runtime
branch, and it is the only place in the arc so far where a family does this.

Argument validation is `check_array_dimensions` in the constructor, so a ragged
array throws at `post`.

### Propagator inventory

**Four propagators, and one of them appears once per dimension.**

| Propagator | Triggers | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|
| index support, one per dimension | `on_change` result, the other indices, and the array when it has non-constants | 1 | always | claims, unless the scope aliases | no |
| result range | `on_bounds` result and the array; `on_change` the indices | 2 | `BC` | **never claims** — see below | no |
| result union | `on_change` result, indices and the array | 3, 4 | `GAC` | claims, unless the scope aliases | no |
| selected-entry equality | `on_change` indices and result | 5 | `_array_has_nonconstants` | claims, unless the scope aliases | via `enforce_equality` |
| contradiction initialiser | — (runs once at root) | 6 | a zero-length dimension | n/a | n/a |

**The trigger sets are as narrow as the reads allow, and the interesting one is
what each propagator does *not* watch.** An index propagator does not watch the
index it writes: a value's support depends on `result`, the *other* indices and
the array, so a self-wake was pure waste before idempotence claims existed and
is now also the thing that makes the claim sound. The result propagators do not
watch `result` for the union arm (they watch it `on_bounds` for the range arm,
which reads bounds), and neither watches the array when every entry is a
constant.

**This is the first family in the arc that claims idempotence, and the way it
guards the claim is the part worth reading.** Three of the four propagators
return `EnableButIdempotent`, on the argument that each writes only variables
that play no part in computing what it writes. But that argument fails the
moment two scope positions share an underlying variable — result also an index,
an index repeated, result or an index inside the array — because then a
propagator's own writes can invalidate the snapshot it read. So
`install_propagators_impl` computes `scope_has_aliasing` up front, over the
underlying variables of result, the indices and every array entry, and **every
claim in the family is conditioned on it**.

The subtlety, stated in the code and worth restating here: the engine's own
trigger-scope downgrade cannot stand in for that check, precisely *because* the
index propagators deliberately omit the variable they write from their triggers.
The engine cannot see aliasing involving a variable it was never told about.

**The range propagator deliberately does not claim**, and the comment gives a
worked counterexample rather than an argument, which is the right way round: it
reads and writes `result`'s bounds, and a bound write that snaps past a hole
tightens the range the next run filters entries against, which can exclude the
entries that supported the old bounds. Concretely, `result ∈ {0,3,6,10}` against
entries `{2,5,9}` first infers `[2,9]`, which snaps to `[3,6]`, and only a
re-run gets `≥ 5` from the sole surviving entry. The union propagator has no
such hazard because value removals are exact.

**Self-disabling.** `None`, except through `enforce_equality`. Every propagator
here returns `Enable` or `EnableButIdempotent`; none returns
`DisableUntilBacktrack`, because none of them is finished after acting — an
index removal can enable a further one on the next wake.

### Mutable state and incrementality

`None.` No `add_constraint_state`, no watch scratch, no cached supports. Every
call recomputes support from scratch.

That is a real design choice here rather than an obvious one, because this is
the first family where an incremental scheme would be conventional — a
support-counting or residue-based `Element` is a standard trick. What the family
does instead is arrange for the *non-incremental* computation to be cheap:
support tests go through `in_domain` and `domains_intersect` rather than
materialising `result`'s domain (#515), the union sweep subtracts whole runs
rather than values (#515 and #878), and the sweep short-circuits as soon as
nothing is left to find support for. The measured per-call cost is
[57–74 ns](#cpu-performance), which is the argument that this was the right
call, though nobody has built the incremental version to compare against.

### Robustness and limits

**Large domains: clean, and by measurement rather than by inspection.** Unlike
[`comparison`](comparison.md), this family cannot be cleared by grep — it is
full of loops, and the question is only ever whether each one is over *values*
or over something bounded. Three `GCS_LARGE_DOMAIN_GUARD` audit rows cover it,
all `Clean`, and the reasoning behind the trio is the most careful in the lane:

| Row | Shape | Why it is a distinct row |
|---|---|---|
| `Element` | wide result, three **narrow** entries, `GAC` | a wide entry erases the whole unsupported set in one `erase_range` and leaves nothing behind; only a narrow entry leaves a wide remainder to remove |
| `Element/BC` | the same instance, `BC` | so the pair is comparable — it is the weaker arm that makes it clean, not an easier instance |
| `Element/holey` | three **full-width** entries with one value knocked out of each | neither row above reaches the sweep's other half: a contiguous entry goes in as one `erase_range` however wide, so nothing exercised an entry that is wide *and* holey |

That third row is #897's, and the bug it caught (#878) is worth knowing as a
shape rather than as an incident. `domain_size(entry) == hi - lo + 1` was the
test for "contiguous, so one `erase_range`"; **one hole is all it takes** to
fail it, and the fallback went value by value, so a 10⁹-wide entry missing a
single value was walked a billion times. Fixed by walking the entry's *runs*,
which is what its domain is either way.

*Measured elsewhere — #897's own table, root propagation only, three entries
`0..w` with one value knocked out, pinned to one core.* 10⁶: 10 ms → 0 ms.
10⁷: 48 ms → 0 ms. 10⁸: 422 ms → 0 ms. 10⁹: 4,238 ms → **0 ms**. Memory was
flat at ~5.5 MB throughout, both ways — which is the part that matters for how
the bug was found: **this one does not die, it just stops**, so the audit row
would have read `Clean` on any machine and the lane's `bad_alloc` fallback
would never have fired. It took the guard build.

**One path is still per-value, and it is the view path.** The GAC union
propagator's per-value fallback carries a `LargeDomainIterationCounter` — one of
three such hand-added sites in the solver, with `all_equal.cc` and `equals.cc` —
because it walks an `IntervalSet` the propagator built for itself, which
`State`'s iterators never see. The counter's own comment records why it is not
optional: without it the probe's outcome is decided by how much memory the
machine has (16 GB and 81 s here, a `bad_alloc` somewhere smaller), which is not
a test result.

**Unbounded domains.** Not separately probed. Every remaining loop is over
array cells, index domain values or domain *runs*, so width does not enter
except on the view path above.

**Negative values and zero.** Fine, and covered: the test matrix includes
negative ranges in every position, and index offsets are exercised by both
frontends.

**Overflow.** `(x - index_starts.at(d)).as_index()` is the arithmetic to worry
about, and it is guarded by `prepare()` having already narrowed each index to
`[start, start + size - 1]`, so the subtraction cannot be negative and the
result cannot exceed the array's size. Not separately probed.

**Per-value costs.** Two: the GAC union propagator's view fallback (above), and
**the index-support rule's justification**, which emits one proof line per value
of the selected array entry's domain. That second one runs only with proofs on,
is not instrumented, and is the subject of [Next steps](#next-steps).

## Inference catalogue

Six rules: one on the index side, three on the result side (two of which are
the two arms of the consistency option), one delegated to `equals`, and one
root contradiction.

Four facts hold across them and are not repeated in each entry.

**Every rule is an explicit derivation, not a bare RUP.** The family contains no
plain `JustifyUsingRUP` except the root contradiction: each of rules 1–4 emits a
nested walk of proof lines at `ProofLevel::Temporary` and then RUPs its
conclusion (`ThenRUP::Yes`). So the **Proof technique** is `RUP+hints`
throughout, and the proof size of a single inference is *not* one line — it is a
product over the index domains, which is what makes this family's proofs the
largest in the curated set.

**The shape of every derivation is the same, and the thesis names it.** Rule out
the conclusion for each way the remaining indices could be assigned, collapsing
one dimension at a time, then let the emptied domain do the rest. The per-tuple
lines rest on **Theorem 2.8** (an equality on a bit sum fixes every bit, which
is how a cell's guarded equality carries a value from entry to result) and the
collapse on **Theorem 3.2** (an emptied defined domain unit-propagates to
conflict). See
[`justification-techniques.md`](../justification-techniques.md); the published
procedures are **JP 3.9, 3.10 and 3.11**, and this family instantiates all
three.

**The reason is a `generic_reason` over the whole scope**, concatenated with
per-rule literals, and assembled only when `inference.want_reasons()` — every
site guards, which is worth stating given what the audit found in
[`comparison`](comparison.md).

**Two wire forms, and the second belongs to `equals`.** `hints::Element`, wire
form `(constraint_id <id>)` with no subhint, carries rules 1–4 and 6. Rule 5
arrives as `equals:((constraint_id <element's id>))`, because `enforce_equality`
is shared code that hints with its `owner` argument. That is sound and the
attribution is right, but it means **the hint name does not identify the
constraint family**, and on this family's own benchmark the `equals`-hinted
assertions outnumber the `element`-hinted ones 13 to 1.

### Rule: index-support

- **Infers** — `indexₖ ≠ v`, for an index value `v` such that no assignment of
  the other indices selects an entry whose domain meets `result`'s.
- **Fires when** — `result`, another index, or an array entry changes; one
  propagator per dimension `k`.
- **Strength** — `GAC` on the index, and unconditionally so: this rule is
  installed and behaves identically under both consistency settings, because
  `_bounds_only` only chooses between the result propagators. `element_test`
  asserts `CheckConsistency::GAC` on every index in every mode, including the
  `BC` ones.
- **Algorithm** — for each value of indexₖ, a recursive search over the other
  index domains for one supporting cell, stopping at the first. Support is
  tested with `in_domain` (constant array) or `domains_intersect` (variable
  array) — never by materialising `result`'s domain, which was the point of
  #515. O(|dom(indexₖ)| · ∏ |dom(index_j)|) membership tests, in *cells*, with
  no per-value work on any domain.
- **Why it is true** — if no cell reachable with `indexₖ = v` can take a value
  `result` can also take, then `indexₖ = v` has no support.
- **Proof technique** — `RUP+hints`, by **JP 3.9 (empty intersection for
  Element)**. For each way the other indices are assigned, emit one line per
  value `w` of the selected entry — `R ⇒ (indexₖ ≠ v) ∨ (entry ≠ w)`, RUP by
  **Theorem 2.8** because the guarded equality forces `result = w` against a
  `result` that cannot take it — then collapse per dimension, and the emptied
  entry domain gives the conclusion by **Theorem 3.2**.
- **Reason** — `generic_reason` over `result`, the other index variables and
  (when the array has non-constants) every entry the search explored. Guarded on
  `want_reasons()`; the vector is a per-value allocation with no small-buffer
  optimisation, so it is skipped in ordinary search.
- **Assertion** — `indexₖ ≠ v ∨ <reason>`. Measured on `langford --size=8`,
  where all 485 element-hinted assertions are this rule:
  ```
  a 1 ~i[_17][eq11] 1 ~i[_33][eq1] 1 ~i[_24][eq3] >= 1::element:((constraint_id _3));
  ```
- **Hint** — `hints::Element{owner}`.
- **Offline reconstructibility** — `hinted`. The procedure is published and the
  reason names every variable the walk ranges over, so a justifier can rebuild
  it — but it must locate the cells' equality rows positionally, because this
  family labels none of them ([Labels](#labels)).
- **Proof size** — `∏_{j≠k} |dom(index_j)| · (|dom(entry)| + 1)` lines per
  inference, plus one per collapsed dimension. **Per value of the array entry's
  domain**, which is this family's largest proof cost and the one thing here
  that is not width-independent. Measured on a 1-D instance where the rule fires
  once at the root: `8w + 16` proof lines for an entry of width `w`, so 653 KB
  at 10³ and **1.01 GB at 10⁶** — for one inference. Only `w` of those lines are
  the rule's; the rest is the encoding layer defining an `eq` atom per value.
  Filed as **#900**, with the interval-wise witness `equals` got in #881 as the
  candidate fix.
- **Gaps** — `None.` for the inference; the derivation's *size* is **#900**.
- **Tightness** — `Not shown.` No mutation lane exists for this family.

### Rule: result-range

- **Infers** — `result ≥ lo` and/or `result ≤ hi`, where `[lo, hi]` is the range
  spanned by the entries whose bounds meet `result`'s current bounds.
- **Fires when** — `result`'s or an entry's bounds move, or an index changes.
  `BC` only.
- **Strength** — `BC`. Interior values with no support survive, deliberately.
- **Algorithm** — one pass over the index domains collecting the min lower and
  max upper bound of the entries still in range, short-circuiting once the found
  range already covers `result`'s bounds. O(cells) bounds reads.
- **Why it is true** — `result` must equal some live entry, so it lies within
  the range those entries span.
- **Proof technique** — `RUP+hints`. **No published procedure for this
  conclusion**: the derivation is JP 3.10's tuple walk with a bound as the
  conclusion instead of a value, and nothing in that argument depends on which
  literal is concluded, so this is a gap in the published list rather than a new
  technique.
- **Reason** — `generic_reason` over the indices, plus the matching bound
  literal for each entry considered and `result`'s two current bounds. Guarded.
- **Assertion** — `result ≥ lo ∨ <reason>`, or the mirrored form.
- **Hint** — `hints::Element{owner}`.
- **Offline reconstructibility** — `hinted`, as rule 1.
- **Proof size** — one line per index tuple plus one per collapsed dimension;
  independent of any domain width.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: result-union-range

- **Infers** — `result ∉ [lo, hi]` for each contiguous run of `result`'s domain
  that no live entry can supply.
- **Fires when** — `result`, an index or an entry changes; `GAC` only, and only
  when `result` and every entry considered are bare
  `SimpleIntegerVariableID`.
- **Strength** — `GAC` on `result`.
- **Algorithm** — copy `result`'s domain, then subtract each live entry's domain
  from it: one `erase_range` for a contiguous entry, or one per run for a holey
  one (#878/#897). The remainder is already an `IntervalSet`, so it is removed
  run by run. O(cells · runs), with no per-value step.
- **Why it is true** — a value of `result` survives iff some live entry can take
  it.
- **Proof technique** — `RUP+hints`, and **this rule has no published form**:
  JP 3.10 states the same fact one value at a time. Stating it over an interval
  costs **two extra lemmas per index tuple**, which carry the range literal
  across the model's half-reified equality — under this tuple's guard, `result`
  inside `[lo, hi]` puts the entry inside it too. Each is RUP by **JP 3.2 /
  Theorem 2.9** with the opposing-bounds triple, exactly as
  [`equals`](equals.md)'s interval bridge. With both in the database the entry's
  own range literal from the reason is a falsified clause and the tuple line is
  propagation. **Two lemmas per tuple, independent of how wide the range is**,
  which is the property the rule exists for.
- **Reason** — `generic_reason` over the indices, plus
  `not_in_range(entry, lo, hi)` per entry considered. Guarded.
- **Assertion** — `¬(result ∈ [lo,hi]) ∨ <reason>`.
- **Hint** — `hints::Element{owner}`.
- **Offline reconstructibility** — `hinted`, and the most demanding in the
  family: a justifier needs the procedure, the two-lemma bridge, *and* the
  positional identification of the cells' rows.
- **Proof size** — three lines per index tuple (two lemmas and the tuple line)
  plus one per collapsed dimension, per removed run. Independent of run width.
- **Gaps** — `None.` for the inference; the *conclusion* degrades to rule 4
  when a view is involved, which is #882.
- **Tightness** — `Not shown.`

### Rule: result-union-value

- **Infers** — `result ≠ v`, one unsupported value at a time.
- **Fires when** — as rule 3, but at least one of `result` or a considered entry
  is a view or constant.
- **Strength** — `GAC` on `result`. Same fixpoint as rule 3, reached one value
  at a time.
- **Algorithm** — the same subtraction, then a walk of the remaining
  `IntervalSet` value by value. **O(unsupported values)**, and the site of the
  family's `LargeDomainIterationCounter`.
- **Why it is true** — as rule 3.
- **Proof technique** — `RUP+hints`, by **JP 3.10 (missing value for Element)**,
  which is this rule exactly: one line per index tuple ruling out the value
  under that tuple's guard, then the collapse by **Theorem 3.2**.
- **Reason** — `generic_reason` over the indices plus `entry ≠ v` per entry
  considered. Guarded.
- **Assertion** — `result ≠ v ∨ <reason>`.
- **Hint** — `hints::Element{owner}`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — one line per index tuple plus one per collapsed dimension,
  **per removed value**. This is the proof-size regression rule 3 exists to
  avoid.
- **Gaps** — `None.` for the inference. It is a proof-*size* and propagation-cost
  fallback, not a strength loss.
- **Tightness** — `Not shown.`

### Rule: selected-entry-equality

- **Infers** — whatever `equals` infers between `result` and the selected entry:
  a value forced, a symmetric difference pruned, or bounds intersected.
- **Fires when** — every index is a singleton, and the array has non-constants.
- **Strength** — as `equals`: `GAC` for two distinct operands.
- **Algorithm** — `enforce_equality(result, entry, …)` with the index equality
  literals as the base reason. See [`equals.md`](equals.md) rules 1–4 for the
  four inferences and their costs.
- **Why it is true** — with the index fixed, the constraint *is* an equality.
- **Proof technique** — `RUP` or `RUP+hints` per the `equals` rule that fires,
  by **JP 3.12** and **JP 3.2**; **JP 3.11 (single value for Element)** is the
  thesis's statement of this rule in the entry-pruning direction, and its
  correctness proof is the one to read, because it is where the index literals
  in the reason do their work. There is no separate derivation here: the index
  literals sit in the base reason, which activates the cell's half-reified rows,
  and `equals`'s procedures then apply to them.
- **Reason** — the index equality literals, plus whatever the `equals` rule
  adds.
- **Assertion** — whatever the `equals` rule asserts. Measured on
  `langford --size=8`:
  ```
  a 1 i[_20][eq8] 1 ~i[_15][eq9] 1 ~i[_40][eq8] >= 1::equals:((constraint_id _23));
  ```
  — where `_23` is `* constraint element _23` in the OPB.
- **Hint** — **`hints::Equals{owner}`, with `owner` this `Element`.** Not
  `hints::Element`. This is the family's most consequential proof-model fact and
  the one most likely to mislead a tool; see [Proof
  performance](#proof-performance).
- **Offline reconstructibility** — `hinted`, and with a caveat that is this
  rule's alone: the hint says `equals`, and a justifier that resolves the
  constraint id expecting `Equals`'s two equality rows will find an `Element`'s
  per-cell half-reified rows instead. What it needs is the cell those rows
  belong to, which the reason's index literals name.
- **Proof size** — as `equals`: one line for the RUP rules, three per interval
  for the bridge.
- **Gaps** — `None.`, and it inherits `equals`'s view degradation along with
  everything else.
- **Tightness** — **shown, by inheritance and only partly.** `equals`'s
  `fixed_operand_reason` and `bridge_lemmas` mutation lanes corrupt
  `enforce_equality` itself, so they cover this rule's derivation as it is
  reached from `equals`. No lane reaches it *through* an `Element`, so the index
  literals' contribution to the reason is not covered.

### Rule: empty-dimension contradiction

- **Infers** — a contradiction.
- **Fires when** — any array dimension has length zero; once, from an
  initialiser, at the root.
- **Strength** — n/a; the model is infeasible.
- **Algorithm** — a length check per dimension in `prepare()`. O(dimensions).
- **Why it is true** — there is no cell to select.
- **Proof technique** — `RUP` against the trivially-false `0 ≥ 1` row the
  encoding emits for this case. The only bare RUP in the family.
- **Reason** — none needed.
- **Assertion** — the empty clause.
- **Hint** — `hints::Element{owner}`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`, and there is nothing to show: the row is
  trivially false.

## Evidence

### Tests

One binary, `gcs/constraints/element/element_test.cc`, run as **five ctest
lanes** selected by an argv mode — `const`, `constgac`, `const2d`, `var`,
`var2d` — plus a view sweep on each, for 15 lanes in total.

- **Enumeration with per-node consistency assertion**, and the mode decides
  which: `solve_for_tests_checking_gac` for the variable-array modes, and
  `solve_for_tests_checking_consistency` for the constant-array ones with
  `CheckConsistency::BC` or `::GAC` on `result` according to the arm and
  **always `::GAC` on the index**. That last part is the evidence for rule 1's
  unconditional GAC claim.
- **Both arms of the option are run on the same instances.** `constgac` differs
  from `const` only by `with_consistency(GAC)`, so the pair is comparable — and
  it exists because `ElementConstantArray` is BC by default, which left the GAC
  propagator's constant-array instantiation reachable but never actually run.
- **VeriPB really runs**, for every case. Seeded, all five modes:
  **96 proofs, all verifying, in 7.14 s** — 20 for `const`, 20 for `constgac`,
  16 for `const2d`, 25 for `var`, 15 for `var2d`. Note the shape of that against
  the other families: `comparison` verifies 1,356 proofs in 3.35 s. An `Element`
  proof costs about **30 times more to check** than a `comparison` one.
- **A view sweep over six positions** in the variable-array mode
  (`add_view_tests(element_constraint_var element_test 6 var)`), and two or
  three in the others.
- **Aliasing**, via the `*_dup_xx` tests — which is what the
  `scope_has_aliasing` guard exists for.
- **Index offsets**, exercised by both frontends' lanes.
- **Seeded**, reproducible with `--seed=N`.
- **`.scp` round-trip** for one `Element` and one `Element2D` in
  `scp_reader_test.cc`, write → read → write, compared byte for byte.
- **Three large-domain audit rows**, described under [Robustness and
  limits](#robustness-and-limits) — the most careful trio in that lane, and one
  of them (`Element/holey`) was added by the change this document is based on.
- **No runtime caps** on the element lanes.

What the tests do **not** cover:

- **No mutation lane.** Every rule answers `Not shown.` for tightness except
  rule 5, which is covered only as `equals` reaches it and not as `Element`
  does. Per the policy in [`TEMPLATE.md`](TEMPLATE.md) that is an ordinary
  state, not outstanding work — but this family is a better candidate than most
  if one is ever wanted, because its derivations are the only ones in the arc
  that emit a nested walk rather than a single line.
- **No large-domain case in the test file itself.** The three audit rows carry
  it, in a build nothing runs by default.
- **No proving case uses a wide array entry.** The index-support rule emits one
  proof line per value of the selected entry's domain, and every entry in the
  test file is narrow, so the cost is exercised only where it is invisible. See
  [Next steps](#next-steps).
- **`Element2D` has no aliasing test across dimensions** — an index repeated in
  both positions. `scope_has_aliasing` would catch it, and nothing checks that
  it does.
- **`langford`, the family's usual benchmark, exercises two of the six rules.**
  See [Proof performance](#proof-performance).

### Benchmarks and examples

In-repo examples and benchmarks posting this family: `langford`, `qap`, `tsp`,
`table_layout`, `p_dispersion`, `hitori`, `seat_moving`, plus both frontends.
The split that matters is which arm they reach:

- **Variable array, `GAC`**: `langford`, `hitori`, `seat_moving`. Only
  `langford` is in a hot loop; the other two finish in under a tenth of a
  second.
- **Constant array, `BC`**: `qap`, `tsp`, `table_layout`, `p_dispersion`.

Recommendations, and they differ by what you are measuring:

- **For CPU benchmarking the family as a whole: `qap --size=12`.** Already
  curated in `dev_docs/benchmarking.md` as `qap_12`. It is `element_2d` over a
  constant array at **97% of calls and 96% of propagation time**, which is the
  most family-dominated benchmark in the arc so far.
- **For the variable-array GAC arm: `langford --size=11`**, also curated. It is
  the only variable-array `Element` in a hot loop in the set, and the only
  benchmark that reaches rule 5 — so it is the one to use for anything touching
  `enforce_equality`.
- **For proof benchmarking: `langford --size=10`** (UNSAT, 60.4 s to verify) or
  **`qap --size=10`** (optimal, 283.8 s), both curated in
  `dev_docs/proof-benchmarks.md`. `langford --size=8` is the right size for
  reading a proof by hand: 3.9 MB, 71,243 lines, 1.39 s to verify.
- **Do not** `--prove` `qap --size=12`: `proof-benchmarks.md` caps it, and
  `--size=11` stays under the cap at 2.0 GB but does not finish verifying inside
  900 s.

### CPU performance

*Measured 2026-09-08 at `977532a6` (i.e. #897 as merged), Release + `GCS_WERROR=ON`,
g++ 15.2.0, AMD Ryzen 9 9950X3D, 30 GB, otherwise idle, `taskset -c 4`. Min of
three.*

| Benchmark | Arm | Time | Recursions | Propagator calls | Busiest type |
|---|---|---|---|---|---|
| `qap 12` | constant array, 2-D, `BC` | 1.72 s | 123,333 | 24,507,109 | `element_2d`, 23,773,491 (97%) |
| `langford 11` | variable array, 1-D, `GAC` | 3.87 s | 256,593 | 29,205,903 | `element`, 25,663,053 (88%) |

Under `GCS_PROPAGATOR_STATS=time`:

| Benchmark | Share of propagation time | Per call |
|---|---|---|
| `qap 12` | **96% of 1,825 ms** | ~74 ns |
| `langford 11` | **39% of 3,750 ms** | ~57 ns |

Two things to read off that pair. `qap` is the cleaner benchmark — at 96% of
propagation time it is very nearly a measurement of this family alone, more so
than `ortho_latin` is for `equals` (18%) and comparable to `difference_chain`
for `comparison` (99%). And the **call share and time share diverge the other
way from `equals`**: there, 71% of calls were 18% of time, because a
not-equals call is trivial. Here 88% of calls are 39% of time on `langford` and
97% are 96% on `qap`, so an `Element` call is roughly as expensive as the
average call in its model, not much cheaper. That is what a nested support
search costs even when it is careful.

`langford`'s effectful share is 3,261,200 of 29,205,903 propagations (11%), with
128,820 contradictions — so nearly nine calls in ten find nothing, and the
narrow trigger sets are doing real work.

**The consistency option, measured.** Both constant-array benchmarks, default
`BC` against `with_consistency(GAC)` patched in, same build and machine:

| Benchmark | Arm | Time | Recursions | Propagations | Effectful |
|---|---|---|---|---|---|
| `qap 12` | `BC` (default) | **1.71 s** | 123,333 | 24,507,109 | 4,679,021 |
| `qap 12` | `GAC` | 3.37 s | 123,333 | 25,452,372 | 7,587,766 |
| `tsp` | `BC` (default) | **11.19 s** | 4,285,745 | 83,372,056 | 41,243,802 |
| `tsp` | `GAC` | 13.67 s | 4,285,745 | 57,702,481 | 38,036,662 |

**The search trees are bit-identical** — 123,333 and 4,285,745 recursions, and
the same solution counts, both ways — while `GAC` makes **62% more effectful
inferences** on `qap`. Every one of those extra prunings was unobserved. `tsp`
shows the same thing from the other side: `GAC` does **fewer** propagations
(57.7M against 83.4M) and is still slower, because it prunes harder per call and
none of it pays.

**The mechanism, which is more general than these two models.** What matters is
which consumers of a variable can observe an interior value at all. In both
models the element's result is consumed by exactly two things: the element
itself, and a bounds-consistent `LinearEquality` (`wcosts == cost` in `qap`,
`dist_sum == obj` in `tsp`). Neither model branches on a result — `qap` branches
on `variable_order::dom(xs)` and `tsp` on `dom(succ)`, the permutation
variables. So nothing outside the constraint can tell a hole in the result from
its absence, and `GAC` is computing a fact nothing can read.

**And for a constant array the element cannot observe it either**, which is what
makes the two defaults look principled rather than arbitrary:

- The index-support rule tests `in_domain(result, array[i])`. `GAC` removes from
  `result` exactly the values no live entry supplies, which are never of the
  form `array[i]` for a live `i` — so those removals cannot change any
  index-support test.
- The equality rule, which is what would push `result`'s domain into an array
  entry, is `if (array_has_nonconstants)` and **is not installed at all** for a
  constant array.

Measured directly, root propagation on a constant-array instance whose `result`
has interior values no entry supplies:

```
BC : index {0 1 2 3}  result {0 1 2 3 4 5 6}
GAC: index {0 1 2 3}  result {0 2 4 6}
```

Different result domain, **identical index domain**. So for a constant-array
`Element`, `GAC` on the result is observable only outside the constraint — and
in these two models nothing outside can observe it. For a *variable* array the
equality rule is installed, a tighter result propagates into the array entries,
and those are ordinary variables that may be branched on or read value-wise;
nothing here argues `GAC` is wasted there. Filed as **#901**, with the general
form — every constraint declaring per-variable whether it might care about
interior values — as **#902**.

**Cross-solver comparison: `Not measured.`** #868's harness exists and the
method is in `dev_docs/cross-solver-benchmarking.md`, but it has been pointed at
`equals` only. `Element` is a good third target for a reason the other two
families lacked: every solver has an `element`, every solver's is expected to be
GAC on the index, and both frontends produce one directly, so the "which model
is defensible" question that dominated #868 barely arises.

**Historical A/B, measured elsewhere.** #897's own table, on the change this
document is based on: `langford --size=11`, medians of five pinned interleaved
runs with search identical throughout, went from 47.587e9 to 47.170e9
instructions (−0.88%) and 19.789e9 to 19.734e9 cycles (−0.28%) — so the #878
fix was slightly *faster* on the benchmark as well as removing the hazard. Three
other shapes were measured and all fixed the hazard; this was the only one that
also won. Do not put those figures in a table beside the ones above: different
commit, different metric, different run.

### Proof performance

*Same build and machine. `langford --size=8`: 1,632 recursions, 300 solutions,
0.040 s to solve and write. VeriPB 3.0.2.*

| Assertion level | Proof size | Lines | Assertions | VeriPB | Verdict |
|---|---|---|---|---|---|
| `Off` (justify everything) | 3.92 MB | 71,243 | 0 | 1.39 s | `VERIFIED COMPLETE ENUMERATION` |
| `Links` | 5.00 MB | 49,498 | 38,465 | — | — |
| `Inferences` | 4.77 MB | 45,093 | 39,593 | — | — |

Verification is **35× the solve time**, and `langford --size=9` is 43× (17.9 MB,
315,626 lines, 7.69 s against 0.177 s). The curated set has the large end, and
`dev_docs/proof-benchmarks.md` puts this family at the top of it:
**`langford11` is the slowest proof to verify in the whole set** at 662.9 s for
669 MB, and instances posting an `Element` hold **four of the top six by proof
size** (`hitori` 937 MB, `langford11` 669, `seat_moving` 645, `qap10` 504).
`langford10` at 101 MB and 60.4 s is the small end of the same shape.

Be careful what that does and does not attribute. `langford11` and `qap10` are
this family's benchmarks and the size is fairly its own; `hitori` and
`seat_moving` post an `Element` among several other constraints, and nobody has
measured the split, so their place in that list is suggestive rather than
evidence. What *is* evidence is the per-cell encoding and the nested
derivations, both measured below.

**Note what the assertion levels do here, because it is the opposite of the
other two families.** Asserting inferences makes the proof *bigger* — 3.92 MB
to 4.77 MB — where it cut `equals`'s by 44% and `comparison`'s by 10.5×. The
reason is that this family's derivations are nested walks whose intermediate
lines are short, so replacing a walk with a single `a` line carrying a full
`generic_reason` over the entire scope is not a saving. A family whose
justifications are already one line per inference gains from the switch; one
whose justifications are a product over index domains, with a wide reason, does
not.

**Where the assertions come from, and this is the finding.** Of the 39,593
assertions at `Inferences` level, `element` is only 485 (1.2%) — behind
`all_different` (17,078), `plus` (13,553) and `equals` (6,545). But `langford`
posts **no `Equals` constraint at all**: it posts `AllDifferent`, `Element` and
`Plus`. Resolving every `equals`-hinted assertion's constraint id against the
OPB's own provenance comments:

| Wire hint | Assertions | Owning family |
|---|---|---|
| `equals` | 6,545 | **`element`, all 6,545** |
| `element` | 485 | `element`, all 485 |

So the family's real proof footprint is **7,030 of 39,593 assertions (17.8%),
of which 93% wear another family's hint** — because rule 5 delegates to
`enforce_equality`, which hints `equals` with the caller's constraint id.

That is sound, and the attribution is right: the derivation genuinely is
`equals`-shaped and the owner genuinely is the `Element`. But for the external
justification tool it is a trap worth stating plainly: **the hint names the
procedure, not the constraint family.** A tool that reads
`equals:((constraint_id _23))` and looks up `_23` expecting an `Equals`
constraint's two equality rows will find an `Element`'s per-cell half-reified
rows. What it wants is the cell, and the reason's index literals name it.

**Which rules the benchmark reaches: two of six.** All 485 element-hinted
assertions on `langford --size=8` are three-literal clauses over `eq` atoms —
rule 1's shape — and **there is not a single range (`in`) literal in the
proof**, so rule 3 contributed nothing. Rules 2 and 4 cannot fire (`langford`
uses the GAC default and has no views), and rule 6 needs an empty dimension. The
reason rule 3 never fires is worth knowing: `langford`'s result variable is a
root singleton (`create_integer_variable(i+1, i+1)`), so there is nothing for
the union sweep to prune. Anyone reading a per-inference proof cost off this
table should know it is an average over rule 1 and rule 5.

**Own contribution against the shared layers.** In the OPB the split is
measurable and clean: two rows per cell are the constraint's, and about four
more per cell are the index variables' own atomic-literal definitions, emitted
lazily on first use inside the block — so **the family's own encoding is about a
third of the block it appears in**, and independent of domain width. In the
`.pbp` the picture is different in kind, because this family's derivations are
its own lines rather than a single assertion pulling in a shared layer:
`langford --size=8`'s 71,243 lines are 43,828 `rup`, 16,319 `del`, 7,056 `pol`
and 1,764 `red`, and the `pol`/`red` pair — the order-literal machinery that
dominated the other two families' proofs — is under 13% here.

## Status, gaps, and next steps

### Proof-logging gaps

**Nothing is left unjustified, and no rule is weakened when proofs are
enabled.** There is no `a`-oracle use and no unlogged inference. Every one of
the six rules emits a real derivation, and three of them instantiate a published
justification procedure exactly.

`None.` on cost gaps in the propagation direction, since #897: the last
width-proportional path that ran with proofs off was the holey-entry
subtraction, and it now walks runs. Every reason in the family is guarded on
`want_reasons()`.

There are two gaps in the other direction — costs paid only when proofs *are*
on — and they are both about the size of a derivation rather than its
correctness:

- **The index-support rule emits one line per value of the selected entry's
  domain** (rule 1), which is **#900**. That is JP 3.9 as published, so it is
  not a divergence, but a proving run over a wide array entry writes a proof
  proportional to that entry's domain size — measured at **1.01 GB and 8,000,016
  lines for a single inference** at width 10⁶, against 0 ms with proofs off. The
  rule itself is well covered, every proving lane exercises it, but only over
  the narrow entries the test file uses, so nothing reaches it at a width where
  the cost would show and nothing instruments it. Only one line per value is the
  rule's own; the other seven are the variable-encoding layer defining an `eq`
  atom for every value of the entry, because the rule's lines name
  `array_var != v`.
- **A view costs the result-union rule its interval conclusion** (#882), so the
  proof goes from three lines per index tuple per *run* to one per tuple per
  *value*.

### Known limitations

**A view turns the GAC union rule per-value** (#882). The `all_simple` guard
covers `result` and every entry considered, so one view anywhere in that set
costs the whole propagation its interval conclusions — in propagation time and
in proof size both. This family is the clearest place to see what #882 costs,
because the code names its two neighbours: `min_max.cc` has the same
restriction for the same reason, and `Among`'s range path needs none because its
lines never cross an equality.

**Bounds consistency is the default for constant arrays, and nothing can select
otherwise from a model file** (#901). `with_consistency` is a C++ call; neither
frontend exposes it, so every MiniZinc and XCSP3 model gets the default. Both
defaults are the right ones on the benchmarks we have — measured under [CPU
performance](#cpu-performance) — and the reason generalises: `GAC` on a result
is worth having only if something can observe an interior value of it, which
for a constant array means something *outside* the constraint. That is the
argument, not "it happens to be faster here".

**The proof is large, and grows with the array.** The encoding is two rows per
cell, and a single inference's derivation is a product over the index domains.
The slowest proof to verify in the curated benchmark set is an `Element`
benchmark, and `qap --size=12` must not be proved at all. This is inherent to
the constraint rather than a defect, and it is the family the paper should cite
when it wants to show what a non-binary constraint's certificate costs.

**Nothing can cite an `Element` row**, because the family labels none of them.
Not a problem today — no presolver wants one — but it makes every
reconstructibility verdict `hinted` rather than `offline`, since a justifier has
to identify the cell's rows positionally. See [Labels](#labels).

**Idempotence is claimed, and the claim rests on an argument the engine cannot
check.** Three propagators claim, conditioned on `scope_has_aliasing`, and the
reason the engine's own trigger-scope downgrade cannot substitute for that check
is that the index propagators deliberately omit the variable they write from
their triggers. If a future change adds the written variable back to the
triggers, the manual check becomes redundant; if a future change adds a
propagator that writes something it also reads, the check must be extended.
There is no test that would catch either mistake — only the aliasing tests,
which pass either way because the claim is merely an optimisation.

### Next steps

Ranked, and all filed.

1. **#900 — give the index-support rule an interval-wise witness.**
   Rule 1 emits one proof line per value of the selected array entry's domain,
   which is JP 3.9 as published and correct — but it is the only remaining
   width-proportional thing in the family, no test reaches it *at a wide
   entry*, and it is uninstrumented because `LargeDomainIterationCounter`
   covers propagation paths rather than justifications. Two things to find out,
   in order: whether an interval-wise witness exists for it at all (the answer
   for the analogous rule
   in [`equals`](equals.md) was yes, #881, and that took a real argument), and
   failing that, whether a proving run over a wide entry is a hazard worth a
   guard. The measurement is cheap: one `Element` over a wide entry, proofs on,
   at a few widths.
2. **#901 — let a model choose the consistency level.** `with_consistency` is a
   C++ call and neither frontend exposes it, so every MiniZinc and XCSP3 model gets
   the default it happens to be given — `BC` for a constant array, `GAC` for a
   variable one — with no way to say otherwise.

   The defaults are measured and both are right (see [CPU
   performance](#cpu-performance): bit-identical trees, `GAC` costing 1.97× on
   `qap` and 1.22× on `tsp`) — but right *because* nothing in those models can
   observe an interior value of the result, which is a property of the models
   and, for the constant-array arm, of the constraint. So the ask is to expose
   the level rather than to change a default; changing one would need a
   benchmark that branches on an element's result or feeds it to a
   domain-consistent consumer, and there is none in the tree.

   **#902** is the general form of the same observation: if every constraint
   declared, per variable, whether it might care about interior values, a
   bounds-only variable could be detected per *model* instead of guessed per
   class. That is a much bigger project, and its caveats are worth reading
   before anyone starts — the brancher is a consumer (`dom` and `dom_wdeg` read
   domain size), so is the objective, and it is a fixpoint rather than one pass.
3. **#868 — point the cross-solver harness at this family.** The best third
   target the arc has: every solver has an `element`, every solver's is GAC on
   the index, and both frontends produce one directly, so the model-choice
   question that dominated #868 for `equals` barely arises.

**Not to do, having been considered.**

*An incremental support scheme.* A support-counting or residue-based `Element` is
the conventional answer to 25M calls, and this family instead made the
non-incremental computation cheap — non-copying support tests (#515), run-wise
subtraction (#515, #878), and an early exit once nothing is unsupported. At
57–74 ns a call the remaining headroom is small, and an incremental scheme would
have to survive the aliasing cases that already cost the family its idempotence
claims. Worth revisiting only with a benchmark where `Element` is both dominant
and *effectful*, which neither `qap` (96% of time, but constant-array BC) nor
`langford` (11% effectful) is.

*Labelling the per-cell rows.* No presolver wants them, and the cost is a label
per row on the largest OPB blocks in the solver. Revisit if a presolver ever
needs to cite one, or if the external justifier turns out to want names rather
than positions.

## Prior art

- **The justification is almost entirely published**, and this family is the
  best-covered in the arc: **JP 3.9** (empty intersection), **JP 3.10** (missing
  value) and **JP 3.11** (single value) from McIlree's thesis (2026) are rules
  1, 4 and 5 respectively, resting on **Theorem 2.8** for the per-tuple lines
  and **Theorem 3.2** for the collapse. Two rules are ours: the interval
  result-union rule (rule 3), which states JP 3.10's fact over a run instead of
  a value at the cost of two bridge lemmas per tuple, and the bounds arm (rule
  2), which is JP 3.10's walk with a bound as the conclusion and is better
  described as a gap in the published list than as a new technique.
- **The propagation algorithm is textbook and deliberately so.** GAC for
  `element` is a support sweep; nobody publishes it. The interesting engineering
  is all in what the sweep avoids doing — not materialising `result`'s domain
  (#515), subtracting runs rather than values (#515, #878) — and none of that is
  novel either, only careful.
- **Two things here would be worth a sentence in a survey.** The
  consistency-as-an-option design, where the level changes propagation strength
  and provably not the OPB encoding, so a proof is a proof of the same problem
  either way. And the idempotence claim conditioned on scope aliasing, which is
  a general pattern for any propagator that omits the variable it writes from
  its own triggers.

## Further reading

- [`dev_docs/justification-techniques.md`](../justification-techniques.md) —
  what licenses this family's derivations: Theorems 2.8 and 3.2, the three
  Element justification procedures, and the two places this family departs from
  them.
- [`equals.md`](equals.md) — rule 5 *is* that family's rules 1–4, via the
  exported `enforce_equality`, and its interval bridge is the same construction
  as rule 3's. Read its catalogue alongside this one.
- [`comparison.md`](comparison.md) — the contrast worth drawing: one
  definitional row against two per cell, one wire form against two, no options
  against one, no idempotence claim against three, and a proof this family's
  outsizes by three orders of magnitude.
- `dev_docs/large-domains.md` — the three audit rows, why they are three, and
  the #878 story in full, including why a hazard that costs 4.2 s and 5.5 MB is
  harder to find than one that costs 78 GB.
- `dev_docs/constraints.md` — the generic three-phase structure, `ArrayParam`,
  and the `install_propagators` dispatch this family specialises.
- `dev_docs/benchmarking.md`, `dev_docs/proof-benchmarks.md` — where `qap` and
  `langford` sit in the curated sets, and the cap on `qap --size=12`.
- `dev_docs/cross-solver-benchmarking.md` — the identical-tree method, for
  whoever picks up item 3.

## Developer commentary

`None.` The family predates the practice of writing design notes, and its
inline comments are the best in the arc so far on the three things a reader will
get wrong: the `scope_has_aliasing` argument and why the engine cannot make it,
the range propagator's non-claim with its worked counterexample, and the
contiguity test in the union sweep with the reason it survives rather than being
subsumed. This document does not duplicate them.

**What this family changed in the template.** `None.` Two sections it stretched
without breaking, recorded here because the next non-binary family will hit them
too:

- **Reification became `None.`** for the first time, and the section is short
  rather than absent. Worth keeping: "this family has no reified form" is a fact
  a reader wants confirmed, especially in a family whose *encoding* is full of
  half-reification.
- **The wire-form inventory has an entry that is another family's.** The
  template's Hint field asks for the `gcs::innards::hints` type, which is the
  right question and gets the surprising answer here. Nothing needed to change,
  but the arc now has a case where a cross-family pivot keyed on hint name would
  attribute 6,545 assertions to the wrong family, and that is worth a line in
  the tracker rather than in the template.
