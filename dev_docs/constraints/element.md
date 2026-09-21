# `Element`: a result equals the array entry an index selects

> **Maturity** production ·
> **Audited** 2026-09-08 at `76bfd836` plus #897, since merged as `977532a6`;
> re-audited 2026-09-21 at `6b220c79` ·
> **Open issues** #901, the one this audit filed that is still open — and it is
> open on its *second* item only, since a level can now be asked for. #966
> (three constraints that read interiors they only watch for bounds) is the
> follow-up #902 left behind, and it is not about this family. #868 is the
> audit-wide cross-solver prerequisite. Tracked under #871.

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

A fourth, since the first pass: it is **the first client of optional interior
pruning**, and still the only one. `consistency::Auto` here means "be
generalised arc consistent on the result exactly where something in this model
could observe the difference", decided once before search from what else is
installed. Everything about that is in [Interior values and optional
pruning](#interior-values-and-optional-pruning), including the shapes where the
promises do not hold and the arm stays GAC.

**What the second pass changed.** Three of this audit's own findings have been
worked on since, and two of them changed what the document says rather than
only what it points at.

| Landed | What it changed here |
|---|---|
| #900 → #929 | the index-support rule's justification is over **runs**, not values: `8w + 16` proof lines for one inference at entry width `w` — 1.01 GB at 10⁶ — become **flat at 45**. It takes the disjointness walk `equals` built in #881, now shared out of `innards/no_overlap_walk.hh` |
| #924 → #925 | the result-union rule picks its form by the **width of the run**, not by the kind of the variables, so there is no view fallback left. `element.cc` no longer carries a `LargeDomainIterationCounter` at all |
| #902 → #965, #967 | `consistency::Auto`, the propagator pair, and the analysis behind it. The reason this family is the interesting one to read on the subject |
| #901 | **still open**, and now only on its second item: `with_consistency` is reachable from three examples via `--element bc\|gac\|auto`, and neither frontend exposes it yet |

The two proof-side fixes are the same finding in two places — *a form chosen by
a type test rather than by what it costs* — and between them they take the last
two per-value sites out of the family. That is worth reading before [Interval
efficiency](#interval-efficiency), which is now where both live.

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

**`with_consistency(ElementConsistency)`** — the first real option in the arc,
and still the only thing this family is tunable by. `ElementConsistency` is
`std::variant<consistency::GAC, consistency::BC, consistency::Auto>`, so those
three and nothing else; asking for `Tabulated` or `VC` is a compile-time error.

**Defaults differ per posted class, and the difference is principled.**

| Class | Default |
|---|---|
| `Element`, `Element2D` | `consistency::GAC` |
| `ElementConstantArray`, `Element2DConstantArray` | `consistency::BC` |

#901 measured why: over a **constant** array, generalised arc consistency on
the result is observable only outside the constraint, and in both benchmarks
that reach one the only outside consumer is a bounds-consistent linear sum — so
`GAC` made 62% more effectful inferences on `qap` over a bit-identical search
tree, and cost 1.2–2x. Over a **variable** array the selected-entry equality
rule *is* installed, so a tighter result propagates into the entries, which are
ordinary variables something may well branch on. Nothing argues `GAC` is wasted
there.

It selects **propagation strength only and never changes the OPB encoding**,
which is the property that makes it an option rather than a model choice: the
proof model is the same either way, so a proof written under one setting is a
proof of the same problem as a proof written under the other. `element_auto_test`
checks that by comparing the `.opb` files of all three settings byte for byte.
That is also why the `.scp` does not record it, and why that is correct rather
than a gap — the `.scp` describes the constraint, not the strategy used to
propagate it.

What it changes is which of the two result propagators runs:

- `GAC` installs the union propagator: `result` keeps only values some live
  array entry can take.
- `BC` installs the range propagator: `result`'s *bounds* are narrowed to the
  range spanned by live entries, and interior values with no support survive.
- `Auto` installs **both**, as an optional-interior-pruning pair, and lets
  `gcs::solve_with()` decide once — before search, after the last presolver —
  which one is live. It does so only over an array of constants whose result is
  not also one of the indices; anywhere else it is `GAC`, because that is where
  the pair's promises hold. Until the choice is made, and in a search that never
  makes it, `Auto` propagates exactly as `GAC` does. See [Interior values and
  optional pruning](#interior-values-and-optional-pruning), which is where the
  argument lives.

**`Auto` is a policy, not a level**, which is why it never appears as a rule's
**Strength** below: each arm states what that arm achieves, and `Auto` says
which arm. Note the contrast with `consistency::Dynamic`, which `Plus` and
`Minus` take: that re-decides at every call on the current domains, where this
decides once for the whole search and can therefore be reported on the stats
channel.

**Nothing installs it by default and neither frontend exposes it** (#901,
still open on that item). What does exist is
`--element bc|gac|auto` in `qap`, `tsp` and `p_dispersion`, spelled like
`langford`'s `--plus`, defaulting to `bc` so those three still reproduce the
MiniCP trees. `p_dispersion`'s tuple variant is the one example where `Auto`
keeps `GAC`: holes in the distances affect its `ArrayMin`.

**The index side is `GAC` under all three settings.** The consistency choice is
only ever read when choosing between the result propagators; the index
propagator watches full domains and tests against `result`'s whole domain, so an
interior hole in `result` still removes a now-unsupported index. That asymmetry
is deliberate, is stated in the code, and is exactly what makes the pair's
second promise the interesting one.

### Variable kinds and views

Result, indices and array entries are all `IntegerVariableID`, so plain
variables, constants and views are accepted throughout, and the test binary
sweeps views over **six** positions in the variable-array mode
(`add_view_tests(element_constraint_var element_test 6 var)`).

**No rule degrades any more.** This section used to describe the family's one
view cost, and it is worth keeping the shape of it because the fix is the same
lesson twice. The GAC union propagator's interval path was guarded on `result`
*and* every array entry it considered being a bare `SimpleIntegerVariableID`;
if any was a view, the whole propagation fell back to removing one value at a
time. The guard was not about propagation — the values removed are identical —
but about the proof: the range conclusion has to carry an order atom from
`result` across the model's half-reified equality to the entry, and a view's
atoms are spelled through the view, so that crossing had not been shown to
bridge one. Two things closed it:

- **#925** stopped asking the question that way. What decides the form is the
  **width of the run**, not the kind of the variables: the bound lemmas name no
  bit vector, only order conditions on `result` and the entry, so they are
  emitted over whichever encoded variable each one resolves to (#924).
- **#904** made that safe for the tree at large, by giving a registered view its
  own range literals linked to the underlying variable's — which is where a
  view's order *and* range atoms now live, and it is also the representation the
  model states this equality in.

So a view here costs nothing in propagation, nothing in proof size, and nothing
in width. The `LargeDomainIterationCounter` that used to sit on the fallback
path is gone with the fallback; `element.cc` carries none.

*The neighbour the code named is still worth repeating*, because it is the
clearest statement of what the range-crossing question actually is:
`min_max.cc`'s range path carried the same restriction for the same reason, and
**`Among`'s did not**, because Among's lines stay within one variable and never
cross an equality at all. That distinction is unchanged by #904 — a range
literal still cannot cross an equality on its own, and still needs its endpoints
converted into bounds first. What changed is only which variables have a range
literal to convert.

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

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| index support, one per dimension | `on_change` result, the other indices, and the array when it has non-constants | derived: **result**, the other indices, and the entries when non-constant | 1 | always | claims, unless the scope aliases | no |
| result range | `on_bounds` result and the array; `on_change` the indices | derived: **the indices only** | 2 | `BC`, or `Auto`'s fallback | **never claims** — see below | no |
| result union | `on_change` result, indices and the array | derived: **the indices and the entries**; result is not in its triggers at all | 3, 4 | `GAC`, or `Auto`'s pruning | claims, unless the scope aliases | no |
| selected-entry equality | `on_change` indices and result | derived: **result and the indices** | 5 | `_array_has_nonconstants` | claims, unless the scope aliases | via `enforce_equality` |
| contradiction initialiser | — (runs once at root) | derived: **nothing** | 6 | a zero-length dimension | n/a | n/a |

**Under `Auto` the two result propagators are one propagator id**, installed by
`install_with_optional_interior_pruning()`, which runs whichever member is live;
the other costs nothing, not even a wake. Each member keeps its own triggers,
its own hole sensitivity and its own idempotence verdict — which is why the
table lists them separately and why the range arm's refusal to claim survives
being paired. For degree and adjacency the pair counts once, over the union of
the two scopes. The shape is measured rather than decorative: installed as two
propagators with one permanently disabled, a pair that fell back took **11% more
L1 misses** than the fallback alone on `qap`, because every per-id array had a
dead slot beside each live one; as one id, 1%.

**The hole-sensitivity column is entirely derived, and every entry is right**,
but two are worth reading rather than skimming, because they are what the whole
`Auto` argument turns on. The **result union** arm does not list `result` at
all: it does not watch the variable it writes, for the same reason the index
propagators do not watch theirs. And the **index support** propagator *is*
affected by holes in `result` — it asks whether the entry at a live index tuple
is still in `result`'s domain. Those two facts together are what make this
family's pair legal and non-trivial; [Interior values and optional
pruning](#interior-values-and-optional-pruning) works through why.

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

### Interior values and optional pruning

**This family is the mechanism's first and so far only client**, so this
section is longer here than it will be anywhere else. The mechanism itself is
[optional-interior-pruning.md](../optional-interior-pruning.md); what follows is
what is true of `Element`.

**Offers.** Under `consistency::Auto`, and only then, the two result
propagators are installed as a pair over one target, `result`:

| | |
|---|---|
| **Targets** | `result` |
| **Pruning** | the result union propagator (rules 3 and 4), generalised arc consistent |
| **Fallback** | the result range propagator (rule 2), bounds consistent |
| **Rules that stop firing under the fallback** | 3 and 4. Rule 2 starts firing instead; rules 1, 5 and 6 are unaffected |

**Promise one: the two differ only in the target's interior.** With **constant**
entries the range is at a fixpoint only once its lower bound is the smallest
live entry in `[lower, upper]`. It gets there by re-running after a bound it
infers snaps past a hole — which is exactly why it must never claim idempotence,
and the two facts are the same fact — and a bound is always in the domain, so
that entry is also the smallest value the union keeps. Likewise at the top. If
no live entry is in range at all, the index propagators wipe out. The union is
never weaker than the range on any domain, so the pruning is at least as strong
as the fallback, and what is left over between them is interior only.

**Promise two: this constraint cannot see those values itself**, and this is the
load-bearing one, because nothing checks it. Of the family's other propagators,
the one that holes in `result` affect is the **index support** rule — it asks
whether the entry at some live index tuple is in `result`'s domain. It keeps the
promise by being an exact support test: the union removes only values no live
entry supplies, which are never of the form `array[i]` for a live `i`, so those
removals cannot change any index-support answer. #901 measured it directly, on a
constant-array instance where `result` has interior values no entry supplies:

```
BC : index {0 1 2 3}  result {0 1 2 3 4 5 6}
GAC: index {0 1 2 3}  result {0 2 4 6}
```

Different result domain, **identical index domain**. Without this promise the
analysis would count the constraint's own index propagator as an observer, every
element would keep its own pruning, and nothing would ever fire on `qap` or
`tsp`.

**The shapes that do not qualify**, which is the more informative half:

- **Any array with a non-constant entry.** The range takes an entry's *bounds*
  and misses the holes in it that the union sees, so `result ∈ [1, 10]` against a
  live entry in `{0, 5, 10}` keeps 1 where the union gets 5 — and that is a
  **bound**, which anything can see. Promise one fails. `Auto` is `GAC` there.
- **`result` doubling as one of the indices.** Then the index propagators prune
  the pair's own target, so promise two's "exact support test" argument no longer
  covers everything that writes to it. `Auto` keeps the plain `GAC` arm.
- **Two index variables aliasing each other**, as `qap`'s `D[x_i][x_i]` does, is
  *not* a disqualifying shape and was checked rather than assumed: every
  propagator here treats the dimensions independently, so they all relax the
  constraint the same way and neither argument changes.

**Observes.** Holes in the **indices** and in the **entries** affect this family
in every arm, and holes in `result` affect the index-support propagator. So an
`Element` in a model keeps alive any other pair whose target is one of its
indices or entries — and, under the second promise, is ignored as an observer of
its *own* result.

**How to see what was decided.** `choose_optional_interior_pruning()` reports a
summary at `StatsLevel::General`, so it appears in the statistics a search
prints at the end, and at `StatsLevel::Detailed` each pruning it kept together
with the constraint that observes it. A search driven some other way than
`gcs::solve_with()` never calls it and keeps every pruning on, which is why
`Auto` is defined to propagate as `GAC` in that case rather than being an error.

**What is tested, and why the obvious test would not work.** Both arms are
sound, so a wrong switch-off can only ever make the solver weaker — no solution
is lost and no proof fails. A comparison of *trees* is the only thing that can
catch it, and `element_auto_test` is that: over two thousand random
constant-array element models, under a brancher that reads only bounds, `Auto`
explores exactly the tree `GAC` does. It also checks that its fixture is worth
running — that about half the models switch something off, and that some of them
are models where `BC` really does explore a different tree (a hole-aware
all-different over the results, mostly) — and a mutation that makes every
pruning unneeded fails it. Where `Auto` chose the same arm for every element it
additionally has to match that arm forced, propagation counts and all, which is
what the one-id shape promises.

**What it costs when it changes nothing.** Over identical search, timed at
eight stack alignments, `Auto` against the arm it chose was 0.9% slower on
`qap`, 0.4% on `tsp` and 1.3% on `p_dispersion --grid 12x12 -p 6`. On the 2011
MiniZinc Challenge `open-stacks` instance the same identical work was 1.9%
*faster* single-threaded and 4.4% slower with an idle second thread present,
which moves glibc's allocator off its single-threaded path. Differences of that
size are heap layout; see [`benchmarking.md`](../benchmarking.md).

### Robustness and limits

**Unbounded domains.** Not separately probed. Every loop in the family is over
array cells, index-domain values or domain *runs*; see [Interval
efficiency](#interval-efficiency) for why none of them is over a width.

**Negative values and zero.** Fine, and covered: the test matrix includes
negative ranges in every position, and index offsets are exercised by both
frontends.

**Degenerate shapes.** A zero-length dimension is a root contradiction (rule 6)
rather than an exception. An index whose domain runs outside the array is
narrowed by `prepare()` rather than rejected. `result` aliasing an index, and an
index repeated, are legal and are what `scope_has_aliasing` exists for — every
idempotence claim in the family is conditioned on it, because a propagator's own
writes can otherwise invalidate the snapshot it read, and the engine's
trigger-scope downgrade cannot stand in for the check precisely because the
index propagators omit the variable they write from their triggers.

**Overflow.** `(x - index_starts.at(d)).as_index()` is the arithmetic to worry
about, and it is guarded by `prepare()` having already narrowed each index to
`[start, start + size - 1]`, so the subtraction cannot be negative and the
result cannot exceed the array's size. Not separately probed.

### Interval efficiency

**Clean on all four questions, by measurement rather than by inspection**, and
unlike [`comparison`](comparison.md) this family cannot be cleared by grep — it
is full of loops, and the question is only ever whether each one is over *values*
or over something bounded. It is also the family where this arc found the most:
three separate per-value sites, on three different axes, none of which the
previous probe could reach.

**1. The propagation side.** Every loop is over array cells, over an index
domain (bounded by the array's size, because `prepare()` narrows each index to
the array's extent), or over domain **runs**. `element.cc` carries no
`LargeDomainIterationCounter` at all any more — it had one until #925, on the
union propagator's per-value fallback, and there is no such fallback now.

The site worth knowing as a *shape* rather than an incident is #878's.
`domain_size(entry) == hi - lo + 1` was the test for "contiguous, so one
`erase_range`", and **one hole is all it takes** to fail it; the fallback went
value by value, so a 10⁹-wide entry missing a single value was walked a billion
times. Fixed in #897 by walking the entry's runs, which is what its domain is
either way.

*Measured elsewhere — #897's own table, root propagation only, three entries
`0..w` with one value knocked out, pinned to one core.* 10⁶: 10 ms → 0 ms.
10⁷: 48 ms → 0 ms. 10⁸: 422 ms → 0 ms. 10⁹: 4,238 ms → **0 ms**. Memory was flat
at ~5.5 MB throughout, both ways — which is the part that matters for how the
bug was found: **this one does not die, it just stops**, so the audit row would
have read `Clean` on any machine and the lane's `bad_alloc` fallback would never
have fired. It took the guard build.

**2. The reason side.** Reasons here are a `generic_reason` over the index
variables concatenated with one literal per entry considered, so their length is
in **cells**, not values — and since #935 `materialise_generic()` finds a holey
domain's runs by reading them off the `IntervalSet` rather than testing every
value between the bounds, which is the improvement this family inherits without
having asked for it. Every reason in the family is guarded on
`inference.want_reasons()`, which it has been since before the first audit; the
index-support reason is a per-value allocation with no small-buffer
optimisation, so the guard matters.

**3. The proof side, which is where both of this pass's fixes are.**

- **#900 → #929, the index-support rule.** It certified "no value of this entry
  is in `result`'s domain" one value of the entry at a time: `8w + 16` proof
  lines for a single inference, of which `w` were the rule's own and seven times
  that was the encoding layer defining an `eq` atom per value. 653 KB at 10³ and
  **1.01 GB at 10⁶** — for one inference. The fact is a disjointness statement,
  which is what the no-overlap walk certifies, so the rule now takes `equals`'s
  witness from `innards/no_overlap_walk.hh` with the index tuple's guard where
  `equals` has a reification condition. **Flat at 45 lines**, against a 13-row
  OPB that does not move; the survey row goes 13,897 → 139,897 steps for a 10x
  width and the proof does not grow at all.
- **#924 → #925, the result-union rule.** It answered "can I say a range about
  these?" with a **type test**, so a view anywhere sent the whole rule down a
  per-value walk of the remainder. The form is now chosen by the **width of the
  run**: two or more values take the range form, a single value stays a
  disequality — because `not_in_range` canonicalises to the same `!=` literal
  and the range form would cost two bound lemmas per feasible index tuple to say
  the same thing. That is a width gate in the sense [large-domains.md](../large-domains.md)
  means it, and it is the right kind: it picks by what the form costs, not by
  what the variable is.

Those two are one finding in two places. **A form chosen by the kind of a
variable is a bug; a form chosen by width is a design.** `Abs` had the same
thing in the arithmetic family (#931), which is what turned it from an incident
into the standing rule.

**4. Where the family stands in the audit lane.** Five rows in
`gcs/large_domain_audit_test.cc`, all pinned `Clean` — more than any other
family in the arc, and the reasoning behind the set is the most careful in the
lane:

| Row | Shape | Why it is a distinct row |
|---|---|---|
| `Element` | wide result, three **narrow** entries, `GAC` | a wide entry erases the whole unsupported set in one `erase_range` and leaves nothing behind; only a narrow entry leaves a wide remainder to remove |
| `Element/BC` | the same instance, `BC` | so the pair is comparable — it is the weaker arm that makes it clean, not an easier instance |
| `Element/holey` | three **full-width** entries with one value knocked out of each | neither row above reaches the sweep's other half: a contiguous entry goes in as one `erase_range` however wide, so nothing exercised an entry that is wide *and* holey (#878) |
| `Element/view-result` | the `Element` row with the **result wrapped** and nothing else changed | the lane exercised widths and holes and never *kinds*; before #925 this walked 10⁹ values while the bare row beside it removed two ranges (#924) |
| `Element/index-support` | a **narrow** result against a **wide** entry | the only probe in the lane where an index value ever loses support, and so the only one that reaches rule 1's justification at all (#900) |

**Three of those five rows exist because a previous probe could not reach the
site**, which is this family's contribution to the method and is worth stating
as such. `Element/view-result` was the lane's first row to put a view on
anything, and the rule it caught — answering an interval question with a type
test — was invisible to two audits that varied only width and holes.
`Element/index-support` is the `HazardNotReached` case that was never labelled
one: rule 1's justification was an unreached site for as long as the table had
`Element` rows, and **a gap nobody has thought of looks exactly like no gap**.
`Element/holey` is the third.

*What the five do not vary.* None of them selects `Auto`, so the pair is
exercised by `element_auto_test` and `element_test`'s three `*auto` lanes but
not at width. That is a smaller gap than it looks — a pair runs exactly one of
two members, and both members have rows — but it is a gap, and it is in [Next
steps](#next-steps).

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
  installed and behaves identically under all three consistency settings,
  because the choice only ever picks between the result propagators.
  `element_test` asserts `CheckConsistency::GAC` on every index in every mode,
  including the `BC` and `Auto` ones. It is also the propagator that makes the
  `Auto` pair's second promise non-trivial — holes in `result` *do* affect it —
  so read [Interior values and optional
  pruning](#interior-values-and-optional-pruning) alongside this entry.
- **Algorithm** — for each value of indexₖ, a recursive search over the other
  index domains for one supporting cell, stopping at the first. Support is
  tested with `in_domain` (constant array) or `domains_intersect` (variable
  array) — never by materialising `result`'s domain, which was the point of
  #515. O(|dom(indexₖ)| · ∏ |dom(index_j)|) membership tests, in *cells*, with
  no per-value work on any domain.
- **Why it is true** — if no cell reachable with `indexₖ = v` can take a value
  `result` can also take, then `indexₖ = v` has no support.
- **Proof technique** — `RUP+hints`. The published form is **JP 3.9 (empty
  intersection for Element)**: for each way the other indices are assigned, one
  line per value `w` of the selected entry — `R ⇒ (indexₖ ≠ v) ∨ (entry ≠ w)`,
  RUP by **Theorem 2.8** because the guarded equality forces `result = w`
  against a `result` that cannot take it — then a collapse per dimension and
  **Theorem 3.2**. That is what gcs emitted until #929 and it is one line per
  value of the entry.

  **Since #929 the certificate is the disjointness walk instead**, and this rule
  is the second caller of it. The fact the rule needs is "no value of the entry
  is in `result`'s domain", which is exactly what
  `walk_no_overlap()` states over *runs*: one move per maximal run, carrying
  `entry ≥ p` up the number line. What the walk needs from a caller is only
  something that makes its two operands equal, and here that is the index
  tuple's guard where [`equals`](equals.md) has a reification condition. Two
  bridge lemma shapes carry a bound across the tuple's half-reified equality;
  negating one leaves the bare difference row and a pair of opposing bounds, RUP
  by **Theorem 2.9** — the same argument as
  `justify_not_in_range_across_equality`'s, with a conjunction's worth of guard
  literals in place of one reification literal.

  Two differences from `equals`'s use of the same walk are worth recording,
  because they are what the shared header now has to accommodate: this rule's
  lemmas are **model consequences**, so they go in plainly, and its conclusion
  is a single `indexₖ ≠ v`. **No published procedure covers the interval
  form**; it is argued from scratch under *Why it is true* and in
  `no_overlap_walk.hh`.
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
- **Proof size** — per index tuple, a few lines per **run** of the two domains
  rather than per value, plus one per collapsed dimension. Independent of either
  domain's width, which is the property the rewrite exists for.

  *Measured by the proof-scaling survey, which is one command away.* **Flat at
  45 lines** at every width tried, against a 13-row OPB that does not move: the
  survey's step count goes 13,897 → 139,897 for a 10x width and the proof does
  not grow at all.

  *What it was, measured elsewhere at `76bfd836` plus #897 and not to be put in
  a table beside the figure above.* `∏_{j≠k} |dom(index_j)| · (|dom(entry)| + 1)`
  lines, so on a 1-D instance where the rule fires once at the root, `8w + 16`
  proof lines for an entry of width `w` — 653 KB at 10³ and **1.01 GB at 10⁶**,
  for one inference. Only `w` of those were the rule's; the other seven-eighths
  were the encoding layer defining an `eq` atom per value, which is what naming
  `entry != v` costs. That was **#900**, and the fix was the one the first audit
  guessed at: the interval-wise witness `equals` got in #881.
- **Gaps** — `None.`, and since #929 without the size qualifier that used to
  follow it.
- **Tightness** — `Not shown.` No mutation lane exists for this family. #929
  added six rows whose domains are disjoint in ways a `lo`/`hi` pair cannot
  state — holes on either side, below as well as above, touching, and down to a
  single value — because nothing in the existing table reached them; those pin
  the *answer* rather than the derivation, which is what a mutation lane would
  do.

### Rule: result-range

- **Infers** — `result ≥ lo` and/or `result ≤ hi`, where `[lo, hi]` is the range
  spanned by the entries whose bounds meet `result`'s current bounds.
- **Fires when** — `result`'s or an entry's bounds move, or an index changes.
  Under `consistency::BC`, or as the **fallback** member of `Auto`'s pair once
  the analysis has decided nothing could observe the interior values rules 3 and
  4 would remove.
- **Strength** — `BC`. Interior values with no support survive, deliberately.
  Under `Auto` that is the whole point: they survive because nothing in the
  model can tell they are there.
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
  independent of any domain width, and in **cells** rather than values.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

Its refusal to claim idempotence is load-bearing twice over, which the
[Propagator inventory](#propagator-inventory) spells out: a bound it infers can
snap past a hole, so it must re-run, and it is that re-run that makes its
fixpoint bounds equal to the union's — which is `Auto`'s first promise. The same
line of code is a correctness condition and the argument for a design.

### Rule: result-union-range

- **Infers** — `result ∉ [lo, hi]` for each contiguous run of `result`'s domain
  that no live entry can supply.
- **Fires when** — `result`, an index or an entry changes. Under
  `consistency::GAC`, or as the **pruning** member of `Auto`'s pair while that
  is live; and, within the propagator, for each unsupported run **two values
  wide or more** (#924). It used to be gated on `result` and every entry
  considered being a bare `SimpleIntegerVariableID`, which is the type test
  #925 replaced with the width one.
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
- **Gaps** — `None.`, and since #925 without a qualifier. The conclusion used to
  degrade wholesale to rule 4 when a view was involved anywhere, which was #924
  — one instance of the general problem #882 named, fixed for this rule by
  testing width instead of kind and for the tree at large by #904 giving views
  their own range literals.
- **Tightness** — `Not shown.`

### Rule: result-union-value

- **Infers** — `result ≠ v`, for an unsupported run exactly one value wide.
- **Fires when** — in the same propagator as rule 3, for each unsupported run of
  **width 1**. That is the whole condition now: since #925 nothing about the
  *kind* of a variable selects this rule, and it is reached once per interval of
  the remainder rather than once per value.
- **Strength** — `GAC` on `result`, as rule 3 — the two are the two forms one
  propagator's conclusion takes, not two strengths.
- **Algorithm** — the same subtraction; this is the single-value arm of the walk
  over the remainder's intervals. No iteration counter, because the branch above
  takes every run of two or more values, so this is reached once per interval and
  never once per value.
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
  per removed run, which at width 1 is per removed value — and that is the
  cheaper of the two forms here, not the expensive one. Rule 3's range form
  would cost **two extra bound lemmas per feasible index tuple** to say the same
  thing, because `not_in_range` over a single value canonicalises to this same
  `≠` literal. That is why the gate is a width test rather than "always prefer
  the interval form": an interval rewrite that is asymptotically better can
  still be worse everywhere anyone actually is, which is the same lesson #939
  recorded about at-least-one covers.
- **Gaps** — `None.`
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

Two binaries now. `gcs/constraints/element/element_test.cc` runs as **eight
ctest lanes** selected by an argv mode — `const`, `constgac`, `constauto`,
`const2d`, `const2dauto`, `var`, `varauto`, `var2d` — plus a view sweep on
seven of the eight (`varauto` has none); the three `*auto` lanes arrived with
#967.
`gcs/constraints/element/element_auto_test.cc` is the second, and it exists
because the property that matters about `Auto` cannot be checked by an
enumeration test at all.

- **Enumeration with per-node consistency assertion**, and the mode decides
  which: `solve_for_tests_checking_gac` for the variable-array modes, and
  `solve_for_tests_checking_consistency` for the constant-array ones with
  `CheckConsistency::BC` or `::GAC` on `result` according to the arm and
  **always `::GAC` on the index**. That last part is the evidence for rule 1's
  unconditional GAC claim.
- **All three settings are run on the same instances.** `constgac` differs from
  `const` only by `with_consistency(GAC)`, so the pair is comparable — and it
  exists because `ElementConstantArray` is BC by default, which left the GAC
  propagator's constant-array instantiation reachable but never actually run.
  The `*auto` lanes add the third: an element on its own drops to `BC` over
  constants and stays `GAC` over variables, which the consistency assertion
  checks directly.
- **`element_auto_test` checks a property no enumeration test can reach.** Both
  arms of the pair are sound, so a wrong switch-off loses no solution and fails
  no proof; only a comparison of **trees** can catch it. Over two thousand
  random constant-array element models, under a brancher that reads only bounds,
  `Auto` explores exactly the tree `GAC` does. Three things about how it is
  built are worth copying for the next client of the mechanism: it checks that
  **its own fixture is discriminating** — that about half the models switch
  something off, and that some of them are models where `BC` really does explore
  a different tree — it checks that a **mutation making every pruning unneeded
  fails it**, and where `Auto` chose one arm for every element it additionally
  has to match that arm forced, propagation counts and all. It also compares the
  `.opb` files of `GAC`, `BC` and `Auto` byte for byte, which is how the
  "propagation strength only" claim in [Options](#options) is enforced rather
  than asserted.
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
- **Five large-domain audit rows**, described under [Interval
  efficiency](#interval-efficiency) — the most careful set in that lane, and
  three of the five exist because an earlier probe could not reach the site they
  cover.
- **No runtime caps** on the element lanes.

What the tests do **not** cover:

- **No mutation lane.** Every rule answers `Not shown.` for tightness except
  rule 5, which is covered only as `equals` reaches it and not as `Element`
  does. Per the policy in [`TEMPLATE.md`](TEMPLATE.md) that is an ordinary
  state, not outstanding work — but this family is a better candidate than most
  if one is ever wanted, because its derivations are the only ones in the arc
  that emit a nested walk rather than a single line.
- **No large-domain case in the test file itself.** The five audit rows carry
  it, in a build nothing runs by default.
- **No `Auto` row in the audit lane**, so the pair is exercised at test widths
  and not at width. See [Next steps](#next-steps).
- **No proving case uses a wide array entry.** This used to be the gap that hid
  #900 — the index-support rule emitted one proof line per value of the selected
  entry's domain, and every entry in the test file is narrow, so the cost was
  exercised only where it was invisible. #929 added an `Element/index-support`
  audit row, which is the only probe in the lane whose result is narrow and
  whose entry is wide, and so the only one where an index value ever loses
  support. The test file itself is still all narrow entries.
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

***Both have been acted on since, and the split between them is instructive.***
#902 is **closed**: declaring hole sensitivity, offering a pruning as optional,
and the least-fixpoint analysis that decides per model which prunings anything
could observe all landed in #965 and #967, and this family is the mechanism's
first client. So the measurement above is no longer an argument for a default —
`consistency::Auto` reaches `BC`'s answer on exactly these two models without
anybody choosing it, and does so by proving nothing can observe the difference
rather than by assuming it. #901 stays open on the narrower question it also
raised, which the general mechanism does not answer: a *model* still cannot ask
for a level. Three examples can, via `--element bc|gac|auto`; neither frontend
can.

The general mechanism also left a finding of its own behind, in the opposite
direction. Auditing every install site for hole sensitivity turned up four
propagators whose triggers *understate* what they read — `Count`, `SubCircuit`
under `Prevent`, `BinPacking`'s upfront sweep, and the learned-nogood store —
and the first three are also **missing wakes**, which is a propagation question
rather than a pruning-analysis one. That is **#966**, and it is not about this
family.

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

**`None.` in the other direction too, which was not true at the first audit.**
Both of the gaps recorded there were costs paid only when proofs *are* on, and
both were about the size of a derivation rather than its correctness; both are
now closed, and the two closures are the same idea:

- **The index-support rule emitted one line per value of the selected entry's
  domain** (rule 1), which was **#900**. JP 3.9 as published, so not a
  divergence, but a proving run over a wide array entry wrote a proof
  proportional to that entry's domain size — **1.01 GB and 8,000,016 lines for a
  single inference** at width 10⁶, against 0 ms with proofs off. Only one line
  per value was the rule's own; the other seven were the variable-encoding layer
  defining an `eq` atom for every value, because the rule's lines named
  `array_var != v`. #929 replaced the certificate with the disjointness walk,
  which states the same fact over runs and names no `eq` atom: **flat at 45
  lines**. The first audit's guess at the fix — that `equals`'s #881 witness
  would carry over — was right.
- **A view cost the result-union rule its interval conclusion** (#924, one
  instance of #882), taking the proof from three lines per index tuple per *run*
  to one per tuple per *value*. #925 made the choice of form a width test rather
  than a kind test, and #904 gave views their own range literals, so there is no
  degraded path left to take.

What is left in this direction is not a gap but a property of the constraint:
the proof is large and grows with the array, because the encoding is two rows
per cell and a single inference's derivation is a product over the index
domains. See [Known limitations](#known-limitations).

### Known limitations

**Bounds consistency is the default for constant arrays, and nothing *in a
model file* can select otherwise** (#901, the open half). `with_consistency` is
a C++ call; neither frontend exposes it, so every MiniZinc and XCSP3 model gets
the default its class carries. Three examples can now ask — `qap`, `tsp` and
`p_dispersion` take `--element bc|gac|auto` — which is enough to benchmark both
directions and not enough to model with.

Both defaults are the right ones on the benchmarks we have, measured under [CPU
performance](#cpu-performance), and the reason generalises: `GAC` on a result is
worth having only if something can observe an interior value of it, which for a
constant array means something *outside* the constraint. That is the argument,
not "it happens to be faster here" — and it is now an argument the solver can
make for itself, per model, as `consistency::Auto`. What a frontend flag would
add on top is the ability to say "GAC anyway", which is a thing a modeller might
want for reasons the analysis cannot see.

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

Ranked. **Two of the three the first pass listed are done** — #900 as #929 and
#902 as #965/#967 — so this list is shorter and its top item is the leftover
half of #901 rather than a proof-size problem.

1. **#901 — let a *model* choose the consistency level.** `with_consistency` is
   a C++ call and neither frontend exposes it, so every MiniZinc and XCSP3 model
   gets the default its class carries. `qap`, `tsp` and `p_dispersion` take
   `--element bc|gac|auto`, which is enough to benchmark with and not enough to
   model with.

   The question this leaves is **where the knob goes**, and it is a frontend
   design question rather than a solver one: a binary flag is the cheap version,
   an annotation the version a model could use per constraint.
   `GlobalCardinality` is the precedent — `scp_reader.cc` reads a level off the
   `.scp` and applies it via `with_consistency`. The level provably does not
   change the OPB encoding, so nothing on the proof side constrains the choice.

   What has changed since this was filed is that the *default* question has
   mostly answered itself: `consistency::Auto` reaches `BC`'s answer on the two
   models that prompted the issue, by proving nothing can observe the
   difference. Whether `Auto` should become the default for the constant-array
   classes is a separate call and is not this issue — it is the one #966's
   neighbour leaves open, and it is Ciaran's.
2. **An `Auto` row in the audit lane.** None of the family's five rows selects
   `Auto`, so the pair is exercised at test widths by `element_auto_test` and
   `element_test`'s three `*auto` lanes and at width by nothing. Not filed, and
   the smallest item here: a pair runs exactly one of two members and both
   members already have rows, so what an `Auto` row would pin is the pair
   machinery rather than either propagator. Worth having for the same reason
   `Element/view-result` was — the axes a row does not vary are where this arc's
   findings have all been.
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
