# Inverse: two arrays that are each other's inverse permutation

> **Maturity** production ·
> **Audited** 2026-09-23 at `00797a97` ·
> **Open issues** filed by this audit: #1047 (an aliased array entry from
> MiniZinc, and XCSP3's unequal-length `channel`, error or abort instead of
> solving), #1048 (8–10× slower than Gecode at equal node counts), #1049 (every
> value's at-most-one written at the root). Found here but not this family's:
> #1046 (`GlobalCardinality` proofs break on a constant in the array). Already
> open and touching this family: #522 (the generalised arc consistent
> `AllDifferent` rebuilds its components every wake), #944 (Hall proofs cost
> one pairwise at-most-one per value), #364 (incremental propagators). Tracked
> under #871.

`Inverse(x, y)` says that `x` and `y` are inverse permutations of each other's
index sets: `x[i] = j` exactly when `y[j] = i`. It is one class with one
propagator. That propagator channels between the two arrays and then runs
[`all_different`](all_different.md)'s generalised arc consistent algorithm on
`x`, so most of this family's inference and proof machinery belongs to that
family, and this document says what is different when `Inverse` drives it.

Three things to know before touching it.

- **It is generalised arc consistent, but only when every position is a
  different variable.** Its fixpoint is channel consistency plus `GAC` on
  `AllDifferent(x)`, and that is `GAC` on the whole constraint when no
  underlying variable appears twice, within an array or across the two.
  `Inverse(x, x)`, which XCSP3's single-list `channel` posts for an involution,
  is weaker: it needs search to refute #413's triangle. So is an array holding
  two views of one variable.
- **It is the cost on `black-hole`, and there it is 8–10 times slower than
  Gecode, over the same number of nodes to the same first solution** (#1048).
  Each pass rescans every `(i, value)` pair through the per-value domain
  generators, with a full `AllDifferent` run, and a call that changes anything
  makes at least two passes (2.4 per call there). Walking intervals instead
  buys 18%; the rest is the design.
- **Its proof starts with a cubic root cost.** With proofs on it writes an
  at-most-one for every value before search, `n·C(n, 2) + 2n` lines. The
  `AllDifferent` justification would otherwise build them lazily, and only for
  the values it needs (#1049). That dominates a proof whose search is short (85%
  of it on a trivial search at `n = 64`), and hardly matters on a long one (1.8%
  on `black-hole`).

## What it is

### Semantics

`Inverse(x, y, x_start = 0, y_start = 0)`, with `|x| = |y| = n`. For every `i`
and `j` in `0..n−1`:

```
x[i] = j + y_start  ⇔  y[j] = i + x_start
```

So `x`'s values are `y`'s indices and the other way round, which is why a
starting index is needed for each array: `x`'s values are numbered from
`y_start`, and `y`'s from `x_start`. `x` is a permutation of `y`'s index set, and
`y` is its inverse. The header's comment says the arrays are zero-indexed by
default, which is right.

Degenerate shapes:

- **Two empty arrays**: satisfied. A data row in `inverse_test`.
- **One variable each**: `x[0] = y_start` and `y[0] = x_start`, by the bounds
  alone. Two data rows.
- **Different lengths**: `prepare()` throws `InvalidProblemDefinitionException`.
  `exception_test` covers it. MiniZinc's glue posts `false` first, which matches
  the standard library (#997); XCSP3's two-list `channel` defines this shape
  differently, and aborts here (#1047).
- **The same variable twice in one array**: the **constructor** throws. The
  model is unsatisfiable (two positions cannot share a value), and fc2eb822 made
  the throw deliberate, but MiniZinc's aliasing reaches it from ordinary models
  (#1047). **The same constant twice is accepted**: it is two positions pinned to
  one value, and the #171 data rows show it failing at the root.
- **The same variable in both arrays** is legal. `Inverse(x, x)` constrains `x`
  to be an involution, and XCSP3's single-list `channel` posts exactly that.
- **All constants**: decided at the root (#254's three rows).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Inverse` | ✓ `inverse`, via `glasgow_inverse` with both arrays' first indices[^mzninv]; `decompose` for `inverse_reif`, `inverse_in_range`, `inverse_set`, `inverse_opt`[^mznstd] | ✓ `channel` over two lists[^xunequal]; ✓ `channel` over one list, as `Inverse(x, x)`; `unsupported` for the one-to-many form (list and value) | ✓ `Inverse`, through `gcspy`'s `post_inverse`, 0-based | ✓ `inverse` | `gcspy` has no start arguments |

[^mzninv]: `fzn_inverse` posts `false` when the lengths differ, `true` when both
    arrays are empty, and otherwise `glasgow_inverse(f, invf, min(index_set(f)),
    min(index_set(invf)))`. Until #997 the glue assumed both started at 1, and a
    non-1-based model got a wrong `UNSATISFIABLE` that verified through the whole
    `cake_pb_cp` chain; see `all_different.md`. An array entry that MiniZinc
    aliases to another, for example through `f[1] = f[2]`, reaches the
    constructor as a repeated handle and prints `=====ERROR=====`, where Gecode
    prints `=====UNSATISFIABLE=====` (#1047).

[^mznstd]: The standard library's decompositions: `inverse_reif` as a reified
    conjunction of `element` equalities, `inverse_in_range` as conditional ones
    plus redundant `global_cardinality` constraints, `inverse_opt` over optional
    values, and `inverse_set` over set variables, which MiniZinc turns into
    Booleans for us. None reaches this class. One small model of each gave
    the same solution count as Gecode (729, 34, 34 and 64).

[^xunequal]: XCSP3 defines `channel` over lists of different lengths as an
    injection, `list1[i] = j → list2[j] = i`. The binding posts `Inverse`
    regardless, whose `prepare()` throws, and nothing catches it: the solver
    aborts with exit status 134. ACE finds 12 solutions to the instance in
    #1047.

CPMpy's upstream GCS interface, checked 2026-09-23, lists `inverse` among its
supported globals and posts it as `post_inverse(fwd, rev)`. CPMpy's `Inverse`
is 0-based, which is what `gcspy` assumes.

### Options

`None.` There is no `with_consistency()`, and nothing else to set.

### Variable kinds and views

Any `IntegerVariableID`: plain, constant or view, in either array. The
propagator asks `in_domain` of a partner and never looks through a view. The
proof handles views through the framework's literals, as every family does.
`inverse_constraint_view_mixed` wraps positions in views of fresh variables.

What the tests do not post is a **view that aliases another position**. This
audit's probe did, against brute force, with every proof checked: two views of
one variable inside `x`, a negated view of one in `x`, a variable shared across
the arrays directly and through a negated view, and `Inverse(x, x)` over four
values (10 involutions). All five matched, and every proof verified. The
constructor's duplicate check compares handles, so two views of one variable
are not caught by it. They need not be for soundness: answers and proofs are
right. But propagation is no longer `GAC`, because the matching treats the two
positions as independent; see rule 5.

### Reification

`None.` MiniZinc's `inverse_reif` decomposes through the standard library. A
reified form would need its own propagator and encoding. Nothing asks for one.

### Relation to other families

**Into this family.** MiniZinc's `inverse`; XCSP3's `channel`, both list forms;
CPMpy's `Inverse`; the `.scp` reader. `examples/talent` posts it to link scenes
to slots.

**Posts as children.** Nothing. `prepare()` narrows each variable to the other
array's index range with `define_bound`, which writes an OPB row and installs an
initialiser but posts no constraint.

**Shares code.**

- **`propagate_gac_all_different`** is [`all_different`](all_different.md)'s,
  and it is most of this propagator's work and most of its proof. `Inverse`
  hands it `x`, the values `x` can take (`y`'s index set), no exclusions, its
  own at-most-one cache and a scratch object. A caller has to hand it the right
  values: `Inverse` once passed `x`'s own indices, which failed at the root on
  any two arrays starting at different indices (#997).
- **`recover_am1`** (`constraints/innards/`), for the root at-most-ones. Its
  other callers are `Among` and `GlobalCardinality`, and the three do not agree
  on its polarity; see rule 4.
- **`hints::Inverse`** is this family's own and used by nothing else.

**Presolvers.** None reads or rewrites `Inverse`.

**Reached only through a decomposition?** No.

**Not a candidate merge.** The family list gives `inverse/` alone. It shares a
propagator with `all_different` but has its own encoding, and the channel rules
are its own. `SymmetricAllDifferent`, which means the same as `Inverse(x, x)`
(an involution is already a permutation), lives in `all_different` and has its
own propagator. That propagator is no stronger on #413's triangle.

## The proof model

### OPB encoding

Definitional, and quadratic in `n`. For every `i`, `j` in `0..n−1`, two clauses:

```
x[i] ≠ j + y_start  ∨  y[j] = i + x_start
y[j] ≠ i + x_start  ∨  x[i] = j + y_start
```

That is `2n²` rows of two literals each, over the variables' equality literals,
so `n²` equality literals per array. Plus, from `define_bound`, one bound row
for each bound of a variable's declared domain that reaches outside the other
array's index range, **only** when it does:

```
x[i] ≥ y_start,  x[i] ≤ y_start + n − 1,  y[j] ≥ x_start,  y[j] ≤ x_start + n − 1
```

The bounds are part of the meaning: without them a value of `x[i]` outside
`y`'s index set would satisfy every row. The at-most-ones that make `x` a
permutation are **not** in the model. They follow, since two positions with one
value would force `y[j]` to two values, and that is what the proof derives
(rule 4). So the model says what the constraint means and nothing more.

**Size is independent of the declared width.** The rows name equality literals
for values inside the index range only, over `BinEnc` of the declared domain,
and the bound rows are single rows. A variable declared over `±10⁹` costs a
few more bits and two bound rows. That is measured under [Robustness and
limits](#robustness-and-limits).

### Labels

None. The rows are unlabelled, and nothing refers to them by label. The
propagator's inferences restate them (rule 1). The at-most-ones are cited by
line number through the cache.

### Cake conformity

| Case | `opbdiff` |
|---|---|
| `scp_chain_inverse_sat` | `none` |
| `scp_chain_inverse_offsets_sat` (arrays starting at 0 and 5) | `none` |

Both chain-verify: the solver's proof checks against the OPB `cake_pb_cp`
derives, and cake re-checks the elaborated core. Neither is a label match, for
three reasons:

- **Cake's rows are labelled and ours are not.** Cake writes the same
  implications as `x_eq − y_eq ≥ 0` under `c[id][i_jge]` and `c[id][i_jle]`.
  They are semantically the same rows.
- **Cake writes every variable's bound rows**, `c[id][X_k_lb]` and friends, even
  when the declared domain already fits. `define_bound` writes none in that
  case.
- **Cake's variable encoding is eager** (the whole `ge` ladder and every
  `eq ⇔ ge ∧ ¬ge` definition), where ours defines literals as rows use them.
  That is the divergence #358 recorded (now closed), shared with `element`.

This audit also checked by hand that declared domains wider than the index
range (`−3..7`, and `±10⁹`) and an out-of-range constant all verify against
cake's OPB as well as ours.

### Proof-time state

- **At the root, when proofs are on at `AssertionLevel::Off`**, an initialiser
  derives one at-most-one per value `v` of `y`'s index set: `C(n, 2)` pairwise
  clauses `x[a] ≠ v ∨ x[b] ≠ v` at `ProofLevel::Temporary`, then
  `recover_am1`'s fold at `ProofLevel::Top`. The line numbers go into a
  `map<Integer, ProofLine>` that the propagator captures and hands to the Hall
  justification. **They are never deleted** and **carry no label**, so an
  external tool cannot find them by name. It does not need to: at every
  assertion level the initialiser returns at once, the map stays empty, and a
  Hall assertion's reconstructor has to derive the at-most-ones itself (rule 4).
- **Lazily, during search**: the at-least-ones the Hall justification needs,
  from the names-and-IDs tracker, cached per variable (and per cover, for a
  definition range over the tracker's threshold, which no instance here
  reaches), and any at-most-one missing from the cache. Since the initialiser filled the cache,
  none is missing.
- **Levels.** The pairwise clauses are `Temporary`. The at-most-ones and the
  tracker's at-least-ones are `Top`. The Hall `pol` and every inference's RUP
  are at `Current`.
- **No proof flags and no proof-only variables.** Everything the justifications
  cite is in the OPB, or is an at-most-one derived from it.
- **`_x_value_am1s` is always non-null**, because the propagator captures it by
  value, and its comment says so. It is empty when proofs are off, because
  nothing fills it.
- **The Hall justification reads `state`**, not the reason, as in
  `all_different.md`. It is safe for the same reason there.

## The implementation

### Initialisation and global data

- **The constructor** rejects a repeated non-constant handle within either
  array. That is a pair loop, `O(n²)`, once.
- **`prepare()`** checks the lengths and calls `define_bound` twice per
  variable, once per bound. Each call does nothing if the declared bound already
  fits.
- **`define_proof_model()`** writes the `2n²` rows.
- **`install_propagators()`** builds `x`'s value list, the scratch object, and,
  when there is a proof model, the at-most-one initialiser.

The root cost that matters is that initialiser: `n·C(n, 2)` RUPs, `n` folds and
`n` deletions of the temporary pairwise lines, so `n·C(n, 2) + 2n` lines,
measured exactly for `n` from 4 to 64. At `n = 64` it is 129,152 of a
152,102-line proof whose search is trivial (#1049). With proofs off there is no
root cost at all beyond the constructor's pair loop.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| `define_bound`'s initialisers | initialiser | — | 6 | a declared bound outside the index range | n/a | one shot |
| at-most-one initialiser | initialiser | — | scaffolding for 4 and 5 | a proof at `AssertionLevel::Off`, and `n ≥ 2` | n/a | one shot |
| the `Inverse` propagator | `on_change`, every `x` and `y` | derived: every variable, truthfully | 1–5 | always | **claims it** (`EnableButIdempotent`), ignored by the engine when positions alias | never |

**Idempotence.** The propagator loops (channel `x`, channel `y`, then `GAC` on
`x`) until a whole pass changes nothing, so a call ends at its own fixpoint, and
it says so in its comment. That is claimed since 74fd6b46. The test harness sets
`GCS_CHECK_IDEMPOTENT_CLAIMS`, which re-runs every honoured claim and aborts if
the re-run infers anything; no lane has tripped it. **The engine ignores the
claim** whenever two positions resolve to one underlying variable
(`positions_alias` in `propagators.cc`). That covers every `Inverse(x, x)`, so
XCSP3's single-list `channel`, and `p1f` 2015, which posts
`inverse(ra, ra) :: domain`, are always requeued.

**It never disables itself**, even when every variable is fixed. It is then one
pass that finds nothing.

**Holes affect**: every variable, and the triggers tell the truth. The channel
asks whether one specific value is in a partner's domain, so a hole anywhere in
`y[j]` can remove a value from `x[i]`, and the `GAC` stage reads whole domains.
An `Inverse` is therefore a reason for a neighbour's interior pruning to stay
on, for every variable it touches.

### Mutable state and incrementality

**Nothing backtrackable.** The propagator keeps the `GacAllDifferentScratch`
across calls: the matching is kept and repaired between wakes, and the
components are rebuilt every run (#522). The at-most-one cache only grows.

**Recomputed per call: everything.** Each pass visits every value of every `x[i]`
and every `y[j]`, `Θ(Σ|D|)`, and asks one `in_domain` each. Then it runs the
whole `GAC` stage. Any pass that changes anything is followed by another, and a
`GAC` removal from `x` needs a further channel pass to reach `y`. On `black-hole`
2013/12 the propagator ran 33,693 times, made 80,550 passes, and ran the `GAC`
stage 77,445 times.

What maintaining it would buy is in [CPU performance](#cpu-performance): Gecode's
channel visits only variables whose domain has shrunk since it last looked, and
pushes their missing values across, instead of re-checking every value still
present (#1048, and the general question is #364).

### Interior values and optional pruning

**What this family offers:** `None.` There is one level, `GAC`, and no
`consistency::Auto`.

**What this family observes:** holes in every variable, as the inventory says.
This is the opposite of [`linear`](linear.md) and
[`comparison`](comparison.md): a variable in an `Inverse` keeps any neighbour's
optional interior pruning alive, and rightly, because removing a value from
`y[j]` removes a value from `x[i]`.

### Robustness and limits

- **Unbounded domains**: `define_bound` narrows every variable to the other
  array's index range at the root, so nothing after that sees a wide domain. A
  probe with `x[0] ∈ ±10⁹`, `x[1] ∈ 0..10⁹` and `y[1] ∈ −5..10⁹` solved and
  verified in 0.064 s with a 25 KB OPB.
- **Negative values and starts**: first-class. `inverse_test` reruns every case
  once more with shifted starts, cycling through `(1, 1)`, `(3, −2)` and
  `(−2, 4)`. `scp_chain_inverse_offsets_sat` uses 0 and 5.
- **Degenerate shapes**: see [Semantics](#semantics). A constant outside the
  index range fails at the root through its bound row, and the `UNSATISFIABLE`
  verifies against cake's OPB too.
- **Overflow**: the only arithmetic is on `Integer`s (`n + start − 1`, the value
  offsets), and `Integer` arithmetic throws on overflow rather than wrapping. So
  an absurd start fails loudly.
- **Aliasing**: see [Variable kinds and views](#variable-kinds-and-views), and
  the strength caveat under rule 5.

### Interval efficiency

`Fine at any width`, because the root narrows every domain to `n` values. But
the propagator is per value throughout, and that matters for the per-value ban
even where it does not matter for width.

1. **Propagation.** Two sites walk values: the channel loops, through
   `State::each_value_mutable`, over every `x[i]` and `y[j]`. Each is bounded
   by `n`, the array length, not by any declared width, because the bounds are
   pinned before the propagator runs. There is no interval structure to exploit
   in the check itself (each value has its own partner), but **the iteration
   can be by interval**: a local switch that walks `copy_of_values` interval by
   interval did the same work 18% faster on `black-hole` (#1048). The `GAC`
   stage's costs are in values and edges, bounded the same way; see
   `all_different.md`.
2. **Reasons.** One literal per channel inference. The `GAC` stage's reasons
   are `generic_reason` over the Hall variables, built only when a proof or
   reasons are wanted.
3. **Proofs.** One line per channel inference. The at-most-ones are per value,
   `C(n, 2)` pairwise lines each, bounded by `n` rather than width, and with no
   width gate because there is no wide case. That per-value, per-pair cost is
   #944's, in its cubic form here (#1049).
4. **The audit lane**: one row, `Inverse`, `NoWidePosition`, over two arrays of
   three variables in `0..2`. **It varies nothing**: no declared domain wider
   than the index range (legal, and trimmed at the root), no starts, no views,
   no holes. So it records the structural fact without probing the one path,
   `define_bound`, that a wide declared domain actually takes.

## Inference catalogue

Six rules. Rules 1 and 2 are the channel, and are this family's own. Rules 3–5
are `all_different`'s generalised arc consistent rules, run on `x` with
`Inverse`'s constraint id, and are recorded here for what differs when
`Inverse` drives them. Rule 6 is the root bound.

Four facts hold across them.

**The wire inventory.**

| Wire form | Hint type | Rules |
|---|---|---|
| `inverse:((constraint_id N))` | `hints::Inverse` | 1, 2 |
| `all_different:((constraint_id N))` | `hints::AllDifferent` | 3, under `Inverse`'s id |
| `all_different:((constraint_id N) (subhint hall))` | `hints::AllDifferentHall` | 4, 5, under `Inverse`'s id |
| `initial_bound` | `hints::InitialBound` | 6, with **no** constraint id |

**Nearly a third of this family's assertions are named for another family.** On
`black-hole` 2013/12 at `AssertionLevel::Inferences`, the 769,930 assertions this
constraint is responsible for are 545,768 `inverse` and 224,162 `all_different`,
all carrying `Inverse`'s id. A justifier dispatching on the hint name alone will
treat 29% of them as `AllDifferent`'s. For rules 4 and 5 it needs the scope the
at-most-ones span, which is `x`, and it gets that from the id through the
`.scp`, as `all_different.md` says. Rule 6's assertion names no constraint at
all.

**What licenses them.** Rules 1 and 2 assert one of the model's own rows, so
unit propagation on that row alone refutes the negation, and no theorem is
needed. Rule 6 asserts an order literal against a bound row over the bit sum,
which also needs the literal's definition: **Theorem 2.7**. Rules 3–5 are `all_different`'s JP 3.1, **JP 3.16** and **JP 3.17**,
with that document's departures and one more of our own. The pairwise clause
`x[a] ≠ v ∨ x[b] ≠ v`, which JP 3.1 takes from a not-equals row and JP 3.16 and
3.17 sum into at-most-ones, has no row here. It is RUP through **two**
channelling rows, which force `y[v]` to two values, and then **Theorem 2.7**
(opposing bounds on one bit sum) on `y[v]`. The thesis's procedures assume
Encoding Procedure 3.9's pairwise clauses. Here each clause is derived instead,
which is sound, but it is a step the procedures do not have.

**Tightness.** No mutation lane exists in this family.

### Rule: channel-x

(Rule 1.)

- **Infers** — `x[i] ≠ v`, or a contradiction when that empties `x[i]`.
- **Fires when** — the `Inverse` propagator's first loop finds `v ∈ D(x[i])`
  with `i + x_start ∉ D(y[v − y_start])`.
- **Strength** — `partial`: support for `x[i] = v` in the one channelling pair
  that mentions it. Not arc consistency on each binary channelling constraint:
  `x[m]` fixed to `d` does not by itself remove `y[d] = j` for `j ≠ m`. Rule 3
  and rule 2 do that between them.
- **Algorithm** — for each `i`, each value of `x[i]`, one `in_domain`. `Θ(Σ|D(x)|)`
  per pass, in **values**, each bounded by `n`.
- **Why it is true** — if `x[i] = v` then `y[v − y_start] = i + x_start`, and that
  value is gone.
- **Proof technique** — `RUP`. The assertion **is** the model row
  `x[i] ≠ v ∨ y[v − y_start] = i + x_start`, so unit propagation on that row
  refutes its negation.
- **Reason** — `{y[v − y_start] ≠ i + x_start}`, one literal. Minimal. Built
  unconditionally, in a `ReasonLiterals` whose inline storage holds it without
  an allocation.
- **Assertion** — `x[i] ≠ v ∨ y[v − y_start] = i + x_start`, verbatim the OPB row.
- **Hint** — `hints::Inverse`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `offline`: the assertion is an input
  constraint.
- **Proof size** — one line of two literals. On `black-hole` 2013/12, 23,292
  firings.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: channel-y

(Rule 2.)

- **Infers** — `y[j] ≠ w`, or a contradiction.
- **Fires when** — the second loop finds `w ∈ D(y[j])` with
  `j + y_start ∉ D(x[w − x_start])`.
- **Strength** — as rule 1, mirrored.
- **Algorithm** — as rule 1, over `y`.
- **Why it is true** — as rule 1, mirrored.
- **Proof technique** — `RUP` against the other row of the pair.
- **Reason** — `{x[w − x_start] ≠ j + y_start}`.
- **Assertion** — `y[j] ≠ w ∨ x[w − x_start] = j + y_start`, the OPB row.
- **Hint** — `hints::Inverse`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line. On `black-hole` 2013/12, 522,476 firings: most of
  this family's volume. The `GAC` stage removes from `x`, and every removal has
  to come back across to `y` through this rule.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: forced-value-deletion

(Rule 3; `all_different.md` rule 3.)

- **Infers** — `x[k] ≠ d`, where `d`'s matched position `m` is fixed to `d`.
- **Fires when** — the `GAC` stage, as in `all_different.md`.
- **Strength** — `GAC` on `AllDifferent(x)`.
- **Algorithm** — as `all_different.md`.
- **Why it is true** — `m` takes `d`, and two positions of `x` cannot share a
  value.
- **Proof technique** — `RUP`. **Different from `AllDifferent`'s**, which is
  JP 3.1 against one pairwise not-equals row. Here there is no such row.
  `x[k] = d` gives `y[d − y_start] = k + x_start` by one channelling row, and
  `x[m] = d` gives `y[d − y_start] = m + x_start` by another. Two values of one
  variable then conflict by **Theorem 2.7**. Still one RUP, two propagation
  steps deeper.
- **Reason** — `{x[m] = d}`, one literal, under the sinks-first ordering
  argument in `all_different.md`.
- **Assertion** — `x[k] ≠ d ∨ x[m] ≠ d`.
- **Hint** — `hints::AllDifferent`, with `Inverse`'s id.
- **Offline reconstructibility** — `offline`: an unhinted RUP of the assertion
  succeeds, whichever rows it goes through.
- **Proof size** — one line. On `black-hole` 2013/12, 210,932 firings.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: hall-set-deletion

(Rule 4; `all_different.md` rule 2.)

- **Infers** — `x[k] ≠ d` for every edge in no maximum matching, batched by
  component.
- **Fires when** — the `GAC` stage.
- **Strength** — `GAC` on `AllDifferent(x)`.
- **Algorithm** — Régin's, as `all_different.md`.
- **Why it is true** — a Hall set of positions uses up its values.
- **Proof technique** — `pol` then `RUP`, by **JP 3.17**, with
  `all_different.md`'s departures. The at-most-ones it sums come from
  `Inverse`'s root cache at `AssertionLevel::Off`, built by `recover_am1` from
  pairwise clauses, each RUP through two channelling rows (as rule 3).
- **Reason** — as `all_different.md`: each Hall variable's domain.
- **Assertion** — `x[k] ≠ d ∨ ¬reason`.
- **Hint** — `hints::AllDifferentHall`, with `Inverse`'s id. Its
  `value_am1_constraint_numbers` points at `Inverse`'s cache, and its
  `all_vars` at `x`.
- **Offline reconstructibility** — `hinted`, as in `all_different.md`. The
  at-most-ones span `x`, which the tool finds from the constraint id through
  the `.scp`. Each pairwise clause is an unhinted RUP whichever rows it goes
  through, so nothing else about `Inverse` needs to be known.
- **Proof size** — one `pol` per component and a RUP per deletion; the
  at-most-ones are paid at the root, `C(n, 2) + 2` lines per value (the pairwise
  RUPs, the fold and a deletion), for every value (#1049).
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

**The polarity of the root at-most-ones.** `Inverse` passes `recover_am1` the
atoms `x[k] ≠ v` and pairwise lines `x[a] ≠ v + x[b] ≠ v ≥ 1`, and gets back
`Σ x[k] ≠ v ≥ n − 1`, which is the at-most-one. `Among` does the same.
`recover_am1`'s header documents the opposite convention (atoms `aₖ`, pairwise
lines `¬aᵢ + ¬aⱼ ≥ 1`), and `GlobalCardinality` uses that one. The helper's
#171 shortcut, which emits `0 ≥ 1` when two atoms are false, is only right for
the convention `Inverse` uses. `GlobalCardinality`'s bounds arm, over a
constant, can reach it, and then emits a line VeriPB rejects (#1046, found by
this audit).

### Rule: hall-violator

(Rule 5; `all_different.md` rule 1.)

- **Infers** — a contradiction.
- **Fires when** — the `GAC` stage's matching leaves a position of `x`
  uncovered.
- **Strength** — `GAC` on `AllDifferent(x)`, when `x`'s positions are
  different variables. **Together with rules 1 and 2 at their common fixpoint,
  `GAC` on `Inverse`**, when no underlying variable appears twice anywhere: at
  the fixpoint `v ∈ D(x[i])` exactly when `i ∈ D(y[v])`, and `x`'s `n` positions
  have `n` values. So a supporting matching for `x[i] = v` is a permutation, and
  its inverse is a support in `y`. The tests check this at every node
  (`solve_for_tests_checking_gac`). **With aliasing it is not**, because the
  matching treats aliased positions as independent. `Inverse(x, x)` over #413's
  triangle (`{1, 2}`, `{0, 2}`, `{0, 1}`) has no solution, and needs three
  recursions and two failures to prove it. And `x = [a, a + 1, b]` with
  `a ∈ 0..1`, `b ∈ 0..2`, over `y` in `0..2`, keeps `b = 1` at the root, though
  its only solutions are `(a, b) = (0, 2)` and `(1, 0)`.
- **Algorithm** — as `all_different.md`.
- **Why it is true** — Hall's theorem.
- **Proof technique** — `pol` then `RUP`, by **JP 3.16**, with the same
  at-most-ones as rule 4.
- **Reason** — the violator's domains.
- **Assertion** — `¬reason`.
- **Hint** — `hints::AllDifferentHall`, with `Inverse`'s id.
- **Offline reconstructibility** — `hinted`, as rule 4.
- **Proof size** — as rule 4. Rules 4 and 5 together carry 13,230 `hall`
  assertions on `black-hole` 2013/12, averaging 35.5 literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: index-range-bound

(Rule 6.)

- **Infers** — `x[i] ≥ y_start`, `x[i] ≤ y_start + n − 1`, and the same for `y`
  with `x_start`, at the root.
- **Fires when** — `define_bound`'s initialiser, for each bound the declared
  domain exceeds.
- **Strength** — `bounds(Z)`, on the index range.
- **Algorithm** — `O(1)` each.
- **Why it is true** — `x[i]` indexes `y`.
- **Proof technique** — `RUP` against the bound row `define_bound` added to the
  OPB.
- **Reason** — none: it holds at the root.
- **Assertion** — the bound.
- **Hint** — the solver-wide `hints::InitialBound`, which carries no constraint id.
- **Offline reconstructibility** — `offline`: the assertion is an input row.
- **Proof size** — one line per trimmed bound.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

| Lane | What it checks |
|---|---|
| `inverse_constraint` | `inverse_test`: 21 instances (13 fixed, 8 random of 2–4 variables), each at starts `(0, 0)` and at one shifted pair, with and without proofs; `solve_for_tests_checking_gac`, so `GAC` at every node; and the two constructor throws |
| `inverse_constraint_view_mixed` | the same, positions wrapped in views of fresh variables |
| `exception_test` | mismatched lengths throw |
| `scp_chain_inverse_sat`, `scp_chain_inverse_offsets_sat` | see [Cake conformity](#cake-conformity) |
| `xcsp_channel_self`, `xcsp_channel_two` | the two XCSP3 list forms, three variables each |
| `minizinc-inverses`, `-offset`, `-shapes`, `-negative`, `-unequal` | non-1-based and enum-indexed arrays, an array that is its own inverse, the same three variables in two orders, negative index sets and empty arrays, unequal lengths (#997, #1011). `inverses` and `-offset` compare against MiniZinc's default solver, `-shapes` against it and the standard library's decomposition, and `-negative` and `-unequal` against the decomposition alone |
| `talent` | the example, with its proof verified |
| `large_domain_audit` | one `NoWidePosition` row, guard build only |

All 12 of the family's ctest lanes pass at `00797a97` (caps off, MiniZinc 2.9.7,
`cake_pb_cp` and `opbdiff` on the path). VeriPB runs in both data-driven lanes;
at `--seed=1` the 42 proofs of `inverse_constraint` all verify. Both are seeded
(`establish_and_announce_seed`) and byte-reproducible with `--seed=N`.

**Runtime caps.** No lane sets or clears one. **The default caps never fire
here**, the first family in the arc where that is true: three unseeded runs of
each data-driven lane, with the default 300-solution and 1,500-recursion caps
passed in the environment, printed no truncation from a local-only print in
`solve_for_tests_with_callbacks`. The same print fires 16 times at
`GCS_TEST_MAX_SOLUTIONS=2`. The instances are small, since the largest has five
positions. So the default capped run checks completeness here too.

**Rules the tests reach**, from local counters at `00797a97`: rules 1 and 2,
and the `GAC` stage, in both data-driven lanes; the `GAC` stage's rules were
counted together. Rule 6 is reached by the one fixed row that declares a
position wider than its index range (a single position over `0..5`); the random
rows draw every domain inside `0..n−1`.

**What the tests do not cover:**

- **An array entry aliased to another** by a MiniZinc equality. The shapes
  lane has an array that is its own inverse and arrays sharing variables in two
  orders, but not two entries of one array made equal, which is #1047.
- **XCSP3 `channel` over lists of different lengths** (#1047).
- **A position that is a view of another position.** Only this audit's probe;
  see [Variable kinds and views](#variable-kinds-and-views).
- **`Inverse(x, x)` in the data-driven test.** It is reached only through the
  XCSP3 and MiniZinc lanes, where its weaker propagation is not checked for, as
  it should not be.
- **Anything of realistic size.** Five positions at most, so the root
  at-most-ones are a handful of lines, and the per-call cost that dominates
  `black-hole` is invisible.
- **Assertion levels.** Nothing checks that at `Inferences` every assertion
  carries `Inverse`'s id, or that the Hall justification is never reached with
  an empty cache.

### Benchmarks and examples

- **In-repo**: `examples/talent`, which links scenes to slots with one
  `Inverse` among many other constraints; its lane verifies a proof. No
  benchmark isolates the family.
- **The corpus.** Of one instance of each of 298 MiniZinc Challenge models,
  twelve reach `Inverse` and flatten: `black-hole` (2011, 2013, 2025),
  `elitserien` (2014, 2016, 2018, 2023), `p1f` 2015, `p1f-pjs` (2020, 2021) and
  `tdtsp` (2015, 2017). The corpus JSON used by earlier audits predates #997 and
  no longer parses. These were flattened again with the current library.
- **For CPU**: `black-hole` 2013/12 (3 s), 2013/18, 2011/9 and 2011/20 (74–134
  s). `Inverse` is 87% of the solve on 2013/12 and 88% on the 2025 instance. On
  the four instances compared with Gecode, it searches the same number of nodes
  to the same first solution. `elitserien` spends 7–15% of its solve in
  `Inverse` and most of it outside propagation; `p1f` 13–15%; `tdtsp` nothing.
- **For proofs**: `black-hole` 2013/12, a 300 MB proof that VeriPB checks in 15
  minutes. The scaling probe below for the root cost.

### CPU performance

All at `00797a97`, Release, GCC 15.2.0, fataepyc-09 (EPYC 7643, boost off),
pinned with `numactl --cpunodebind=0 --membind=0 taskset -c N setarch -R`,
2026-09-23, one run each unless stated. Counters were compiled out for timing.

**Against Gecode 6.3.0**, through `minizinc --solver gecode` on the same model
and data. `black-hole` writes `inverse(x, y) :: domain`, so Gecode posts its
domain-consistent channel.

| instance | nodes (both) | GCS | Gecode | ratio | GCS propagations | Gecode propagations |
|---|---|---|---|---|---|---|
| 2013/12 | 14,031 | 3.035 s | 0.366 s | 8.3× | 400,311 | 651,867 |
| 2013/18 | 312,905 | 74.5 s | 7.20 s | 10.4× | 10,357,959 | 14,369,803 |
| 2011/9 | 346,973 | 90.2 s | 9.75 s | 9.2× | 10,369,837 | 16,207,493 |
| 2011/20 | 916,488 | 134.3 s | 12.9 s | 10.4× | 17,862,592 | 26,666,085 |

Equal node counts and the same first solution on all four. That is what equal
strength on this model would give, though it does not show the trees are the
same node for node. The two solvers count propagations differently, but ours is
not the larger. Three other instances fail at Gecode's root, and three do not
finish in 120 s.

**Where the time goes**, on 2013/12. `GCS_PROPAGATOR_STATS=time`: `Inverse`
2.654 s of 3.052 s, over 33,693 calls, 79 µs each. `perf`:
`propagate_gac_all_different` 15.6%, the per-value generator 16.6%,
`IntervalSet::each` 12.0%, `State::in_domain` 10.0%, the propagator's own
lambda 8.2%, `find_strongly_connected_components` 5.1%, and allocation about 6%.
So the per-value generators are 29% and the `GAC` stage about a fifth.

**An interval walk alone** (`copy_of_values`, then `each_interval` and a plain
loop), as a local switch: 2.463, 2.470 and 2.476 s against 3.011, 2.995 and
3.026 s, same nodes. That is 18%, and leaves the gap to Gecode at about 6.7×.

**Why Gecode is faster.** Its domain channel (`gecode/int/channel/dom.hpp`) has
the same shape as ours: channel, domain-consistent `distinct` on `x` only,
channel back. But it keeps each view's last-propagated size, visits only views
whose size changed, and walks the complement of their domain within the
bounds it last saw, pruning the partner. It makes one ordered pass rather than looping, keeps its `distinct`
graph between calls, and handles an assignment-only event by value propagation
alone. Ours re-checks every value still present, at least twice per effectful
call, and rebuilds the `AllDifferent` components each time (#522). #1048 has the
options.

**What this benchmark exercises**, on 2013/12: rules 1 and 2 (23,292 and
522,476 firings, from counters), and from the `Inferences` proof's assertions,
210,932 forced-value deletions and 13,230 Hall assertions. Rule 6 never fires: every domain is
declared `1..52`.

### Proof performance

**`black-hole` 2013/12**, 52 cards, 14,031 nodes.

| | solve | proof | VeriPB |
|---|---|---|---|
| proofs off | 3.04 s | — | — |
| `AssertionLevel::Off` | 6.47 s | 1,416,686 lines, 300 MB | 908.6 s, `VERIFIED SATISFIABLE` |
| `Off`, root at-most-ones skipped (local switch) | 6.48 s | 1,391,794 lines, 285 MB | 919.9 s, `VERIFIED SATISFIABLE` |
| `AssertionLevel::Inferences` | 6.51 s | 1,251,276 lines, 310 MB | 6.4 s, `UNDER ASSERTIONS SATISFIABLE` |

Checking the justified proof takes **140 times** as long as checking the
asserted one, and 300 times the solve without proofs. Its 1.30 million RUP
steps carry no VeriPB antecedent hints. Where the checking time goes was not
measured further.

**Assertions at `Inferences`**, by wire form: `inverse` 545,768 (two literals
each), `table` 399,321, `all_different` 210,932 plain and 13,230 `hall`,
`comparison` 25,898, and the solver's own `backtrack` 13,998 and `solx_block` 1.
This constraint is responsible for 769,930 of 1,209,148, or **64%**. The
`inverse` count equals the counters' firings of rules 1 and 2 exactly.

**Own against shared**, as a function of `n`: a probe posting one `Inverse` over
full domains and taking the first solution in input order. That is the identity
permutation, where no Hall set fires. All verified.

| n | OPB rows | proof lines | of which root at-most-ones | proof lines without them |
|---|---|---|---|---|
| 4 | 192 | 152 | 32 | 120 |
| 8 | 704 | 650 | 240 | 410 |
| 16 | 2,688 | 3,470 | 1,952 | 1,518 |
| 32 | 10,496 | 21,782 | 15,936 | 5,846 |
| 64 | 41,472 | 152,102 | 129,152 | 22,950 |

Without the at-most-ones the proof is exactly `1.5·n(n − 1)` lines of this
family's own inferences (rules 1–3), and the shared literal layers are
`4n² + 8n` (`2n²` order-literal `pol`s, `2n² + 4n` `core` moves, `4n` unit
bounds). The at-most-ones add exactly `n·C(n, 2) + 2n` (pairwise RUPs, folds
and deletions), which is 85% of the
proof at `n = 64`. On `black-hole` the search needs 32 of the 52 at-most-ones
eventually, so skipping the root saves only 1.8% of the lines, and checking was
no faster. On `inverse_constraint` at `--seed=1` it saves 11% (#1049).

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified, and nothing is asserted at
`AssertionLevel::Off`. The propagator is the same with proofs on and off. At the
assertion levels, the Hall assertions (rules 4 and 5) carry an `all_different`
hint whose at-most-one cache is empty, so a reconstructor derives the
at-most-ones itself, over the scope it finds from the constraint id.

### Known limitations

- **A MiniZinc model that makes two entries of one array equal gets
  `=====ERROR=====`**, not `=====UNSATISFIABLE=====` (#1047). `circuit` does
  the same.
- **XCSP3 `channel` over lists of different lengths aborts** (#1047).
- **Slow**: 8–10 times Gecode's time at equal node counts, where it dominates
  (#1048).
- **Proofs carry a cubic root cost**: `n·C(n, 2) + 2n` lines before search
  (#1049).
- **Not generalised arc consistent under aliasing.** `Inverse(x, x)`, or an
  array holding two views of one variable, can need search to refute.
  `SymmetricAllDifferent` is no stronger on #413's triangle.
- **No reified form.**

### Next steps

Ranked by what they buy for what they cost.

1. **#1046** — not this family's, but found here: `GlobalCardinality` proofs
   can abort (both arms) or be rejected (the bounds arm) when its array holds a
   constant, in 135 of 300 random instances. It is reachable
   from MiniZinc, and it is the most serious finding of this audit.
2. **#1047** — decide where a repeated handle from MiniZinc becomes a
   contradiction (front-end glue, or the constructors, as `AllDifferent` does),
   for `Inverse` and `Circuit` both; and implement or `report_unsupported` the
   unequal XCSP3 `channel`. Small either way, with a lane each.
3. **#1049** — delete the root initialiser and let the Hall justification build
   what it uses. Deleting code; the lazy path already verifies on everything
   tried. Also correct `recover_am1`'s header while there.
4. **#1048** — walk intervals (18%, and it removes this family's only per-value
   iteration), then make the channel incremental and push-based, and skip `GAC`
   runs that cannot find anything. Re-measure on the four `black-hole` instances
   above. A real project; the first step is an afternoon.
5. **Tests.** A larger instance in `inverse_test` (a few dozen positions, so
   the root cost and the per-call cost are visible), a wide declared domain in
   the audit-lane row, and an inferences-level check that every assertion
   carries `Inverse`'s id. Unfiled.

## Prior art

Channelling between a permutation and its inverse is the classic dual-model
constraint. Hnich, Smith and Walsh (*Dual modelling of permutation and
injection problems*, JAIR 2004) compare the propagation strengths of
channelling and `AllDifferent` on either side. The fact used here, that
channel consistency together with `GAC` on `AllDifferent(x)` is `GAC` on the
pair when every position is a different variable, has a short argument, given
under rule 5. It is why the propagator runs
`AllDifferent` on one side only, which dacd1eea ("Only need to alldiff on one
side", 2024) made so. Régin (1994) is the matching algorithm. Gecode's `channel` is the
reference implementation. On the proof side, nothing is published for `Inverse`
specifically. The channel is a single RUP against its own model row, and the
`AllDifferent` part is McIlree's JP 3.16 and 3.17, with the at-most-ones
derived through the channelling rows rather than read from a clique encoding.
That last step is the only thing here that is ours.

## Further reading

- [`all_different.md`](all_different.md): the generalised arc consistent
  algorithm, its Hall justifications, the sinks-first order that the proof
  depends on under aliased views, and the history of `Inverse`'s value-set bug.
- [`justification-techniques.md`](../justification-techniques.md): the
  unit-propagation facts behind JP 3.1, 3.16 and 3.17.
- `gcs/constraints/all_different/symmetric_all_different_test.cc`: the instances
  on which channelling plus bipartite matching is weaker than an involution's
  `GAC` (#413's triangle), which apply to `Inverse(x, x)` as they stand.

## Developer commentary

**Checking a helper's callers found a bug in another family.** Reading how
`Inverse` calls `recover_am1` showed that its three callers disagree about the
atoms' polarity, and the helper's shortcut for two false atoms is right for only
one of them. A 300-seed sweep of `GlobalCardinality` with constants in its
array then found the wrong `0 ≥ 1` in 8 runs, and an unrelated missing case
(an at-least-one over a constant) aborting 127 more. The counting audit had
read every rule of that constraint and missed both, because its tests put
constants only in all-constant rows. A shared helper's contract is worth
checking against every caller whenever one of them is being audited.

**A constraint built from another family's propagator inherits its proof
precondition silently.** JP 3.16 and 3.17 assume a clique of pairwise
not-equals rows. `Inverse` has none, and its proofs verify anyway, because each
pairwise clause is one more unit-propagation step away through the channelling
rows. That is fine for VeriPB, and invisible to a justifier that dispatches on
the hint name, which is `all_different`'s. The constraint id is what tells the
two apart.
