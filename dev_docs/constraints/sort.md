# `Sort` and `ArgSort`: one array is another sorted, and the permutation that sorts it

> **Maturity** production ·
> **Audited** 2026-09-29 at `c9ceea25` ·
> **Open issues** none filed by this audit yet; see [Next steps](#next-steps)
> for what it would file. Already open and touching this family: #262 (a
> dominance prelude for permutation auxiliaries, which would change how `pos`
> is pinned), #833 (the large-domain policy), #868 (cross-solver comparisons;
> this document gives one, by hand). Tracked under #871.

`Sort(x, y)` says `y` is `x` sorted into non-decreasing order. `ArgSort(x, p,
offset)` says `p` is the **stable** permutation that sorts `x`: ties are broken
by original index, so `p` is a function of `x`. Both run the Mehlhorn–Thiel
bounds-consistent sortedness propagator over a proof-only stable-rank encoding,
and every inference it makes is certified, including the Hall-interval ones: as
far as this audit knows, no certified sortedness propagator existed before.
`ArgSort` adds internal sorted values, a channel to `p`, a propagator that
prunes `p` by the ranks each element can reach, and a generalised arc
consistent `AllDifferent` on `p`. The design and the derivations are in
[`sortedness.md`](../sortedness.md), which stays as this family's long note;
this document audits it.

Four things to know before touching it.

- **`Sort` is `bounds(Z)` on both arrays, over distinct variables, and GAC is
  out of reach** (Rusu proves it NP-hard). `ArgSort` is not `bounds(Z)` on `x`
  or on `p`, which is known and recorded in `sortedness.md`.
- **With proofs off, `Sort` can spend most of its time on proof-only work.**
  Every Hall-case bound runs an `O(n³)` search for a Hall band whose only use is
  the justification, and runs it with no proof being written. On a Hall-heavy
  benchmark, skipping it takes the solve from 25.1 s to 0.77 s, on the same
  tree. The share grows with `n`, since each search is `O(n³)`, and with how
  often Hall cases fire: at `n = 20` the same benchmark calls it about as often
  per node as at `n = 100`, but each call costs 7.2 µs against 1.35 ms, so it is
  21% of the solve; the Gecode enumeration below never calls it.
- **`ArgSort` is up to cubic per call, and one of its loops walks a domain.**
  Its rank propagator reads up to `Θ(n³)` bounds per call: 173 s where `Sort`
  alone takes 1.3 s at `n = 80`, on overlapping windows. And when ties leave a
  hole in an element's reachable ranks, it finds a threshold value by stepping
  through that element's values one at a time: 5.5 s at the root for a domain
  of width 10⁹, proofs off, for a value only the proof uses.
- **Its proofs are expensive in `n` twice over.** A root derivation of the
  permutation facts is `Θ(n³)` lines: 1.3 million, and 118 s to check, at
  `n = 80`, before search. And an order-statistic inference is `Θ(n²)` lines
  and `Θ(n²)` literals: most of its lines are three-literal clauses, and only
  about `n` carry the `O(n)` reason. A Hall inference is `O(n²)` lines, not
  measured for literals.

## What it is

### Semantics

- **`Sort(x, y)`**: `|x| = |y|`, `y` is a multiset permutation of `x`, and
  `y[0] ≤ y[1] ≤ … ≤ y[n−1]`. Different lengths throw
  `InvalidProblemDefinitionException` at install. An empty pair is vacuously
  true; nothing is installed.
- **`ArgSort(x, p, offset)`**: `|x| = |p|`, `p` is a permutation of
  `offset..offset+n−1`, `x[p[j]−offset] ≤ x[p[j+1]−offset]`, and ties go by
  index: `x[p[j]−offset] = x[p[j+1]−offset] ⇒ p[j] < p[j+1]`. The offset
  defaults to 0. `p` is a permutation for every `n`, including `n = 1`, as
  MiniZinc documents; MiniZinc's own decomposition leaves `p` free when `n = 1`,
  which `argsortshapes.mzn` notes and avoids. Different lengths throw.
- **A repeated variable** is accepted: `Sort{(a, a), (b, c)}` means `b = c = a`.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Sort` | ✓ `fzn_sort` | n/a[^xsort] | ?[^gcspy] | ✓ `sort` | |
| `ArgSort` | ✓ `fzn_arg_sort_int`, with `offset` read off `x`'s index set[^mznarg] | n/a[^xsort] | ?[^gcspy] | ✓ `arg_sort`, with the offset as a trailing atom | |
| reified `sort` | ✓ in part: MiniZinc's function form still posts a native `glasgow_sort` inside the reified decomposition | n/a | — | — | no lane covers it |
| reified `arg_sort` | `decompose`: the stdlib's `fzn_arg_sort_int_reif`, fully | n/a | — | — | |
| `arg_sort` over floats | `unsupported` | n/a | — | — | no float variables |

[^xsort]: XCSP3 has no sortedness constraint; its `ordered` orders an existing
    sequence, which is [`increasing`](increasing.md).

[^gcspy]: `gcspy` binds nothing in this family.

[^mznarg]: `p` is indexed from 1, but its values are indices of `x`, so the
    binding passes `min(index_set(x))` as the offset, and guards the empty
    case. Getting this wrong was #987, a wrong answer on arrays not indexed
    from 1 that the certified chain verified, because the chain starts at the
    `.scp`. `argsortoffset.mzn` and `argsortshapes.mzn` (from #1006) pin it: `x`
    indexed from −3, from 0, from 100 and by an enum, repeated variables, and
    the function form over one element. `fzn_arg_sort_int.mzn` also includes the
    stdlib's reified decomposition explicitly, since a reified call cannot
    flatten a builtin body.

`sort` is positional, and so is `Sort`: no index set matters there.

### Options

`None.`

### Variable kinds and views

Plain variables, constants and views, for `x`, `y` and `p`. Every propagator
reads bounds (and, for `p`, membership), and the proof treats a view through
its own proof variable. **Not separately exercised:** neither test has a
`view_mixed` lane.

### Reification

No reified class. From MiniZinc, a reified `arg_sort` decomposes fully in the
standard library, while a reified `sort` decomposes into a native `Sort` on a
fresh array (the function form) plus reified equalities with `y`. No lane
covers the latter, and nothing in the corpus posts either constraint at all
(see [Benchmarks](#benchmarks-and-examples)).

### Relation to other families

- **Decomposes into it:** MiniZinc's reified `sort`, through the function form
  (see [Reification](#reification)). Nothing inside the solver.
- **Child constraints:** none posted as constraints, but `ArgSort` **installs**
  another family's propagator directly: `propagate_gac_all_different` from
  [`all_different`](all_different.md), over `p`, fed by `am1` lines recovered
  lazily from this family's own at-most-one rows.
- **Shares code:** `Sort` and `ArgSort` share `define_sortedness_proof_model`
  and `install_sortedness_propagator` (`sortedness.hh`); `ArgSort` calls both
  with its internal `y`. `recover_am1_from_pairs` is the shared clique fold.
- **Presolvers:** none reads either.

## The proof model

### OPB encoding

This is `cake_pb_cp`'s `cencode_sort` and `cencode_argsort`
(`cp_to_ilp_sortingScript.sml`), label for label.

**`Sort(x, y)`**, for `n` elements, with `w = ⌈log₂ n⌉`:

```
y[i] ≤ y[i+1]                                           @c[id][<i>]
before[ip][i]  ⇔  x[ip] − x[i] ≤ (ip < i ? 0 : −1)      n² flags x[id][<ip>_<i>][bf], two-way reified
pos[i] ∈ 0..n−1                                         proof-only, w bits v[id][<i>_<b>][pos]
pos[i] = Σ_ip before[ip][i]                             @c[id][rle<i>], @c[id][rge<i>]
bits(pos[i]) spell j  ⇒  y[j] = x[i]                    @c[id][cle<i>_<j>], @c[id][cge<i>_<j>]
```

`before[ip][i]` is "`x[ip]` comes before `x[i]` in the order by value, then by
index"; the diagonal is always false and is counted, as cake does. So `pos[i]`
is `x[i]`'s stable rank, a **function of `x` alone**, which is what lets a
solution pin every auxiliary by unit propagation, and lets a wrong leaf be
refuted by plain RUP. The channel is guarded by the conjunction of `pos[i]`'s
bits, not by an `=` atom, so no `pos[i] = j` atom enters the OPB; the proof
introduces them on first use.

**`ArgSort(x, p, offset)`** adds internal sorted values `y[j]`, real state
variables over `[min lb(x), max ub(x)]` that are never branched on, and the
encoding above over `{x, y}` with the arg-sort labels (`@c[id][yle<i>]`,
`@c[id][acle…]`, `@c[id][acge…]`), and then:

```
offset ≤ p[j] ≤ offset + n − 1                          define_bound, a row per side where p[j] is wider
Σ_j [p[j] = offset + k] ≤ 1                             @c[id][perm<k>am1]
p[j] = offset + k  ⇒  y[j] = x[k]                       @c[id][vcle<j>_<k>], @c[id][vcge<j>_<k>]
p[j] = offset + k  ⇒  pos[k] = j                        @c[id][rcle<j>_<k>], @c[id][rcge<j>_<k>]
yge[j]  ⇔  y[j] ≥ y[j+1]                                flags v[id][<j>][yge]
yge[j]  ⇒  p[j] + 1 ≤ p[j+1]                            @c[id][tb<j>]
```

The at-most-one rows and the range rows make `p` a bijection; the rank channel
ties it to the stable rank; the tie-break row is the stability clause.

**It is definitional**, both of them: every row is the constraint's meaning or
an auxiliary's definition, and the auxiliaries are determined by `x` (and `p`).
**Size:** `Θ(n²)` rows (the `before` flags and the channel), and
`Θ(n²·(log n + log W))` literal occurrences for domains of width `W`: the
`before` rows alone are `n²` comparisons over bit sums of `Θ(log W)` bits.
`ArgSort` adds another `Θ(n²)` rows. **Logarithmic in domain
width**: nothing is per value, so the row count does not depend on width, and
only the bit sums' literals grow, with the bit width. The fact-check measured
`Sort` at `n = 10` going from 85 KB at `W = 9` to 541 KB at `W = 10⁹`
(`sortwidth.cc`). Measured for `Sort` over `0..n−1`: 469 rows at `n = 10`,
1,739 at 20, 6,679 at 40, 26,159 and 8.8 MB at 80.

### Labels

As above. Rules cite the witness lines (`rank_ge`, `rank_le`, the `before`
halves) by line number from `define_proof_model`, not by label. The labels are
there so that the solver's OPB and cake's line up.

### Cake conformity

`scp_chain_{sort,arg_sort}_{sat,unsat}` chain-verify in `none` mode. `Sort`'s
encoding is cake's row for row, and `ArgSort`'s is up to the differences
below, so the propagator's steps resolve against cake's OPB. The `Sort` cases
stay `none` for the literal-encoding divergence (#358) the whole section
shares. The `ArgSort` cases would stay `none` after #358 too: of their three
differences, the omitted `plb`/`pub` rows and the `rcge0_k` coefficients are
not literal encoding. By the fact-check's `opbdiff` runs, `sort_sat` would pass
`strict` and `sort_unsat` differs by one `@i[Y1][ub]` row. The `ArgSort` cases
(`arg_sort_sat` and `arg_sort_unsat` alike) differ three ways, 100 rows
matching, 43 differing and 18 only in cake's:

- `p`'s literal definitions: the solver's 42 `@i[P][ge|eq][f|r]` rows against
  cake's 54 `@c[_1][peq*]`;
- cake's six `plb*` / `pub*` range rows, which the solver omits because
  `define_bound` returns early when `p`'s declared domain already fits;
- three `rcge0_k` rows where cake gives the guard coefficient 0 and the solver
  1, both tautologies.

Two accommodations make `ArgSort` line up:

- cake encodes each `y[j]` as a free, always-signed bit sum with no bound rows,
  so the solver names `y`'s bits to match (including a sign bit even over a
  non-negative range) and derives `y[j]`'s range in the proof, once, at the root
  (see [Proof-time state](#proof-time-state));
- cake reifies each `p[j]`'s `≥` atoms under its own labels, so the solver marks
  `p`'s atoms for their labels to be recovered in the proof (an `ia`
  re-declaration), so that its order-chain `pol` steps resolve against either
  OPB.

### Proof-time state

- **At the root, `Sort`** (and `ArgSort`'s inner sortedness): an initialiser at
  `InitialiserPriority::Expensive` derives the permutation facts at
  `ProofLevel::Top`: totality and antisymmetry of `before` (a saturated `pol`
  per pair), transitivity (a `pol` and a RUP per ordered triple), the rank gaps
  `before[i][ip] ⇒ pos[ip] ≥ pos[i] + 1` (an exact `pol` per ordered pair), an
  at-least-one per `pos[i]`, and an injectivity at-most-one per rank from
  `recover_am1_from_pairs`. The order-statistic and Hall-case justifications
  reuse them (antisymmetry, injectivity and at-least-one lines). **This
  is `Θ(n³)` lines**, paid once. It runs only at `AssertionLevel::Off`; at the
  assertion levels it is skipped, since the rules are asserted.
- **At the root, `ArgSort`:** a second initialiser, at `SimpleDefinition`
  priority, derives `y[j] ≥ min lb(x)` and `y[j] ≤ max ub(x)` for each `j` by a
  case split on `p[j]`, keeping only the two bounds at `Top`. Also `Off` only.
- **During search:** each inference's lemmas, at `Temporary`.
- **Naming:** the flags and bits as above; `pos[i] = j` atoms are introduced
  lazily under `pos`'s name.
- **Proof-only auxiliaries determined on a solution:** yes: `pos` by `x`
  through `before`, `yge` by `y`.

## The implementation

### Initialisation and global data

`Sort::prepare()` checks the lengths. `ArgSort::prepare()` also marks `p`'s
atoms for label recovery, pins `p`'s range with `define_bound`, finds `x`'s
overall range, and allocates the `n` internal `y`. `define_proof_model()`
builds the encoding and keeps the witness (`before`, `pos`, the rank lines),
which every justification reads. The two initialisers above are the only root
work.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| permutation-facts initialiser | — (root, `Expensive`) | n/a | scaffolding | `Sort` and `ArgSort`, proofs at `Off` | n/a | n/a |
| Mehlhorn–Thiel sortedness | `on_bounds`, `x` and `y` | derived: **nothing** | 1–6 | `Sort`; `ArgSort` over its internal `y` | never claims | never |
| sorted-value range initialiser | — (root, `SimpleDefinition`) | n/a | scaffolding | `ArgSort`, proofs at `Off` | n/a | n/a |
| channel | `on_bounds` `x`, `y`; `on_change` `p` | derived: **`p`** | 7, 8 | `ArgSort` | never claims | never |
| achievable rank set | `on_bounds` `x`; `on_change` `p` | derived: **`p`** | 9, 10 | `ArgSort` | never claims | never |
| GAC `AllDifferent` on `p` | `on_change` `p` | derived: **`p`** | [`all_different`](all_different.md)'s | `ArgSort` | **claims** (`EnableButIdempotent`) | per `all_different` |

**The sortedness propagator reads bounds only**, so no hole affects it. The two
`ArgSort` propagators declare `p` as hole-sensitive through `on_change`, which
over-reports: they read `in_domain(p[j], v)` only to skip a pruning already
made, and `p` being fixed, which the channel does use, is a bounds event. It
costs nothing, since the `AllDifferent` on the same `p` is genuinely
hole-sensitive.

**Idempotence.** Only the `AllDifferent` claims it, for the reason
[`all_different.md`](all_different.md) gives. The others make no claim, and
whether one sortedness pass is a fixpoint was not checked. None of them
self-disables.

### Mutable state and incrementality

For the sortedness, channel and rank propagators, `None.` Every call rebuilds
the matching and the SCCs, and the rank sets, from the current bounds. The
`AllDifferent` on `p` is the exception: it keeps
[`all_different`](all_different.md)'s GAC scratch and its matching across
wakes (#526), and an `am1_lines` cache
that fills lazily from the `perm<k>am1` rows (`arg_sort.cc`, around lines
511–520).

### Interior values and optional pruning

**Offers.** `None.` There is no stronger arm to make optional, and GAC is
NP-hard.

**Observes.** Nothing on `x` or `y`: the whole vocabulary there is bounds. On
`p`, holes matter, through the `AllDifferent`.

### Robustness and limits

**Unbounded domains.** `Sort` is fine: the propagator and the encoding are in
`n`, not in width. `ArgSort` is not, at one site: see [Interval
efficiency](#interval-efficiency).

**Negative values and zero.** Tested: `sort_test` has `[−1, 1]` and random
lower bounds from −1, `arg_sort_test` `[−2, 0]` and random lower bounds from −2.

**Degenerate shapes.** Empty, single and all-fixed arrays are tested per #254,
for both. **A repeated variable** breaks `Sort`'s bounds consistency, which
assumes distinct variables: on random shapes with repeats, the root fails
`bounds(Z)` on 162 of 2,000 instances (`tmp/fd-ordering/ordcheck.cc`, `sort
alias`, seed 2; 175 at seed 1 and 166 at seed 3). A negated view of the same
variable, `(v, −v)`, breaks it too. The duplicate run in `sort_test`
(`x = (a, a)`) checks it by enumeration only. **Two `ArgSort`s in one problem** once shared their `y`
atoms' names and gave a proof VeriPB rejected (#1010); `arg_sort_test` now
posts two.

**Overflow.** The algorithms compare bounds as `long long` and write
`L = ly[j]` style constants back; nothing adds to a bound but `± 1` inside
`infer_*`. The `ArgSort` threshold search (below) does `v + 1` in `long long`
up to `ub(x[k])`, which cannot exceed the domain cap.

### Interval efficiency

**`Sort` is fine at any width. `ArgSort` has one width-proportional walk, on
the propagation path, for a value only the proof uses.**

1. **The propagation side.**
   - *Sortedness:* two sorts, two priority-queue sweeps, a Tarjan SCC over the
     interval adjacency (`O(n²)`, not the thesis's linear version), and, for
     each Hall-case bound and each matching failure, `find_band`, a search of
     every rank interval `[a, b]` against every element: **`O(n³)` per call to
     it, run with proofs off**, as an invariant check, though its result is
     read only by the justification. No value walks.
   - *`ArgSort`'s rank propagator:* for each element `k`, up to `O(n)`
     candidate values (not de-duplicated), each costing `O(n)` bounds reads:
     **up to `Θ(n³)` bounds reads per call**, re-reading the same `n` bounds
     throughout. That is the worst case, reached when the windows overlap; with
     separated windows the fact-check measured about 3.3 times per doubling
     (0.49, 1.61 and 5.42 s at `n = 20`, 40 and 80, `argsort_sep.cc`). Then,
     for a rank `j` that is a hole inside `k`'s interval (the tie case), a
     threshold `U` is
     found by **stepping `v` from `lb(x[k])` one value at a time** until the
     count of possible predecessors reaches `j`, each step `O(n)`. With
     `x₀ ∈ 0..W` and `x₁ = x₂ = W/2`, it walks about W/2 values: 0.56 s at
     `W = 10⁸` and 5.47 s at `W = 10⁹`, one propagation, proofs off
     (`probes/argwide.cc`; Release `c9ceea25`, fataepyc-10, 2026-09-29). `U` is
     read only by the justification, and the count is a step function of `v`
     that changes only at the other elements' bounds, so it is `O(n log n)`
     from those breakpoints.
   - *Channel:* `O(n²)` per call. *`AllDifferent`:* over `n` values, as there.
2. **The reason side.** Two bound literals per element, never per value.
   `Sort`'s whole-scope reason is built once at install and materialised only
   when a proof wants it. `ArgSort`'s channel and rank propagators construct a
   `bounds_reason` per inference, which copies its variable list into a shared
   allocation even with proofs off; only the domain walk is deferred. Nothing
   in the family calls `want_reasons()`. None is minimal: see the rules.
3. **The proof side.** No line is per value. The root is `Θ(n³)` lines, an
   order-statistic inference `Θ(n²)` lines of which about `n` carry the
   `O(n)` reason, and a Hall-case one `O(n²)` lines: see
   [Proof performance](#proof-performance). All of it is in `n`.
4. **The audit lane.** Two rows, both `Clean`: `Sort` over three and three wide
   plain variables, and `ArgSort` over three wide `x` and a narrow `p`. Neither
   has a **tie**, so the `ArgSort` row never reaches the hole case, and even if
   it did, the guard counts `State` iterations and this walk is a plain `for`
   loop: a guard build of `c9ceea25` runs the probe at `W = 10⁸` without
   tripping. A row with two equal `x` and a wide third would reach the site;
   instrumenting it needs a counter in the loop.

## Inference catalogue

Ten rules of this family's own: six in the shared sortedness propagator, which
`Sort` runs on `(x, y)` and `ArgSort` on `(x, its y)`, and four in `ArgSort`'s
channel and rank propagators. `ArgSort`'s `AllDifferent` on `p` is
[`all_different`](all_different.md)'s rules and hints, and its am1 lines come
from this family's `perm<k>am1` rows. The numbering follows the code's order.

Four facts hold for the sortedness rules.

**Every rule is certified, and the procedures are ours.** No published
justification procedure covers sortedness; [`sortedness.md`](../sortedness.md)
derives each case. They lean on the root permutation facts, on the channel, and
on one **Hall pigeonhole on the rank line**: a rank interval `[a, b]` and a set
`S` of elements whose feasible ranks all lie inside it, with `|S| > b − a + 1`.
The pigeonhole is the `all_different` Hall argument (JP 3.16's shape) with ranks
as the slots and the root injectivity lines as the capacity. A bound's Hall case
is the same pigeonhole under the negated goal.

**The reason is the whole scope,** `bounds_reason(x ++ y)`: two literals per
element, or one when fixed.

**One wire form per propagator.** `hints::Sort`, `(constraint_id <id>)`, for
rules 1–6, under whichever constraint installed the propagator (so `ArgSort`'s
inner sortedness says `sort` with `ArgSort`'s ID); `hints::ArgSort`,
`(constraint_id <id>)`, for rules 7–10. No subhint distinguishes a rule's
cases. Measured at `Definitions`: 615 `sort` annotations on a `Sort` over four
and four in `0..3`; 288 `arg_sort`, 218 `sort` and 76 `all_different` on an
`ArgSort` over four in `0..2`.

**The `find_band` invariant.** Whenever a Hall case fires, a band must exist;
if `find_band` finds none it throws `UnexpectedException` rather than weaken the
proof. That check runs with proofs off too, which is the cost measured below.

### Rule: y-window-infeasible

- **Infers** — a contradiction.
- **Fires when** — after normalising the `y` windows (lower bounds running max
  left to right, upper bounds running min right to left), some `ly[j] >
  uy[j]`.
- **Strength** — part of `bounds(Z)`.
- **Algorithm** — the two normalisation sweeps, `O(n)`.
- **Why it is true** — some `k₁ ≤ j ≤ k₂` has `lb(y[k₁]) > ub(y[k₂])`, but a
  sorted `y` needs `y[k₁] ≤ y[k₂]`.
- **Proof technique** — `RUP sequence`, ours: the monotonicity clauses
  `(y[m] ≤ V) ∨ (y[m+1] > V)` for `m = k₁..k₂−1` at `V = ub(y[k₂])`, each RUP from
  one sortedness row, then the closing RUP walks the chain down.
- **Reason** — the whole scope. The derivation needs only `lb(y[k₁])` and
  `ub(y[k₂])`.
- **Assertion** — `¬reason`.
- **Hint** — `hints::Sort`.
- **Offline reconstructibility** — `offline`: `k₁`, `k₂` and `V` are readable
  off the reason's `y` bounds.
- **Proof size** — `k₂ − k₁` lemmas.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: no-matching

- **Infers** — a contradiction.
- **Fires when** — Glover's greedy matching of `y` positions to `x` elements
  (down or up sweep) finds no element for some position.
- **Strength** — part of `bounds(Z)`.
- **Algorithm** — the sweeps, `O(n log n)`; then `find_band`, `O(n³)`.
- **Why it is true** — a set `S` of elements can only take ranks in `[a, b]`,
  and there are more of them than ranks.
- **Proof technique** — `RUP sequence` plus a `pol`, ours: the normalised
  window lemmas `y[k] ≤ uy[k]`, `y[k] ≥ ly[k]`; per `i ∈ S`, the exclusions
  `pos[i] ≠ k` for `k` outside `[a, b]` and the restricted at-least-one; then a
  `pol` of those against the injectivity lines for `[a, b]`.
- **Reason** — the whole scope.
- **Assertion** — `¬reason`.
- **Hint** — `hints::Sort`.
- **Offline reconstructibility** — `search`: the band is not in the hint, and
  finding one is the `O(n³)` scan `find_band` does (or a matching algorithm);
  it is in the baseline context, since it follows from the reason's bounds.
- **Proof size** — `O(n)` window lemmas plus `O(|S|·n)` exclusions: `O(n²)`
  lines, most of them emitted under the `O(n)` reason. Not measured.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: y-lower-bound

- **Infers** — `y[j] ≥ L`.
- **Fires when** — the up sweep's matching gives a larger lower bound than
  `y[j]` has.
- **Strength** — `bounds(Z)` on `y`, with rules 4–6. Checked by brute force at
  the root over random domains **with holes** (`ordcheck.cc`, `sort`, 2,000
  instances of up to three and three): no `bounds(Z)` failure on `x` or `y`,
  while `bounds(D)` fails on 83 of them and GAC on 644 (seed 1). `sort_test`
  checks `bounds(Z)` at every node, on domains that start as intervals and
  gain holes from the test brancher (see [Tests](#tests)). Mehlhorn and Thiel
  prove it, over distinct variables; see [Robustness](#robustness-and-limits)
  for repeats.
- **Algorithm** — as rule 2's sweeps.
- **Why it is true** — three cases: (a) *normalisation*, an earlier `y` already
  has lower bound `L`; (b) *order statistic*, at least `n − j` elements are
  individually forced `≥ L`, so the `(j+1)`-th smallest is; (c) *Hall*, the
  bound follows from the windows of the other `y`s confining some elements.
- **Proof technique** — `RUP sequence`, per case: (a) the monotonicity chain;
  (b) the count line, the rank bridges and per-element
  `(pos[i] ≠ j) ∨ (y[j] ≥ L)` lines, then the surjectivity `pol` for rank `j`;
  (c) the rule-2 pigeonhole under the negated goal, with the goal literal ORed
  into each assumption-dependent clause. See `sortedness.md` for each.
- **Reason** — the whole scope.
- **Assertion** — `y[j] ≥ L ∨ ¬reason`.
- **Hint** — `hints::Sort`.
- **Offline reconstructibility** — (a), (b) `offline`: the case, and the
  constants, follow from the clause and the reason's bounds. (c) `search`, as
  rule 2.
- **Proof size** — (a) `O(j)`; (b) `Θ(n²)` lines and `Θ(n²)` literals: for
  the lower bound, `n(n − 1)` three-literal pivot RUPs and `n(n − 1)` inner
  `pol`s (`sort.cc`, around lines 525–546); for the upper bound, `n(n − 1)`
  three-literal RUPs folded into `n` `pol`s (around 693–714). Only about
  `n + 2` file lines carry the `O(n)` reason's literals: the count line, the
  `n` per-element lines and the closing RUP (around 555, 560, 565, 722, 729
  and 739). The `n` folds of the count line into the rank bounds (`RANKUB2`,
  `RANKLB2`) are short `pol a b +` lines; they depend on the reason, which is
  why `2n + 1` derived constraints do, but they do not print it. Measured as
  lines longer than `2n` literals per order-statistic inference: 12.1 at
  `n = 10` and 24.4 at `n = 20`
  (`tmp/fd-ordering/factcheck3/sort/linesizes.py`). (c) `O(n²)` lines, most
  under the `O(n)` reason (the `j + 1` chain lines and the final `pol` are
  not); not measured.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: y-upper-bound

- **Infers** — `y[j] ≤ U`. The mirror of rule 3, on the down sweep.
- **Fires when**, **Strength**, **Algorithm**, **Reason**, **Hint**,
  **Offline reconstructibility**, **Proof size**, **Gaps**, **Tightness** — as
  rule 3.
- **Why it is true** — (a) a later `y` already has upper bound `U`; (b) at least
  `j + 1` elements are individually forced `≤ U`; (c) Hall.
- **Proof technique** — as rule 3, mirrored.
- **Assertion** — `y[j] ≤ U ∨ ¬reason`. Measured at `Inferences`, `Sort` over
  four and four in `0..3`, `y[0] ≤ 0` once `x[0] = 0`:
  ```
  a 1 ~i[y[0]][ge1] 1 ~i[x[0]][eq0] 1 ~i[x[1]][ge0] 1 i[x[1]][ge4] … 1 ~i[y[3]][ge0] 1 i[y[3]][ge4] >= 1
    ::sort:((constraint_id _1));
  ```

### Rule: x-lower-bound

- **Infers** — `x[i] ≥ L`, with `L` the lower bound of the smallest `y` that
  `x[i]` can be matched to in some perfect matching.
- **Fires when** — the reduced intersection graph's SCCs place `x[i]` no lower
  than position `jl`, and `ly[jl]` exceeds `lb(x[i])`.
- **Strength** — `bounds(Z)` on `x`, with rules 3, 4 and 6; see rule 3.
- **Algorithm** — the SCC pass, `O(n²)`.
- **Why it is true** — two cases: *intersection*, `x[i]` cannot sit below
  `jl` because every lower `y` window ends below `x[i]`'s; *Hall*, the other
  elements' windows fill the lower ranks.
- **Proof technique** — `RUP sequence`: intersection, the per-rank clauses
  `(pos[i] ≠ k) ∨ (x[i] ≥ L)`, closed by `pos[i]`'s at-least-one; Hall, the
  pigeonhole under the negated goal.
- **Reason** — the whole scope.
- **Assertion** — `x[i] ≥ L ∨ ¬reason`.
- **Hint** — `hints::Sort`.
- **Offline reconstructibility** — intersection `offline`; Hall `search`.
- **Proof size** — intersection `n` lines; Hall `O(n²)`.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: x-upper-bound

The mirror of rule 5, `x[i] ≤ U` from the largest `y` it can match. Every field
as rule 5, mirrored.

### Rule: channel-disjoint

- **Infers** — `p[j] ≠ offset + k`.
- **Fires when** — `x[k]`'s and `y[j]`'s bounds do not overlap, in `ArgSort`'s
  channel propagator.
- **Strength** — `partial`: it and rules 8–10 together are not `bounds(Z)` on
  `p`. The root probe (`ordcheck.cc`, `argsort`, seed 1) finds `bounds(Z)`
  failing on 399 of the 1,623 instances whose root did not fail, at 637
  endpoints of `x` and 15 of `p`, as [`sortedness.md`](../sortedness.md)'s
  caveat predicts: the stable tie-break tightens both beyond what the reused
  propagator sees. A counterexample on `p`: `x₀ = 1`, `x₁ ∈ {0, 3}`,
  `x₂ ∈ 0..3`, `p₀ ∈ 0..2`, `p₁ ∈ {1, 2}`, `p₂ ∈ {0, 2}`. The root keeps
  `p₀ = 2`, its upper bound, which no solution has (`probes/argcex.cc`). Two
  comments in `arg_sort.cc` (around lines 262–263 and 312) claim `bounds(Z)`
  on `p` all the same, and are wrong.
- **Algorithm** — `O(n²)` bounds and membership checks.
- **Why it is true** — position `j` holds element `k` only if `y[j] = x[k]`.
- **Proof technique** — `RUP`: the value channel half-reified on
  `p[j] = offset + k` and the two bounds contradict (Theorem 2.6, then 2.9 for
  the equality half).
- **Reason** — `x[k]`'s and `y[j]`'s bounds, four literals; the two that
  separate them would do.
- **Assertion** — `p[j] ≠ offset + k ∨ ¬reason`.
- **Hint** — `hints::ArgSort`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: channel-fixed

- **Infers** — up to four bounds: `y[j]` and `x[k]` each tightened to the
  other's.
- **Fires when** — `p[j]` is fixed to `offset + k`.
- **Strength** — `partial`, as rule 7.
- **Algorithm** — `O(1)` per fixed position.
- **Why it is true** — `y[j] = x[k]`.
- **Proof technique** — `RUP`, as rule 7.
- **Reason** — the other variable's two bounds, and `p[j] = offset + k`; one of
  the two bounds would do.
- **Assertion** — `bound ∨ ¬reason`.
- **Hint** — `hints::ArgSort`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: rank-outside-interval

- **Infers** — `p[j] ≠ offset + k`.
- **Fires when** — `j` lies outside `[a_k, b_k]`, where `a_k` counts the
  elements that precede `k` in every assignment and `b_k` those that can.
- **Strength** — `partial`, as rule 7.
- **Algorithm** — part of the rank propagator's up-to-`Θ(n³)`-per-call pass.
- **Why it is true** — `k`'s stable rank is at least the number of elements
  that must precede it, and at most the number that can.
- **Proof technique** — `pol`, then `RUP`: for `j < a_k`, `rank_ge[k]` plus a
  RUP line `before[i][k] ≥ 1` per forced predecessor gives `pos[k] ≥ a_k`; for
  `j > b_k`, `rank_le[k]` plus `¬before[i][k]` lines gives `pos[k] ≤ b_k`;
  then the rank channel makes `p[j] ≠ offset + k` RUP.
- **Reason** — the bounds of all of `x`. Not minimal: the elements whose
  precedence is undecided are named too.
- **Assertion** — `p[j] ≠ offset + k ∨ ¬reason`. Measured at `Inferences`,
  `ArgSort` over four in `0..2`:
  ```
  a 1 ~i[p[1]][eq0] 1 ~i[x[0]][eq0] 1 ~i[x[1]][ge0] 1 i[x[1]][ge3] 1 ~i[x[2]][ge0] … >= 1
    ::arg_sort:((constraint_id _1));
  ```
- **Hint** — `hints::ArgSort`.
- **Offline reconstructibility** — `offline`: `a_k` and `b_k` follow from the
  reason's bounds.
- **Proof size** — `O(n)` lines.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: rank-hole

- **Infers** — `p[j] ≠ offset + k`, for `j` inside `[a_k, b_k]` but
  unreachable.
- **Fires when** — ties among the other elements make the count of `k`'s
  predecessors jump over `j` as `x[k]` crosses their common value.
- **Strength** — `partial`, as rule 7.
- **Algorithm** — the reachable set, from `O(n)` sampled values of `x[k]`, each
  counted in `O(n)`; then the threshold `U`, **by a walk over `x[k]`'s values**
  (see [Interval efficiency](#interval-efficiency)).
- **Why it is true** — there is a value `U` with at most `j − 1` possible
  predecessors at `x[k] ≤ U` and at least `j + 1` forced ones at
  `x[k] ≥ U + 1`, so neither side puts `k` at rank `j`.
- **Proof technique** — two `pol`s pivoting on the constant `U` (line A folds
  `rank_le[k]` with `(x[k] ≥ U+1) ∨ ¬before[i][k]` clauses, line B folds
  `rank_ge[k]` with `(x[k] ≤ U) ∨ before[i][k]`), then `RUP` through the rank
  channel by the case split on `x[k] ≥ U + 1`.
- **Reason** — the bounds of all of `x`.
- **Assertion** — `p[j] ≠ offset + k ∨ ¬reason`.
- **Hint** — `hints::ArgSort`.
- **Offline reconstructibility** — `search`, but cheap: `U` is not carried,
  and the reconstructor recomputes it from the reason's bounds (the same step
  function the propagator walks, which the breakpoints give directly).
- **Proof size** — `O(n)` lines.
- **Gaps** — `None.` **Tightness** — `Not shown.`

## Evidence

### Tests

- **`sort_test`** (`sort_constraint`): pairs, triples with duplicates,
  negative and asymmetric ranges, narrow `y` forcing `x`, overlapping windows
  for the Hall cases, nested bands, infeasible `y` windows, a rank-line Hall
  violator, #254's degenerate arrays, a duplicate `x = (a, a)`, and eight random
  instances up to five long. Under `solve_for_tests_checking_consistency` with
  `bounds(Z)` on both `x` and `y` at every node, on domains that start as
  intervals; with and without proofs. Seeded. Its own comment notes that the
  large-count order-statistic case is **not** exercised, since the harness
  cannot take the wide domains it needs.
- **`arg_sort_test`** (`arg_sort_constraint`): distinct values, many ties,
  0- and 1-based, single element, #254's degenerate arrays, negative values,
  separated domains (rule 7), tie-induced rank holes (rule 10), two `ArgSort`s
  in one problem (#1010), and eight random instances up to four long. Plain
  `solve_for_tests`: enumeration and the proof, **no consistency check**,
  deliberately, since `x` and `p` are not `bounds(Z)`.
- **`scp_chain_{sort,arg_sort}_{sat,unsat}`:** see [Cake
  conformity](#cake-conformity).
- **MiniZinc:** `sorttest.mzn`, `argsorttest.mzn`, `argsortoffset.mzn`,
  `argsortreif.mzn`, `argsortshapes.mzn`.
- **Audit lane:** the `Sort` and `ArgSort` rows.

**Runtime caps.** No lane sets or clears one, and the default caps never fire:
58 runs of `sort_test` and 48 of `arg_sort_test`, all complete
(`GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500 … --seed=1`, at
`c9ceea25`). Neither has a `view_mixed` lane.

**Tightness:** no mutation lane. `sortedness.md` records a 200-seed random
sweep and an `n = 20` order-statistic probe verifying with no assertions, run
while the proofs were written; neither is in the tree.

**What the tests do not cover.**

- **Views.** No lane mixes them in.
- **Holey initial domains,** for `Sort`'s per-node check; the root probe
  covers them. Holes made by branching do reach the check: the shared test
  brancher rejects random intervals (`value_order::reject_random_interval`),
  and under the branching pair of `--seed=1` (`variable_order::random(p, 1)`,
  `reject_random_interval(2)`) a `Sort` with `x` and `y` of length three in
  `0..3` has a hole at 68 of its 84 trace callbacks, and at 38 to 68 of 70 to
  84 across seeds 1, 2, 3, 7 and 42 (`holes.cc` and, for the seed range,
  `holes_seed.cc`, in `tmp/fd-codex-1005/ordering/probes/`: standalone probes,
  not counts from inside `sort_test`). Both the check and the sortedness
  propagator read only bounds, so a hole matters there only where a pushed
  bound lands past it. `sort_test` posts only the one `Sort`, so holes made by
  another constraint are not exercised (`arg_sort_test`'s two `ArgSort`s
  share no variable).
- **`ArgSort` with repeated variables, offsets other than 0 and 1, or `p`
  domains wider than the index range,** in C++; MiniZinc's
  `argsortshapes.mzn` covers all three (a repeat, offsets −3 and 100, wider
  `p`). **Holey initial `p` domains** are untested everywhere. Holes in `p`
  do arise during search, from `ArgSort`'s own propagators and from the test
  brancher: an `ArgSort` with `x` of length three in `0..3` and `p` in `0..2`
  has a hole in `p` at 17 of its 103 trace callbacks under the branching
  pair of `--seed=1` (17 to 26 of 97 to 103 across seeds 1, 2, 3, 7 and 42,
  `holes_seed.cc`), and at 12 of 21 under in-order smallest-first branching,
  which makes none itself (`tmp/fd-codex-1005/ordering/probes/holes2.cc`).
  `arg_sort_test` checks enumeration and proofs there, not consistency.
- **A reified `sort`,** which MiniZinc still sends to the native builtin.
- **`n` beyond five,** so neither the `Θ(n³)` root nor the `O(n³)` per-call
  searches show up as cost.
- **A tie over a wide domain,** which is what reaches the `ArgSort` walk.
- **Real instances:** none; none exists in the corpus.

### Benchmarks and examples

- **In the repository:** none.
- **Corpus:** **no model posts either.** Of the 285 flattened MiniZinc
  Challenge models none calls `sort` or `arg_sort`, and `gt-sort` 2025, missing
  from that corpus because its data are JSON, posts `strictly_increasing` and
  `alldifferent` once flattened, not `sort`. (#248, a wrong answer on
  `gt-sort`, and #251, "no native propagator", are both closed.)
- **For CPU:** synthetic. The enumeration below for Gecode; `sort_bench2.cc`
  (`tmp/fd-ordering/ab/`) for the Hall-heavy cost: a hidden assignment in
  `0..R`, `x` windows reaching up to `w` either side of it, and `y` windows up
  to `w` either side of its sorted image, so the instance is feasible and the
  windows overlap. The proof runs below use `R = 0.6n`, `w = 10`.
- **For proof verification:** the same, at `n = 10` (1.76 million lines, 42 s)
  and the root probe (`probes/sortroot.cc`) for the initialiser alone. Do not
  run the Hall benchmark with proofs past `n = 20`: at `n = 40` it passed 1.4 GB
  within minutes.

### CPU performance

*Release build of `c9ceea25` (GCC 15.2.0, `-O3 -march=native`); Gecode 6.3.0,
built locally; fataepyc-10, boost off, pinned to one core, fixed malloc
thresholds; wall time of the whole solve, proofs off; 2026-09-29.*

**Against Gecode's `sorted`.** Enumerating every `x ∈ 0..d−1` of length `n` with
`y = sort(x)`, branching on `x` then `y` in input order
(`bench/sort_gcs.cc`, `sort_gecode.cc`). Both are bounds consistent and neither
fails, so both explore the same assignments (GCS branches one child per value,
Gecode in two, so their node counts differ). Median of five:

| n | d | Solutions | GCS | Gecode | Ratio |
|---|---|---|---|---|---|
| 6 | 5 | 15,625 | 0.090 s | 0.029 s | 3.1 |
| 7 | 5 | 78,125 | 0.479 s | 0.165 s | 2.9 |
| 8 | 4 | 65,536 | 0.486 s | 0.150 s | 3.2 |

No failure means this exercises the `y` bounds from fixed `x`, not the Hall
cases, where the next table's cost is.

**The proof-only Hall search, with proofs off.** A/B on `sort_bench2.cc`,
stopped after 20,000 callbacks (the solver reports 20,114 and 27,349 recursions
for the two `n = 100` rows), the only difference being `find_band` returning a
trivial band when there is no logger (`ab/sort_noband.cc`). The tree is the
same by construction, and the recursions, propagations and solutions are
identical either way. Three runs each, all within 4%:

| n | R | w | Seed | `find_band` calls | As it is | Without it | Ratio |
|---|---|---|---|---|---|---|---|
| 20 | 20 | 3 | 1 | 6,083 | 0.211 s | 0.167 s | 1.26 |
| 100 | 100 | 5 | 1 | 6,602 | 9.55 s | 0.626 s | 15 |
| 100 | 60 | 10 | 3 | 22,702 | 25.1 s | 0.773 s | 32 |

(`R` is the range of the hidden assignment, `w` the window half-width; medians
of three.)

At `n = 100` the search is **93 to 97% of the solve**, and at `n = 20` 21%.
The `n = 20` row calls it about as often per node (6,083 calls in 20,000
recursions, against 6,602 in 20,114 at `n = 100`); the difference is the cost
per call, 7.2 µs against 1.35 ms, 187 times, roughly as `O(n³)` predicts
(`(100/20)³ = 125`). So the share grows with `n` and with how often Hall
cases fire; the Gecode enumeration fires none. The invariant it checks is a
proof invariant; with no proof there is nothing for it to protect.

**`ArgSort` against `Sort` on the same `x`.** `n` elements in `0..9`, branching
on `x`, 20,000 nodes (`bench/argsort_bench.cc`), one run each:

| n | `Sort` | `ArgSort` | Ratio |
|---|---|---|---|
| 10 | 0.121 s | 0.521 s | 4.3 |
| 20 | 0.211 s | 2.87 s | 14 |
| 40 | 0.465 s | 21.1 s | 45 |
| 80 | 1.27 s | 173 s | 136 |

On these overlapping windows `ArgSort` grows by 5.5, 7.4 and 8.2 times per
doubling, approaching cubic; with separated windows it is about 3.3 (above). At
`n = 40`, `perf` puts 52% of cycles in `State::bounds` and 41% in an `ArgSort`
propagator lambda, and the inner sortedness propagator under 2%. By its loop
structure the lambda is the rank propagator: up to `Θ(n³)` bounds reads per
call, against `Θ(n²)` for the channel. Reading the bounds once per call, into a
vector, removes the first half; computing the reachable set from the sorted
breakpoints removes the cube.

**Cross-solver for `ArgSort`: `Not measured.`** Gecode's `sorted` with a
permutation is not stable, so it is a different relation.

### Proof performance

*Same build and machine; VeriPB 3.0.2 with `--force-checked-deletion`.*

**The root.** `Sort` over `0..n−1`, stopping at the root (`probes/sortroot.cc`):
the permutation facts alone.

| n | OPB rows | Proof lines | Proof bytes | VeriPB |
|---|---|---|---|---|
| 10 | 469 | 3,274 | 206 KB | 0.03 s |
| 20 | 1,739 | 22,844 | 1.57 MB | 0.33 s |
| 40 | 6,679 | 170,884 | 12.2 MB | 5.74 s |
| 80 | 26,159 | 1,322,564 | 96.4 MB | 118 s |

**Lines grow by 7 to 8 per doubling: cubic.** At `n = 80` about 75% of them are
the transitivity lines (`2n(n − 1)(n − 2)`) and 19% the pairwise at-most-one
lines `recover_am1` folds (`n·C(n, 2)`). The
solver writes the `n = 80` root in 0.83 s; VeriPB takes 118 s to check it,
before any search.

**Per inference, on `sort_bench2.cc`** with proofs, 2,000 nodes, `R = 0.6n`,
`w = 10`, seed 3:

| n | `sort` inferences | of them order-statistic | Hall cases (`find_band` calls) | Lines, `Off` | Bytes, `Off` | Lines per inference | VeriPB, `Off` | Bytes, `Inferences` |
|---|---|---|---|---|---|---|---|---|
| 10 | 10,832 | 10,822 | 4 | 1,760,093 | 125 MB | 162 | 41.7 s | 6.8 MB |
| 20 | 20,901 | 20,619 | 247 | 13,388,609 | 980 MB | 641 | 466 s | 21.1 MB |

Almost every inference here is an **order-statistic** bound (rule 3 or 4, case
b), not a Hall case; the case counts are the fact-check's (`cases_all.txt`).
Lines per inference quadruple as `n` doubles because each order-statistic
inference is `Θ(n²)` lines. They are not all long: bytes per line stay flat
(71 and 75 B), lines with more than `2n` literals are 7.3% and 3.7% of them,
and those hold about half of all literal occurrences at both sizes (the
fact-check's `line_sizes.txt`). So an order-statistic inference is `Θ(n²)`
literals too. Asserting the inferences cuts the proof by 18 and 46 times.

**Assertion levels.** On `Sort` over four and four in `0..3`: `Off` is 18,360
lines and verifies; `Definitions` 3,902 lines and 615 assertions, and
`Inferences` 3,291 lines, are accepted under assertions (`s UNDER ASSERTIONS`,
not `VERIFIED`); `Links` fails. On `ArgSort` over four in `0..2`: `Off` 10,030
lines and verifies, `Definitions` 2,130 and `Inferences` 1,680 are accepted
under assertions, and `Links` fails (`probes/runfam.sh`). Above `Off` the
family's inferences are `a` lines, so only `Off` checks the family. The
`Links` failure is at a `solx` step, which is generic rather than this
family's: other families' probes fail at `Links` the same way. At
`Definitions` the inferences are asserted and the root initialisers skipped,
which between them are most of the drop from `Off`.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified at `Off`; the propagators are the same
with proofs on or off. (`sortedness.md` records the earlier stages, when the
Hall counts were asserted; they are all certified now.)

### Known limitations

- **`ArgSort` is not bounds consistent on `x` or `p`,** because the stable
  tie-break is invisible to the reused sortedness propagator. No
  bounds-consistent algorithm for the stable form is known.
- **A repeated variable** makes `Sort` weaker than bounds consistent.
- **`Sort` is much slower than it need be with proofs off** when Hall reasoning
  fires, because it searches for the proof's Hall band anyway.
- **`ArgSort` is up to cubic per call,** and **stalls on a tie over a wide
  domain,** in proportion to the width.
- **The proof of either costs `Θ(n³)` lines before search,** and `Θ(n²)` lines
  per order-statistic inference, `O(n²)` per Hall inference.

### Next steps

1. **Skip `find_band` with proofs off.** Run the search only when a logger will
   read the band; with none, the matching's own failure is the evidence. The
   A/B above: up to 32 times, same tree. Small. Filed as #1140. With proofs on,
   the band search itself can be `O(n²)` or better (a sweep over the sorted
   interval endpoints, as López-Ortiz et al. do for `all_different`), which is
   the second half of the same issue.
2. **Make `ArgSort`'s rank propagator `O(n² log n)` or better, and remove its
   walk.** Read the bounds once per call; compute each element's reachable set
   from the sorted breakpoints of the others' bounds; find `U` from those
   breakpoints, and only when a logger will read it. Filed as #1139, with both
   tables. The walk is the more urgent half: it is the only width-proportional
   site in the family, and no current guard or audit row can see it. While
   there, correct the two comments that claim `bounds(Z)` on `p`.
3. **Add a tie row to the audit lane,** two equal `x` and a wide third, with a
   counter in the threshold loop so that it can trip.
4. **Consider a cheaper root.** The `Θ(n³)` transitivity lines exist to prove
   `pos` a permutation; #262's dominance prelude, or deriving only the facts
   the order-statistic and Hall cases use, might avoid them. Research, not a
   fix.
5. **Minimal reasons** for rules 1–6: each needs only a handful of the scope's
   bounds, and the lines emitted under the reason carry all of them. On the
   order-statistic proofs that is a constant factor, at most about 2, since
   those lines hold about half the literals; on the Hall proofs, where most
   lines carry the reason, it may be more, but that was not measured.

## Prior art

Bleuzen-Guernalec and Colmerauer (*Constraints* 5, 2000) and Mehlhorn and Thiel
(CP 2000; Thiel's thesis, 2004) give bounds consistency for sortedness in
`O(n log n)`; Gecode's `sorted` implements Thiel's algorithm, and Choco's
`keySort` and SICStus's `keysorting` the stable variant `ArgSort` is. Rusu
(TCS 2017) proves domain consistency NP-hard. As far as this audit knows, no
certified sortedness propagator existed before this one: the encoding is
`cake_pb_cp`'s, and the Hall-on-the-rank-line certificate is ours. The details
are in [`sortedness.md`](../sortedness.md).

## Further reading

- [`sortedness.md`](../sortedness.md): the semantics, the encoding's design
  constraint (auxiliaries determined by `x`), the survey of algorithms, the
  Mehlhorn–Thiel implementation notes, and the derivation of every proof case,
  including why the count line is RUP and how the band is found. 385 lines;
  read it before changing a justification.
- [`all_different.md`](all_different.md): the propagator `ArgSort` runs on `p`.
