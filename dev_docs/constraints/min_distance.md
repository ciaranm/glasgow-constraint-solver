# `MinDistance`: the smallest distance between any two selected sites

> **Maturity** production ·
> **Audited** 2026-09-30 at `c9ceea25`; re-audited 2026-10-08 at `0a5b4ec6`
> for #1168 ·
> **Open issues** filed by this audit: #1169 (the ladder's build is
> `Θ(L · n²)` with proofs), #1170 (the matching bound concludes less than its
> certificate proves), #1171 (`z`'s lower bound is never raised before every
> position is fixed). **Fixed since the audit**: #1168 (the overflows), by
> #1215, with #1214 for view offsets: out-of-range inputs are refused at
> construction; see [Re-audit, 2026-10-08](#re-audit-2026-10-08). Already open
> and touching this family: #833 (the large-domain policy), #944 (interval
> cardinality instead of an at-most-one per value, which names this family's
> per-site at-most-ones). Tracked under #871.

### Re-audit, 2026-10-08

One fix to this family has merged since the audit. The status line and next
step 3 were brought into line with it on 2026-10-05; this pass does the other
passages, at `0a5b4ec6`.

| Issue | Fixed by | What changed here |
|---|---|---|
| #1168, distances near `2⁶³` crashed the proof model, `CheckOnly`, and every mode through an offset view on `z` | #1215 (with #1214) | the constructor checks every distance and requirement against `±(2⁶⁰ − 1)` and throws `IntegerOverflow` outside it (`min_distance.cc:40–42`); #1214 refuses a view offset, and a declared domain, outside the same range. The propagators and `define_proof_model` are unchanged. The summary loses its bullet on it; [Semantics](#semantics), [Robustness and limits](#robustness-and-limits)' **Overflow** (now history), [Tests](#tests) and [Known limitations](#known-limitations) follow; [Next steps](#next-steps) item 3 already had. `min_distance.cc`'s lines after the constructor moved down by four, and the present-tense citations of it moved with them; those of `scp_reader.cc` and `names_and_ids_tracker.cc`, moved by other merges, are re-pointed at `0a5b4ec6` too, and the Overflow record's are labelled `c9ceea25`'s |

#1117 (`table`), which the Overflow paragraph compared this to, was closed
by #1215 too.

**What was measured again**, at `0a5b4ec6` on fataepyc-10, pinned to cores
32–39 with the malloc thresholds fixed: the inputs of the audit's overflow
shapes, rebuilt as
`tmp/fd871-comments-1008/ordsmall/probes/min_distance/refuse.cc` (each is now
refused, below), and `integer_ranges_test`'s `MinDistance` cases
(two refusals, and 25 edge shapes, each solved with and without proofs, all
25 proofs verified; `probes/tests/ir.txt`).
Nothing else was re-taken: no other figure involves an out-of-range input,
and the family's code is unchanged apart from the constructor's check.

`MinDistance(x, z, D, R, propagation)` says that `z` is the smallest distance
`D[x_i, x_j]` over all pairs of positions `i < j`, where each `x_i` picks one
of `n` candidate sites and `D` is a symmetric distance matrix; an optional
requirements matrix `R` adds pairwise lower bounds. It is the constraint of
the p-dispersion problem, from Lagerkvist's *Propagation Algorithms for the
Minimum-Distance Constraint over Selected Points* (ModRef 2026), and it is a
Glasgow extension with no frontend vocabulary: only the C++ API and the `.scp`
reader post it. One definitional encoding serves five propagation modes, from a
checker to the paper's conflict-matching bound, and every inference is
certified. The design and the derivations are in
[`min-distance-proofs.md`](../min-distance-proofs.md), which stays as this
family's long note; this document audits it.

Four things to know before touching it.

- **Its strength is partial by design, and one-sided on `z`.** Before every
  position is fixed, nothing raises `z`'s lower bound, not even to `0`: with
  two positions over two sites 5 apart and `z ∈ −3..9`, the root leaves `z ∈
  −3..5` in every mode but `CheckOnly`, which leaves `−3..9`.
  `z` gets upper bounds only (the pairwise bound, and the matching bound in the
  `…Match` modes); `x` gets forward checking (`ForwardBound`, the default) or
  pairwise arc consistency against `max(R_ij, lb(z))` (`PairSupport`).
  Generalised arc consistency is NP-hard here (it contains independent set).
- **With proofs on, building the encoding is `Θ(L · n²)` for `L` distinct
  distances, and `L` can reach `n(n−1)/2 + 1`.** On random Euclidean instances
  with many distinct distances (1,219 levels at `n = 50`, 82,426 at `n = 600`,
  against maxima of 1,226 and 179,701) the root takes 8.9 s at `n = 400` and
  26.4 s at `n = 600`, against 4 ms and 9 ms with proofs off. Most of it is one
  linear scan of every site pair, repeated per distance level, in
  `define_proof_model`. With 140 distinct distances `n = 600` takes 1.35 s.
- **The matching bound proves less than its own certificate does.** A
  refutation at level `t` concludes `z ≤ t − 1`, but the conflict graph is the
  same for every level down to the next smaller distance `t*`, so the same
  matching and the same derivation, guarded at `z ≤ t*`, conclude `z ≤ t*`.
  An experiment build with that guard cuts `PairSupportMatch`'s tree on
  20-site random Euclidean instances by 26 to 52% with six positions and 5 to
  58% with eight (seeds 1–7), and by under 8% with four; every proof it wrote
  verified. Grids, whose rounded distances are consecutive integers, do not
  change. See [Rule: matching-bound](#rule-matching-bound).
- **Assertions carry no hint.** The family has no `hints.hh`, so its `a` lines
  at the assertion levels name neither the constraint nor the rule. `Links`
  fails here the generic way, at a backtracking RUP, on about 4% of small
  random instances; `Definitions` and `Inferences` are accepted under
  assertions.

## What it is

### Semantics

For positions `x₀, …, x_{p−1}` over sites `0..n−1`, a symmetric `n × n` matrix
`D` of non-negative integers with a zero diagonal, and an optional `p × p`
matrix `R`:

```
z = min_{0 ≤ i < j < p} D[x_i, x_j]        and, with R,   D[x_i, x_j] ≥ R_ij  for all i < j
```

- **Duplicate selections are allowed**, and contribute the diagonal: two
  positions on one site make `z ≤ 0`. `z ≥ 1` therefore forbids duplicates,
  which is how `p_dispersion` posts it (`--initial-lb`, default 1).
- **`R` is read above the diagonal only.** Its diagonal and lower triangle are
  ignored and may hold anything; `R_ij = 0` is vacuous. An `R_ij > 0` forbids
  `x_i = x_j`. The `p_dispersion` example converts the literature's strict
  `r_ij` to this `≥` form (`R_ij = r_ij + 1`) at the call site.
- **`p ≥ 2`**, else `InvalidProblemDefinitionException`, thrown by `prepare()`
  when the problem is solved, not at `post`. So is a non-square, asymmetric,
  empty or negative `D`, a `D` with a non-zero diagonal, and an `R` that is not
  `p × p` or has a negative entry above the diagonal (`min_distance.cc:52–89`).
  The test's seven rejection cases cover six of these eight checks, squareness
  twice; an empty `D` and `p < 2` are untested (both throw, checked by hand).
- **Every distance and requirement must lie in `±(2⁶⁰ − 1)`**, the bounded
  range of [`integer-ranges.md`](../integer-ranges.md), since #1215: the
  constructor checks them (`min_distance.cc:40–42`) and throws
  `IntegerOverflow`, at construction rather than in `prepare()`. `z`'s
  declared domain, and a view's offset on it, must lie in the same range
  (#1214).
- **A position's values outside `0..n−1` are removed**, not rejected:
  `prepare()` pins every `x_i` to `0..n−1` with `define_bound`, which writes a
  range row to the OPB only where the declared domain is wider, and removes the
  rest by an initialiser (hint `initial_bound`).
- **`n = 1`** puts every position on site 0, so `z = 0`. **`p > n`** forces a
  duplicate, so `z ≤ 0`.
- **A repeated variable** (`x_i` and `x_j` the same variable) is accepted and
  means those two positions pick the same site, so `z ≤ 0`; no propagator
  exploits that before the variable is fixed (see
  [Robustness](#robustness-and-limits)).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `MinDistance` | `unsupported`[^vocab] | `n/a`[^vocab] | `unsupported`[^vocab] | ✓ `min_distance`, with `R` as an optional trailing matrix; the propagation mode is not written[^scpmode] | no cake chain: `cake_pb_cp` has no rule[^cake] |

[^vocab]: No frontend has a vocabulary for it: neither MiniZinc's standard
    library nor XCSP3 defines a minimum-distance global, and `minizinc/mznlib`,
    `xcsp/` and `gcspy` bind nothing here. The cells follow the row #569 added
    to `frontend-support-matrix.md`. `examples/p_dispersion` is the only
    in-tree model.

[^scpmode]: `read_min_distance` (`scp_reader.cc:957`) posts at the default,
    `ForwardBound`, whatever wrote the file, as the regular variants do; a
    `PairSupportMatch` model read back from its `.scp` propagates differently.
    Its comment calls `Z` "a lower bound on the pairwise distance between the
    chosen sites", which is incomplete rather than wrong: `Z` is the greatest
    such bound, the minimum itself.

[^cake]: `cake_pb_cp out.scp` on a `min_distance` model prints `unsupported
    constraint: min_distance` (checked on three `.scp` files, plain, with `R`
    and maximising, `tmp/fd-small/min_distance/scp/`; each verifies under VeriPB
    against the solver's own OPB). So there is no `scp_chain_min_distance*`
    case, and the encoding below is checked against nothing but its own
    definition.

### Options

**`propagation`**, a `MinDistancePropagation`, default `ForwardBound`. It
selects propagators only; `define_proof_model` never reads it, so **the OPB is
identical in all five modes** (checked: byte-identical `.opb` for all five on
the probe shapes below).

| Mode | Installs | Paper |
|---|---|---|
| `CheckOnly` | the check-only propagator: acts on fixed pairs, pins `z` once every position is fixed | none; the encoding's regression check |
| `ForwardBound` | the forward propagator without its support scan | §4.1, `global-forward-bound` |
| `PairSupport` | the forward propagator with its support scan | §4.2, `global-pair-support` |
| `ForwardBoundMatch` | `ForwardBound`, plus the matching propagator | §4.4, Algorithm 1 |
| `PairSupportMatch` | `PairSupport`, plus the matching propagator | §4.4 |

The default is the paper's cheapest real propagator. On the 10 × 10 grid with
`p = 10` below, `PairSupportMatch` is the fastest mode, which is the paper's
qualitative result, so the default is a choice nobody has revisited rather
than a measured one. `CheckOnly` is kept on purpose, as the check that the
encoding alone certifies every consequence by RUP (`constraints.md`, "Worked
examples"); `min_distance_test` runs every case under it.

No `with_consistency()`, and no legacy no-op tunables.

### Variable kinds and views

`x` and `z` accept plain variables, constants and views. The propagators read
`x`'s visible values as site indices and `z` by its bounds, and the proof names
a view through its own literals. `min_distance_test` has a `view_mixed` lane
(it sizes the wrap for six positions, but no case posts more than four of `x`
plus `z`), and this audit ran 750 random enumerations with a negated, offset
view on `x₀` (`sweep.sh view`, five modes × 150 seeds): every solution count
matched a brute force and every proof verified. A constant position is
exercised in the fixed specs; the matching derivation skips a constant's
at-least-one by design.

### Reification

`None.` There is no reified or half-reified form, and no frontend that would
reify one.

### Relation to other families

- **Decomposes into it:** nothing. `p_dispersion`'s default `--variant tuple`
  is the alternative: one `Element2DConstantArray` per position pair, an
  `ArrayMin`, and a `GreaterThanEqual` per requirement.
- **Child constraints:** none.
- **Shares code:** `recover_am1_from_pairs`
  (`innards/proofs/am1_from_pairs.hh`), the clique fold with a guard riding
  through it, which `all_different`, `sort`, `subcircuit`, `disjunctive` and
  the `inferred_disjunctive` presolver also call; its guarded shape exists for
  this family (#805).
  `NamesAndIDsTracker::need_constraint_saying_variable_takes_at_least_one_value_over_cover`,
  shared with `all_different`, `bin_packing` and the counting family.
  `Propagators::define_bound`, for the site range.
- **Presolvers:** none reads or writes it.
- **Reachable only from:** the C++ API and the `.scp` reader. Nothing in the
  MiniZinc Challenge corpus can reach it.

## The proof model

### OPB encoding

Over the **candidate sites** `S` (values in `0..n−1` some position can take at
install) and, per site `a`, the positions `P_a` that can take it. `z_lo` and
`z_hi` are `z`'s bounds at install, and `L = sorted({0} ∪ {D[a,b] : a < b in
S})` the distance levels.

```
u_a  ⇔  Σ_{i ∈ P_a} [x_i = a] ≥ 1                         flag f[..][mindist_u_<a>], per site
Σ_{i ∈ P_a} [x_i = a] + (p−1)·[z ≥ 1] ≤ p                   per site with |P_a| ≥ 2; if z_lo ≥ 1, just ≤ 1; if z_hi ≤ 0, omitted
¬u_a ∨ ¬u_b ∨ [z ≤ D[a,b]]                                  per site pair a < b, omitted when z_hi ≤ D[a,b]
¬[x_i = a] ∨ ¬[x_j = b]                                     per i < j, a ∈ dom x_i, b ∈ dom x_j with D[a,b] < R_ij
d_a  ⇔  Σ_{i ∈ P_a} [x_i = a] ≥ 2                          flag mindist_d_<a>, lazily, for level 0
w_ab ⇔  u_a + u_b ≥ 2                                       flag mindist_w_<a>_<b>, lazily
m_k  ⇔  m_{k−1} ∨ (the d and w witnesses at level L_{k−1})   flag mindist_m_<L_{k−1}>
[z ≥ L_k] ∨ m_k                                             per level with z_lo < L_k (m_0 is false)
```

The first three kinds push `z` down: a selected pair of distinct sites bounds
it by their distance, and a duplicate by `0`. The last line is the
**min-attained ladder**, which pushes `z` up: at each level, either `z` reaches
it or some pair strictly closer is selected. The `(p−1)` coefficient in the
count row is the least that lets a duplicate force `[z ≤ 0]`, which is written
as `[z ≥ 1]` on the left. [`min-distance-proofs.md`](../min-distance-proofs.md)
derives each row and explains why `u_a` alone cannot express the diagonal.

**It is definitional.** Every row is the constraint's meaning or a flag's full
reification, and every flag is fixed by unit propagation from a complete `x`,
so a solution pins `z` to exactly the minimum.

**Size.** `n` site flags and at most `n` count rows; up to `n(n−1)/2` pair
clauses and witness flags, up to `n(n−1)/2 + 1` ladder rows, and up to `L`
accumulator flags; and up to `p²·n²/2` requirement clauses. **Nothing depends
on `z`'s width**: `z` contributes `≥` literals per level (two OPB rows each),
not per value. The `u`, `d` and count rows have at most `p + 1` terms (degree
at most `p`); an `m` flag's reification has one per witness at its level, `n`
at level 0 and up to `O(n²)` when many distances tie. Measured on random
Euclidean instances, `p = 5`, `z ∈ 1..max D`, integer points in a square of
side 100,000, so most but not all distances distinct (`mdroot.cc`):

| `n` | Levels | OPB lines | OPB bytes |
|---|---|---|---|
| 50 | 1,219 | 13,436 | 2.2 MB |
| 100 | 4,844 | 50,752 | 8.4 MB |
| 200 | 17,992 | 183,970 | 30.5 MB |
| 400 | 54,067 | — | 90.8 MB |

(OPB lines are constraints plus two: a comment and the `preserved:` line.) At
`n = 50`, 4,836 of the 13,436 lines define `z`'s 2,418 `≥` literals (a level
`t` needs `[z ≥ t]` for the ladder and `[z ≥ t+1]` for the pair clause), and the
`w` and `m` flags another 4,884. With few distinct distances (points in a
square of side 100) the ladder is short: 5,544 lines at `n = 50` with 119
levels.

**Building it is `Θ(L · n²)`.** `witnesses_at(v)` (`min_distance.cc:230`) scans
every candidate pair for the distance `v`, and the ladder calls it once per
level (`:258`), so the build is quadratic in the pairs when every distance is
distinct; see [Initialisation](#initialisation-and-global-data).

### Labels

`None.` Every row is written unlabelled by `add_constraint`. The rules cite no
row by line number either: every derivation is RUP or a `pol` over lines the
justification itself derives, and the four flag kinds are found by name.

### Cake conformity

**Not checked: `cake_pb_cp` has no rule for `min_distance`** (see the frontend
table). So no `scp_chain` case exists, `opbdiff` has nothing to compare against,
and nothing but `CheckOnly`'s all-RUP proofs and the enumeration tests stands
behind the encoding. The `.scp` side is covered: `scp_reader_test` has two
`min_distance` cases (enumeration with and without `R`, and a write → read →
write round trip), and every proving test run reads its own `.scp` back
(`check_scp_writer_reader_symmetry`).

### Proof-time state

- **At the root:** the `define_bound` range rows and their initialiser, when
  `x` is wider than `0..n−1`. With many levels the root proof is the shared
  layer: order-chain `pol`s linking each of `z`'s `≥` literals to its
  neighbours, 4,821 of the 5,071 root `pol` lines for 2,418 literals at `n = 50`
  with 1,219 levels. The family writes no scaffolding of its own.
- **During search:** each inference's lemmas at `ProofLevel::Temporary` (the
  pair bound's per-value lines, the matching's pairwise clauses, clique folds
  and sum), except the matching's at-least-ones. Those come from
  `need_constraint_saying_variable_takes_at_least_one_value_over_cover`, which
  the tracker emits once per variable (per distinct cover, in the cover form)
  and caches: at `TopAndCore` in the per-value form, at `Top` in the cover form
  (see [Interval efficiency](#interval-efficiency) for which). On the 5 × 5 grid
  under `PairSupportMatch`, 871 clique folds share one at-least-one per
  position.
- **Deleted:** only the temporaries, when each justification closes; the
  cached at-least-ones stay.
- **Naming:** the flags are `f[<k>][mindist_u_<a>]`, `mindist_d_<a>`,
  `mindist_w_<a>_<b>` and `mindist_m_<t>`, with `<k>` the tracker's running
  counter, so a tool locates them by the suffix. No row is labelled.
- **In the OPB, not introduced in the proof:** all four flag kinds are
  `create_proof_flag_fully_reifying` in `define_proof_model`, so they are model
  flags. Each is determined by unit propagation on a solution (`u` and `d` from
  the `x` literals, `w` from `u`, `m` from `d`, `w` and the previous `m`).
- **Proof-only vectors:** `_position_sites`, `_sites` and `z`'s install bounds
  are filled by `prepare()` whether or not a proof is being written, and the
  matching propagator reads `_position_sites` with proofs off too. Nothing
  dangles.

## The implementation

### Initialisation and global data

`prepare()` validates `D` and `R` (squareness first, then symmetry and signs,
`O(n²)`), pins each `x_i` to `0..n−1`, and records each position's candidate
sites by `n` membership tests per position (`O(p · n)`), their union, and
`z`'s bounds. `install_matching_propagator` also sorts every off-diagonal
distance of `D` into a level list (`O(n² log n)`), with proofs on or off.

`define_proof_model()`, with proofs on only, is the one root cost that
dominates, on instances with many distinct distances. Pinned to one core, root
only, proofs on, `p = 5`, three runs each within 1%:

| `n` | Levels | Root, proofs on | Root, proofs off |
|---|---|---|---|
| 100 | 4,844 | 0.20 s | 0.4 ms |
| 200 | 17,992 | 1.23 s | 1.2 ms |
| 300 | 35,953 | 3.93 s | — |
| 400 | 54,067 | 8.93 s | 4.2 ms |
| 600 | 82,426 | 26.4 s | 9.2 ms |
| 600, square of side 100 | 140 | 1.35 s | — |

*Release `c9ceea25`, GCC 15.2.0, fataepyc-10, boost off, fixed malloc
thresholds, files on `/dev/shm`, 2026-09-30; `mdroot.cc`, random points in a
square of side 100,000 (or 100 for the last row), seed 1.*

`perf` at `n = 400` puts 77.7% of cycles in `define_proof_model` itself, nearly
all of it on the distance comparison inside `witnesses_at` and the matrix reads
beside it. The last row is the control: the same `n` with 140 levels. Sorting
the site pairs by distance once would make the build `O(n² log n)`.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| `define_bound` initialisers | — (root, default priority) | n/a | the site range | `x_i` wider than `0..n−1` | n/a | n/a |
| check-only | `on_instantiated` each `x_i`; `scope_only` `z` | derived: **`z`**, which it never reads | 1, 2, 3 | `CheckOnly` | never claims | never |
| forward | `on_change` each `x_i`; `on_bounds` `z` | derived: **`x`** | 3, 4, 5, 6, 7 | every other mode; rule 7 under `PairSupport…` only | never claims | never |
| matching | `on_change` each `x_i`; `on_bounds` `z` | derived: **`x`** | 8, 9 | `ForwardBoundMatch`, `PairSupportMatch` | never claims | never |

**Holes.** The forward and matching propagators read `x`'s interior values
(supports, the active site set), so `on_change` is honest there, and they read
only `z`'s bounds. The check-only propagator's `scope_only` on `z` declares a
hole sensitivity it does not have, since it never reads `z`; it only matters
under `CheckOnly`, and over-reporting is never unsound.

**Idempotence.** No propagator claims it, and whether one call reaches a
fixpoint was not checked. There is reason to doubt it for the forward
propagator: it walks the pairs once per call, so a pruning found at a later pair
can remove a support an earlier pair relied on, and its full-assignment pin can
raise `z`'s lower bound, which feeds every threshold (its `on_bounds` trigger
re-queues it, as the code comments). None disables itself, even once every
position is fixed.

### Mutable state and incrementality

`None.` Every call recomputes from the current domains: the forward
propagator's thresholds, pair bounds and support scans, and the matching
propagator's active site set and matchings. The paper's advisor-based
scheduling, which skips pairs whose domains have not changed, is deliberately
not implemented (`min-distance-proofs.md`, "Deliberately not implemented"): it
would buy time, not search or proofs, and it would need an advisor mechanism
GCS lacks.

### Interior values and optional pruning

**Offers.** `None.` There is no optional-interior-pruning pair.

**Observes.** Holes in `x` matter to both real propagators. `z` is read by its
bounds only, except that the check-only propagator declares it through
`scope_only`; see the inventory.

### Robustness and limits

**Unbounded domains.** `z` is fine at any width: it is read by bounds and
encoded per level. `x` is pinned to `0..n−1` before any propagator runs, so its
cost is in `n`, the matrix size, not in the declared width.

**Negative values and zero.** A negative `z` lower bound is legal and tested
(`z ∈ −2..6`, and random windows from −1); it is never raised to 0 before `x`
is fixed, since no rule raises `z`'s lower bound. A zero off-diagonal distance
is tested (`d3_zero`). Negative distances and requirements are rejected.

**Degenerate shapes.**
- **`p > n`,** with `z ≥ 1`, is infeasible by pigeonhole. No mode notices at the
  root: over three sites 4 apart with `p = 4` and `z ∈ 1..9`, `ForwardBound`,
  `PairSupport` and both matching modes fail after 10 recursions, `CheckOnly`
  after 49, and the
  proofs verify (`mdfam pigeon`). The matching modes reach `z ∈ 1..3` at the
  root; with the stronger guard under [Rule:
  matching-bound](#rule-matching-bound), the experiment build fails the root.
- **A repeated variable** is sound in every mode and its proofs verify, the
  matching's included, where the same literal appears twice in a clique: 750
  random enumerations with one aliased pair (`sweep.sh alias`, all matching the
  brute force) and the prototype with `x₃ = x₀` (`mdfam protoalias`, `z ≥ 1`
  unsatisfiable, and `protoalias0`, optimum 0). Nothing propagates the alias
  before it is fixed: at the root, `PairSupport`'s domains keep 1,850 values
  with no pairwise support once the alias is counted (2,000 instances, seed 1).
- **A constant position** is tested. **An empty `x`** is rejected (`p ≥ 2`).

**Overflow.** Nothing reachable now. Since #1215 a distance or requirement
outside `±(2⁶⁰ − 1)` is refused at construction, and since #1214 so are a
view offset and a declared domain outside that range. Every shape below needs
one of those, and at `0a5b4ec6` each is refused with `IntegerOverflow`: a
distance of `2⁶³ − 16`, `2⁶³ − 1`, `2⁶³ − 2⁶¹`, `2⁶²` or `2⁶⁰`, a `z` over
`−2⁶¹..2⁶¹ − 1`, and the views `w − (2⁶³ − 100)` and `w − 2⁶²`, while `2⁶⁰ − 1`
is accepted (`tmp/fd871-comments-1008/ordsmall/probes/min_distance/refuse.cc`).
At the edge, `integer_ranges_test` solves two positions over two sites at
distance `2⁶⁰ − 1` in all five modes, with `z` plain over the whole range or a
view at either end of it (`w ± (2⁶⁰ − 1)`, `−w ± (2⁶⁰ − 1)`), with and without
proofs, against brute force, and every proof verifies. The propagators and
`define_proof_model` did not change, so the shapes would come back if the
range were widened; [Next steps](#next-steps) item 3 lists their fixes.

The audit's record, at `c9ceea25` (its present tense and line numbers are
that commit's): for a plain `z`, two
shapes threw, both needing a distance within `2⁶¹` of `2⁶³`. An offset view on
`z` moved both thresholds by its offset, and added a third, with proofs off:
- **`define_proof_model`, when `z`'s lower bound is negative.** The ladder
  writes `[z ≥ t]` for every level above `z_lo`, including levels above `z_hi`,
  and reifying a `≥` literal far above a signed bit encoding overflows (from
  `min_distance.cc:249`, through `need_gevar` → `reify` → `reification_shape`;
  gdb). With `x` over two sites and `z ∈ −1..10`, `D = 2⁶³ − 16` verifies, `2⁶³
  − 15` throws a `ProofError` ("reification constant … the most negative
  Integer") and `2⁶³ − 14` up to `2⁶³ − 1` an `IntegerOverflow` (`-16 +
  -9223372036854775807`). With `z` over the widest domain, `−2⁶¹..2⁶¹ − 1`, it
  throws from `2⁶³ − 2⁶¹` up. A plain non-negative `z` never throws. A view
  moves the threshold by its offset, since the ladder's `[z ≥ t]` is `[w ≥ t −
  offset]`: with `z = w − (2⁶³ − 100)` and `w ∈ 0..10`, `D = 100` throws
  `IntegerOverflow` from `:249` under `ForwardBound` and `D = 99` verifies (the
  fact-check's `ov.cc`, re-run here; `D = 1000` throws under `PairSupportMatch`
  too); the fact-check also has `z = w − 2⁶²` throwing at `D = 2⁶²` and not at
  `1.5 · 2⁶¹`. For a plain `z`, with proofs off, this shape did not throw. The
  same class as #1117 (`table`), also closed by #1215.
- **`CheckOnly`'s pair bound**, `infer_less_than(z, D[a,b] + 1)`
  (`min_distance.cc:328`), overflows at `D[a,b] = 2⁶³ − 1` once both endpoints
  are fixed, **with proofs off too**. The forward propagator's pin does the
  `≥` half first, which fails before its `+ 1` can run, and its pair bound only
  runs below `ub(z)`, so for a plain `z` the default modes do not throw.
- **The pins, through an offset view on `z`, with proofs off, in every mode.**
  The full-assignment pin infers `z ≥ μ`, which the view turns into `w ≥ μ −
  offset`, and that overflows. With `z = w − (2⁶³ − 100)`, `w ∈ 0..10` and `x`
  over two sites, the four real modes throw `IntegerOverflow` (`100 -
  -9223372036854775708`) from `D = 100` and are fine at 99, and `CheckOnly`
  throws from `D = 99`; with `z = w − 2⁶²` all five throw at `D = 2⁶²` and not
  at `2⁶² − 20` (`view_overflow_proofs_off.txt`). gdb puts the throw at the
  forward propagator's pin (`min_distance.cc:535`) and the check-only one's
  (`:350`). With proofs on, the ladder (`:249`) throws first. So stopping the
  ladder at `z_hi` (next step 3) does not fix the view shape.

Everything else compares or subtracts values of one matrix or one domain.

### Interval efficiency

**Fine at any width.** `z` is bounds-only everywhere, and `x` cannot be wider
than `n`.

1. **The propagation side.** Every value walk is over an `x` domain, and every
   `x` domain is inside `0..n−1`: the forward prune (`O(n)` per fixed
   endpoint), the pair bound (`O(|dom x_i| · |dom x_j|)` per pair), the support
   scan (the same, per pair, under `PairSupport`), and the matching's active
   set (`O(p · n)`) and greedy matchings (`O(|A|²)` per probe, `O(log L)`
   probes). So a call is up to `O(p² · n²)`, bounded by the matrix, not by any
   width. `prepare()`'s site loop is `O(p · n)` in-domain tests. `z` is never
   walked.
2. **The reason side.** Every reason is `generic_reason` over one, two or all
   of `x`, materialised by runs (#935) and only when a proof wants it, or a
   short `ExplicitReason`. Constructing one copies a variable list per
   inference even with proofs off; nothing calls `want_reasons()`.
3. **The proof side.** Two sites emit a line per value, both bounded by `n`:
   the pair bound's per-value lemmas over the smaller endpoint domain, and the
   matching's pairwise clauses over the sites' literals. The matching's
   at-least-one per position has **two forms, chosen by width**: the per-value
   at-least-one over the variable's whole definition range when that range is
   at most 100 values, and a cover of its still-possible sites above that
   (#939; `at_least_one_cover_threshold = 100_i`,
   `names_and_ids_tracker.cc:93`, tested at `:681`). The threshold is on the
   declared range: a position declared over more than 100 values gets the
   cover: any instance whose `x` is declared over more than 100 sites
   (`p_dispersion`'s are, from 101 sites up), and a narrower model whose `x` is
   declared wider and then clamped. Every instance measured here where the matching
   fires (grids up to 10 × 10, whose `0..99` is exactly 100; the 20- to 40-site
   random instances; the prototype) is at or below it, so uses the per-value
   form; a 120-site random instance under `PairSupportMatch` writes cover-form
   at-least-ones. The gate is on width, except that a variable with no bits, or
   a view the tracker has not registered, always takes the per-value form
   (`names_and_ids_tracker.cc:690`, `:703`). The encoding is per level, not per
   value of `z`.
4. **The audit lane.** One row, `MinDistance`, `Clean`: two positions over
   `{0, 1}` with a wide `z`, under the default mode
   (`large_domain_audit_test.cc:843`). The `[.proofscaling]` survey measures it
   at 24 OPB lines and 38 proof lines at widths 10³ and 10⁴ alike. The row does
   not vary: a **wide `x`**, so the `define_bound` clamp is never exercised;
   holes; views; `R`; or the other four modes. It has no row in the `"Large
   domain proof sizes"` case, and none is needed while `z` stays bounds-only.

## Inference catalogue

Nine rules. Rules 1–3 belong to the check-only propagator (rule 3 also to the
forward one), 4–7 to the forward propagator, 8–9 to the matching propagator.
The numbering follows the code.

Facts that hold for every rule:

- **Every rule is certified, by procedures of our own.** None is a published
  justification procedure. The RUP rules go through the definitional flags:
  `[x_i = a]` sets `u_a` by its reification, two `u`s fire a pair clause, and
  within `z` Theorem 3.3 carries a `[z ≤ D]` or `[z ≥ t]` to any weaker literal.
  Rule 5 is JP 3.9's shape (per-value lemmas, then a collapse by an
  at-least-one) with a bound as the conclusion, and rule 8 is JP 3.16's Hall
  pigeonhole with a guard literal riding through it.
- **No hint.** Every rule passes `JustifyUsingRUP{}` or
  `JustifyExplicitly{…}` with the default `NoHint`, so at the assertion levels
  its `a` line carries no `::` annotation at all: on the 5 × 5 grid with
  `p = 6` below, 16,475 of `PairSupportMatch`'s assertions at `Definitions`, all
  bare. A reconstructor must recognise the rule from the clause's shape. The
  shapes do differ (a `z` upper bound with two positions' domains; a `≠`
  with one fixed position and a `z` bound; a `z` bound with every position's
  domain), but nothing states them.
- **No rule is weakened with proofs on.** The propagators never test for a
  logger.

### Rule: check-requirement

- **Infers** — a contradiction.
- **Fires when** — the check-only propagator (`CheckOnly`) finds two fixed
  endpoints `x_i = a`, `x_j = b` with `D[a,b] < R_ij`.
- **Strength** — `checker`, per pair.
- **Algorithm** — `O(p²)` over the fixed positions, per call.
- **Why it is true** — the requirement says `D[x_i, x_j] ≥ R_ij`.
- **Proof technique** — `RUP`: the requirement clause
  `¬[x_i = a] ∨ ¬[x_j = b]` has both literals false under the reason.
- **Reason** — the two fixed positions, `generic_reason({x_i, x_j})`: two
  literals. Minimal.
- **Assertion** — `¬reason`, an explicit `contradiction()`.
- **Hint** — none.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: check-pair-bound

- **Infers** — `z ≤ D[a,b]`.
- **Fires when** — the check-only propagator finds `x_i = a`, `x_j = b` fixed.
  It infers for every fixed pair on every call, most of them no-ops.
- **Strength** — `partial`: `z`'s upper bound from fixed pairs only.
- **Algorithm** — as rule 1.
- **Why it is true** — `z` is at most every selected pair's distance.
- **Proof technique** — `RUP`. For `a ≠ b`: `u_a` and `u_b` from their
  reifications, then the pair clause. For `a = b`: the count row forces
  `[z ≤ 0]`. When the pair clause was omitted (`z_hi ≤ D[a,b]`) the inference
  is a no-op.
- **Reason** — the two fixed positions. Minimal.
- **Assertion** — `z ≤ D[a,b] ∨ ¬reason`; a conflict (when `z`'s lower bound
  exceeds `D[a,b]`) is the same line.
- **Hint** — none.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: full-assignment-pin

- **Infers** — `z ≥ μ`, then `z ≤ μ`, where `μ` is the minimum pairwise
  distance of the fixed positions.
- **Fires when** — every position is fixed; in the check-only and the forward
  propagators alike.
- **Strength** — `checker`: this is what makes a full assignment with the wrong
  `z` fail.
- **Algorithm** — `O(p²)`.
- **Why it is true** — the definition.
- **Proof technique** — `RUP`, each half. The lower half is the ladder: with
  every `x` fixed, unit propagation fixes every `u`, `d`, `w` and `m` flag, and
  `[z ≥ μ] ∨ m` at level `μ` (a level, since `μ` is `0` or a candidate pair's
  distance) has `m` false. The upper half is the closest pair's clause, or the
  count row when `μ = 0` by a duplicate.
- **Reason** — every position, `generic_reason(x)`: `p` literals. The upper
  half needs only the closest pair's two.
- **Assertion** — `z ≥ μ ∨ ¬reason` and `z ≤ μ ∨ ¬reason`. Measured at
  `Inferences`, a 3 × 3 grid with `p = 4` under `PairSupport`:
  ```
  a 1 i[z][ge10] 1 ~i[x[0]][eq0] 1 ~i[x[1]][eq1] 1 ~i[x[2]][eq2] 1 ~i[x[3]][eq3] >= 1;
  ```
- **Hint** — none.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line each.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: forward-prune

- **Infers** — `x_j ≠ b`.
- **Fires when** — the forward propagator finds `x_i` fixed to `a` and `D[a,b]
  < T_ij = max(R_ij, lb z)`, for every pair `(i, j)` in both directions.
- **Strength** — `partial`: forward checking on each pair's binary constraint
  `D[x_i, x_j] ≥ T_ij`. Under `ForwardBound`, 473 values across 167 of 2,000
  random root fixpoints still lack a pairwise support, which rule 7 removes
  (`mdcheck.cc fb`, seed 1).
- **Algorithm** — `O(n)` per fixed endpoint and pair.
- **Why it is true** — with `x_i = a` and `x_j = b`, either the requirement
  fails (`D[a,b] < R_ij`) or `z ≤ D[a,b] < lb z`.
- **Proof technique** — `RUP`: `u_a` from `[x_i = a]`; assuming `[x_j = b]`,
  `u_b`, then the pair clause (or, for `b = a`, the count row) gives
  `[z ≤ D[a,b]]` against `z ≥ lb z`; or the requirement clause directly.
- **Reason** — `x_i = a`, plus `z ≥ lb z` only when `z` carries the threshold
  (`D[a,b] ≥ R_ij`). Minimal.
- **Assertion** — `x_j ≠ b ∨ ¬reason`. Measured at `Inferences`, the matching
  prototype under `PairSupportMatch`:
  ```
  a 1 ~i[x[2]][eq0] 1 ~i[x[0]][eq0] 1 ~i[z][ge1] >= 1;
  ```
- **Hint** — none.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: pair-upper-bound

- **Infers** — `z ≤ u_ij`, where `u_ij = max{D[a,b] : a ∈ dom x_i, b ∈ dom
  x_j, D[a,b] ≥ R_ij}`.
- **Fires when** — the forward propagator finds that set non-empty with
  `lb z ≤ u_ij < ub z`, for any pair.
- **Strength** — `partial`: `z`'s upper bound is the least of the pairwise
  maxima, the paper's `pair-forward-bound`. It is not `bounds(D)` on `z`: at
  2,000 random root fixpoints `z`'s upper bound has no support in 615 of the
  1,382 satisfiable instances under `PairSupport`, and 632 under `ForwardBound`
  (`mdcheck.cc`, seed 1).
- **Algorithm** — `O(|dom x_i| · |dom x_j|)` per pair.
- **Why it is true** — whichever sites `x_i` and `x_j` take, their distance is
  at most `u_ij` or they break the requirement; either way `z ≤ u_ij`.
- **Proof technique** — `RUP sequence`, ours, JP 3.9's shape: for each `a` in
  the smaller endpoint domain, the lemma `¬[x_loop = a] ∨ [z ≤ u_ij]` by RUP
  (every partner `b` dies by its pair clause once `z > u_ij`, or by the
  requirement clause, and the partner's domain closes it); then the conclusion
  by RUP from the lemmas and `x_loop`'s domain (`ThenRUP::Yes`).
- **Reason** — both endpoints' domains, `generic_reason({x_i, x_j})`, by runs.
  No `z` literal: negating the conclusion supplies it.
- **Assertion** — `z ≤ u_ij ∨ ¬reason`. Measured at `Inferences`, the 3 × 3
  grid under `PairSupport`:
  ```
  a 1 ~i[z][ge23] 1 ~i[x[0]][eq1] 1 ~i[x[1]][ge6] 1 i[x[1]][ge9] 1 i[x[1]][eq7] >= 1;
  ```
- **Hint** — none.
- **Offline reconstructibility** — `offline`: the two positions, their
  domains and `u_ij` are in the clause, and either endpoint works as the loop.
- **Proof size** — `|dom x_loop| + 1` lines, at most `n + 1`, each carrying the
  two-domain reason.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: pair-infeasible

- **Infers** — a contradiction.
- **Fires when** — the forward propagator finds no `D[a,b] ≥ R_ij` over the two
  domains, or its maximum below `lb z`.
- **Strength** — `partial`, as rule 5.
- **Algorithm** — as rule 5.
- **Why it is true** — no choice of the two sites satisfies both the
  requirement and `z`'s lower bound.
- **Proof technique** — `RUP sequence`, as rule 5, with lemmas `¬[x_loop = a]`
  and a closing contradiction.
- **Reason** — both endpoints' domains, plus `z ≥ lb z` when some pair
  satisfies the requirement (so the `z` bound is what kills it).
- **Assertion** — `¬reason`, an explicit `contradiction()`.
- **Hint** — none.
- **Offline reconstructibility** — `offline`.
- **Proof size** — as rule 5.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: pair-support

- **Infers** — `x_i ≠ a`.
- **Fires when** — under `PairSupport` and `PairSupportMatch` only, no `b ∈ dom
  x_j` has `D[a,b] ≥ T_ij`, for any ordered pair.
- **Strength** — `partial`: arc consistency on every pair's binary constraint
  `D[x_i, x_j] ≥ max(R_ij, lb z)`, on distinct variables. At the root, no value
  is left without a pairwise support in 6,000 random instances (`mdcheck.cc ps`
  and `psm`, seeds 1–3), and `min_distance_test` checks the invariant at every
  search node. Not GAC: 2,273 of 11,339 values left have no support in the whole
  constraint, in 486 of 2,000 instances (seed 1). Weaker with a repeated
  variable, which it treats as two.
- **Algorithm** — `O(|dom x_i| · |dom x_j|)` per ordered pair, stopping at the
  first support.
- **Why it is true** — `x_i = a` would leave `x_j` no value compatible with the
  requirement and `z`'s lower bound.
- **Proof technique** — `RUP`, one line: assuming `[x_i = a]`, each `b` in
  `x_j`'s domain dies as in rule 4, and `x_j`'s domain closes.
- **Reason** — `x_j`'s domain, plus `z ≥ lb z` when `lb z > R_ij`. `a` itself
  is not in it.
- **Assertion** — `x_i ≠ a ∨ ¬reason`. Measured at `Inferences`, the 3 × 3
  grid, with `x₃ ∈ 4..8` minus 5:
  ```
  a 1 ~i[x[2]][eq7] 1 ~i[x[3]][ge4] 1 i[x[3]][ge9] 1 i[x[3]][eq5] 1 ~i[z][ge11] >= 1;
  ```
- **Hint** — none.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.` **Tightness** — `Not shown.`

### Rule: matching-bound

- **Infers** — `z ≤ t − 1`, where `t` is the refuted distance level in
  `max(lb z, 1)..ub z` that the binary search settles on.
- **Fires when** — the matching propagator (`…Match` modes), on any change to
  `x` or `z`'s bounds, finds a level `t` whose conflict graph over the active
  sites `A` (the union of the `x` domains; `a ~ b` when `D[a,b] < t`) has a
  greedy maximal matching `M` with `|A| − |M| < p`.
- **Strength** — `partial`: a relaxation of the independent-set bound on `z`.
  With it, `z`'s root upper bound has no support in 389 of the 1,382
  satisfiable instances under `PairSupportMatch`, against 615 under
  `PairSupport` (seed 1).

  **It infers less than its certificate proves.** The conflict graph for any
  `t′` in `(t*, t]`, where `t*` is the largest off-diagonal distance below `t`
  (or 0), is the same graph, so the matching that refutes `t` refutes `t* + 1`,
  and the conclusion could be `z ≤ t*`. The derivation is unchanged but for the
  guard literal: each cross-site clause's pair has `D[a,b] < t`, hence `D[a,b]
  ≤ t*`, and the same-site clauses give `z ≤ 0 ≤ t*`.
  [`min-distance-proofs.md`](../min-distance-proofs.md) argues that `z ≤ t*`
  is not RUP from `z ≤ t − 1`, which is true, but it never needs to be derived
  from it.

  An experiment build of `c9ceea25` with the guard at `t*`, switched by an
  environment variable, measured it
  (`tmp/fd-small/min_distance/tstar-guard.patch`, not for commit).
  `p_dispersion --random-euclidean 20 --points 6 --seed 1 --span 1000`:
  `PairSupportMatch` from 2,816 recursions to 1,380, with 7.62 MB of proof to
  6.83 MB and 4.84 s of checking to 3.68 s; `ForwardBoundMatch` from 3,148 to
  1,823. The same instance with 30 and 40 sites: 15,251 to 11,817 and 29,088 to
  24,216 (`PairSupportMatch`, proofs off). Over seeds 1–7 at 20 sites
  (`PairSupportMatch`, proofs off, `tstar_seeds.txt`), it cuts 26 to 52% with
  six positions, 5 to 58% with eight (40 to 58% on four seeds, 3, 4, 5 and 7; 5
  to 16% on the other three, 1, 2 and 6) and 0 to 8% with four. At 30 and 40
  sites the fact-check found six positions cutting only 0 to 37% (seeds 2–4)
  and eight cutting 54 to 57% at 30 sites (seeds 2–4). The pigeonhole shape
  under [Robustness](#robustness-and-limits) fails at the root instead of
  stopping at `z ∈ 1..3`, and the matching test's prototype gets `z ≤ 3` where
  the test pins `4` (39 recursions to 26). Grids do not change: rounded grid
  distances are consecutive integers, so `t* = t − 1`. Every proof the
  experiment wrote verified: the instances above, and 2,400 random enumerations
  under both `…Match` modes, plain, with a repeated variable and with a negated
  view, half of them with distances spread ten apart so that `t*` falls well
  below `t − 1` (the stronger guard changed the proof on 50 of 100 of those
  checked), all matching a brute force
  (`tmp/fd-small/min_distance/sweep_exp.sh`).
- **Algorithm** — the active set, `O(p · n)`; a binary search over the levels,
  each probe a greedy matching in `O(|A|²)`; the greedy matching is only weakly
  monotone in `t`, so the search finds a refuted level, not necessarily the
  smallest (paper §4.4).
- **Why it is true** — if `z ≥ t ≥ 1`, the `p` positions take `p` distinct
  sites pairwise at least `t` apart, an independent set of size `p` in the
  conflict graph; any independent set misses an endpoint of every matched edge,
  so has at most `|A| − |M| < p` members.
- **Proof technique** — `counting argument`, by a `RUP sequence` and a `pol`,
  ours, JP 3.16's pigeonhole under the guard `g = [z ≤ t − 1]`: per matched
  edge and per unmatched site, a guarded at-most-one over the positions' `= site`
  literals, from pairwise clauses `¬l ∨ ¬l′ ∨ g` (each RUP: cross-site by the
  pair clause, same-site by the count row, same-position by the variable's own
  at-most-one) folded by `recover_am1_from_pairs` with the guard at coefficient
  `|L| − 1`, each pinned by an `ia`; then each non-constant position's
  at-least-one (per value over its definition range up to 100 values, else a
  cover of its still-possible sites; see [Interval
  efficiency](#interval-efficiency)); one `pol` sums and divides by the
  total guard coefficient, leaving `g`; then the conclusion by RUP. The
  preconditions are `t ≥ 1` (the same-site clauses need `z ≤ 0 < t`) and that
  the literal sets range over the positions whose install-time domain holds the
  site, which the encoding's rows name.
- **Reason** — every position's domain, `generic_reason(x)`, by runs; no `z`
  literal.
- **Assertion** — `z ≤ t − 1 ∨ ¬reason`. Measured at `Definitions`, the
  prototype under `PairSupportMatch`, at the root:
  ```
  a 1 ~i[z][ge5] 1 ~i[x[0]][ge0] 1 i[x[0]][ge5] 1 ~i[x[1]][ge0] 1 i[x[1]][ge5] … 1 i[x[3]][ge5] >= 1;
  ```
- **Hint** — none; not even the matching, the level or the active set.
- **Offline reconstructibility** — `search`, and cheap: `t` is in the clause,
  `A` in the reason, and `D` in the `.scp`, so a reconstructor rebuilds a
  maximal matching of the conflict graph in `O(|A|²)` (the solver's greedy one
  is deterministic, and any matching with `|A| − |M| < p` will do), then writes
  the counting derivation. Nothing solver-side is needed.
- **Proof size** — per edge `C(|L_ab|, 2)` guarded clauses with `|L_ab| ≤ 2p`,
  per unmatched site `C(|P_c|, 2)`, so `O(|A| · p²)` RUP lines; a fold of `|L|
  − 1` `pol`s and one `ia` per clique; an at-least-one per position on its
  first use only in the per-value form, which the tracker caches at
  `TopAndCore` (in the cover form, one per distinct cover, cached at `Top`);
  one summing `pol`; the closing RUP. The prototype's root inference, the first
  use, is 85 lines: 62 guarded clauses, four at-least-ones, 14 fold `pol`s,
  three `ia` pins, one sum and one closing RUP.
- **Gaps** — `None.`
- **Tightness** — shown once, not in the tree: #805 removed the `ia` pin and
  found `DropAnAtMostOne`, `NaiveOneShot` and `SkipFinalDivision` each rejected
  at this call site (recorded in `am1_from_pairs.hh`). `am1_from_pairs_test`
  runs lanes on the helper itself in "min_distance's shape", with the guard
  riding through: honest control lanes on synthetic cliques of 2 to 12 members,
  and guarded mutation lanes on cliques of 2 to 9.

### Rule: matching-contradiction

- **Infers** — a contradiction.
- **Fires when** — as rule 8, with the refuted `t ≤ lb z`.
- **Strength**, **Algorithm**, **Why it is true**, **Proof technique**,
  **Proof size**, **Gaps**, **Tightness** — as rule 8, closing by RUP against
  `z ≥ lb z`.
- **Reason** — every position's domain, plus `z ≥ lb z`.
- **Assertion** — `¬reason`, an explicit `contradiction()`.
- **Hint** — none.
- **Offline reconstructibility** — `search`, as rule 8.

## Evidence

### Tests

- **`min_distance_test`** (`min_distance_constraint`, plus
  `min_distance_constraint_view_mixed`): seven malformed-definition rejections,
  then 19 fixed specs and eight random instances (`n` up to 5, `p` up to 4,
  distances up to 4, half with `R`), each under all five modes, without and
  with proofs. The fixed specs cover `p = 2` to 4, tied distances, a zero
  off-diagonal distance, `z` with a hole, offset and negative, holey and
  partial `x` domains, a constant position, and feasible, duplicate-forbidding,
  infeasible and heterogeneous `R`. Plain `solve_for_tests` against a brute
  force of the definition, **no consistency check**, except that the two
  `PairSupport…` modes check the pairwise-support invariant at every node.
  VeriPB runs on every proof: 135 per run. Seeded.
- **`min_distance_matching_test`** (`min_distance_matching`): the directed
  prototype (five sites, `D = 5` but `D[0,1] = D[2,3] = 3`, `p = 4`), where only
  the matching can lower `z`: it checks the root bound drops to 4 under both
  `…Match` modes and stays at 5 under the other two, that `z = 5` fails at the
  root, and verifies four proofs (`s VERIFIED BOUNDS -3 <= obj <= -3` and the
  infeasible pair).
- **`scp_reader_test`**: two cases, see [Cake conformity](#cake-conformity).
- **`am1_from_pairs_test`**: the guarded fold, on synthetic cliques.
- **Audit lane:** the `MinDistance` row.
- **`p_dispersion`** (ctest): runs the binary's defaults, which is the `tuple`
  decomposition on a 3 × 3 grid. **It never posts `MinDistance`.**

**Runtime caps.** No lane sets or clears one, and the defaults never fire: 24
runs (seeds 1–12, plain and `view_mixed`), all complete, no `truncated run`,
at most 256 solutions per solve (`GCS_TEST_MAX_SOLUTIONS=300
GCS_TEST_MAX_RECURSIONS=1500 min_distance_test --seed=N`, at `c9ceea25`).

**Tightness:** see rule 8. No lane mutates any other rule.

**What the tests do not cover.**

- **Repeated variables.** No spec aliases a position; this audit's sweep did.
- **A wide `x`,** which only the clamp would see; and `n` beyond 5, so neither
  the `Θ(L · n²)` build nor the `O(p² · n²)` calls show up as cost.
- **Distances near `2⁶³`** need no test now: they are refused at
  construction (#1215). `integer_ranges_test` covers the refusal of a
  distance one past either end of the range (requirements are checked but
  have no refusal case), and solves at the largest in-range distance in all
  five modes, with `z` plain or a view at either end, with and without
  proofs; see [Robustness](#robustness-and-limits).
- **Strength.** Nothing checks the `…Match` modes' `z` bound beyond the one
  prototype, and nothing checks `ForwardBound`'s forward checking at all, beyond
  the solutions.
- **The mode round trip through the `.scp`,** which resets to `ForwardBound`.
- **The assertion levels.** No lane runs them; `Links` fails the generic way on
  about 4% of small random instances (see [Proof
  performance](#proof-performance)).
- **Real instances:** none. `p_dispersion --file` reads MDPLIB, and no test
  runs one.

### Benchmarks and examples

- **In the repository:** `examples/p_dispersion`, maximising `z` over grid,
  random Euclidean or MDPLIB-file instances, with `--variant` choosing the
  `tuple` decomposition or one of the five modes, and `--homogeneous-req` or a
  file for `R`. Its ctest uses `tuple` only.
- **Corpus:** none can reach it; no frontend binds it.
- **For CPU:** `p_dispersion --grid 10x10 --points 10`, the design note's
  benchmark: the four real modes prove the optimum in 42 to 70 s and `tuple`
  in 98 s, and the `…Match` modes separate. `CheckOnly` does not finish in
  300 s.
- **For proof verification:** `--grid 5x5 --points 6`, which verifies in 2 to
  15 s per mode; `--grid 4x4 --points 4` for a quick one. The random Euclidean
  roots above for the encoding: do not prove at `n = 400` or more unless the
  build cost is the point.

### CPU performance

*Release build of `c9ceea25` (GCC 15.2.0, `-O3 -march=native`); fataepyc-10,
boost off, pinned to one core, fixed malloc thresholds; `p_dispersion` wall
time, proofs off, `--grid 10x10 --points 10 --initial-lb 1`, branching in order
over `x` then `z`; 2026-09-30.*

| Variant | Recursions | Propagations | Time | Per recursion |
|---|---|---|---|---|
| `tuple` (`Element2DConstantArray` + `ArrayMin`) | 1,470,678 | 93,198,652 | 97.7 s | 66 µs |
| `CheckOnly` | over 66.9M | — | over 300 s | — |
| `ForwardBound` | 2,260,878 | 2,492,981 | 60.4 s | 27 µs |
| `PairSupport` | 1,470,678 | 1,704,253 | 69.7 s | 47 µs |
| `ForwardBoundMatch` | 1,474,396 | 1,835,505 | 46.6 s | 32 µs |
| `PairSupportMatch` | 595,420 | 855,073 | 42.1 s | 71 µs |

Medians of three, each within 1.3%; every run proves `z = 4` optimal.
`CheckOnly` timed out twice at 300 s, after 68.6M and 66.9M recursions, and
was not run a third time. `PairSupport` explores exactly the decomposition's
tree (the same 1,470,678 recursions, in the decomposition's default `BC` for
`Element`) at 1.4 times its speed, with 55 times fewer propagations. The
matching pays for itself: it costs `PairSupport` about 1.5 times per node and
cuts its tree 2.5 times, so `PairSupportMatch` is the fastest mode and the
default, `ForwardBound`, is 1.4 times slower. The `x` domains are 100 wide and
every call rescans every pair, so the per-node cost is the `O(p² · n²)` of
[Interval efficiency](#interval-efficiency); the paper's advisors would attack
that. A grid never reaches the `t*` difference of rule 8.

**Not a regression.** The design note's much smaller times (under
[Proof performance](#proof-performance)) are the machine's: the July merge of
the matching (`4a337e68`) built here takes 67.6 s for `PairSupport` and 40.6 s
for `PairSupportMatch` on the same instance and core, one run each, against
69.5 s and 42.1 s for `c9ceea25` run beside it: the same trees, and about 3%
between the builds, which one run each cannot separate from layout noise and
this audit did not chase.

**Against another solver: `Not measured.`** Gecode 6.3.0 has no
minimum-distance global (nothing in its headers), and the paper's
implementation is not part of it. A decomposition in another solver would
search a different tree, so a wall-clock ratio would not isolate the
propagator.

### Proof performance

*Same build and machine; VeriPB 3.0.2 with `--force-checked-deletion`, its own
`--stats` total.*

**`p_dispersion --grid 5x5 --points 6`**, maximising, each mode proving `z = 2`
optimal:

| Variant | Recursions | Proof lines | Proof bytes | VeriPB |
|---|---|---|---|---|
| `tuple` | 1,505 | 264,851 | 27.2 MB | 12.4 s |
| `CheckOnly` | 100,451 | 498,591 | 17.9 MB | 15.3 s |
| `ForwardBound` | 1,777 | 42,586 | 2.30 MB | 2.37 s |
| `PairSupport` | 1,505 | 37,039 | 2.06 MB | 2.13 s |
| `ForwardBoundMatch` | 1,209 | 64,058 | 3.54 MB | 2.81 s |
| `PairSupportMatch` | 669 | 63,783 | 3.60 MB | 2.39 s |

(medians of three checks, each within 1%. `tuple`'s is 12.4 to 12.5 s across
three sets of five on quiet cores: two here, 12.34 to 12.47 s and 12.37 to
12.44 s, medians 12.36 and 12.40 (`veripb_tuple.txt`), and the fact-check's,
median 12.5 s. An earlier set beside a build gave 13.8 s.) The matching more
than halves `PairSupport`'s tree and costs 1.75 times its proof bytes, for 12%
more check time. The dedicated constraint's proofs are 7.6 to 13 times smaller
than the decomposition's in bytes and check 4.4 to 5.8 times faster.

**Own against shared, and the assertion levels.** On the same instance:

| Mode | Level | Lines | Family assertions | VeriPB |
|---|---|---|---|---|
| `PairSupport` | `Off` | 37,039 | — | 2.13 s |
| | `Definitions` | 32,061 | 24,290 | 0.45 s |
| | `Links` | 32,055 | 24,290 | 0.43 s |
| | `Inferences` | 30,063 | 24,290 | 0.06 s |
| `PairSupportMatch` | `Off` | 63,783 | — | 2.39 s |
| | `Definitions` | 22,908 | 16,475 | 0.24 s |
| | `Links` | 22,902 | 16,475 | 0.24 s |
| | `Inferences` | 18,904 | 16,475 | 0.04 s |

The `Off` times are the medians above, the others single checks. Every family
assertion is bare (no hint). `Definitions`, `Links` and `Inferences` are
accepted under assertions (`s UNDER ASSERTIONS`) here, and so are all four
probe shapes (enumeration, with `R`, the prototype and a 3 × 3 grid) under all
five modes, all of which branch in order, smallest value first. But `Links`
does fail, the generic way: over 200 random small instances in each of the five
modes (`n ≤ 6`, `p ≤ 4`, split and random branching), 42 of the 1,000 proofs
end in `Error: Checking error` at `Links`, in every mode, at a backtracking
RUP, usually after a `solx` (seven are unsatisfiable runs with none); the
smallest (two positions over two sites, `z ∈ 0..1`) fails on a RUP over a
one-bit variable.
The same 1,000 are accepted under assertions at `Definitions` and `Inferences`
(the fact-check's `ts.cc`). Only `Off` checks the family. Under `PairSupport`
the derivations add about 1.2 lines per inference (37,039 lines at `Off`
against 32,061 with the 24,290 inferences asserted); under `PairSupportMatch`
about 3.5 (63,783 against 22,908 with 16,475), the matching's 871 clique folds
being most of the difference. Everything not a family assertion at
`Definitions` (7,771 and 6,433 lines) is the shared layers, branching and the
objective.

**The root, alone.** From the random Euclidean roots above, VeriPB checks the
root in 0.03 s at `n = 50`, 0.13 s at 100 and 0.46 s at 200 (`NO CONCLUSION`,
proofs of 10,166, 38,686 and 132,524 lines, about half of them `core id -1` and
most of the rest order-chain `pol`s for `z`'s literals). So checking the
encoding is cheap; building it is not.

**Figures measured elsewhere.** `min-distance-proofs.md` reports the 5 × 5 grid
at 1.96 MB and 0.68 s (`PairSupport`), 3.17 MB and 0.66 s (`PairSupportMatch`)
and 27.6 MB and 9.7 s (`tuple`), and the 10 × 10 grid at 595k nodes and 12.4 s
(`PairSupportMatch`), 1.47M and 20.9 s (`PairSupport`) and 1.47M and 32.4 s
(`tuple`), from "one release build on one machine", written in July 2026
(33618ea5 and d78882d3). The node counts match this audit's exactly. The times
do not, nor do the proof sizes (the `tuple` proof is 27.2 MB here and
`PairSupportMatch`'s 3.60 MB; #805's fold, which added `ia` pins and layered
`pol`s to the matching certificate, came after), and the two sets should not be
put in one table.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified at `Off`, with no `a` line, and the
propagators are the same with proofs on or off.

### Known limitations

- **`z`'s lower bound rises only when every position is fixed**, not even to
  `0` before then. A model that
  reads `z` elsewhere (a satisfaction model, or `z` in a sum) learns nothing
  from the sites still open; `p_dispersion` does not notice, since maximising
  supplies the lower bound.
- **Generalised arc consistency on `x` is out of reach** (independent set).
  `PairSupport` gives pairwise arc consistency only, and treats a repeated
  variable as two.
- **The matching bound stops short of what it proves** (rule 8).
- **With proofs, building the model is quadratic in the site pairs** when
  most distances are distinct: 26 s at 600 sites with 82,426 distinct
  distances.
- **No frontend reaches it,** and no `cake_pb_cp` rule checks its encoding.
- **Its assertions carry no hint.**

### Next steps

1. **Build the ladder from pairs sorted by distance.** One sort of the
   candidate pairs replaces the per-level scan: `O(n² log n)`, not `Θ(L · n²)`.
   Small, contained in `define_proof_model`, and the encoding is unchanged (the
   same rows in the same order). Would take `n = 600` from 26.4 s towards the
   1.35 s of the few-levels control. Filed as #1169.
2. **Guard the matching at `z ≤ t*`, not `z ≤ t − 1`.** A three-line change
   to the guard, the contradiction test and the inferred bound in
   `install_matching_propagator`, with the derivation unchanged; the argument
   and the experiment are under rule 8 (26 to 52% off the tree on 20-site
   random instances with six positions, 5 to 58% with eight, under 8% with
   four, none on grids). The matching test's expected root bound goes
   from 4 to 3, and `min-distance-proofs.md`'s paragraph on `z ≤ t − 1` goes.
   Filed as #1170.
3. **Stop the ladder at the first level above `z_hi`**, writing that level's
   clause as `m_k ≥ 1` and nothing above it: every higher clause is implied.
   That drops rows. **None of this audit's overflows is reachable now.** They
   were filed together as #1168, which #1215 closed (2026-10-04): a distance
   outside `±(2⁶⁰ − 1)` is refused at construction, as (since #1214) is a
   view offset outside that range, and `integer_ranges_test` solves at the
   largest in-range distance in all five modes, with a plain `z` and with
   views at either end, with and without proofs. If the range is ever
   widened, the fixes would be: the ladder stop above, for the
   `define_proof_model` overflow on a plain `z`; failing the node when `μ >
   ub(z)` rather than inferring `z ≥ μ` (or overflow-safe view arithmetic),
   for the pins through an offset view; and skipping `CheckOnly`'s pair bound
   when `D[a,b] ≥ ub(z)`, where it changes nothing, as the forward
   propagator's pair bound already does, so that `D[a,b] + 1` is never formed
   at `2⁶³ − 1`. Writing that bound as `z ≤ D[a,b]` is no fix: `operator<=`
   builds `z < D[a,b] + 1` itself (`variable_condition.hh:173–175`), and `z <=
   Integer::max_value()` throws `Integer overflow: 9223372036854775807 + 1`
   before any inference runs (`tmp/fd-codex-1005/small/probes/le.cc`).
4. **Raise `z`'s lower bound before everything is fixed:** `z ≥ min_{i<j}
   l_ij`, with `l_ij` the least distance two positions' domains allow (0 if
   they share a site), and at least `z ≥ 0`. `O(p² · n²)`, the same loop as
   `u_ij`. The justification is a `RUP sequence` through the ladder, one line
   per witness below the bound and no case split: if `D[a,b]` is below the
   bound, no two distinct positions can take `a` and `b`, so under the reason
   `w_ab` forces `u_a` and `u_b` and then both values on the one position that
   can take them, which the order encoding refutes; each `¬w_ab` (and `¬d_a`)
   is one RUP, and `z ≥ L` follows by RUP (checked by the fact-check's
   `zlb.cc`: the bare conclusion is rejected, three witness lines then the
   conclusion verify). Filed as #1171 for Ciaran to weigh, since the
   paper's use case does not need it.
5. **A `hints.hh`,** with a subhint per rule and, for the matching, the level
   and the matched edges. Not worth an issue on its own
   (`gcs-hint-sufficiency-is-empirical`); the justifier will show what it needs.
6. **Make the `p_dispersion` ctest post the constraint,** say `--variant
   min-distance-psm` on the default grid beside the `tuple` run, and add a
   repeated-variable spec to `min_distance_test`.
7. **Bring `min-distance-proofs.md` up to date:** its prototype certificate is
   "combined by 4 pol lines", and its cost `O(|M|)` pol lines, both from before
   #805's shared fold (now 14 fold `pol`s, three `ia` pins and one sum on the
   same instance, and a fold's worth of `pol`s per clique); its at-least-one is
   now the tracker's cached one, a cover of the still-possible sites above 100
   values of definition range (#939); and its figures are from another
   machine. And correct `read_min_distance`'s comment about `Z`.

## Prior art

Lagerkvist (ModRef 2026) gives the propagators this family implements, the
forward bound, the pair-support filtering and the conflict-matching bound, and
the heuristic `heur-aggr` variant this family deliberately omits because it
prunes without entailment. p-dispersion itself is an old facility-location
problem (Erkut, 1990; Kuby, 1987). As far as this audit knows no earlier
certified propagator exists for it: the encoding, the ladder and the guarded
counting certificate for the matching bound are ours, and the certificate
reuses the Hall-set pigeonhole of the all-different justification (Elffers,
Gocht, McCreesh and Nordström, AAAI 2020; McIlree's thesis, JP 3.16) with a
guard literal carried at an exact coefficient.

## Further reading

- [`min-distance-proofs.md`](../min-distance-proofs.md): the encoding row by
  row, including why the diagonal needs counts rather than `u_a`; why the
  check-only mode came first; each propagator's justification, the guarded
  counting derivation in full and the exact-coefficient induction; the
  measured trade-offs; and what was deliberately left out (the paper's
  `heur-aggr` and advisors). 348 lines; read it before changing a
  justification, and see next step 7 for where it is stale.
- [`constraints.md`](../constraints.md), "Worked examples": this family's
  check-only bring-up as the model for stage 1.
