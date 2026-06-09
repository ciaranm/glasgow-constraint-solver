# The Sort and ArgSort constraints

This document covers the `Sort` and `ArgSort` constraints (MiniZinc `sort`
and `arg_sort`): their semantics, the OPB encoding the solver uses for proof
logging, a survey of propagation algorithms, and the plan for certifying a
bounds-consistent propagator. For the general constraint-implementation
pattern see [constraints.md](constraints.md); for the MiniZinc bindings see
[minizinc.md](minizinc.md).

## Semantics

- **`Sort(x, y)`** — `y` is `x` sorted into non-decreasing order: `y` is a
  multiset-permutation of `x` and `y[0] <= y[1] <= ... <= y[n-1]`. `y` is a
  function of `x` (the sorted sequence is unique). MiniZinc `sort`, Gecode
  `sorted`.
- **`ArgSort(x, p, offset)`** — `p` is the **stable** sorting permutation:
  `p` is a permutation of `{offset, ..., offset+n-1}` with
  `x[p[j]-offset] <= x[p[j+1]-offset]` and the tie-break
  `x[p[j]] == x[p[j+1]] -> p[j] < p[j+1]`. The stable tie-break makes `p` a
  function of `x` too (unique). MiniZinc `arg_sort`, the verbatim stdlib
  `fzn_arg_sort_int` includes the tie-break clause. Core API is 0-based with
  an `offset`; the FlatZinc binding passes `offset = 1`.

XCSP3 has no sortedness constraint (only `ordered`, which orders an existing
sequence); this is a MiniZinc/Gecode/Choco/SICStus family.

## Consistency: what is achievable

Rusu (*NP-hardness of sortedness constraints*, TCS 2017 / arXiv 1506.02442)
proves **domain consistency (GAC) for `sort` is NP-hard**, even when the `x`
domains are pairwise disjoint, by reduction from Not-All-Equal-3SAT. The
permutation and stable variants are NP-hard too. So:

- **GAC is off the table** — do not attempt it.
- The practical target is **bounds consistency over interval domains**
  (`bounds(Z)`), which is what every real solver implements.
- Even there, only the **sorted (`y`) side** is cheaply made bounds-consistent;
  full bounds consistency on the **source (`x`) and permutation (`p`)** sides
  runs back into the hardness wall and is handled by weaker, costlier passes.

Both constraints run the Mehlhorn-Thiel bounds-consistent propagator (below),
achieving `bounds(Z)` on the source `x` and the sorted values. `ArgSort`
additionally runs a channel pass and GAC `all_different` on the permutation `p`
(see its section). No leaf checker is needed: once `x` is fixed the
achievable-rank-set propagator collapses each element's reachable ranks to its
single stable rank and prunes `p` to the unique permutation, so a bad `p` is a
domain wipeout before any leaf.

## The OPB encoding (proof model)

Both constraints must be defined in OPB for VeriPB. The design constraint that
shapes everything: **every proof-only auxiliary variable must be a function of
the core variables**, determined by unit propagation, or VeriPB cannot verify
solution (`solx`) lines (see
[the proof-only-aux memory rule] and the discussion in this file's history).

### Sort

`Sort` exposes the sorted values `y` as its real output and keeps the
permutation proof-only. The central constraint for VeriPB is **UP-determinism**:
every proof-only auxiliary variable must be uniquely determined by the real
variables (x and y) via unit propagation, or VeriPB cannot verify solution
(`solx`) lines.

The naive approach — "some permutation matrix `p[i][j]` with `p[i][j]=1 ⟹
y[j]=x[i]`" plus doubly-stochastic constraints — fails because with duplicate
`x` values, multiple permutation matrices satisfy the constraints equally well.
UP cannot pick the canonical one.

**The fix (current encoding):** make the permutation canonical by deriving it
from the *stable rank* of `x` — a function of `x` alone. The OPB model encodes
this in three layers:

```
before[ip][i]  ==  x[ip] comes before x[i] under the stable order (value, index)
               ==  (ip < i) ? (x[ip] <= x[i]) : (x[ip] < x[i])
               [fully reified flag, both halves in OPB]

rank[i][j]     ==  exactly j of the n-1 before-flags for row i are set
               [proof-only binary flag; OPB has forward-ge, forward-le, al1]

p[i][j]        ==  x[i] is placed at sorted position j  (equivalently y[j] = x[i])
               [proof-only binary flag]
```

Plus `y[j] <= y[j+1]` (sortedness) and the doubly-stochastic constraints
`Σ_j p[i][j] = 1` and `Σ_i p[i][j] = 1`, plus the p-rank link
`~p[i][j] + rank[i][j] >= 1` (wrong-rank positions cannot hold the element),
plus the channel `p[i][j] → y[j] = x[i]`.

**UP-determinism chain:** given a solution's `x` values, the OPB constraints
determine everything by unit propagation:

1. `before[ip][i]` ← x comparison (bidirectional reification pinned by fixed x)
2. For each row `i`, the unique `j*` with `Σ before = j*` forces `rank[i][j'] = 0`
   for all `j' ≠ j*` (forward-ge/le eliminate them), then the al1 forces
   `rank[i][j*] = 1`
3. `p[i][j'] = 0` for `j' ≠ j*` (p-rank link + rank=0) and `p[i][j*] = 1`
   (row al1 + all others excluded)
4. `y[j*] = x[i]` (channel)

This encoding is `O(n^2)` OPB constraints, **domain-width independent**.

**Why not the `dom` step (reviewer suggestion)?** A natural alternative — encode
just the doubly-stochastic p model, then use VeriPB's `def_order`/`dom`
mechanism to canonicalise p at proof time — was fully explored. The core insight
is that the before/rank flags *can* be defined as proof extension variables
(using `red` steps before `def_order`, making them regular proof variables
that the `dom` witness can reference). However, the `def_order` transitivity
proof for the canonical-condition constraints requires establishing
`v_rank = u_rank` across two O⪯ instantiations, which demands an explicit
multi-step pol chain through x-equality → bef-consistency → rank-consistency.
VeriPB's augmented-format autoprovability cannot close these goals automatically.
Rather than write a complex generated transitivity proof, we place the before and
rank flags directly in the OPB model — achieving the same UP-determinism with
no proof-time machinery at all. The `dom` step infrastructure added to
`ProofLogger` (`emit_dom_step`, `emit_load_order`, `write_raw_to_proof`)
remains available for future use.

### ArgSort

`ArgSort`'s permutation `p` is a real, branched variable, so it is assigned on
every solution — determined for free, no canonicalisation needed.

**Reuse of Sort.** Rather than re-deriving the sorted values, `ArgSort`
allocates `n` internal real variables `y[j]` (spanning the `x` value range) and
runs the shared sortedness helpers (`define_sortedness_proof_model` /
`install_sortedness_propagator`, factored out of Sort) on `{x, y}`. This reuses
Sort's entire certified apparatus — the stable-rank `pos` witness, the root
permutation pol, and the Mehlhorn-Thiel propagator — so `x` and `y` are kept
`bounds(Z)`-consistent with no new proof obligations. Crucially `ArgSort` keeps
the returned `SortednessWitness` (the `before` flags, `pos`, and the `rank_ge`/
`rank_le` lines) so it can channel `p` to `pos` and prove rank prunings. The
`y[j]` are set up in the proof (`set_up_integer_variable`) but never branched on.

**Channel to `p`.** On top of that, `ArgSort` adds:

- `all_different(p)` as at-most-one-per-position (`O(n)` constraints, positions
  range over exactly `n` values so this is already width-independent). At
  runtime the framework's GAC `all_different` propagator runs on `p`; the
  per-value at-most-one lines make its pairwise not-equals clauses RUP, so its
  am1-line cache fills itself lazily — pure reuse.
- the value channel `y[j] = x[p[j] - offset]`, half-reified on the `p`
  literals, and a fully-reified equality flag per consecutive pair driving the
  stability tie-break `eq_j -> p[j] < p[j+1]` (the inner Sort already gives
  `y[j] <= y[j+1]`, so the flag captures exactly the ties).
- a **channel propagator**: (1) if `dom(x[k])` and `dom(y[j])` are disjoint then
  `p[j] != offset + k`; (2) once `p[j] = offset + k` is fixed, `x[k]` and `y[j]`
  hold equal values, so their bounds are intersected. Each pruning is plain RUP —
  the reified channel reduces the cross-variable step to a single-variable bound
  contradiction.
- the **inverse channel** `p[j] = offset + k  <->  pos[k] = j` (definitional:
  position `j` holds element `k` exactly when `k`'s stable rank is `j`), plus an
  **achievable-rank-set propagator**. For a fixed value `vk` of `x[k]`, the
  number of elements below `k` can be any integer in `[#forced(vk),
  #possible(vk)]`; the union of these intervals over `vk in [lk, uk]` is `k`'s
  exact reachable rank set (it suffices to sample the `O(n)` breakpoints). This
  set can have **holes**: ties among the other elements make the count jump (e.g.
  `x[i]=x[i']=0` forces `before[i][k]` and `before[i'][k]` to move together), so
  the reachable set is generally *not* the whole interval `[a_k, b_k]`. Position
  `j` can hold element `k` only if `j` is reachable.

  - **Outside the interval** (`j < a_k` or `j > b_k`): explicit pol on the
    element's own bound — `below` derives `pos[k] >= a_k` from `rank_ge[k]` plus
    the forced `before[i][k] >= 1` lines, `above` derives `pos[k] <= b_k` from
    `rank_le[k]` plus the forced `!before[i][k]` lines.
  - **Hole inside the interval**: there is a threshold value `U` with
    `#possible(U) <= j-1` and `#forced(U+1) >= j+1`, so `x[k] <= U => pos[k] <=
    j-1` and `x[k] >= U+1 => pos[k] >= j+1`. The proof pivots on the *constant*
    `U` (mirroring Sort's pivot-bridge): line A folds `rank_le[k]` with the
    `(x[k] >= U+1) v !before[i][k]` clauses, line B folds `rank_ge[k]` with the
    `(x[k] <= U) v before[i][k]` clauses; the inverse channel then closes
    `p[j] != offset+k` by RUP via the case split on `[x[k] >= U+1]`.

**Consistency achieved.** `bounds(Z)` on `x`, `y`, **and `p`**, fully certified.
The achievable-rank-set propagator gives bounds consistency on `p`: if rank `j`
is reachable for element `k`, then some `x`-assignment places `k` at rank `j`,
and that assignment is itself a complete solution with `p[j] = offset + k` — so
the exact reachable set *is* the BC-supported set. This matches the strength of
Gecode's `sorted` with permutation variables (Thiel's algorithm), but certified.
Full GAC on `p` remains NP-hard (rank-feasible but integer-infeasible values can
survive); that residual is the frontier and is deliberately not pursued.

The asymmetry between Sort's and ArgSort's witnesses is deliberate:
- **Sort** uses `SortPermWitness` (the p-based encoding above); the
  stable-rank construction is baked into the OPB model.
- **ArgSort** still uses `SortednessWitness` (before/pos integer encoding,
  shared with ArgSort's internal sorted-values subproblem); its real
  permutation variable `p` channels directly to `pos`, so the argmax
  achievable-rank-set reasoning can reference `rank_ge`/`rank_le`/`before`
  directly without the p[i][j] layer.

## Survey of propagation algorithms

| Approach | Complexity | Consistency | Notes |
|---|---|---|---|
| **Decomposition** (MiniZinc default for non-native solvers) | per-propagator | strictly weaker than `bounds(Z)` | `alldifferent(p)` + variable-index `element`/channel + `increasing(y)`, each in isolation; misses the global order-statistic/Hall reasoning. The variable-index `element` is the weak link. Produces large proofs (cf. issue #251). |
| **Bleuzen-Guernalec & Colmerauer** (CP'97 `O(n^2)`; *Constraints* 5:85–118, 2000 `O(n log n)`) | `O(n log n)`, proven optimal | `bounds(Z)` | "Smallest enclosing `2n`-block": sweep over sorted endpoints. Geometric predecessor of MT. |
| **Mehlhorn & Thiel** (CP 2000, LNCS 1894 pp.306–319; full spec in Thiel's PhD thesis) | `O(n)` + endpoint sort | `bounds(Z)` on `y` | Bipartite interval-intersection matching; greedy/SCC. Gecode's choice. **The one to implement.** |

Real solvers: **Gecode `sorted`** = Thiel's algorithm, bounds only; the
`Perm=true` variant adds permutation inferences and a second propagation pass.
**Choco `keySort` / SICStus `keysorting`** = the stable variant (our
`ArgSort`). **OR-Tools, Chuffed, Pumpkin** have *no* dedicated sortedness
propagator — all decompose. In particular **no certifying/explained sortedness
propagator exists anywhere**, so a VeriPB-certified one would be novel.

### The Mehlhorn–Thiel algorithm (implementation notes)

Input: `2n` intervals `X_1..X_n` (the `x` array) and `Y_1..Y_n` (the sorted
array), each `[lb, ub]`. `S` = tuples whose second half is the sorted first
half. Goal: narrow all `2n` intervals to bounds consistency.

1. **Normalise the `Y` ranges** (they must be sorted-consistent): left-to-right
   `lb(Y_{i+1}) := max(lb(Y_i), lb(Y_{i+1}))`; right-to-left
   `ub(Y_{i-1}) := min(ub(Y_i), ub(Y_{i-1}))`.

2. **Intersection graph** `G`: bipartite on `{x_i}` and `{y_j}`, edge
   `{x_i, y_j}` iff `X_i ∩ Y_j != ∅`. The neighbours of each `x_i` form a
   contiguous interval of `y`-indices (convexity). A perfect matching ⇔ a
   feasible tuple in `S`.

3. **Matching (Glover's greedy)**: define `f(j)` (the `x` matched to `y_j`) for
   `j = 1..n` in order: among `x_i` that intersect `y_j` and are not yet used,
   pick the one with **smallest upper bound** `ub(X_i)`. If none with
   `ub(X_i) >= lb(Y_j)` exists, there is **no perfect matching** (fail). With a
   priority queue this is `O(n log n)`; via the offline-min / union-find
   reduction it is `O(n)`.

4. **`y` bounds**: a *down sweep* (match `y_j` to min-`ub` available `x`)
   yields the tightened **upper** bounds `ub(Y_j)`; a symmetric *up sweep*
   yields the **lower** bounds `lb(Y_j)`.

5. **`x` bounds**: orient each matched edge `x → y` and add reverse edges for
   all edges; an edge lies in *some* perfect matching iff it is in a **strongly
   connected component** (the *reduced* intersection graph). For each `x_i`,
   let `y_{jl}`, `y_{jh}` be its smallest/largest neighbour in the reduced
   graph; then `lb(X_i) := max(lb(X_i), lb(Y_{jl}))` and
   `ub(X_i) := min(ub(X_i), ub(Y_{jh}))`. The SCCs are computed in `O(n)` by an
   adapted Cheriyan–Mehlhorn–Gabow DFS exploiting the interval structure.

Overall `O(n)` + the cost of sorting the `x` endpoints (so `O(n log n)`, or
`O(n)` for integer endpoints in a polynomial range), and asymptotically
optimal.

The inferences this propagator makes — the only things the proof must justify —
are exactly four bound tightenings (`lb(y)` up, `ub(y)` down, `lb(x)` up,
`ub(x)` down) plus a no-matching contradiction.

## Proof logging

The propagation proofs are complete and fully certified (`s VERIFIED` across
the full `sort_test` suite). The approach changed significantly when the
encoding moved from `pos[i]` integers to `p[i][j]` binary flags; this section
documents the current (p-based) proof structure.

### Key simplification: surjectivity and injectivity for free

The old `pos[i]` encoding required deriving the permutation properties of `pos`
at the proof root via an expensive `O(n^3)` chain (totality → antisymmetry →
transitivity → rank-gap → `recover_am1` injectivity), before every bound proof
could reuse the surjectivity pol. With the `p[i][j]` doubly-stochastic model,
these properties are **model constraints**:

- **Injectivity** (`Σ_i p[i][j] ≤ 1`): the column at-most-one from the OPB
  model — `col_am1[j]`.
- **Surjectivity** (`Σ_i p[i][j] ≥ 1`): the counting pol
  `Σ_i row_al1[i] + Σ_{k≠j} col_am1[k]` gives `Σ_i p[i][j] ≥ 1` with no
  root initialiser needed.

There is no `install_initialiser` in `install_sort_propagator_perm`; the
doubly-stochastic lines are referenced directly from the model. This eliminates
the `O(n^3)` root cost entirely.

### The Hall witness (band pigeonhole over p columns)

Every inference — contradiction, y-bounds, x-bounds — reduces to the same
pigeonhole argument. A rank interval `[a,b]` and set `S` of x's whose
feasible-rank intervals `[lo_i, hi_i)` ⊆ `[a,b]`, with `|S| > b−a+1`.

The proof (`fail_hall_perm` in `sort.cc`):

1. **Normalized y-bounds** as RUPs: `NUY[k]: y_k ≤ uy[k]` (top-down) and
   `NLY[k]: y_k ≥ ly[k]` (bottom-up). Each exclusion `~p[i][k]` for `k` outside
   `[a,b]` is then one-step RUP from the channel `p[i][k]=1 ⟹ x[i]=y[k]` and
   the normalized bound (`k<a: y_k ≤ uy[k] < lx[i]`; `k>b: y_k ≥ ly[k] > ux[i]`).

2. **Restricted row al1**: for each `i∈S`, `Σ_{k∈[a,b]} p[i][k] ≥ 1` (RUP from
   the OPB `row_al1[i]` minus the excluded positions).

3. **Counting pol**: `Σ_{i∈S} restricted_al1[i] + Σ_{k∈[a,b]} col_am1[k]`
   simplifies to `−Σ_{k∈[a,b]} Σ_{i∉S} p[i][k] ≥ |S| − (b−a+1) ≥ 1`. Since
   the LHS is non-positive, this is a contradiction.

For the bound inference sub-cases, the goal literal (`y[j] ≤ U`, `x[i] ≥ L`,
…) is ORed into the assumption-dependent exclusions and restricted-al1s (anchored
by a `BNLY`/`BNUY` y-sortedness chain under the negated goal), and the closing
RUP discharges it.

### The three cases for each y-bound

Certifying `ub(y[j]) = U` (and its lb mirror) splits as before:

1. **Normalization** (`U = uy[j]`, propagated from a later y via step-1 min):
   pure y-sortedness chain — identical to the old pos-based proof.

2. **Order statistic** (`≥ j+1` x's have `ux[i] ≤ U`): under the negated goal
   `y[j] ≥ U+1`, a BNUY chain gives `y[k] ≥ U+1` for all `k ≥ j`. For each
   `i` with `ux[i] ≤ U`: `~p[i][k] + [y[j]<U+1] ≥ 1` for `k ≥ j` is RUP
   (channel + BNUY + reason); the restricted al1 `[y[j]<U+1] + Σ_{k<j} p[i][k]
   ≥ 1` follows. The counting pol over `j+1` such restricted-al1s and `j`
   `col_am1[k<j]` gives the contradiction. **No pivot bridge needed** — the
   BNUY chain + channel directly exclude wrong columns.

3. **Hall** (`< j+1` x's forced `≤ U`): `find_band` on the shifted feasible
   intervals (`hi'[i] = min(hi_i, j)` for `ux[i] ≤ U`) finds the violating band
   `[a,b]`; the same pigeonhole runs under the negated-goal assumption.

### The x-bound cases

- **Intersection** (`jl = lo_i[i]`): for each column `k`, `~p[i][k] + [x[i]≥L]
  ≥ 1` is RUP under the reason — `k < lo_i` is excluded unconditionally
  (channel + `uy[k] < lx[i]`), `k ≥ lo_i` gives `x[i] = y[k] ≥ ly[k] ≥ L`
  via the channel. The `row_al1[i]` then closes via the closing RUP.

- **Hall** (`jl > lo_i[i]`): `find_band` on `hi'[i] = jl`, same pigeonhole
  under the negated goal.

**All cases fully certified**: the whole `sort_test` suite verifies `s VERIFIED`
with no assertions. `find_band` returning a violator is an invariant wherever an
inference fired; a miss throws `UnexpectedException` rather than silently
weakening the proof.

## References

Papers are in `~/claude/papers/` (the user has institutional publisher logins
for anything missing):

- Mehlhorn & Thiel, "Faster Algorithms for Bound-Consistency of the Sortedness
  and the Alldifferent Constraint", CP 2000, LNCS 1894, pp. 306–319
  (`3-540-45349-0_23.pdf`).
- Thiel, *Efficient Algorithms for Constraint Propagation and for Processing
  Tree Descriptions*, PhD thesis, Saarland, 2004 (sortedness chapter is the
  implementable spec) (`ThielSven_ProfDrKurtMehlhorn.pdf`).
- Bleuzen-Guernalec & Colmerauer, "Optimal Narrowing of a Block of Sortings in
  Optimal Time", *Constraints* 5(1–2):85–118, 2000 (`A_1009870418160.pdf`).
- Rusu, "NP-hardness of sortedness constraints", arXiv 1506.02442 / TCS 2017.
- López-Ortiz, Quimper, Tromp, van Beek, "A fast and simple algorithm for
  bounds consistency of the alldifferent constraint", IJCAI 2003 (the reusable
  Hall-interval data structure).
