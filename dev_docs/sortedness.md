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
(see its section). A checking propagator that rejects bad leaves is kept as a
cheap backstop, but it is no longer the only inference.

## The OPB encoding (proof model)

Both constraints must be defined in OPB for VeriPB. The design constraint that
shapes everything: **every proof-only auxiliary variable must be a function of
the core variables**, determined by unit propagation, or VeriPB cannot verify
solution (`solx`) lines (see
[the proof-only-aux memory rule] and the discussion in this file's history).

### Sort

`Sort` exposes the sorted values `y` as its real output and keeps the
permutation proof-only. A naive "some permutation `pos` with `y[pos[i]]=x[i]`"
encoding fails: with duplicate values the permutation is **not unique**, so UP
can't pin it on a solution. The fix is to make `pos` the **canonical stable
rank** of `x` — a function of `x` alone:

```
before[i'][i]  ==  x[i'] comes before x[i] under the order (value, then index)
               ==  (i' < i) ? (x[i'] <= x[i]) : (x[i'] < x[i])      [fully reified flags]
pos[i]         ==  sum over i' != i of before[i'][i]                [proof-only int, = stable rank]
channel        ==  (pos[i] = j) -> y[j] = x[i]
```

Plus `y[j] <= y[j+1]`. Because `pos` is determined by `x`, the channel pins
`y = sorted(x)`, so a violated leaf is refuted by **plain RUP** (no Hall/
pigeonhole proof needed for the *checker*). The encoding is `O(n^2)` and
**domain-width independent** — no `O(number of values)` constraints. This
mirrors the spirit of `Inverse`/`all_different` (compact clique-style OPB,
per-value facts recovered lazily) without needing `propagate_gac_all_different`
(which requires real state variables, not proof-only ones).

### ArgSort

`ArgSort`'s permutation `p` is a real, branched variable, so it is assigned on
every solution — determined for free, no canonicalisation needed.

**Reuse of Sort.** Rather than re-deriving the sorted values, `ArgSort`
allocates `n` internal real variables `y[j]` (spanning the `x` value range) and
installs an inner `Sort{x, y}` on them. This reuses Sort's entire certified
apparatus verbatim — the stable-rank `pos` witness, the root permutation pol,
and the Mehlhorn-Thiel propagator — so `x` and `y` are kept `bounds(Z)`-
consistent with no new proof obligations. The `y[j]` are set up in the proof
(`set_up_integer_variable`) but never branched on; they are an internal witness.

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
- a **channel-consistency propagator**: (1) if `dom(x[k])` and `dom(y[j])` are
  disjoint then `p[j] != offset + k`; (2) once `p[j] = offset + k` is fixed,
  `x[k]` and `y[j]` hold equal values, so their bounds are intersected. Each
  pruning is justified by plain RUP from the channel line and the two bounds —
  the reified channel reduces the cross-variable step to a single-variable bound
  contradiction, which VeriPB's RUP handles.

**Consistency achieved.** `bounds(Z)` on `x` and `y` (Mehlhorn-Thiel) plus GAC
`all_different` and channel-consistency on `p`. This is deliberately **weaker
than full `bounds(Z)` on `p`**, which is the costly NP-hard-adjacent pass (cf.
Gecode making its `Perm=true` permutation inferences a separate, optional pass);
that pass is future work.

The asymmetry with Sort's witness is deliberate: a proof-only permutation (Sort)
*forces* the stable-rank construction; a real permutation (ArgSort) channels
directly to the reused sorted values.

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

## Proof logging plan

No certifying sortedness propagator existed, so the proofs were designed from
scratch. **This is now complete: every inference is certified and the suite
verifies with no assertions** (see "The Hall witness" below for the final
shape). The staged approach that got us there:

1. **Implement the propagator with `AssertRatherThanJustifying` for every
   inference** (a development-only "trust me" step — never merged). Get strong
   bounds-consistency tests passing; VeriPB then verifies everything *subject to
   the cheating assertions*, which exercises the algorithm and the encoding
   without yet paying the proof cost.
2. **Then take each inference-producing site in turn** and ask: *precisely what
   is the general nature of what is being inferred here, and why is it true?*
   Often the answer dictates the proof directly; when it doesn't, it states a
   sharp question to work on. (The crux turned out to be the permutation/
   surjectivity of the stable rank, then a single Hall pigeonhole over the rank
   line shared by every bound and the contradiction.)

The expected shape (to be confirmed site-by-site): each bound tightening is a
**Hall-interval witness** — the set of `x` (or `y`) variables whose
bound-intervals saturate a contiguous block — structurally the same as gcs's
existing `all_different` Hall-set proofs (`recover_am1` +
`justify_all_different_hall_set_or_violator`), so that machinery should be
reusable. **Open question / risk:** MT reasons over interval-intersection
matchings, whereas our `Sort` witness `pos` is the *stable total order*; the
two need not line up, so whether MT's bound prunings are cleanly derivable
(RUP + Hall-style `pol`) from the stable-rank encoding is the thing to settle
as we go.

### Where the y-upper-bound proof stands (worked out site-by-site)

Certifying `ub(y[j]) = U` splits into **three cases**, distinguished cheaply in
the propagator from `uy[j]`, `ux[phi[j]]` and the count of x's forced `<= U`:

1. **Normalization** (`U = uy[j] <= ux[phi[j]]`, and `uy[j] < ouy[j]`): the
   bound came from a *later* `y`'s upper bound via the step-1 right-to-left min,
   so it is pure `y`-sortedness. **Honest:** emit the monotonicity clauses
   `(y[k] <= U) v (y[k+1] > U)` for `k = j..n-2` (each RUP from the single
   sortedness constraint `y[k] <= y[k+1]`); the closing RUP walks the chain up
   to the witnessing position.
2. **Order statistic** (`U = ux[phi[j]]` and `>= j+1` of the x's are
   *unconditionally* forced `<= U`, i.e. `ux[i] <= U`): the `(j+1)`-th smallest
   value is `<= U`. **Fully honest.** The count line
   `Σ_k [x_k <= U] >= j+1` is *plain RUP under the reason* (each of the `>= j+1`
   forced terms is independently entailed by its own upper bound — no
   cross-constraint step). This is genuinely RUP at any count, not a
   small-numbers artefact: `examples/sort_count_probe` drives the root
   order statistic over 20 *non-fixed* x's whose upper bounds sit strictly
   below the threshold, and VeriPB checks the resulting degree-20 count line
   (the literals stay variable — nothing is constant-folded). Fold it through
   the pivot bridge (`RANKLB`,
   `RANKLB2`) and the per-`i` extended-reason lines `(pos[i] != j) v (y[j] <=
   U)` — all RUP under the reason. **Surjectivity** `Σ_i [pos[i] = j] >= 1` is
   now honest too (see below), so this case is fully certified.
3. **Hall** (`U = ux[phi[j]]` but `< j+1` x's forced `<= U`): the tightening is
   a genuine matching argument — the `y`-domains commit some x to a lower
   position, freeing the matched x for `j` — so the simple count is *false* and
   must not be claimed. The whole bridge (pivot, rank bounds, per-position
   lines, surjectivity) is shared with case 2 and honest; **the only remaining
   assert is the count line `count_U >= j+1` itself**, which needs a Hall
   witness drawing on the `y`-domains.

### Surjectivity (the permutation), once at the root

`Σ_i [pos[i] = j] >= 1` — rank `j` is occupied — needs `pos` to be a
permutation, which needs the order to be total and transitive. An
`install_initialiser` derives this once at `ProofLevel::Top` and every bound
justification reuses it (the Cumulative/Disjunctive bridge pattern). The chain,
all over the `before` flags (whose two reification halves are captured in
`define_proof_model`):

- **totality** `before[a][b] + before[b][a] >= 1` = `rev(a,b) + rev(b,a)`,
  saturated (the `x` terms cancel);
- **antisymmetry** `¬before[a][b] + ¬before[b][a] >= 1` = `fwd(a,b) + fwd(b,a)`,
  saturated;
- **transitivity** `¬before[k][i] + ¬before[i][i'] + before[k][i'] >= 1`: sum
  `fwd(k,i) + fwd(i,i') + rev(k,i')` (the `x` terms cancel, leaving a flags-only
  `>= s+1` where the lex tiebreak slack `s >= 0` varies), then take the clause
  as a **RUP from that sum** — magnitude-independent, unlike saturate-then-
  divide which depends on the reif big-M exceeding `s`;
- **rank gap** `GAP[i][i'] : pos[i'] - pos[i] + n·before[i'][i] >= 1` (i.e.
  `before[i][i'] => pos[i'] >= pos[i]+1`) = `rank_ge[i'] + rank_le[i] +
  Σ_{k≠i,i'} T[k] + (n-1)·TOT[i][i']` — an *exact* pol (no saturate);
- **injectivity** `Σ_i [pos[i]=k] <= 1` via the `recover_am1` fold (inlined
  because `pos` is proof-only), whose pairwise `¬[pos[i]=k] + ¬[pos[i']=k] >= 1`
  is RUP from the two `GAP`s + antisymmetry.

Then per bound, surjectivity of rank `j` is the counting pol
`Σ_i al1_i + Σ_{k≠j} inj_k` (the `n(n-1)` constants cancel, leaving
`Σ_i [pos[i]=j] >= 1`), where `al1_i = Σ_k [pos[i]=k] >= 1` is a `Top` RUP. This
is `O(n^3)` at the root (the transitivity clauses) but paid once. With it,
`examples/sort_count_probe` (n = 20, all order-statistic) verifies `s VERIFIED`
with **no assertions**.

So the count (the feared "P3") was *not* the hard part — it is RUP whenever
true, and the case split says when.

### The other inferences (same shape)

- **`lb(y[j])`** mirrors `ub(y[j])` exactly: it uses the "out" flag
  `before[j'][m]` + antisymmetry to *upper*-bound `pos[i]`
  (`x_i < L ⇒ pos[i] ≤ j-1`), with the same per-position lines and the *same*
  surjectivity pol. Normalization and order-statistic cases honest; only the
  Hall count asserted.
- **`lb(x[i]) ≥ ly[jl]` / `ub(x[i]) ≤ uy[jh]`** reduce to a rank bound on `x_i`
  plus the channel. The **intersection** case (`jl = lo_i`, resp.
  `jh = hi_i-1`) is honest: for every rank `k`, `(pos[i] ≠ k) ∨ (x_i ≥ L)` is
  RUP under the reason — `k < lo_i` is impossible (`y_k ≤ uy[k] < lx[i] ≤ x_i`
  would break the channel), and `k ≥ lo_i` gives `x_i = y_k ≥ ly[k] ≥ L`; the
  at-least-one line for `pos[i]` closes it. When the SCC strictly tightens the
  rank range past the intersection extremes (`jl > lo_i`), it is a genuine Hall
  argument and stays asserted.

### The Hall witness (the band)

The shared certificate is a pigeonhole **on the rank line**: a rank interval
`[a,b]` and a set `S` of x's whose feasible-rank intervals `[lo_i,hi_i)` are all
`⊆ [a,b]`, with `|S| > b−a+1`. The slots are ranks; capacity 1 per rank is the
root injectivity (`inj_lines`); membership "pos[i] ∈ [a,b]" comes from excluding
every outside rank via the channel and a normalized y-bound. Concretely
(`fail_hall` in `sort.cc`):

- emit `NUY[k]: y_k ≤ uy[k]` (top-down) and `NLY[k]: y_k ≥ ly[k]` (bottom-up) as
  single-step RUP chains, so each exclusion `(pos[i] ≠ k)` is one-step RUP
  (`k<a`: `y_k ≤ uy[k] < lx_i`; `k>b`: `y_k ≥ ly[k] > ux_i`);
- per `i∈S`, the restricted at-least-one `Σ_{k∈[a,b]}[pos[i]=k] ≥ 1` from the
  root `al1[i]` minus the exclusions;
- pol the restricted-al1s against `inj_k` for `k∈[a,b]` ⟹ `|S| ≤ b−a+1`,
  contradiction. (Empty band `b=a−1` ⟹ a single x with no feasible rank; its
  restricted-al1 is already `0 ≥ 1`.)

**This certifies every inference.** The no-matching contradiction uses the
pigeonhole directly (pure y-window case: a sortedness chain; matching case: the
band). The bound Hall sub-cases are the *same* pigeonhole **under the
negated-goal assumption** (route a / Cor 2.1): the assumption shifts one
endpoint of each feasible-rank interval (e.g. `ub(y_j)`: every `x` with
`ux ≤ U` gets `hi'[i] = min(hi_i, j)`; `lb(x_i)`: `hi'[i] = jl`), `find_band`
finds the violator, the goal literal (`y_j ≤ U`, `x_i ≥ L`, …) is ORed into the
assumption-dependent clauses (anchored by a `BNLY`/`BNUY` sortedness chain), and
the closing RUP discharges it. The whole `sort_test` suite, the n=20 probe, and
a 200-seed random sweep verify `s VERIFIED` with **no assertions**; the
Mehlhorn–Thiel propagator is fully VeriPB-certified. `find_band` returning a
violator is an invariant whenever an inference fired, so a miss throws
`UnexpectedException` rather than weakening the proof.

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
