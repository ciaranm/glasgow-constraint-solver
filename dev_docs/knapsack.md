# `Knapsack`: proof strategies, and the upfront-DAG design

There is a single public `Knapsack` constraint with two proof-logging
strategies, both fully proof-logging and both cake-conformant (#200),
selected with `with_proof_strategy(proof_strategy::…)`:

- **`proof_strategy::PerCall` (the default)** — the per-call DP
  implementation. It rebuilds its DP table and proof scaffolding from
  scratch on every propagation call, at `ProofLevel::Temporary`. This is
  what all frontends, `scp_reader`, the `examples/knapsack` solver and
  the primary `knapsack_test` get. **It is the default because its
  proofs verify substantially faster** (3.6–18× faster VeriPB time than
  the upfront variant — see "Benchmarking" below). It lives in
  `gcs/constraints/knapsack/knapsack.{hh,cc}`.
- **`proof_strategy::Upfront` (opt-in)** — the upfront-DAG
  reimplementation. It builds the statically-reduced layered DAG once in
  `prepare()` and emits paper-style proof scaffolding once at
  `ProofLevel::Top`, leaving only search-state-dependent `pol` steps for
  the per-call sweep. **It produces 3–6× smaller proofs** (and ~3× faster
  solver wall time), at the cost of the slower verification above. Prefer
  it only when proof size or its distribution matters. Its install path
  (`install_knapsack_upfront`) lives in
  `gcs/constraints/knapsack/knapsack_upfront.{hh,cc}` and is exercised by
  `knapsack_upfront_test` (which posts
  `Knapsack{…}.with_proof_strategy(proof_strategy::Upfront{})`). Both
  strategies draw the same inferences and share the same OPB; the choice
  is proof-only.

The rest of this note is a working-design record of the **upfront-DAG**
approach, retained because it is the more intricate of the two and
because it is the candidate for the #200 unified layered-DAG framework.
It is not a record of what currently exists in every stage — read
`gcs/constraints/knapsack/knapsack_upfront.{hh,cc}` for that, and
`gcs/constraints/knapsack/knapsack.{hh,cc}` for the default per-call DP.

The high-level approach mirrors `BinPacking` Stage 3
([`bin-packing.md`](bin-packing.md)) but generalised to *k* partial-sum
coordinates: build the layered DAG once in `prepare()`, emit the
paper-style proof scaffolding *plus per-coordinate forward chains,
joint-state implications, joint layer-ALOs, joint backward chains and
phantom rules* once at `ProofLevel::Top` in `install_initialiser`, and
then run a slim per-call sweep that emits dead-state ~S lines at
`ProofLevel::Current` (cached for the rest of the subtree) plus
cap-exceeded and totals-bound `pol` steps at `ProofLevel::Temporary`.

## Constraint definition

Both classes share the same definition. For each `x ∈ 0..k−1`:

```
Σ_i coefficients[x][i] · vars[i]  =  totals[x]
```

Coefficients are non-negative; item variables and total variables have
non-negative lower bounds. Two constructors (on each class):

- `Knapsack(weights, profits, vars, weight, profit)` — the canonical
  `k = 2` shape used by MiniZinc and the `examples/knapsack` solver.
- `Knapsack(coefficients, vars, totals)` — the general `k ≥ 1` form
  used by XCSP3 (multi-condition knapsacks) and any caller that wants
  more than two summed quantities.

Items can take arbitrary non-negative integer values (not just 0/1).
Both propagators are full GAC on both the item variables and every
`totals[x]`.

## OPB encoding: spec-faithful, propagator-agnostic

Both classes' `define_proof_model` emit exactly one linear equality per
total:

```
Σ_i coefficients[x][i] · vars[i]  ==  totals[x]
```

That's the entire model contribution. A human reading the OPB sees
the textbook knapsack semantics with no propagator vocabulary. For
`KnapsackUpfront` the DAG-shaped scaffolding lives in the proof body via
`install_initialiser` (see "Top-level scaffolding" below); this is the
same encoding-vs-scaffolding split that
[`bin-packing.md`](bin-packing.md) and
[`disjunctive-proof-logging.md`](disjunctive-proof-logging.md)
document.

The two `add_labelled_constraint(eq)` line numbers — `sum ≤ total` and
`sum ≥ total`, labelled `@c[<id>][<row>_le]` / `[<row>_ge]` to match
cake_pb_cp's per-row labels — are captured so the per-call `pol` steps
for cap-exceeded and totals-bound filtering can use them as operands.
Both classes label rows identically, so both chain-verify against
cake_pb_cp; the default per-call `Knapsack` is the one `scp_reader`'s
`knapsack` keyword posts and the one the `knapsack_sat` / `knapsack_unsat`
`scp_cases` chain tests exercise.

## Staging (KnapsackUpfront)

Stages 1 and 2 are shipped. Stage 1 is documented for completeness;
Stage 2 strictly subsumes it.

### Stage 1 — checker (superseded)

- OPB as above.
- Propagator fires only when every `vars[i]` is single-valued.
- For each `x`, infer `totals[x] = Σ_i coefficients[x][i] · value(vars[i])`
  via RUP — the natural OPB equality closes it.
- Tests temporarily ran via `solve_for_tests` (no GAC check) and on a
  small subset of the data set, because a pure checker can't keep
  search tractable through wide-domain totals.

### Stage 2 — upfront DAG, paper-style proof, full GAC

For each layer `i ∈ 0..n` (where `n = vars.size()`), the DAG has nodes
keyed by a *k*-vector `w` of partial sums:

```
w[x]  =  Σ_{j < i} coefficients[x][j] · vars[j]
```

Layer 0 contains exactly the zero vector. Edges from `(i, w)` are
labelled by values `v ∈ initial dom(vars[i])` and land at
`(i+1, w + v · coefficients[*][i])`.

#### Static reduction

Performed in `prepare()` against initial item domains: forward
reachability from `(0,…,0)`. The per-coordinate cap is the sum of
maximum item contributions, **not** intersected with
`initial upper(totals[x])`.

Capping by the initial total upper looks tempting but breaks the
proof: the per-call "eliminated by current total bound" case needs a
Top-level flag for the over-bound successor to reference in its `pol`
step. If that flag doesn't exist, the proof chain can't close. So
every reachable partial-sum vector under any combination of initial
item domain values gets a Top-level flag, including ones that the
initial total bound already rules out. The initial total bound is
then enforced by the same per-call "eliminated" path that the search
will use for tighter current bounds anyway, so nothing is lost in
strength.

Backward reduction (filtering out states with no path to a layer-`n`
accepting node under initial totals) is **not** applied during static
construction, for the same reason: the per-call propagator emits
dead-state lines (`~S` for forward-reach states with no live path
forward) and needs those flags to exist.

#### Joint phantoms

The DAG is closed under *forward* transitions but not under *backward*
ones: a layer-(i+1) DAG node `succ` and a value `v` for `vars[i]` can
yield a parent vector `parent = succ − v · coefficients[*][i]` that is
non-negative everywhere but isn't itself in the layer-`i` DAG. We call
these *phantoms*. They arise whenever the forward construction reaches
`succ` via some other parent, but the backward edge for this
particular `v` lands on a non-reached vector.

Phantoms are a problem only because the joint backward chains below
need a parent flag to chain against. The scaffolding therefore also
creates a phantom `S_{i,parent}` for every such parent, plus phantom
`g_up` / `g_dn` flags for any coordinate value that doesn't already
appear in the DAG's projection at this layer. We then follow up with
a `~S_phantom ≥ 1` RUP saying "this state is unreachable".

Phantoms are computed *transitively* in descending layer order: at
each layer `i` from `n−1` down to 0, we add the non-negative-but-non-
DAG backward edges from `DAG[i+1] ∪ phantoms[i+1]`. This closure is
necessary because phantom rules (below) recursively rely on the
phantom flags of *their own* backward parents.

There are two phantom sub-cases, distinguished by whether the joint
phantom is also per-coord infeasible at some coordinate:

- **Per-coord-phantom** (some `p[x*]` is not in the DAG's projection
  at layer `i`, coord `x*`). The phantom rule is closed by pair-wise
  `pol` steps: for every feasible `u` at this layer-coord, emit
  `pol succ.g_up_{u}.fwd + p.g_dn_{x*}.fwd ; saturate` (or the swapped
  variant for `u < p[x*]`). Each pair-wise line says
  `¬g_up_{u} ∨ ¬g_dn_{p[x*]} ≥ 1`. The closing `~S_phantom ≥ 1` RUP
  then UP-closes through goal-negation: forcing `g_up_{p[x*]}` and
  `g_dn_{p[x*]}` to 1 makes every pair-wise line force the
  corresponding feasible `u`'s flag to 0; the joint layer-`i` ALO is
  contradicted because every DAG joint state with `s[x*] = u` has its
  `~S` propagated through conjunction-rev.

- **Joint-only-phantom** (every coord projection feasible, joint not).
  No extra `pol` scaffolding is needed beyond the backward chains
  emitted for `phantoms[i]` as `succ`. The closing `~S_phantom ≥ 1`
  RUP UP-closes via: backward chain `~S_phantom + (vars[i−1] ≠ val) +
  parent.S ≥ 1` for each `val`, plus the recursively-derived
  `~parent.S = 1` (the parent is itself a phantom because DAG is
  forward-closed — see below), plus the implicit var-domain ALO.

The phantom-rules-must-be-non-DAG observation is the key: DAG is closed
under forward steps, so if any phantom `p ∈ phantoms[i]` had a DAG
backward parent at layer `i−1`, `p` would itself be in `DAG[i]`. So
*every* backward parent of a phantom is either negative-coord (handled
by a direct backward chain without a parent term), per-coord-phantom,
or joint-only-phantom. The recursion bottoms out either at layer 0
(where `per_coord_feasible[0][x] = {0}`, so every phantom is the
per-coord case and closes without recursion) or at negative-coord
parents.

#### Top-level scaffolding

For each `(i, w)` with `w ∈ DAG[i] ∪ phantoms[i]`, three reified flags
at `ProofLevel::Top` via `create_proof_flag_reifying`:

```
g_up_{i,x,w_x}  ⇔  Σ_{j<i} coefficients[x][j]·vars[j]  ≥  w_x
g_dn_{i,x,w_x}  ⇔  Σ_{j<i} coefficients[x][j]·vars[j]  ≤  w_x
S_{i,w}         ⇔  Σ_x (g_up_{i,x,w_x} + g_dn_{i,x,w_x})  ≥  2k
```

`g_up` / `g_dn` flags are *shared across states with the same
coordinate value at the same layer* — distinct state vectors with the
same `w_x` reuse the same per-coord flag pair. Only the conjunction
flag `S_{i,w}` is per-state.

This is the paper-style scaffolding from Demirović et al., CP 2024
§3.3 ("Knapsack as a Constraint";
`ciaranm.github.io/papers/cp2024-dp.pdf`), generalised to *k*
partial-sum dimensions. For `k = 1` it reduces to the `BinPacking`
Stage 3 shape (one `g_up`, one `g_dn`, one `S` per node).

On top of these reifications the initialiser emits (all at `Top`):

1. **Per-coord forward chains** for every `(parent, val, succ)` edge
   in `DAG[i] → DAG[i+1]` and every coord `x`:
   `pol succ.g_up.rev + parent.g_up.fwd ; saturate`, then RUP
   `¬parent.g_up_x ∨ (vars[i] ≠ val) ∨ succ.g_up_x ≥ 1`. Same shape
   for `g_dn`.
2. **Joint state forward chain** `¬parent.S ∨ (vars[i] ≠ val) ∨
   succ.S ≥ 1`, RUP from the per-coord chains plus the conjunction
   reification.
3. **Layer-0 ALO** `S_{0,(0,…,0)} ≥ 1`, RUP from the reverse
   reification axioms (running sum at layer 0 is the empty sum = 0).
4. **Per-state implications and layer ALOs**, by induction. For each
   `i = 0..n−1`: for every `s ∈ DAG[i]`, RUP
   `¬S_{i,s} + Σ_v S_{i+1, s+v·coeffs} ≥ 1`; then RUP
   `Σ_{w ∈ DAG[i+1]} S_{i+1, w} ≥ 1`.
5. **Joint backward chains** for every `(succ, val)` with
   `succ ∈ DAG[i+1] ∪ phantoms[i+1]`. Three flavours by parent
   category: negative-coord (direct `¬succ.S ∨ (vars[i] ≠ val) ≥ 1`),
   DAG parent (per-coord + joint chain through the parent flag),
   phantom parent (same shape, but the parent flag is a phantom flag).
6. **Phantom rules** in ascending layer order, as described above.
   Layer-0 phantoms close immediately; layer-`i` phantoms close
   through backward chains plus recursively-derived `~parent.S`
   from layers `< i`.

#### Per-call propagator

The per-call sweep walks the static DAG layer by layer under current
item domains. The walk itself is identical with or without proof
logging; the proof emissions are gated on `logger != null`.

Forward walk: for each `i = 0..n−1`, accumulate `growing[i+1] =
{ parent + val·coeffs : parent ∈ growing[i], val ∈ current_dom(vars[i]) }
∩ DAG[i+1]`, recording predecessor edges. Cap-exceed states with
`w[x] > state.upper_bound(totals[x])` are erased from `growing`. After
each layer, for every `w ∈ DAG[i+1]` not in `growing[i+1]`:

- If `w` is cap-exceeded under the current totals upper bound: emit a
  `pol` step combining `succ.g_up.fwd + opb_lines[x].first +
  state.upper_bound(totals[x])` at `Temporary`, then a `~S_{i+1,w} ≥ 1`
  RUP at `Current` (cached in the `DeadCache` below).
- Otherwise (forward-unreachable in current call): just the
  `Current` RUP. UP closes it via the Top-level backward chains plus
  the cached `~parent.S` of any dead predecessor at layer `i`.

After all layers, the propagator filters the layer-`n` set by current
totals domain — both by lower bound (symmetric `pol` against
`g_dn.fwd + opb_lines[x].second + state.lower_bound(totals[x])`) and
by interior holes — emitting `~S` and `~g_dn` lines for the rejected
states.

If the layer-`n` set is empty, an explicit empty RUP under the reason
plus `inference.contradiction` closes the call.

Otherwise the propagator collects the bound and interior inferences:
`totals[x] ≥ min(w[x])`, `totals[x] ≤ max(w[x])`, and `totals[x] ≠ v`
for unreachable interior values. For each `x` and each surviving
layer-`n` state, it emits a terminal `pol` against the relevant
`g_up.fwd` / `g_dn.fwd` and the OPB equation, followed by per-state
RUPs `¬state.g_up ∨ (totals[x] ≥ lo) ≥ 1`, then aggregates with
`(totals[x] ≥ lo) ≥ 1` and `(totals[x] ≤ hi) ≥ 1` so a plain
`JustifyUsingRUP` on the `inference.infer_all` call can close.

A backward pass walks the recorded predecessor map from the surviving
layer-`n` set: any intermediate state with no path forward gets `~S`
emitted at `Current` (cached); any item value at layer `i−1` not in
the supported set is `inference.infer(vars[i−1] ≠ val,
JustifyUsingRUP)`-pruned.

#### `DeadCache`: cross-subtree dead-state dedup

Once a DAG node `S_{i,w}` has been proven dead during a propagation
call, that fact stays true for every descendant search node until
backtracking above the depth at which it was first established. The
`DeadCache` is a backtrack-restored `vector<set<vector<Integer>>>`
(plus a parallel `dead_g_dn[i][x]` for the layer-`n` lower-bound
filter) registered via `add_constraint_state`, threaded into
`propagate()` as a reference. Each of the dead-state emission sites
(forward walk, layer-`n` lower-bound filter, layer-`n` interior
filter, backward pass) checks the cache, emits at
`ProofLevel::Current` and adds to the cache only when it's the first
time the state has been proven dead in this subtree.

#### Why so much at Top?

Moving the per-(parent, val, succ) chains and the joint state ALOs
out of every per-call walk and into a single Top-level emission is
the main proof-size win compared to the default per-call DP `Knapsack`:
chains are defined once per constraint instead of once per propagation
call. The cost is the phantom-rule machinery — DAG forward-closure
leaves backward edges that need explicit `~S_phantom` derivations to
keep the per-call dead-state RUPs closable. The pair-wise pol approach
for per-coord-phantoms and the recursive backward chain for
joint-only-phantoms together handle all phantom cases the
forward-closed DAG can produce.

What remains at `Temporary` in the per-call walk is exactly the
search-state-dependent pieces: the cap-exceeded `pol` (depends on
the current totals upper), the lower-bound and interior-hole `pol`
chains (depend on the current totals domain), and the per-state
terminal-bound `pol` lines that close the actual `inference.infer_all`
RUP for the `totals[x] ≥ lo` / `≤ hi` conclusions. Everything else
the per-call needs is already in the database at `Top` or `Current`.

## Memory footprint

The static DAG plus its scaffolding can grow large. With *k*
coordinates and per-coord cap `C`, a fully populated layer has up
to `Π_x C` states; for `k = 4` and `C = 30` this is over 800k nodes
per layer. In practice the partial-sum reachability is sparse — most
combinations of partial sums aren't actually realised by any item
assignment — but it is *possible* to construct a `KnapsackUpfront`
instance that exhausts memory at root. The phantom set adds another
multiplicative factor proportional to `|dom(vars[i])|` (each DAG node
can spawn up to `|dom|` phantom backward parents per layer; the
transitive closure can be larger again).

There is no footprint guard on `KnapsackUpfront`. The same blowup
affects the default per-call `Knapsack` (just at a different time —
per-call rather than once at root) and the same set of inputs would
exhaust either. A future cross-cutting project (#200's unified
framework) will need a size-aware strategy across `BinPacking`,
`Knapsack`, and the prospective `CostMDD`. Until then, callers with
wide-domain wide-cap instances should stick to the default per-call
`Knapsack` (whose blowup is at least deferred and shared across the
subtree) or provide tight initial bounds on `totals[x]`.

## Frontends

`Knapsack` (the default per-call class) is the user-facing class.
Frontends bind to it directly:

- **MiniZinc** — `fzn_glasgow.cc`'s `glasgow_knapsack` branch posts
  `Knapsack{weights, profits, vars, weight, profit}` (the 2-total
  constructor).
- **XCSP3** — `buildConstraintKnapsack` posts the general k-total
  constructor (XCSP3's `knapsack` element can carry an arbitrary
  number of weight/profit pairs).

`KnapsackUpfront` has no frontend keyword of its own; it is posted
directly in C++ (and by `knapsack_bench --upfront`). Its `s_expr`
keyword is `knapsack_upfront`, which has no `scp_reader` case — only the
default `Knapsack` (keyword `knapsack`) round-trips through scp and is
the class the `scp_reader` `knapsack` keyword posts.

## Relation to other constraints

- **`BinPacking` Stage 3** — `k = 1` version of the same idea, with
  the per-bin DAG factored over a single load axis. `KnapsackUpfront`'s
  per-coord flag sharing across same-`w_x` states matches what
  `BinPacking` gets for free with a scalar `w`. `BinPacking` doesn't
  have a phantom problem because its per-bin DAG is scalar — backward
  edges from a layer-(i+1) DAG node either land on a DAG node, fall
  out of bounds, or get clipped by the cap.
- **`MDD`** — `MDD`'s natural definition *is* the layered DAG, so its
  state flags live in the OPB. `Knapsack`'s natural definition is the
  sum equations, so `KnapsackUpfront`'s DAG belongs in the proof body —
  the same encoding/scaffolding split as `BinPacking`.
- **#200 unified framework** — the layered-DAG abstraction (per-layer
  node counts, transitions, accepting terminals) is the dispatch
  point. `MDD` is one user-supplied DAG; `BinPacking` synthesises one
  scalar DAG per bin; `KnapsackUpfront` synthesises one *k*-dim DAG per
  constraint; future `CostMDD` adds edge weights against a totalcost
  variable. The default per-call `Knapsack` is kept as the correctness
  reference and the shipping default until the unified framework is
  ready to absorb both ideas.

## Benchmarking

The default per-call `Knapsack` lives in
`gcs/constraints/knapsack/knapsack.{hh,cc}` and is exercised by
`knapsack_test`; the opt-in `KnapsackUpfront` lives in
`gcs/constraints/knapsack/knapsack_upfront.{hh,cc}` and is exercised by
`knapsack_upfront_test`. To benchmark the two, the `knapsack_bench`
example posts the same problem with either class (`--upfront` selects
`KnapsackUpfront`, default is `Knapsack`) and times the difference; the
test pair is intentionally aligned (same data, same expected solutions,
same GAC check) so a divergence in either correctness or runtime is
easy to spot.

Measured on the four curated bench instances (10–9 items 0/1, k=2–3,
deterministic `dom_then_deg + smallest_first` enumeration):

| inst | per-call solve | upfront solve | per-call pbp | upfront pbp |
|------|---------------:|--------------:|-------------:|------------:|
| 1    | 1.11s          | 0.30s         | 124 MB       | 21 MB       |
| 2    | 1.21s          | 0.31s         | 142 MB       | 27 MB       |
| 3    | 0.71s          | 0.30s         | 82 MB        | 19 MB       |
| 4    | 0.91s          | 0.31s         | 104 MB       | 33 MB       |

`KnapsackUpfront` drops solver wall time ~3× and proof size ~3–6×. But
VeriPB verify time on the upfront proofs is *longer* (8–30s vs 1–2s,
i.e. the default per-call `Knapsack` verifies 3.6–18× faster) despite
the smaller file: the line-type mix has shifted out of `red` (~24 % →
~7 %) and into `pol` (~19 % → ~43 %), and each Top-level pol step
touches the long-running per-coord / joint flag families, which
linearly grows VeriPB's per-line work. This verify-time gap is exactly
why `Knapsack` (per-call) is the default and `KnapsackUpfront` is the
opt-in: the checker is on the critical path for the CI proof suite and
for anyone who verifies proofs routinely, whereas the smaller-proof win
only matters when proof size or distribution is the binding constraint.
Trimming the phantom-rule scaffolding (especially the layer-by-layer
recursive backward chains for joint-only-phantoms) is the obvious next
lead if the upfront checker-time regression becomes a problem.

A deterministic regression case for `KnapsackUpfront`'s per-call
dead-state path (`run_knapsack_upfront_regression` at the top of
`knapsack_upfront_test`) catches joint-only-phantom proof failures that
the random branching used by `solve_for_tests_checking_gac` reliably
masks; keep it at the head of the test main so a future regression of
the phantom-rule logic shows up before the random tests even start.

<!-- vim: set tw=72 spell spelllang=en : -->
