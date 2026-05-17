# `BinPacking`: design and staging

This is a working-design note for the `BinPacking` propagator (#148). It
captures the intended shape so future stages are predictable and so the
extraction towards the unified path-DAG framework (#200) doesn't lose
context. It is not a record of what currently exists in every stage —
read `gcs/constraints/bin_packing.{hh,cc}` for that.

## Constraint definition

Two forms, sharing one propagator:

- **Variable loads.** `loads[b]` equals
  `Σ_i { sizes[i] : items[i] == b }`. Items range over
  `0..loads.size() − 1`.
- **Constant capacities.** `Σ_i { sizes[i] : items[i] == b ] ≤ capacities[b]`.
  Items range over `0..capacities.size() − 1`.

Item sizes are non-negative. Frontends with non-zero-based bin indices
(MiniZinc's `lb_array(bin)..ub_array(bin)`; XCSP3's per-bin index
ranges) shift to 0-based at the binding so the gcs class always sees
items in `0..num_bins − 1`.

A `bounds_only` flag on every constructor selects the cheaper
propagation strategy: when set, only the Stage 2 bounds pass runs;
when clear (the default), Stage 2 is followed by the Stage 3
per-bin DAG sweep.

## OPB encoding: spec-faithful, propagator-agnostic

`define_proof_model` emits exactly the natural definition: per bin `b`,
the load equation (or capacity inequality). A human reading the OPB
sees a sum of per-(bin, item) indicator terms equated against either a
load variable or a constant bound. No per-bin DAG state flags, no
auxiliary scaffolding — those are propagator vocabulary and belong in
the proof body, not the model.

This is the same encoding-vs-scaffolding split that
`disjunctive-proof-logging.md` documents as "declarative OPB encoding
with a propagator-introduced bridge". The principle is repeated here
because the staged propagator below leans on it: each stage is allowed
to strengthen the *proof scaffolding* (and the corresponding
propagation), but the OPB stays the same shape — the per-bin sum
equations.

## Staging

Stages 1, 2 and 3 are shipped. Stage 1 is documented for completeness;
Stage 2 strictly subsumes it. Stage 3 sits on top of Stage 2 as a
GAC-strength (per bin, not joint) pass.

### Stage 1 — checker (superseded)

- OPB as above.
- Propagator fires only when every `items[i]` is single-valued.
- Variable-load form: infer `loads[b] = computed_sum_b` via RUP — the
  load equation closes it.
- Constant-cap form: contradict if any `computed_sum_b > capacities[b]`,
  RUP-closed by the corresponding `≤` line.

### Stage 2 — per-bin bounds

For each bin `b`, partition items into three buckets in one pass:
forced-into-`b` (single-valued at bin `b`), excluded-from-`b` (bin `b`
no longer in the item's domain), and still-possibly-in-`b`. Then:

- `floor_b = Σ sizes[i]` over forced-into-`b`.
- `ceiling_b = floor_b + Σ sizes[i]` over still-possibly-in-`b`.

Inferences (variable-load form):

- Lift `loads[b]` lower bound to `floor_b` when above. RUP from the
  per-bin OPB equation plus the forced-into-`b` `items[i] == b`
  literals.
- Drop `loads[b]` upper bound to `ceiling_b` when below. RUP from the
  per-bin equation plus the excluded-from-`b` `items[i] != b` literals.
- For each still-possibly-in-`b` item `i`: if `floor_b + sizes[i] >
  upper(loads[b])`, prune `items[i] != b` (else assigning forces a
  load overflow). Reason: forced-into-`b` literals + the `loads[b]`
  upper bound.
- For each still-possibly-in-`b` item `i`: if `ceiling_b - sizes[i] <
  lower(loads[b])`, force `items[i] = b` (else excluding drops the
  ceiling below the floor). Reason: excluded-from-`b` literals + the
  `loads[b]` lower bound.

Inferences (constant-cap form):

- Contradict when `floor_b > capacities[b]`. Reason: forced-into-`b`
  literals.
- For each still-possibly-in-`b` item `i`: if `floor_b + sizes[i] >
  capacities[b]`, prune `items[i] != b`. Reason: forced-into-`b`
  literals.

All inferences RUP-close from the Stage 1 OPB encoding alone — no new
proof scaffolding needed. The Stage 1 all-fixed check is structurally
subsumed: when every item is single-valued, `floor_b == ceiling_b ==`
the exact bin sum and the load-bound inferences collapse to the same
equality.

Each propagation call sweeps every bin once. Inferences inside one
bin's sweep don't update its own `floor_b` / `ceiling_b` mid-sweep;
the framework re-fires the propagator on any domain change and the
next call catches anything missed.

`bounds_only=true` runs only Stage 2 (no Stage 3 DAG); leave it clear
(the default) to add Stage 3 on top.

### Stage 3 — per-bin partial-load DAG, per-bin GAC

For each bin `b` a layered DAG: layer `i` corresponds to item `i`,
nodes are partial-load values `w ∈ {0..C_b}`, edges are
"`items[i] == b`" (load `+= sizes[i]`) or "`items[i] ≠ b`" (load
unchanged), terminals are layer-`n` nodes whose load lies in
`loads[b]`'s domain (or `≤ capacities[b]`). `C_b = Σ_i sizes[i]` —
matching Knapsack, no intersection with `loads[b]`'s initial upper or
`caps[b]` (Knapsack's "Static reduction" rationale carries over: the
per-call cap-exceeded path needs a Top flag for the over-bound
successor to chain against).

**Scaffolding shape (paper-style inequality reifications + conjunction
main state).** For each forward-reachable `(b, i, w)`, three reified
flags at `ProofLevel::Top` via `create_proof_flag_reifying`:

- `g_up_{b,i,w}` ⇔ `Σ_{j<i} sizes[j]·(items[j]==b) ≥ w`
- `g_dn_{b,i,w}` ⇔ `Σ_{j<i} sizes[j]·(items[j]==b) ≤ w`
- `S_{b,i,w}` ⇔ `g_up_{b,i,w} + g_dn_{b,i,w} ≥ 2`  (sum exactly w)

The conjunction-of-sub-states pattern is from Demirović et al., CP
2024 §4 ("Knapsack as a Constraint"; PDF at
`ciaranm.github.io/papers/cp2024-dp.pdf`), specialised to one
partial-sum dimension. For Knapsack the conjunction adds further
sub-states (`P_↑/↓` over profit) — same shape, more legs.

On top of these reifications the initialiser emits (all at `Top`):

1. **Phantom flags** for non-DAG backward parents that backward chains
   reference. For `k = 1` every phantom is per-coord-phantom and
   closes via a pair-wise `pol` against `DAG[i]`'s feasible projection
   plus a closing `~S_phantom ≥ 1` RUP.
2. **Per-coord and joint forward chains** for every `(parent, branch,
   succ)` edge: `pol succ.g_up.rev + parent.g_up.fwd ; saturate` then
   the RUP twin, same for `g_dn`, then `~parent.S + branch-lit +
   succ.S ≥ 1`.
3. **Layer-0 ALO** `S_{b,0,0} ≥ 1`, plus per-layer ALOs and per-state
   implications by induction.
4. **Joint backward chains** for every `(succ, branch)` with succ in
   `DAG[i+1] ∪ phantoms[i+1]`. Three flavours: negative-coord
   (`include` with `w' < sizes[i]`, direct RUP), DAG parent (per-coord
   + joint chain), phantom parent (same shape, phantom flag).
5. **Phantom closure** as above.

This is the k=1 specialisation of Knapsack's `emit_scaffolding`; the
two implementations duplicate substantially. Folding both into a shared
layered-DAG scaffolder is tracked under #200.

**Per-call sweep.** Structural port of Knapsack's `propagate` to
`k = 1`. Forward walk under current item domains restricted to the
static DAG (with `LiveNode` predecessor tracking); for each
`w ∈ DAG[i+1] \ growing` either a cap-exceeded `pol` step against the
LE half of the per-bin OPB line (plus current load upper for
variable-load) followed by `~S` RUP at `Current`, or a pure
forward-unreachable `~S` RUP. Variable-load form additionally filters
layer `n` by current `loads[b]` lower bound (`~g_dn` + `~S` cached) and
interior holes; terminal `loads[b] ≥ lo` / `≤ hi` inferences emit
per-state `pol` chains and aggregating RUPs. Backward pass over the
predecessor map emits `~S` for dead intermediates and infers
`items[i] ≠ b` for unsupported bin candidates. Empty layer-`n` →
empty RUP + `inference.contradiction`.

All per-call dead-state lines are gated on a backtrack-restored
`DeadCache` so they're emitted at most once per `(b, i, w)` per
subtree. Statically-dead `~S` lines are NOT pre-emitted at Top because
the natural pol-based derivations for the wider load-bound cases
(single-valued loads, interior holes) need the same per-call pol+RUP
machinery and the cache prevents redundant emission anyway.

**Benchmarks vs the pre-#200 BinPacking (which emitted nothing per
call, relying on VeriPB's UP through the reifications + natural OPB).**
`examples/bin_packing_bench` instances:

| inst | layout | old proof | new proof | old veripb | new veripb | old solve | new solve |
|------|--------|----------:|----------:|-----------:|-----------:|----------:|----------:|
| 1 | 10it 3bin capa | 2.6 MB | 22 MB | 1.8s | 14.6s | 0.25s | 0.31s |
| 2 | 10it 3bin load | 14 MB | 296 MB | 10.3s | 102s | 2.34s | 2.54s |
| 5 | 8it 2bin tight capa | 155 KB | 1.1 MB | <0.01s | 0.10s | 0.006s | 0.01s |
| 6 | 8it 2bin wide-sizes | 177 KB | 1.2 MB | <0.01s | 0.14s | 0.008s | 0.01s |

Proof size grows 7–21×, VeriPB verify time grows 8–14×, solver wall
time grows 1.1–1.5×. This is a **regression** on every measured axis,
the opposite of the Knapsack result (3× solve, 3–6× proof shrink).
Reason: pre-#200 BinPacking emitted essentially nothing per call and
leaned on VeriPB UP to do the lookup against the reified flags. The
new design replaces that implicit work with explicit chains —
principled and aligned with the #200 unified framework path, but on
these benchmarks strictly more verbose. The trade-off is robustness
(no more "if RUP can't close, copy the MDD template" fragility) for
size. Worth revisiting if any of these axes becomes a measured pain
point.

**Per-bin GAC, not joint GAC.** Each bin's DAG sees only its own
constraint; cross-bin interactions that route an item elsewhere are
invisible. Worked example:
`items=[(0,1),(0,1),(0,1)] sizes=[1,2,2] caps=[3,2]` has 2 solutions
both with `items[0] = 0`, but Stage 3 doesn't prune `items[0] = 1` —
each bin alone admits it (bin 0 via "item 0 just leaves", bin 1 via
"item 0 takes its one unit while items 1, 2 sit out"). Joint GAC for
BinPacking reduces to subset-sum and is NP-hard. Shaw 2004-style
cardinality reasoning (the L2 Martello-Toth lower bound + shaving) is
a natural Stage 4-equivalent strengthening within the per-bin
envelope; tracked under #209.

**Footprint.** Per bin: ~`3 × surviving_nodes` flags, each with two
reification axioms. For `n=20`, `C_b=20`, 5 bins, ~6 000 flags +
~12 000 axiom lines after static reduction — workable. For `n=50`,
`C_b=100`, 10 bins it can climb into the high tens of thousands;
`bounds_only=true` is the user-visible escape hatch. There is no
general "warn when a constraint's OPB footprint gets large" mechanism
in the solver yet; documented here as a known sharp edge.

## Frontends

- **XCSP3** — four `binPacking` signatures land on this propagator:
  single `<condition>`, `<limits>` (constants or variables), `<loads>`
  (constants or variables). Per-bin `<conditions>` (signature 4) and
  variable capacities under `<limits>` are deferred as `unsupported`.
- **MiniZinc** — `fzn_bin_packing` / `fzn_bin_packing_capa` /
  `fzn_bin_packing_load` are overridden in `mznlib/`, dispatched via
  `glasgow_bin_packing_capa` / `glasgow_bin_packing_load`.

## Relation to other constraints

- **`MDD`** (#149) — `MDD`'s natural definition *is* the layered DAG,
  so its state flags belong in the OPB. `BinPacking`'s natural
  definition is the sum equations, so its per-bin DAGs (when added in
  Stage 3) belong in the proof scaffolding, not the OPB.
- **`Knapsack`** — retrofitted to the same `install_initialiser` +
  Top-level scaffolding pattern Stage 3 uses here, generalised to *k*
  partial-sum coordinates. See [`knapsack.md`](knapsack.md). The
  legacy per-call-DAG implementation is preserved as `KnapsackLegacy`
  for benchmarking.
- **#200 unified framework** — the layered-DAG abstraction (per-layer
  node counts, transitions, accepting terminals) is the dispatch point.
  `MDD` is one user-supplied DAG; `BinPacking` synthesises `num_bins`
  scalar DAGs from items + sizes + per-bin bound; `Knapsack`
  synthesises one *k*-dim DAG per constraint; future `CostMDD` adds
  edge weights against a totalcost variable.

<!-- vim: set tw=72 spell spelllang=en : -->
