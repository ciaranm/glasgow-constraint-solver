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
`loads[b]`'s domain (or `≤ capacities[b]`). `C_b` is
`min(upper(loads[b]) [or caps[b]], Σ_i sizes[i])`.

**Scaffolding shape (paper-style inequality reifications + conjunction
main state).** For each statically-reduced `(b, i, w)`, three reified
flags at `ProofLevel::Top` via `create_proof_flag_reifying`:

- `g_up_{b,i,w}` ⇔ `Σ_{j<i} sizes[j]·(items[j]==b) ≥ w`
- `g_dn_{b,i,w}` ⇔ `Σ_{j<i} sizes[j]·(items[j]==b) ≤ w`
- `S_{b,i,w}` ⇔ `g_up_{b,i,w} + g_dn_{b,i,w} ≥ 2`  (sum exactly w)

The conjunction-of-sub-states pattern is from Demirović et al., CP
2024 §4 ("Knapsack as a Constraint"; PDF at
`ciaranm.github.io/papers/cp2024-dp.pdf`), specialised to one
partial-sum dimension. For Knapsack the conjunction adds further
sub-states (`P_↑/↓` over profit) — same shape, more legs.

Both the initialiser and the propagator capture a
`shared_ptr<BridgeMap>`; the initialiser writes flag handles, the
propagator reads them inside justification callbacks. This is exactly
the "third reusable idea" of `disjunctive-proof-logging.md` (declarative
OPB + propagator-introduced bridge), with the bridge vocabulary being
partial sums instead of time-table actives.

**Static reduction.** Performed in `prepare()` against initial item
domains: forward reachability from `(0,0)` intersected with backward
reachability from accepting terminals. Only surviving `(b, i, w)`
gets flag handles emitted at Top, and only surviving nodes are walked
by the runtime sweep.

**Per-call sweep.** Adapted from `MDD::propagate_mdd`: forward then
backward reachability against the *current* item domains; the per-bin
`alive` set is the intersection. For each `(item i, bin b)` candidate,
`items[i] = b` is supported iff there exists alive `(i, w)` with alive
`(i+1, w + sizes[i])`. Otherwise infer `items[i] ≠ b` via
`JustifyUsingRUP`. VeriPB chains through the reification axioms +
natural OPB + current reason to close the proof — no explicit dead-node
emission chain has proved necessary in practice (the bridge flags +
natural OPB equation give enough unit-propagation reach on the cases
tested so far).

**Per-bin GAC, not joint GAC.** Each bin's DAG sees only its own
constraint; cross-bin interactions that route an item elsewhere are
invisible. Worked example:
`items=[(0,1),(0,1),(0,1)] sizes=[1,2,2] caps=[3,2]` has 2 solutions
both with `items[0] = 0`, but Stage 3 doesn't prune `items[0] = 1` —
each bin alone admits it (bin 0 via "item 0 just leaves", bin 1 via
"item 0 takes its one unit while items 1, 2 sit out"). Joint GAC for
BinPacking reduces to subset-sum and is NP-hard. Shaw 2004-style
cardinality reasoning is a natural Stage 4-equivalent strengthening
within the per-bin envelope; tracked as a follow-up.

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
- **`Knapsack`** — currently builds and tears down its partial-sum DAG
  *and* its proof scaffolding on every propagation call, at
  `ProofLevel::Temporary`. The user goal flagged on issue #200 is to
  retrofit `Knapsack` to the `install_initialiser` + Top-level
  scaffolding pattern that `BinPacking` Stage 3 will introduce. Stage
  3's code shape should make that retrofit straightforward.
- **#200 unified framework** — the layered-DAG abstraction (per-layer
  node counts, transitions, accepting terminals) is the dispatch point.
  `MDD` is one user-supplied DAG; `BinPacking` synthesises `num_bins`
  DAGs from items + sizes + per-bin bound; `Knapsack` (after retrofit)
  is one DAG per equation; future `CostMDD` adds edge weights against
  a totalcost variable.

<!-- vim: set tw=72 spell spelllang=en : -->
