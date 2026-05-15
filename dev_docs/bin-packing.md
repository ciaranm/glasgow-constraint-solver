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

A `bounds_only` flag is reserved on every constructor; it currently has
no effect (Stage 1 propagates as a checker) and selects the cheaper
strategy once stronger reasoning lands.

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

Stage 1 is the only thing shipped today.

### Stage 1 — checker

- OPB as above.
- Propagator fires only when every `items[i]` is single-valued.
- Variable-load form: infer `loads[b] = computed_sum_b` via RUP — the
  load equation closes it.
- Constant-cap form: contradict if any `computed_sum_b > capacities[b]`,
  RUP-closed by the corresponding `≤` line.

Stage 1's `bounds_only` flag is documented but ignored. Sufficient
for end-to-end correctness; search does most of the work.

### Stage 2 — per-bin bounds

Per-bin bounds reasoning: maintain `load_min_b / load_max_b` from
currently-fixed items (lower) and currently-possibly-assigned items
(upper). Variable-load form prunes `loads[b]` bounds; constant-cap form
prunes `items[i]` values that would force a bin over its cap.

All inferences RUP-closable from the Stage 1 OPB encoding alone — no
new proof scaffolding required. `bounds_only=true` selects this as the
terminal strength.

### Stage 3 — per-bin partial-load DAG, GAC

For each bin `b` a layered DAG: layer `i` corresponds to item `i`,
nodes are partial-load values `w ∈ {0..C_b}`, edges are
"`items[i] == b`" (load `+= sizes[i]`) or "`items[i] ≠ b`" (load
unchanged), terminals are layer-`n` nodes whose load lies in
`loads[b]`'s domain (or `≤ capacities[b]`).

State flag per (bin, layer, node) and the transition clauses are
introduced via `Propagators::install_initialiser` at `ProofLevel::Top`,
*once* before search, derived from the per-bin OPB sum equation. The
bridge map (`shared_ptr<BridgeMap>` or similar) is captured by both the
initialiser and the propagator. The propagator runs the standard
forward / backward sweeps, infers `items[i] ≠ b` when no surviving DAG
path supports a value, and RUP-justifies against the Top-level
scaffolding. Mirrors `MDD::propagate_mdd` structurally; specialises
`disjunctive-proof-logging.md`'s "third reusable idea" with the path-
DAG vocabulary instead of the time-table one.

State-flag footprint is `O(n × Σ_b C_b)`; for capacities much larger
than `n` the GAC DAG is impractical. `bounds_only=true` is the user-
visible escape hatch (set the flag at construction time and Stage 3 is
skipped entirely). A heuristic auto-select threshold is a future
project.

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
