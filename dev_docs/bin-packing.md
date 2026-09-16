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

The `with_consistency(...)` fluent setter selects the propagation
strength: `consistency::GAC` (the default) runs the Stage 2 bounds pass
followed by the Stage 3 per-bin DAG sweep (per-bin GAC); `consistency::BC`
runs the Stage 2 bounds pass alone (the cheaper option, for when per-bin
capacity is much larger than the number of items).

The `with_proof_strategy(...)` fluent setter selects the Stage 3
*proof-emission* strategy (only meaningful under `consistency::GAC`). It
changes only the proof, never the set of inferences drawn or the
solutions found:

- **`proof_strategy::PerCall` (the default).** Only the reified per-node
  state flags are defined at `ProofLevel::Top`; every aggregation is left
  to the per-call sweep's `JustifyUsingRUP` prunes, which RUP-close
  through those flags plus the natural per-bin OPB equations. This wins
  on both proof size and VeriPB verify time (see the benchmark table
  below), so it is the default.
- **`proof_strategy::Upfront` (opt-in).** The initialiser additionally
  derives the full forward/backward chain scaffolding once at
  `ProofLevel::Top`, so the per-call sweep only has to reference it.
  Larger, slower-to-verify proofs with no measured benefit on the
  in-tree benchmarks; kept for robustness and A/B measurement.

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

Stages 1, 2, 3 and 4 are shipped. Stage 1 is documented for
completeness; Stage 2 strictly subsumes it. Stage 3 sits on top of
Stage 2 as a GAC-strength (per bin, not joint) pass, and Stage 4 (#209)
is the opt-in cross-bin pass that reaches what no single bin can see.

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

**Reified per-node state flags (both proof strategies).** For each
forward-reachable `(b, i, w)`, three reified flags at `ProofLevel::Top`
via `create_proof_flag_reifying`:

- `g_up_{b,i,w}` ⇔ `Σ_{j<i} sizes[j]·(items[j]==b) ≥ w`
- `g_dn_{b,i,w}` ⇔ `Σ_{j<i} sizes[j]·(items[j]==b) ≤ w`
- `S_{b,i,w}` ⇔ `g_up_{b,i,w} + g_dn_{b,i,w} ≥ 2`  (sum exactly w)

The conjunction-of-sub-states pattern is from Demirović et al., CP
2024 §4 ("Knapsack as a Constraint"; PDF at
`ciaranm.github.io/papers/cp2024-dp.pdf`), specialised to one
partial-sum dimension. For Knapsack the conjunction adds further
sub-states (`P_↑/↓` over profit) — same shape, more legs. Both proof
strategies (below) define exactly these flags at Top; they differ only
in how much aggregation is pre-derived versus left to VeriPB's unit
propagation per call. The strategy is picked by the `upfront_proof`
constructor flag.

**Default strategy — per-call (`upfront_proof = false`).** The
initialiser emits nothing beyond the flag definitions above. The
per-call sweep (`run_stage3_for_bin`) recomputes the alive `(i, w)`
nodes under the current item domains (forward ∩ backward reachability
restricted to the static DAG) and, for each item whose "in bin `b`"
edge has no support in the alive DAG, prunes `items[i] ≠ b` with a bare
`JustifyUsingRUP`. VeriPB closes each prune by unit propagation through
the reified flags plus the natural per-bin OPB equation — no chain,
dead-node, or per-`(parent, val)` lines are written per call. Load
bounds are left to the Stage 2 bounds pass (`run_stage3_for_bin` prunes
item variables only). This is the smaller, faster-verifying proof
(benchmark below), so it is the default.

**Opt-in strategy — upfront (`upfront_proof = true`).** On top of the
flag definitions the initialiser derives the full chain scaffolding
(all at `Top`):

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

The upfront per-call sweep (`propagate_bin`) is a structural port of
Knapsack's `propagate` to `k = 1`. Forward walk under current item
domains restricted to the static DAG (with `LiveNode` predecessor
tracking); for each `w ∈ DAG[i+1] \ growing` either a cap-exceeded
`pol` step against the LE half of the per-bin OPB line (plus current
load upper for variable-load) followed by `~S` RUP at `Current`, or a
pure forward-unreachable `~S` RUP. Variable-load form additionally
filters layer `n` by current `loads[b]` lower bound (`~g_dn` + `~S`
cached) and interior holes; terminal `loads[b] ≥ lo` / `≤ hi`
inferences emit per-state `pol` chains and aggregating RUPs. Backward
pass over the predecessor map emits `~S` for dead intermediates and
infers `items[i] ≠ b` for unsupported bin candidates. Empty layer-`n` →
empty RUP + `inference.contradiction`. All per-call dead-state lines
are gated on a backtrack-restored `DeadCache` so they're emitted at
most once per `(b, i, w)` per subtree. Statically-dead `~S` lines are
NOT pre-emitted at Top because the natural pol-based derivations for the
wider load-bound cases (single-valued loads, interior holes) need the
same per-call pol+RUP machinery and the cache prevents redundant
emission anyway.

**Benchmark — why per-call is the default.** `bin_packing_bench` (built from
`benchmarks/bin_packing_bench/`), per-call (default) versus upfront
(`--upfront`):

| inst | layout | per-call proof | upfront proof | per-call veripb | upfront veripb | per-call solve | upfront solve |
|------|--------|---------------:|--------------:|----------------:|---------------:|---------------:|--------------:|
| 1 | 10it 3bin capa | 2.6 MB | 22 MB | 1.8s | 14.6s | 0.25s | 0.31s |
| 2 | 10it 3bin load | 14 MB | 296 MB | 10.3s | 102s | 2.34s | 2.54s |
| 5 | 8it 2bin tight capa | 155 KB | 1.1 MB | <0.01s | 0.10s | 0.006s | 0.01s |
| 6 | 8it 2bin wide-sizes | 177 KB | 1.2 MB | <0.01s | 0.14s | 0.008s | 0.01s |

Upfront proofs are 7–21× larger and 8–14× slower to verify than
per-call, while solver wall time stays within 1.1–1.5× (the extra
inferences `propagate_bin` draws barely move the search on these
instances). Per-call wins decisively on both proof axes, so it is the
default; upfront is an off-by-default opt-in (`upfront_proof = true`, or
`--upfront` in the bench) kept for robustness and A/B measurement. The
upfront design is the one that generalises to the #200 unified
path-DAG framework, which is why it is retained rather than deleted.
Worth revisiting if a future model makes either axis a measured pain
point.

**Per-bin GAC, not joint GAC.** Each bin's DAG sees only its own
constraint; cross-bin interactions that route an item elsewhere are
invisible. Worked example:
`items=[(0,1),(0,1),(0,1)] sizes=[1,2,2] caps=[3,2]` has 2 solutions
both with `items[0] = 0`, but Stage 3 doesn't prune `items[0] = 1` —
each bin alone admits it (bin 0 via "item 0 just leaves", bin 1 via
"item 0 takes its one unit while items 1, 2 sit out"). Joint GAC for
BinPacking reduces to subset-sum and is NP-hard, and stays out of
scope. Stage 4 below is the strengthening *within* the per-bin
envelope, and does prune this example.

**Footprint.** Per bin: ~`3 × surviving_nodes` flags, each with two
reification axioms. For `n=20`, `C_b=20`, 5 bins, ~6 000 flags +
~12 000 axiom lines after static reduction — workable. For `n=50`,
`C_b=100`, 10 bins it can climb into the high tens of thousands;
`bounds_only=true` is the user-visible escape hatch. There is no
general "warn when a constraint's OPB footprint gets large" mechanism
in the solver yet; documented here as a known sharp edge.

### Stage 4 — cross-bin cardinality (Shaw §4)

Everything above reasons about one bin at a time, so a joint infeasibility
that no single bin can see survives Stage 3. Stage 4 is the pass that
catches those, and it is opt-in:
`with_cardinality_reasoning(bin_packing::Shaw{})`, defaulting to
`bin_packing::NoCardinality{}` (measurements below).

The motivating example is the one #209 was opened with:
`items=[(0,1),(0,1),(0,1)] sizes=[1,2,2] caps=[3,2]`. Only two solutions
exist, both with `items[0] = 0`, but with `items[0] = 1` bin 1 has one
unit left and neither size-2 item fits, so both land in bin 0 and overflow
it — while bin 0's DAG alone is happy to let item 0 leave, and bin 1's
alone is happy to take it.

**The bound.** One cutting-planes derivation, parameterised by a threshold
`α`. Write `x_{i,b}` for `[items[i] == b]`, `D_i` for `items[i]`'s current
domain, `c_i = ceil(sizes[i] / α)`, `T_b` for the counted size that can
still go in bin `b`, and `cap_b` for the bin's capacity (constant-cap
form) or the current upper bound of `loads[b]` (variable-load form). For
each bin, take its capacity row, weaken away the items not being counted,
and divide:

```
    sum_{i in S, b in D_i} sizes[i] ~x_{i,b} >= T_b - cap_b
      --- alpha d --->
    sum_{i in S, b in D_i} c_i ~x_{i,b} >= R_b,   R_b = ceil((T_b - cap_b) / alpha)
```

Sum those over every bin and add `c_i` times each counted item's
at-least-one row. Every `~x + x` pair collapses to a constant, leaving

```
    sum_{i in S} c_i (terms for the bins D_i has lost) >= DELTA
    DELTA = sum_b max(0, R_b) - sum_{i in S} c_i (|D_i| - 1)
```

whose surviving terms are exactly the ones the reason rules out. So
`DELTA >= 1` is a contradiction.

**Why one family covers both classical bounds.** `α = 1` gives `c_i =
sizes[i]`, and (with every item free to go anywhere) `DELTA >= 1` reduces
to `sum_i sizes[i] > sum_b cap_b` — the energy bound, which is a plain
`pol` with no division. A large `α` gives `c_i = 1` for the items above
the threshold and `R_b` counts how many of them a bin cannot take, so
`DELTA >= 1` reduces to "more big items than big-item slots" — pigeonhole,
which unit propagation cannot do at all, and which is why the division
step is load-bearing rather than cosmetic. The rounding in between is
what the Martello–Toth L2 bound is made of, and Shaw §4 is where bin
packing gets it. `DELTA` is piecewise constant in `α` with breakpoints at
the item sizes, so the distinct sizes plus 1 are the whole family.

**Which items are counted.** `S(α)` is the items with `sizes[i] >= α`,
plus every item already pinned to a bin whatever its size. An item below
the threshold buys less than a whole unit of a bin's divided capacity
while costing `c_i (|D_i| - 1)`, so it only pays its way once `|D_i| = 1`
— which is exactly where that cost is zero. This is the domain-aware
form of the threshold rule L2 uses: the classical bound has no domains to
be aware of, and `|D_i| - 1` is where ours reads them.

**`max(0, R_b)` and not `R_b`.** A bin with room to spare has a negative
`R_b` that would drag the sum down. Such a bin supplies the trivially
true `sum c_i ~x_{i,b} >= 0` instead of its capacity row — its terms are
still needed, because they are what the at-least-one rows cancel against,
but its slack is not allowed to pay for another bin's overflow. Sabotaging
this (mutation 5 below) is rejected by VeriPB, so it is not an
optimisation: taking the capacity row there derives a *different, weaker*
line than the arithmetic assumed.

**Shaving.** The same computation with one item's domain overridden to a
single bin: if `DELTA >= 1` under `items[h] = b`, then `items[h] != b`.
The hypothesis costs the proof nothing. `h`'s at-least-one row is stated
over its *real* domain, so the bins it is not being shaved into survive as
positive terms, and the closing RUP's negated goal is what kills them —
the "extended reason" shape of `constraints.md`, arrived at by leaving a
row alone rather than by adding a disjunct. Only one item is hypothesised
at a time; the incremental form is `DELTA(h, b) = base_less_h - without +
with_h - penalty_less_h`, so the whole shaving scan costs `O(bins)` per
item on top of the sweep that was going to happen anyway.

**What it emits.** Per inference: one trivially-true weakening line per
bin whose capacity row is used, one `pol` per bin, and one `pol` summing
them against the at-least-one rows — then `ThenRUP::Yes` closes. No new
proof flags, no new OPB rows, and nothing at `Top`: Stage 4 needs no
scaffolding at all, which is the main reason it came in at a fraction of
the 300–500 lines #209 estimated for the proof side. The reason is the
shared generic reason over the item variables, plus each bin's load upper
bound in the variable-load form.

**Where the work goes.** Per propagation call the sweep is `O(items ×
bins)` to read the domains, then `O(items)` per threshold to recompute the
weights and the penalty. The per-bin totals are maintained across the
threshold list rather than recomputed: `S(α)` only grows as `α` falls, so
the thresholds are walked largest-first and each item folds into the
totals once. The shaving scan is gated on `base - penalty + c_h |D_h| >=
1`, a necessary condition that costs `O(1)` per item, so the `O(bins)`
work happens only where a prune is possible.

**Benchmark.** `bin_packing_bench`, default (per-call) Stage 3 proofs,
`--cardinality` against the default, one core of an otherwise idle
fataepyc-10:

| inst | layout | recursions | +S4 | solve | +S4 | proof | +S4 | veripb | +S4 |
|------|--------|-----------:|----:|------:|----:|------:|----:|-------:|----:|
| 1 | 10it 3bin capa | 7 192 | 7 192 | 41ms | 48ms | 2.94 MB | 2.97 MB | 3.60s | 3.61s |
| 2 | 10it 3bin load | 20 029 | 20 029 | 127ms | 158ms | 14.46 MB | 14.46 MB | 13.5s | 13.5s |
| 3 | 12it 4bin capa wide | 5 654 897 | 5 654 897 | 35.1s | 41.2s | — | — | — | — |
| 4 | 12it 4bin load wide | 2 726 033 | 2 726 033 | 25.3s | 30.1s | — | — | — | — |
| 5 | 8it 2bin tight capa | 63 | 47 | 0.64ms | 0.59ms | 201 KB | 208 KB | 0.01s | 0.02s |
| 6 | 8it 2bin wide-sizes | 83 | 71 | 0.74ms | 0.74ms | 217 KB | 224 KB | 0.01s | 0.02s |
| 7 | 9it 4bin pigeonhole capa | 4 485 | **1** | 34ms | **0.23ms** | 1.64 MB | **189 KB** | 0.17s | **0.01s** |
| 8 | 9it 4bin pigeonhole load | 4 485 | **1** | 35ms | **0.24ms** | 2.29 MB | **190 KB** | 0.31s | **0.01s** |

Instances 7 and 8 are what the pass is for: nine items each over a third
of a bin and four bins, so two fit in a bin and three do not, leaving
eight places for nine items. No capacity row is violated and no per-bin
DAG edge is lost until the search has committed two items to a bin, so
Stages 2 and 3 enumerate their way to the contradiction while Stage 4
refutes it where it stands — 4 485 search nodes down to one, a proof
8.7–12× smaller, and 17–31× faster to verify.

Instances 1 to 4 are the other side of the trade and are why the default
is off. They enumerate every solution, so extra pruning cannot shorten
the search (1 and 2 lose a few propagation calls but not a single node),
and the sweep is pure overhead: 17–24% of solve time, on the two large
ones 17% and 19%. Proofs grow 0–4% where Stage 4 fires without changing
the tree, and instance 2's is byte-identical because it never fires
there at all. On this curated set the pass is a clear loss on four
instances, roughly neutral on two, and decisive on two; that profile is
an opt-in, not a default.

**Mutation testing.** Seven sabotages, each run against the whole
`bin_packing_test` lane at two pinned seeds (the lane reseeds per run, so
an unpinned mutation result measures the seed — three of these were
seed-dependent before the fixtures below were added):

| mutation | outcome |
|----------|---------|
| infer at `DELTA >= 0` instead of `>= 1` (contradiction) | lost solutions, **and** VeriPB rejects the `pol` |
| the same for the shaving arm | lost solutions, **and** VeriPB rejects |
| drop the `alpha d` division | VeriPB rejects |
| drop every at-least-one row from the final `pol` | VeriPB rejects |
| drop two of the at-least-one rows | VeriPB rejects |
| drop one of the at-least-one rows | **survives** |
| use the capacity row where `max(0, R_b)` chose the trivial one | VeriPB rejects |

The threshold is exactly right: at `DELTA = 0` the derivation does not
close, so the `>= 1` is the proof's own boundary and not a safety margin.

Two of those took a fixture to pin down, and both fixtures are in the
suite because of it. The clamp one needs a bin that is *slack and
occupied* at the moment the bound fires — `{7,7,7,1}` over caps
`{10,10,100}` with the unit item pinned to the big bin — because with
every bin tight the clamp never chooses differently, and with the slack
bin empty its line has no terms to distort. The at-least-one ones need
enough counted items that VeriPB cannot finish the cancellation itself.

That last row is the one to know about, and it is not worth exploiting:
with a single row missing the resulting line still propagates that item
out of every bin in its domain, and VeriPB's own unit propagation then
closes against the encoding's at-least-one. Drop two and it cannot.
Dropping "the ones UP would have re-derived" would be fixture-shaped
rather than argument-shaped, so every counted item's row goes in.

**Deliberately not done.**

- *Bin subsets.* The derivation sums over every bin, using each item's
  `|D_i|` rather than a common bin-set size, so a restricted domain is
  already read at full strength and there is no Hall-set search to run.
  A genuine subset argument would need `S` and the bin set chosen
  together, and nothing in the measurements asks for it.
- *Exact per-bin cardinality.* "How many of `S` fit in bin `b`" is a
  knapsack question, and the greedy answer (the `k` smallest) is stronger
  than `floor(cap_b / α)`. It is not one division, so it is not one `pol`,
  and the threshold family already recovers the cases that matter.
- *Load bounds.* Stage 4 infers item prunes and contradictions only; the
  load variables are left to Stage 2.
- *Bins whose ceiling cannot be cited.* In the variable-load form the
  ceiling enters the `pol` as a bound literal on `loads[b]`, which
  `add_bound_p_term` states for a plain variable only: a view operand
  would need explicit `pol` arithmetic over a view (see
  `view-proof-logging.md`) and a constant has no bound literal at all.
  Such a bin contributes zero to `DELTA` instead, which costs strength
  and never soundness. The decision is made from the operand's *kind*,
  so the inferences drawn do not depend on whether proofs are being
  written — the alternative, throwing `UnimplementedException` the way
  the `upfront` Stage 3 strategy does for the same operands, is what the
  degenerate-load fixtures exist to keep out.
- *Joint GAC.* Still NP-hard, still out of scope. Stage 4 strengthens the
  envelope, it does not close it.

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
- **`Knapsack`** — the opt-in `KnapsackUpfront` variant is retrofitted
  to the same `install_initialiser` + Top-level scaffolding pattern
  Stage 3 uses here, generalised to *k* partial-sum coordinates. See
  [`knapsack.md`](knapsack.md). The default `Knapsack` remains the
  per-call DP implementation (it verifies faster); `KnapsackUpfront`
  is the smaller-proof opt-in.
- **#200 unified framework** — the layered-DAG abstraction (per-layer
  node counts, transitions, accepting terminals) is the dispatch point.
  `MDD` is one user-supplied DAG; `BinPacking` synthesises `num_bins`
  scalar DAGs from items + sizes + per-bin bound; `Knapsack`
  synthesises one *k*-dim DAG per constraint; future `CostMDD` adds
  edge weights against a totalcost variable.

<!-- vim: set tw=72 spell spelllang=en : -->
