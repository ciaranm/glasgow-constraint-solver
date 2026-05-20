# `Regular`: design and proof scaffolding

Working-design note for the `Regular` propagator. The high-level
approach mirrors [`mdd.md`](mdd.md) (when written) and
[`knapsack.md`](knapsack.md) (when written) — build the layered graph
once in `prepare()`, emit the proof scaffolding (per-val backward
chains, statically-dead-state lines) once at `ProofLevel::Top` via
`install_initialiser`, and run a slim per-call sweep that emits at
most one cache-gated `~state[i][q]` line at `ProofLevel::Current`
per state-death.

## The three implementations

This file covers three implementations of the `Regular` constraint that
coexist in the codebase:

| Class                | Strategy                                                                 | File                                  |
|----------------------|--------------------------------------------------------------------------|---------------------------------------|
| `RegularLegacy`      | Per-call propagator emits per-(parent, val) intermediates each call.     | `gcs/constraints/regular/regular_legacy.{cc,hh}` |
| `Regular`            | Upfront per-val backward chains + statically-dead-state lines at Top, then per-call cache-gated `~state[i][q]` lines for dynamic state-deaths. | `gcs/constraints/regular/regular.{cc,hh}` |
| `RegularBacchus`     | Upfront Bacchus encoding (per-(i, q, v) transition extension variables + AL1s) derived from the natural OPB at Top; per-call propagator emits no proof. | `gcs/constraints/regular/regular_bacchus.{cc,hh}` |

The OPB is identical across all three — DFA semantics, no propagator
internals (see [Constraint definition](#constraint-definition) and
[OPB encoding](#opb-encoding) below). What differs is what each
implementation derives in its initialiser at search root, and what its
per-call propagator emits.

`gcs/constraints/regular.hh` is a top-level shim that includes all three.
For new code, post `Regular` (the default — see below); `RegularLegacy`
and `RegularBacchus` are retained primarily for benchmarking and for
issue #200's unified layered-DAG follow-up.

## Default: the upfront `Regular`

**`Regular` (this upfront-scaffolding propagator) is the default.**
Everything posts it — both frontends
(`xcsp_glasgow_constraint_solver`, `fzn_glasgow`), the constraint
tests, and the `regular_random` example. `RegularLegacy` — the older
per-call propagator that re-emits per-`(parent state, val)`
intermediate aggregations on every propagation call — is preserved
only as the `--legacy` opt-in twin, for side-by-side benchmarking and
as a correctness reference.

The reason for defaulting to upfront is that it **wins on both axes
that matter for proof logging**, measured within-branch (same search
tree to the digit — only the propagator is toggled):

- **Proof size: 13–55× smaller.** At the largest sampled instance the
  upfront `Regular` produced a 9 MB proof against `RegularLegacy`'s
  496 MB (7660 solutions).
- **VeriPB verification time: 2.3–7× faster** (1.66 s vs 11.69 s on
  that instance).

Both effects grow with search size: the fixed root scaffold amortises,
and the displaced per-call volume compounds. (At trivially small search
— tens of solutions — the fixed root scaffold is not yet amortised, so
upfront can be marginally bigger/slower; the crossover is well below
any real instance.)

This is the *narrow-diagram* case of the general decision-diagram
proof-strategy analysis: because a `Regular` automaton is narrow, the
permanent Top-level scaffold is tiny, so it adds almost no per-line
"DB-tax" to the rest of the proof, while the per-call `RegularLegacy`
baseline is very verbose (large displacement). Displacement far
exceeds the tax, so upfront wins size *and* time. See
[`decision-diagram-proof-strategies.md`](decision-diagram-proof-strategies.md)
for the cost model, the predictive rule, and how the same analysis
lands MDD, Knapsack and BinPacking on different defaults.

For the broader unification goal across `MDD`, `Regular`, `Knapsack`
and `BinPacking`, see issue #200.

## Constraint definition

A `Regular` constraint over a sequence `vars[0..n-1]` is parameterised
by a deterministic finite automaton:

- `num_states`, the number of DFA states (state `0` is the start)
- `transitions[q][val]`, a partial map from `(state, symbol) -> next
  state` shared across all positions
- `final_states`, the set of accepting states

The sequence `vars[0..n-1]` is accepted iff feeding the symbols from
left to right starting at state `0` ends in a state in `final_states`.

Each of the three classes supports the same two constructors (sparse
map / dense table form) plus a `short_reasons` boolean that is
forwarded to the propagator but unused (or near-unused) by `Regular`
and `RegularBacchus`. Keeping the flag as a dummy lets one
`regular_random` binary benchmark all three variants from one call
site.

## Layered DAG view

`Regular` is structurally a layer-uniform MDD: each input position
yields a copy of the same state set `0..num_states-1`, and the same
transition function applies at every position. Layer `i` holds the
DFA state after consuming the first `i` symbols, so there are
`n + 1` layers in total.

## OPB encoding

`define_proof_model` in all three classes emits:

```
state_i_is_q          (proof flag for each (i, q), i ∈ 0..n, q ∈ 0..num_states-1)
∑_q state_i_is_q == 1  for every layer i              (exactly-one per layer)
state_0_is_0 >= 1                                     (start state pinned)
∑_{f ∈ final_states} state_n_is_f >= 1                (accept at the end)
```

and, for every layer `i ∈ 0..n-1`, every state `q`, and every value
`val` in the OPB alphabet (the union of all transition keys and every
variable's initial domain):

- If `transitions[q]` has no entry for `val`:
  `(vars[i] != val) + ~state_i_is_q >= 1`
- Otherwise, where `q' = transitions[q][val]`:
  `~state_i_is_q + (vars[i] != val) + state_{i+1}_is_q' >= 1`

A human reading the OPB sees DFA semantics, not propagator internals.

## `Regular`'s Top-level scaffolding

`install_initialiser` emits, **once** at search root and only if proof
logging is enabled:

1. **Per-val backward chains.** For each `(i, q', val)` with
   `val ∈ initial dom(vars[i])`:
   ```
   ~state_{i+1}_is_q' + (vars[i] != val) + ∑_{q : T(q,val)=q'} state_i_is_q >= 1
   ```
   These are RUP-derivable from the OPB forward chains plus the
   per-layer exactly-one.

2. **Statically-dead-state lines.** A state is statically dead iff it
   has no path from the root forward, or no path forward to any
   accepting state, under initial domains. `Regular` emits
   `~state_i_is_q >= 1` for each at Top, in an order that lets RUP
   close (see source for ordering).

The per-subtree `DeadCache` is pre-populated with the static-dead set
so the per-call propagator's first emission for those states is a
no-op.

### `Regular`'s per-call propagator

For each propagation call: build the per-call support graph (forward,
backward), prune values whose support set is empty (`JustifyUsingRUP`),
and emit a cache-gated `~state_i_is_q >= 1` at Current for each newly
dead state. With the Top-level scaffolding plus the cached lines, both
the state-death RUPs and the value-pruning RUPs close on the proof DB.

## `RegularBacchus`'s Top-level scaffolding (issue #215)

Following [Bacchus, "GAC via unit propagation," CP 2007], the
`install_initialiser` derives a stronger scaffolding so that the
per-call propagator can emit **no proof lines at all** — every
value-pruning is `NoJustificationNeeded`, and VeriPB closes the
eventual backtrack RUP by UP on the Top-level encoding.

Concretely, for every `(i, q, v)` with `T(q,v)` defined:

1. Create a fresh transition flag `t[i][q][v]` via redundance, fully
   reifying
   `t[i][q][v] ⇔ (vars[i] = v ∧ state_i_is_q ∧ state_{i+1}_is_T(q,v))`.

2. Sum the OPB forward chain
   `~state_i_is_q + (vars[i] != v) + state_{i+1}_is_T(q,v) >= 1` with
   the t-flag reverse line via `pol` to derive
   `2·~state_i_is_q + 2·(vars[i] != v) + state_{i+1}_is_T(q,v) + ~state_{i+1}_is_T(q,v) + t[i][q][v] >= 2`.
   The complementary `state + ~state` pair is what unlocks the AL1
   RUPs below — VeriPB's UP collapses it during the RUP check.

3. Outgoing AL1: `~state_i_is_q + ∑_{v ∈ dom_q} t[i][q][v] >= 1`
   (one per `(i, q)` with `dom_q` non-empty).

4. Incoming AL1: `~state_{i+1}_is_q' + ∑_{(p, v) : T(p,v)=q'} t[i][p][v] >= 1`
   (one per `(i+1, q')`).

5. Variable-support AL1: `(vars[i] != v) + ∑_{q : T(q,v) def} t[i][q][v] >= 1`
   (one per `(i, v)` with `v` in the initial domain).

3–5 are emitted as RUP, and close via UP given the t-defs from step 1
and the per-(q, v) pol lines from step 2.

### `RegularBacchus`'s per-call propagator

The graph maintenance (forward/backward sweeps, `decrement_outdeg` /
`decrement_indeg`) is unchanged — still needed to *decide* which
values to prune — but every `infer_not_equal` call uses
`NoJustificationNeeded` and is passed `logger = nullptr`. No proof
line is written per call.

## Benchmark (regular_random)

`regular_random --legacy [--short-reasons]` and `--bacchus` expose the
three variants from one binary; the default runs `Regular`. Sampled at
the seeds in `examples/regular_random/CMakeLists.txt` and a few
additional ad-hoc seeds at each size:

| n  | seed         | variant     | solve   | verify | opb    | pbp    |
|---:|-------------:|-------------|--------:|-------:|-------:|-------:|
| 10 |  1           | Regular     | 0.00s   | 0.01s  |   24 KB |  167 KB |
| 10 |  1           | Bacchus     | 0.00s   | 0.06s  |  184 KB |  508 KB |
| 14 |  1           | Regular     | 0.01s   | 0.04s  |   ~     |  443 KB |
| 14 |  1           | Bacchus     | 0.02s   | 0.31s  |  462 KB | 1366 KB |
| 18 |  1           | Regular     | 0.02s   | 0.14s  |   ~     |  953 KB |
| 18 |  1           | Bacchus     | 0.06s   | 1.18s  |  970 KB | 2974 KB |
| 22 |  1           | Regular     | 0.06s   | 0.32s  |   ~     | 1761 KB |
| 22 |  1           | Bacchus     | 0.12s   | 4.61s  | 1744 KB | 5635 KB |
| 22 | -1115540197  | Regular     | 0.02s   | 0.12s  |   ~     |  843 KB |
| 22 | -1115540197  | Bacchus     | 0.05s   | 1.01s  |  909 KB | 2526 KB |

`RegularBacchus` produces proofs that are 2–3× larger than `Regular`'s
and VeriPB verifies them 5–20× slower at the sampled sizes. The
Bacchus encoding is wider — `O(n · |Q| · |Σ|)` extension variables and
AL1 RUP lines, vs `Regular`'s `O(n · |Q| · |Σ|)` per-val backward chains
and per-layer static-dead lines — and the per-(q, v) pol intermediate
that unlocks the AL1 RUPs costs another `O(n · |Q| · |Σ|)` lines.
Whereas `Regular`'s upfront scaffolding amortises across a per-call
sweep that emits at most one cache-gated line per state-death,
`RegularBacchus`'s upfront scaffolding pays the cost of strong-UP
propagation per branch regardless of how much per-call work the
propagator saves — and in `regular_random`'s search shape the saved
per-call lines don't make up the difference.

This matches the [BinPacking/Knapsack pattern
regression](https://github.com/ciaranm/glasgow-constraint-solver/issues/212):
the upfront-only approach beats the per-call-intermediates approach
only when per-call work is the dominant cost. `Regular`'s per-call
propagator is already lean (one line per state-death, cache-gated),
so further compressing it via UP closure leaves less to gain than the
Bacchus encoding's scaffolding costs to set up.

`RegularBacchus` is kept on the branch for issue #200 / the unified
layered-DAG follow-up: the t-flag definitions and AL1 derivations are
useful primitives even if the all-NoJustNeeded shape doesn't win
standalone.

## #200 follow-up

`Regular`, `RegularBacchus` and `MDD` now share related Top-scaffolding
shapes. Folding `Regular` and `MDD` into a single layered-DAG
scaffolder is the natural next step; `RegularBacchus` adds a third
axis (transition extension variables) that may or may not be worth
sharing across implementations depending on its measured value for
larger / different problem shapes.
