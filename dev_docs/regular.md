# `Regular`: design and proof scaffolding

Working-design note for the `Regular` propagator. The high-level
approach mirrors [`mdd.md`](mdd.md) (when written) and
[`knapsack.md`](knapsack.md) (when written) — build the layered graph
once in `prepare()`, emit the proof scaffolding (per-val backward
chains, statically-dead-state lines) once at `ProofLevel::Top` via
`install_initialiser`, and run a slim per-call sweep that emits at
most one cache-gated `~state[i][q]` line at `ProofLevel::Current`
per state-death.

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

Two constructors are supported, mirroring `RegularLegacy`:

- `Regular(vars, num_states, vector<unordered_map<Integer,long>>
  transitions, final_states)` — sparse map form.
- `Regular(vars, num_states, vector<vector<long>> transitions,
  final_states)` — dense table form (`-1` for no transition).

The `short_reasons` constructor parameter is kept on the new `Regular`
for API parity with `RegularLegacy` and for benchmarking
(`regular_random --legacy --short-reasons` covers the
short-reasons-on-legacy variant). It is forwarded to the propagator
but the new design emits at most one proof line per state-death, so
its effect is small or zero on this path.

## Layered DAG view

`Regular` is structurally a layer-uniform MDD: each input position
yields a copy of the same state set `0..num_states-1`, and the same
transition function applies at every position. Layer `i` holds the
DFA state after consuming the first `i` symbols, so there are
`n + 1` layers in total.

This makes `Regular` a degenerate case of `MDD` where every layer
shares its node set and transition function. The new implementation
exploits that fact only at the level of OPB encoding (one shared
alphabet rather than per-layer) and the scaffolding emission loop
(no per-layer state-count or transition lookup); the proof
derivations are the same as in `MDD`.

## OPB encoding (unchanged from `RegularLegacy`)

`define_proof_model` emits:

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

## Top-level scaffolding (new in `Regular`)

`install_initialiser` emits, **once** at search root and only if proof
logging is enabled:

1. **Per-val backward chains.** For each `(i, q', val)` with
   `val ∈ initial dom(vars[i])`:
   ```
   ~state_{i+1}_is_q' + (vars[i] != val) + ∑_{q : T(q,val)=q'} state_i_is_q >= 1
   ```
   These are RUP-derivable from the OPB forward chains plus the
   per-layer exactly-one: assume `state_{i+1}_is_q' = 1` and
   `vars[i] = val`; AMO at layer `i+1` forces every other
   `state_{i+1}_*` to zero; layer-`i` ALO forces some non-parent
   `state_i_is_q* = 1`; the OPB forward chain for `(q*, val)`
   UP-contradicts.

2. **Statically-dead-state lines.** A state is statically dead iff
   it has no path from the root forward, or no path forward to any
   accepting state, under initial domains. For each dead `(i, q)`
   `Regular` emits `~state_i_is_q >= 1` at Top:
   - Forward-unreachable nodes in ascending layer order — their RUP
     uses the new per-val backward chains plus already-emitted
     earlier-layer `~state_{i-1}_*` lines.
   - The rest (forward-reachable but no path forward to a final
     state) in descending layer order — their RUP uses the OPB
     forward chains plus already-emitted later-layer `~state_{i+1}_*`
     lines, plus the `final_states` ALO at layer `n`.

The per-subtree `DeadCache` is pre-populated with the static-dead set
so the per-call propagator's first emission for those states is a
no-op.

## Per-call propagator

For each propagation call:

1. On the first call, build the support graph (forward-reachability,
   then accepting-state filter, then backward-reachability) under the
   current domain. Each newly-dead `(i, q)` triggers one cache-gated
   `~state_i_is_q >= 1` line at Current.
2. On every call, for each value `val` that the propagator's record
   of `states_supporting[i][val]` knows still has support but is now
   absent from `vars[i]`'s current domain, drop the corresponding
   edges; the resulting `out_deg`/`in_deg` reductions cascade through
   `decrement_outdeg` / `decrement_indeg`, each step optionally
   emitting one cache-gated `~state_i_is_q >= 1` line at Current when
   a state's last edge disappears.
3. Final inferences: for every `(i, val)` where
   `states_supporting[i][val]` is empty, infer `vars[i] != val` with
   `JustifyUsingRUP{}` against the generic reason. The OPB forward
   chains plus the Top-level backward chains plus the cached
   `~state_*_*` lines let UP close it without any per-call
   intermediate emissions.

The contrast with `RegularLegacy` is exactly the same as the
MDD/Knapsack contrast: the legacy implementation emitted per-(parent
state, val) intermediate aggregations on every propagation call;
`Regular` does that work once at root.

## Benchmark (regular_random)

`regular_random --legacy [--short-reasons]` exposes all three
variants from one binary. Sampled at the seed already hard-coded into
`add_test(regular_random-seeded ...)`:

| n  | variant            | solve | proof    | verify |
|---:|--------------------|------:|---------:|-------:|
| 10 | new                | 0.00s | 86 KB    | 0.00s  |
| 10 | legacy             | 0.01s | 1.76 MB  | 0.03s  |
| 10 | legacy + short-rsn | 0.00s | 454 KB   | 0.04s  |
| 14 | new                | 0.00s | 230 KB   | 0.02s  |
| 14 | legacy             | 0.06s | 8.76 MB  | 0.13s  |
| 14 | legacy + short-rsn | 0.01s | 1.75 MB  | 0.24s  |
| 18 | new                | 0.01s | 490 KB   | 0.06s  |
| 18 | legacy             | 0.25s | 33.3 MB  | 0.51s  |
| 18 | legacy + short-rsn | 0.04s | 4.95 MB  | 0.98s  |

The new `Regular` produces proofs that are 4–68× smaller than the
legacy default and 1.5–10× smaller than the legacy with
`short_reasons` enabled, and VeriPB verifies them faster on every
sampled size. This matches the MDD-reimpl shape (proof shrink + slim
per-call); it doesn't follow the `BinPacking` regression because
`RegularLegacy`'s per-call work is far from already-lean.

## #200 follow-up

`Regular` and `MDD` now share the same Top-scaffolding shape modulo
layer-uniform vs per-layer transitions. Folding both into a single
layered-DAG scaffolder is the natural next step; that's the scope of
issue #200.
