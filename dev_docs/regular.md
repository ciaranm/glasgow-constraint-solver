# `Regular`: design and proof scaffolding

Working-design note for the `Regular` propagator. The high-level
approach mirrors [`mdd.md`](mdd.md) (when written) and
[`knapsack.md`](knapsack.md) (when written) — build the layered graph
once in `prepare()`, emit the proof scaffolding (per-val backward
chains, statically-dead-state lines) once at `ProofLevel::Top` via
`install_initialiser`, and run a slim per-call sweep that emits at
most one cache-gated `~state[i][q]` line at `ProofLevel::Current`
per state-death.

## The three proof strategies

There is a single public `Regular` constraint. Its proof-logging
strategy is selected with the fluent
`with_proof_strategy(proof_strategy::…)` setter (see
[`proof_strategy.hh`](../gcs/proof_strategy.hh)), defaulting to
`Upfront`:

| `proof_strategy::` | Strategy                                                                 | Implementation |
|--------------------|--------------------------------------------------------------------------|----------------|
| `PerCall`          | Per-call propagator emits per-(parent, val) intermediates each call.     | `gcs/constraints/regular/regular_legacy.{cc,hh}` |
| `Upfront` (default) | Upfront per-val backward chains + statically-dead-state lines at Top, then per-call cache-gated `~state[i][q]` lines for dynamic state-deaths. | `gcs/constraints/regular/regular.{cc,hh}` |
| `Bacchus`          | Upfront Bacchus encoding (per-(i, q, v) transition extension variables + AL1s) derived from the natural OPB at Top; per-call propagator emits no proof. Deterministic automata only (not regex/NFA input). | `gcs/constraints/regular/regular_bacchus.{cc,hh}` |

The OPB is identical across all three — DFA semantics, no propagator
internals (see [Constraint definition](#constraint-definition) and
[OPB encoding](#opb-encoding) below). What differs is what each strategy
derives in its initialiser at search root, and what its per-call
propagator emits; the choice never changes the inferences drawn or the
solutions found.

The public `Regular` front-end (`gcs/constraints/regular/regular.{cc,hh}`)
*is* the `Upfront` implementation; for `PerCall` and `Bacchus` its
`install()` constructs and delegates to the sibling implementations,
which are internal to the constraint (not part of the public API — they
are no longer named in `gcs/constraints/regular.hh`). Everything posts
`Regular`; benchmarking picks a strategy with `with_proof_strategy(...)`.

## Default: `proof_strategy::Upfront`

**The upfront-scaffolding strategy is the default.** Everything posts a
plain `Regular` — both frontends (`xcsp_glasgow_constraint_solver`,
`fzn_glasgow`), the constraint tests, and the `regular_random` example.
The `PerCall` strategy — the older per-call implementation that re-emits
per-`(parent state, val)` intermediate aggregations on every propagation
call — is reachable via `with_proof_strategy(proof_strategy::PerCall{})`
(the `regular_random --legacy` flag), for side-by-side benchmarking and
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

`Regular` supports two automaton constructors (sparse map / dense table
form) plus a regex form, and a `short_reasons` boolean (via
`with_short_reasons()`) forwarded to the propagator but unused (or
near-unused) by the `Upfront` and `Bacchus` strategies. Keeping the flag
as a dummy lets one `regular_random` binary benchmark all three
strategies from one call site.

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
the seeded ctest baseline plus four ad-hoc seeds at each size. `rec` is
the `recursions` count and `props₀` is the first integer of the
`propagations:` line from `--stats` (identical across variants since
they make the same propagator decisions; included so the reader can
gauge how much of the work is search vs initialisation).

| n  | seed         | rec | props₀ | variant | solve | verify | opb     | pbp     |
|---:|-------------:|----:|-------:|---------|------:|-------:|--------:|--------:|
| 10 |  1           |  11 |     17 | Regular | 0.00s | 0.01s  |  ~      |  167 KB |
| 10 |  1           |  11 |     17 | Bacchus | 0.00s | 0.06s  |  184 KB |  508 KB |
| 10 | -1115540197  |  11 |     21 | Regular | 0.00s | 0.00s  |  ~      |   86 KB |
| 10 | -1115540197  |  11 |     21 | Bacchus | 0.00s | 0.02s  |  104 KB |  218 KB |
| 14 |  1           |  15 |     23 | Regular | 0.01s | 0.04s  |  ~      |  443 KB |
| 14 |  1           |  15 |     23 | Bacchus | 0.02s | 0.31s  |  462 KB | 1366 KB |
| 14 | -1115540197  |  15 |     25 | Regular | 0.00s | 0.02s  |  ~      |  230 KB |
| 14 | -1115540197  |  15 |     25 | Bacchus | 0.01s | 0.11s  |  257 KB |  625 KB |
| 18 |  1           |  19 |     30 | Regular | 0.02s | 0.14s  |  ~      |  953 KB |
| 18 |  1           |  19 |     30 | Bacchus | 0.06s | 1.18s  |  970 KB | 2974 KB |
| 18 | -1115540197  |  18 |     36 | Regular | 0.01s | 0.05s  |  ~      |  490 KB |
| 18 | -1115540197  |  18 |     36 | Bacchus | 0.02s | 0.35s  |  524 KB | 1390 KB |
| 22 |  1           |  23 |     34 | Regular | 0.06s | 0.32s  |  ~      | 1761 KB |
| 22 |  1           |  23 |     34 | Bacchus | 0.12s | 4.61s  | 1744 KB | 5635 KB |
| 22 | -1115540197  |  23 |     45 | Regular | 0.02s | 0.12s  |  ~      |  843 KB |
| 22 | -1115540197  |  23 |     45 | Bacchus | 0.05s | 1.01s  |  909 KB | 2526 KB |

Caveat: `regular_random`'s instances above do almost no search —
`recursions` is ~`n + 1` and `propagations` stays in the tens — so
the table is dominated by initialisation work, which is the regime
where `Regular`'s lean per-call sweep needs the fewest lines and
Bacchus's upfront scaffolding pays its highest fixed cost. On these
shallow / no-search instances Bacchus's PBP is 2–3× larger than
`Regular`'s and VeriPB verifies it 5–20× slower.

### Search-intensive: `regular_random --all`

`--all` enumerates every accepting string instead of stopping at the
first solution, which forces real search at much smaller `n`. The
picture flips on PBP size:

| n | seed         | rec    | props₀ | sols   | variant | solve | verify | pbp      |
|--:|-------------:|-------:|-------:|-------:|---------|------:|-------:|---------:|
| 4 |  1           |    238 |    293 |    165 | Regular | 0.00s | 0.10s  |   74 KB  |
| 4 |  1           |    238 |    293 |    165 | Bacchus | 0.00s | 0.10s  |   69 KB  |
| 5 |  1           |   2260 |   2484 |   1746 | Regular | 0.02s | 0.20s  |  730 KB  |
| 5 |  1           |   2260 |   2484 |   1746 | Bacchus | 0.02s | 0.20s  |  461 KB  |
| 5 | 42           |   1877 |   2259 |   1364 | Regular | 0.02s | 0.10s  |  660 KB  |
| 5 | 42           |   1877 |   2259 |   1364 | Bacchus | 0.01s | 0.20s  |  376 KB  |
| 6 |  1           |  40654 |  43763 |  32985 | Regular | 0.50s | 18.71s | 14394 KB |
| 6 |  1           |  40654 |  43763 |  32985 | Bacchus | 0.40s | 22.62s |  8578 KB |
| 6 | 42           |  17597 |  21336 |  13785 | Regular | 0.21s |  3.60s |  6572 KB |
| 6 | 42           |  17597 |  21336 |  13785 | Bacchus | 0.17s |  4.80s |  3690 KB |
| 6 | -1115540197  |   3620 |   4473 |   2600 | Regular | 0.04s | 0.30s  |  1838 KB |
| 6 | -1115540197  |   3620 |   4473 |   2600 | Bacchus | 0.02s | 0.30s  |  753 KB  |

With real search Bacchus's PBP is 40–60% **smaller** than `Regular`'s
— the all-NoJustNeeded per-call shape is paying its way: every node
in the search tree that `Regular` would emit a cache-gated
`~state[i][q]` line for, `RegularBacchus` writes nothing, and the
upfront scaffolding absorbs the closure work for all of them. The
catch is that VeriPB still spends ~20–30% more wall-clock time
verifying the smaller proof, because each backtrack RUP now has to UP
through a wider proof DB (the t-flag defs + per-`(q, v)` pol lines +
three families of AL1s).

So the headline result is shape-dependent:
- **Decision / shallow search** (no `--all`): Bacchus loses on every
  axis — bigger PBP, slower verify.
- **All-solutions / deep search** (`--all`): Bacchus's PBP shrinks by
  ~half but verify is still ~20–30% slower per byte.

This matches the [BinPacking/Knapsack pattern
regression](https://github.com/ciaranm/glasgow-constraint-solver/issues/212):
the upfront-only approach beats per-call-intermediates only when
per-call work is the dominant cost. `regular_random --all` is that
regime for proof size; whether it is ever that regime for verify time
depends on problem structure not measured here.

`RegularBacchus` is kept on the branch for issue #200 / the unified
layered-DAG follow-up: the t-flag definitions, per-`(q, v)` pol
intermediates, and AL1 derivations are useful primitives whose value
shows up clearly in the all-solutions regime even if shallow-search
benchmarks alone would not predict it.

## Worked example: nonogram

`regular_random` exercises the propagator on random automata, which is
right for stress-testing but says nothing about a *structured* use of
`Regular`. The `examples/nonogram` binary is the structured companion:
a nonogram ("paint by numbers") is solved by giving each row and each
column its own small DFA over the alphabet `{empty, filled}` and posting
one `Regular` per line. It is the canonical application of the
constraint and mirrors the MiniZinc Challenge 2013 `nonogram` model
(`2013/nonogram/non.mzn`).

Each clue — a list of run lengths like `[3, 1]` — is expanded to the
same 0/1 "cons" run-with-gap string the MiniZinc model uses (a run of
`k` becomes `k` ones; runs are separated by a single zero), and that
string is read directly into the layer-uniform DFA. Cells take values
`0 = empty` / `1 = filled` so the dense transition table is indexed by
cell value.

Run it with a built-in picture, a random instance, or a Challenge data
file, and select the variant to benchmark:

```shell
./build/nonogram --puzzle heart            # built-in pictures: plus, heart, duck
./build/nonogram --random 20 --seed 1      # random size-by-size instance
./build/nonogram --dzn 2013/nonogram/dom_10.dzn --stats
./build/nonogram --dzn dom_10.dzn --all --bacchus   # benchmark RegularBacchus
```

`--legacy` / `--bacchus` pick the other two implementations (default is
the upfront `Regular`), and `--all` enumerates every solution — the same
knobs `regular_random` exposes, so the three implementations can be
compared on the same instance. See
[`benchmarking.md`](benchmarking.md#benchmarking-proof-shape-changes).

## #200 follow-up

`Regular`, `RegularBacchus` and `MDD` now share related Top-scaffolding
shapes. Folding `Regular` and `MDD` into a single layered-DAG
scaffolder is the natural next step; `RegularBacchus` adds a third
axis (transition extension variables) that may or may not be worth
sharing across implementations depending on its measured value for
larger / different problem shapes.
