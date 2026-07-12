# Frontend support matrix

The same constraint shows up under three frontends — FlatZinc/MiniZinc
(`minizinc/`), XCSP3 (`xcsp/`), and (planned) CPMpy. This document is the
single source of truth for "which gcs propagator do we have, and which
frontends expose it".

When you add a propagator or a frontend binding, update the relevant row.
Cells contain one of:

- **✓** — fully supported
- **decompose** — supported by translating to other primitives at parse time
  (note in a footnote how, if non-obvious)
- **unsupported** — frontend deliberately does not handle this shape
- **solver gap (#NNN)** — propagator does not yet exist; tracked under the
  given issue number
- **frontend gap (#NNN)** — propagator exists but the frontend has not yet
  been wired up to it
- **n/a** — concept does not apply to this frontend
- **?** — not yet investigated

This is a working document; a `?` is fine and signals a row that needs
attention.

## Constraints in XCSP3-core

These are the rows defined by [XCSP3-core
v3.2](https://arxiv.org/abs/2009.00514). MiniZinc and CPMpy column entries
record whether each frontend reaches the same gcs propagator (or its natural
equivalent for that frontend's vocabulary).

| Constraint family | gcs propagator | MiniZinc | XCSP3 | CPMpy |
|---|---|---|---|---|
| intension (algebraic exprs) | various via tree walk | ✓ | ✓ (tree walker) | ? |
| extension (table) | `Table` / `NegativeTable` | ✓ | ✓ | ? |
| regular | `Regular` | ✓ | ✓ (DFA with named states + transitions) | ? |
| mdd | `MDD` | ✓ (deterministic only)[^mdd] | ✓ | ? |
| allDifferent | `AllDifferent` | ✓ | ✓ | ? |
| allDifferent-list / -matrix | various decompositions | ? | matrix ✓ (rows + columns `AllDifferent`); list `s UNSUPPORTED` | ? |
| allEqual | `AllEqual` | ✓ | ✓ | ? |
| ordered (increasing/decreasing) | `Increasing` / `Decreasing` | ✓ | ✓ (basic + lengths form) | ? |
| precedence (value precedence) | `ValuePrecede` | ✓ | ✓ (with explicit values, `covered=false`) | ? |
| sum (linear) | `WeightedSum` | ✓ | ✓ | ? |
| count | `Count` (single value) / `Among` (multi-value set) | ✓ | ✓ (incl. atMost/atLeast/exactlyK/among special-cases) | ? |
| nValues | `NValue` | ✓ | ✓ (basic; without-`except` form) | ? |
| cardinality (GCC) | decompose to `Count` | ? | ✓ via decompose (constant values + constant occurs; closed flag) | ? |
| maximum / minimum (constraint) | `ArrayMax` / `ArrayMin` | ✓ | ✓ (basic with `XCondition`; indexed form pending) | ? |
| element | `Element` / `Element2D` | ✓ | ✓ (1D vector and constant-list; 2D matrix variable + constant) | ? |
| channel (inverse) | `Inverse` | ✓ | ✓ (1- and 2-list inverse; one-to-many form `s UNSUPPORTED`) | ? |
| noOverlap (Disjunctive) | `Disjunctive` (1D, var durations) / `Disjunctive2D` (2D, var sizes)[^disj] | ✓ (1D + 2D `diffn`, var durations/sizes) | ✓ (1D + 2D, var durations/sizes) | ? |
| cumulative | `Cumulative`[^cum] | ✓ (var s/d/r/b) | ✓ (var s/d/r/b) | ? |
| binPacking | `BinPacking` (per-bin GAC)[^bp] | ✓ (`fzn_bin_packing` / `_capa` / `_load`) | ✓ (signatures 1/2/3; per-bin condition list `s UNSUPPORTED`) | ? |
| knapsack | `Knapsack` | ✓ | ✓ (basic with two `XCondition`s; not yet exercised by a test) | ? |
| circuit | `Circuit` | ✓ | ✓ (basic; sub-circuit with size param `s UNSUPPORTED`); semantics mismatch with XCSP3 spec, see #167 | ? |
| instantiation | `Equals` to constant | ✓ | ✓ | ? |
| lex (ordered list) | `LexLessThan` / `LexLessThanEqual` / `LexGreaterThan` / `LexGreaterEqual` | ✓ | ✓ (lists; matrix as lex² over rows + columns) | ? |
| slide (meta-constraint) | apply template per window | ? | ✓ (parser unfolds into per-window constraints) | ? |

The MiniZinc column is best-effort: see `minizinc/fzn_glasgow.cc` for the
authoritative list of `fzn_*` builtins handled there.

## Constraints outside XCSP3-core

XCSP3-core deliberately omits some constraints that MiniZinc and CPMpy
expect. These get their own rows. CPMpy-specific gaps (half-reified `And`/`Or`,
`LessThanEqualIf`, etc.) are tracked under
[#61](https://github.com/ciaranm/glasgow-constraint-solver/issues/61) — link
each row here to the relevant sub-bullet there as those features are
addressed.

| Constraint family | gcs propagator | MiniZinc | XCSP3 | CPMpy | Notes |
|---|---|---|---|---|---|
| half-reified comparisons (`LessThanEqualIf`, …) | partially via `Comparison` + reif | ? | n/a | gap (#61) | |
| half-reified `And` / `Or` | – | ? | n/a | gap (#61) | |
| `Among` | `Among` | ✓ | n/a (use count) | ? | |
| `SmartTable` | `SmartTable` | ✓ | n/a | ? | Glasgow-specific extension |

## Solver gaps tracked elsewhere

- [#146](https://github.com/ciaranm/glasgow-constraint-solver/issues/146) — `Disjunctive`: 1D shipped (variable starts, constant *or* variable durations, strict and non-strict incl. zero-length escape; variable durations via the Cumulative end-proxy technique, fully VeriPB-certified — see #384). `Disjunctive2D` (2D `noOverlap` / `diffn`) shipped: variable origins, constant *or* variable sizes (rotation), strict and non-strict (incl. zero-area sizes via a reified zero-size escape clause), pairwise time-table strength, fully VeriPB-certified. k-D, optional tasks, and a sweep / cumulative-relaxation propagator are open follow-ups under the same issue.
- [#147](https://github.com/ciaranm/glasgow-constraint-solver/issues/147) — `Cumulative`: full `cumulative(var s, var d, var r, var b)` shipped with time-table propagation and VeriPB proofs (the `(le, int)` and `(le, var)` XCSP3 conditions). Edge-finding and energetic (stronger-than-time-table) propagation are open follow-ups under the same issue.
- [#148](https://github.com/ciaranm/glasgow-constraint-solver/issues/148) — `BinPacking`: Stage 1 (checker), Stage 2 (per-bin bounds), and Stage 3 (per-bin partial-load DAG, per-bin GAC) all shipped. Open follow-ups: Shaw-style cardinality reasoning to push beyond per-bin towards (still-not-joint) joint GAC ([#209](https://github.com/ciaranm/glasgow-constraint-solver/issues/209)), and unification with `MDD` / `Knapsack` under #200. See `bin-packing.md`.
- [#200](https://github.com/ciaranm/glasgow-constraint-solver/issues/200) — `Knapsack`: the default per-call DP implementation is kept as the default (its proofs verify 3.6–18× faster), with an opt-in upfront-DAG variant `KnapsackUpfront` (Stage 1 checker + Stage 2 full GAC with paper-style proof scaffolding at `ProofLevel::Top`) that produces 3–6× smaller proofs. Open follow-up: factor the layered-DAG infrastructure shared with `MDD` and `BinPacking` into a common framework. See `knapsack.md`.

[^cum]: Time-table propagation (mandatory-part load profile with bound pushes), now over variable origins, durations, demands, and capacity; every inference is VeriPB-certified — see [`cumulative-proof-logging.md`](cumulative-proof-logging.md). MiniZinc forwards `s`/`d`/`r`/`b` straight to `glasgow_cumulative` (constants pass through as constant variables); XCSP3 handles all four constant/variable length×height overloads and a constant- or variable-capacity `le` condition. Edge-finding / energetic reasoning remain out of scope.

[^disj]: 1D `Disjunctive`: variable starts, constant *or* variable durations, strict/non-strict; time-table specialised to heights=1, capacity=1 (variable durations fold into the pairwise ordering flags directly, with a reified zero-length escape clause in non-strict mode). 2D `Disjunctive2D` (non-overlapping rectangles, variable origins, constant or variable sizes): pairwise time-table — mandatory-box overlap is a contradiction, and a pair forced to overlap on one axis is pushed apart on the other. Both are fully proof-logged pairwise against the declarative OPB encoding ([`disjunctive-proof-logging.md`](disjunctive-proof-logging.md)); 2D adds a 4-way separation clause per pair. Outside the envelope (k-D, optional tasks): XCSP3 raises an unsupported error.

[^mdd]: MiniZinc's `fzn_mdd` is bound to the gcs `MDD` propagator; `mdd_nondet` (where multiple edges from a node may share label values) and `cost_mdd` (with totalcost) fall through to the MiniZinc stdlib's default decomposition. Tracked alongside the unified path-DAG framework (#200).

[^bp]: Stage-3 envelope: per-bin natural-definition OPB (sum equations) plus a Stage 2 bounds pass and a Stage 3 per-bin partial-load DAG sweep that achieves per-bin GAC on items (and load values, for the variable-load form). The DAG flags live at `ProofLevel::Top` as inequality reifications + a conjunction main state, emitted by an `install_initialiser` (the "third reusable idea" of `disjunctive-proof-logging.md`). `bounds_only=true` skips Stage 3 and runs Stage 2 alone — use this when the per-bin capacity is much larger than the number of items and the DAG flag count would balloon. Joint (cross-bin) GAC is not attempted; it is NP-hard for BinPacking. Outside the envelope (variable capacities under XCSP3 `<limits>`, per-bin `<conditions>` list): XCSP3 raises an unsupported error.

## Related documents

- [`constraints.md`](constraints.md) — the structural pattern for adding a propagator
- [`minizinc.md`](minizinc.md) — how the MiniZinc binding works
- The XCSP3 binding is documented in [`../xcsp/README.md`](../xcsp/README.md)

<!-- vim: set tw=100 spell spelllang=en : -->
