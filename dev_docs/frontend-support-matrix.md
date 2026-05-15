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
| intension (algebraic exprs) | various via tree walk | ✓ | frontend gap (#150) | ? |
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
| noOverlap (Disjunctive) | `Disjunctive` (basic case)[^disj] | ✓ (basic case) | ✓ (basic case) | ? |
| cumulative | `Cumulative` (basic case)[^cum] | ✓ (basic case) | ✓ (basic case) | ? |
| binPacking | `BinPacking` (per-bin bounds)[^bp] | ✓ (`fzn_bin_packing` / `_capa` / `_load`) | ✓ (signatures 1/2/3; per-bin condition list `s UNSUPPORTED`) | ? |
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
| `Among` | `Among` | ? | n/a (use count) | ? | |
| `SmartTable` | `SmartTable` | ✓ | n/a | ? | Glasgow-specific extension |

## Solver gaps tracked elsewhere

- [#146](https://github.com/ciaranm/glasgow-constraint-solver/issues/146) — `Disjunctive`: basic case shipped (variable starts, constant lengths, both strict and non-strict). Variable lengths, 2D / k-D `Disjunctive2D`, and optional-task variants are open follow-ups under the same issue.
- [#147](https://github.com/ciaranm/glasgow-constraint-solver/issues/147) — `Cumulative`: basic-case shipped (constant lengths, heights, capacity; only the `(le, int)` XCSP3 condition; variable starts only; checker-only propagation). Variable d/r/b, edge-finding, and proof logging for stronger propagation are open follow-ups under the same issue.
- [#148](https://github.com/ciaranm/glasgow-constraint-solver/issues/148) — `BinPacking`: Stage 1 (checker) and Stage 2 (per-bin bounds) shipped; Stage 3 (per-bin DAG GAC) is the only open follow-up under the same issue. See `bin-packing.md`.

[^cum]: Stage-1 envelope: variable origins, constant lengths/heights/capacity. Propagator is a pure feasibility checker (fires only when every start is fixed). Outside this envelope: MiniZinc lets the stdlib decomposition apply; XCSP3 raises an unsupported error.

[^disj]: Stage-1 envelope: variable starts, constant lengths, with strict/non-strict zero-length semantics resolved at construction. Time-table propagation specialised to heights=1, capacity=1; fully proof-logged via the declarative pairwise OPB encoding plus a propagator-introduced bridge ([`disjunctive-proof-logging.md`](disjunctive-proof-logging.md)). Outside the envelope (variable lengths, 2D/k-D, optional tasks): MiniZinc errors at flattening via `fix()`; XCSP3 raises an unsupported error.

[^mdd]: MiniZinc's `fzn_mdd` is bound to the gcs `MDD` propagator; `mdd_nondet` (where multiple edges from a node may share label values) and `cost_mdd` (with totalcost) fall through to the MiniZinc stdlib's default decomposition. Tracked alongside the unified path-DAG framework (#200).

[^bp]: Stage-2 envelope: per-bin natural-definition OPB (sum equations) plus a propagator that maintains `floor_b` / `ceiling_b` from the forced-into and possibly-in items per bin. Variable-load form lifts `loads[b]` floor, drops the ceiling, prunes items that would overflow, and forces items whose absence would underflow. Constant-cap form contradicts on a forced overflow and prunes items that would push the floor over capacity. `bounds_only` is reserved for Stage 3 (per-bin DAG GAC) and currently has no effect. Outside the envelope (variable capacities under XCSP3 `<limits>`, per-bin `<conditions>` list): XCSP3 raises an unsupported error.

## Related documents

- [`constraints.md`](constraints.md) — the structural pattern for adding a propagator
- [`minizinc.md`](minizinc.md) — how the MiniZinc binding works
- The XCSP3 binding is documented in [`../xcsp/README.md`](../xcsp/README.md)

<!-- vim: set tw=100 spell spelllang=en : -->
