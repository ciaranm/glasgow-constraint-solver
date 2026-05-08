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
| mdd | solver gap (#149) | ? | solver gap (#149) | ? |
| allDifferent | `AllDifferent` | ✓ | ✓ | ? |
| allDifferent-list / -matrix | various decompositions | ? | matrix ✓ (rows + columns `AllDifferent`); list `s UNSUPPORTED` | ? |
| allEqual | `Equals` chain (decompose; native propagator tracked in #61) | ✓ | ✓ via decompose (#150) | ? |
| ordered (increasing/decreasing) | `Increasing` / `Decreasing` | ✓ | ✓ (basic + lengths form) | ? |
| precedence (value precedence) | `ValuePrecede` | ✓ | ✓ (with explicit values, `covered=false`) | ? |
| sum (linear) | `WeightedSum` | ✓ | ✓ | ? |
| count | `Count` (single value) / `Among` (multi-value set) | ✓ | ✓ (incl. atMost/atLeast/exactlyK/among special-cases) | ? |
| nValues | `NValue` | ✓ | ✓ (basic; without-`except` form) | ? |
| cardinality (GCC) | decompose to `Count` | ? | ✓ via decompose (constant values + constant occurs; closed flag) | ? |
| maximum / minimum (constraint) | `ArrayMax` / `ArrayMin` | ✓ | ✓ (basic with `XCondition`; indexed form pending) | ? |
| element | `Element` / `Element2D` | ✓ | ✓ (1D vector and constant-list; 2D matrix variable + constant) | ? |
| channel (inverse) | `Inverse` | ✓ | ✓ (1- and 2-list inverse; one-to-many form `s UNSUPPORTED`) | ? |
| noOverlap (Disjunctive) | solver gap (#146) | ? | solver gap (#146) | ? |
| cumulative | solver gap (#147) | ? | solver gap (#147) | ? |
| binPacking | solver gap (#148) | ? | solver gap (#148) | ? |
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

- [#146](https://github.com/ciaranm/glasgow-constraint-solver/issues/146) — `Disjunctive` (covers XCSP3 `noOverlap`, MiniZinc `fzn_disjunctive`)
- [#147](https://github.com/ciaranm/glasgow-constraint-solver/issues/147) — `Cumulative`
- [#148](https://github.com/ciaranm/glasgow-constraint-solver/issues/148) — `BinPacking`
- [#149](https://github.com/ciaranm/glasgow-constraint-solver/issues/149) — `MDD`

## Related documents

- [`constraints.md`](constraints.md) — the structural pattern for adding a propagator
- [`minizinc.md`](minizinc.md) — how the MiniZinc binding works
- The XCSP3 binding is documented in [`../xcsp/README.md`](../xcsp/README.md)

<!-- vim: set tw=100 spell spelllang=en : -->
