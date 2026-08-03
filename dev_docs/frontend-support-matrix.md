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
| intension (algebraic exprs) | various via tree walk | ✓ | ✓ (tree walker; an affine top-level ordering posts one linear inequality instead of an auxiliary variable per compound operand)[^intaff] | ? |
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
| cumulative, optional tasks | `Cumulative` presence form[^cumopt] | ✓ (`fzn_cumulative_opt`, and `fzn_disjunctive_opt` riding it) | n/a — no such form in XCSP3 | ? |
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
| binary comparison (`x <op> y`, `x <op> y + d`) | `Comparison`, or a two-term `WeightedSum` | ✓ | ✓ | ? | Which of the two, and why it matters, in [^cmp] |
| difference logic (`x - y <= d` as a *system*) | `DifferenceConstraints`; or the `DifferenceLogic` presolver over constraints posted individually | ✓ presolver only, opt-in `--difference-logic` | ✓ presolver only, opt-in `--difference-logic` | ? | Glasgow-specific extension ([#571](https://github.com/ciaranm/glasgow-constraint-solver/issues/571)); see [^dl] for why there is no predicate |
| `MinDistance` | `MinDistance` | unsupported | n/a | unsupported | Glasgow-specific extension; no frontend vocabulary for it |
| `SmartTable` | `SmartTable` | ✓ | n/a | ? | Glasgow-specific extension |

## Solver gaps tracked elsewhere

- [#146](https://github.com/ciaranm/glasgow-constraint-solver/issues/146) — `Disjunctive`: 1D shipped (variable starts, constant *or* variable durations, strict and non-strict incl. zero-length escape; variable durations via the Cumulative end-proxy technique, fully VeriPB-certified — see #384). `Disjunctive2D` (2D `noOverlap` / `diffn`) shipped: variable origins, constant *or* variable sizes (rotation), strict and non-strict (incl. zero-area sizes via a reified zero-size escape clause), pairwise time-table strength, fully VeriPB-certified. k-D, optional tasks, and a sweep / cumulative-relaxation propagator are open follow-ups under the same issue.
- [#147](https://github.com/ciaranm/glasgow-constraint-solver/issues/147) — `Cumulative`: full `cumulative(var s, var d, var r, var b)` shipped with time-table propagation and VeriPB proofs (the `(le, int)` and `(le, var)` XCSP3 conditions). Edge-finding and energetic (stronger-than-time-table) propagation are open follow-ups under the same issue.
- [#148](https://github.com/ciaranm/glasgow-constraint-solver/issues/148) — `BinPacking`: Stage 1 (checker), Stage 2 (per-bin bounds), and Stage 3 (per-bin partial-load DAG, per-bin GAC) all shipped. Open follow-ups: Shaw-style cardinality reasoning to push beyond per-bin towards (still-not-joint) joint GAC ([#209](https://github.com/ciaranm/glasgow-constraint-solver/issues/209)), and unification with `MDD` / `Knapsack` under #200. See `bin-packing.md`.
- [#200](https://github.com/ciaranm/glasgow-constraint-solver/issues/200) — `Knapsack`: the default per-call DP implementation is kept as the default (its proofs verify 3.6–18× faster), with an opt-in upfront-DAG variant `KnapsackUpfront` (Stage 1 checker + Stage 2 full GAC with paper-style proof scaffolding at `ProofLevel::Top`) that produces 3–6× smaller proofs. Open follow-up: factor the layered-DAG infrastructure shared with `MDD` and `BinPacking` into a common framework. See `knapsack.md`.

[^cum]: Time-table propagation (mandatory-part load profile with bound pushes), now over variable origins, durations, demands, and capacity; every inference is VeriPB-certified — see [`cumulative-proof-logging.md`](cumulative-proof-logging.md). MiniZinc forwards `s`/`d`/`r`/`b` straight to `glasgow_cumulative` (constants pass through as constant variables); XCSP3 handles all four constant/variable length×height overloads and a constant- or variable-capacity `le` condition. Edge-finding / energetic reasoning remain out of scope.

[^cumopt]: Optional tasks: a `{0, 1}` presence variable per task, absent tasks
    consuming nothing, with the presences ordinary problem variables so a model
    can maximise over them. Time-table strength on the tasks known present, plus
    presence falsification — a task with no start position left that fits is
    inferred absent — all VeriPB-certified; an undecided task's own start bounds
    are deliberately not pruned (see
    [`cumulative-proof-logging.md`](cumulative-proof-logging.md)). MiniZinc
    redefines `fzn_cumulative_opt` to `glasgow_cumulative_opt`, splitting each
    `var opt int` start with `occurs`/`deopt` the way the Gecode and OR-Tools
    libraries do; `fzn_disjunctive_opt` rides the same builtin at unit demands
    and capacity 1. `fzn_disjunctive_strict_opt` deliberately does not: strict
    disjunctive forbids a zero-duration task from sitting inside another, and a
    task consuming nothing for no time is invisible to a resource profile.
    XCSP3 defines no optional-task cumulative at all — every
    `buildConstraintCumulative` overload in the parser is
    origins/lengths/heights[/ends] plus a condition — so there is nothing to
    map, and the XCSP frontend records that rather than leaving it open.
    `cake_pb_cp` has no encoder for the optional form, so it is outside the
    verified-encoding chain; `constraint_type()` is `cumulative_optional` so
    that gap is named rather than silently mismatched against the plain
    encoder.

[^disj]: 1D `Disjunctive`: variable starts, constant *or* variable durations, strict/non-strict; time-table specialised to heights=1, capacity=1 (variable durations fold into the pairwise ordering flags directly, with a reified zero-length escape clause in non-strict mode). 2D `Disjunctive2D` (non-overlapping rectangles, variable origins, constant or variable sizes): pairwise time-table — mandatory-box overlap is a contradiction, and a pair forced to overlap on one axis is pushed apart on the other. Both are fully proof-logged pairwise against the declarative OPB encoding ([`disjunctive-proof-logging.md`](disjunctive-proof-logging.md)); 2D adds a 4-way separation clause per pair. Outside the envelope (k-D, optional tasks): XCSP3 raises an unsupported error.

[^intaff]: `xcsp_glasgow_constraint_solver.cc` keeps `recognizeSpecialIntensionCases = false`, so every `<intension>` still arrives as one typed tree, but `post_intension_top_level` tries an affine peephole first for `le`, `lt`, `ge` and `gt`. Operands built only from variables, integers, `add`, `sub` and `neg` are folded into a single `LinearLessThanEqual` over the instance's own variables; anything else (a `mul`, a `dist`, …) falls back to the ordinary walk, and `eq` is deliberately excluded, because `Equals` over two variables is domain-consistent and a linear equality is only bounds-consistent. Measured on a 12-variable network of 31 such constraints, the peephole removes 31 auxiliary variables, 64 % of the OPB lines and 72 % of the proof lines.

[^cmp]: Both frontends reach a *linear* inequality rather than `Comparison` for essentially every binary ordering. MiniZinc 2.10's flattener emits `int_lin_le([1,-1],[x,y],d)` even for a bare `x <= y`, so `int_le` / `int_lt` are bound but hardly ever produced; XCSP3 gets there via the intension peephole of [^intaff]. Either arrival is lifted by the difference-logic presolver — a `Comparison` donor since [#596](https://github.com/ciaranm/glasgow-constraint-solver/pull/596) labelled its rows, counted separately as `DifferenceLogicStats::comparison_edges_lifted` — so which of the two a frontend produces is a question of *size*, not of reach: reaching a `Comparison` whose operand is a compound expression means paying for the auxiliary variable that built the operand, which is what [^intaff] removes. Reified comparisons (`int_le_reif`, an `le` inside an expression) still go to the `*Iff` constraints.

[^dl]: There is no FlatZinc builtin and no XCSP3-core constraint for a difference-constraint *system*, and inventing a Glasgow-only predicate for one would be worse than useless: the presolver detects the shape automatically from ordinary two-term inequalities, so a model gets the global propagator without being rewritten, and a predicate would only let a model ask for something it cannot express any better. Both binaries therefore expose it as a flag rather than a vocabulary: `--difference-logic` adds the presolver, `--difference-logic-simplify on|off` controls the root simplification stage, defaulting off and on respectively to match `gcs::DifferenceLogic`'s own defaults. **Unconditional edges only, from either frontend**: `DifferenceLogic` also lifts a half-reified donor of either family (`LinearLessThanEqualIf`, `LessThanEqualIf`, …), which is where the paper's scheduling wins come from, but neither frontend produces one. `minizinc/mznlib/` declares no `*_imp` predicates, so MiniZinc's flattener never half-reifies and emits `int_lin_le_reif` (which the presolver counts under `skipped_reified`); and the XCSP3 binding turns a top-level `imp(b, le(...))` into an `Or` over a fully-reified control. Declaring `int_lin_le_imp` is the obvious next step for MiniZinc, but it changes flattening for every model, so it wants measuring on its own rather than smuggling in here.

[^mdd]: MiniZinc's `fzn_mdd` is bound to the gcs `MDD` propagator; `mdd_nondet` (where multiple edges from a node may share label values) and `cost_mdd` (with totalcost) fall through to the MiniZinc stdlib's default decomposition. Tracked alongside the unified path-DAG framework (#200).

[^bp]: Stage-3 envelope: per-bin natural-definition OPB (sum equations) plus a Stage 2 bounds pass and a Stage 3 per-bin partial-load DAG sweep that achieves per-bin GAC on items (and load values, for the variable-load form). The DAG flags live at `ProofLevel::Top` as inequality reifications + a conjunction main state, emitted by an `install_initialiser` (the "third reusable idea" of `disjunctive-proof-logging.md`). `bounds_only=true` skips Stage 3 and runs Stage 2 alone — use this when the per-bin capacity is much larger than the number of items and the DAG flag count would balloon. Joint (cross-bin) GAC is not attempted; it is NP-hard for BinPacking. Outside the envelope (variable capacities under XCSP3 `<limits>`, per-bin `<conditions>` list): XCSP3 raises an unsupported error.

## Related documents

- [`constraints.md`](constraints.md) — the structural pattern for adding a propagator
- [`minizinc.md`](minizinc.md) — how the MiniZinc binding works
- The XCSP3 binding is documented in [`../xcsp/README.md`](../xcsp/README.md)

<!-- vim: set tw=100 spell spelllang=en : -->
