# Developer Documentation

This directory contains in-depth notes for developers (human or AI) working on
the Glasgow Constraint Solver. Each document covers one architectural area in
more detail than the top-level `README.md` does.

These docs are aimed at people changing the solver's code, not at users of the
library. For an introduction to *using* the solver, start with the top-level
`README.md`.

## Contents

- [State and variables](state-and-variables.md) — how variables and their
  state are represented inside the solver: the `IntegerVariableID` family,
  the `State` class, the `IntervalSet` domain representation, chronological
  backtracking via epochs, and the inference paths through which propagators
  modify domains. Read first when changing the solver internals.
- [Implementing a constraint](constraints.md) — the structural pattern every
  constraint follows: class shape, the `install` method, the propagator
  framework, triggers, the inference and justification APIs, OPB encoding
  building blocks, and the testing pattern. Start here when adding any new
  constraint.
- [Reification](reification.md) — additional machinery for *reified* constraints:
  the `ReificationCondition` static and `EvaluatedReificationCondition` runtime
  types, the `install_reified_dispatcher` helper, the OPB encoding pattern,
  and the conventions for writing new reified constraints. Read
  `constraints.md` first.
- [MiniZinc bindings](minizinc.md) — how the `minizinc/` directory plugs into
  the MiniZinc / FlatZinc ecosystem: `fzn-glasgow`, the `mznlib/` predicate
  overrides, `.msc` solver-config files, the cross-solver test harness, and
  the recipe for exposing an existing C++ constraint.
- [XCSP3 bindings](xcsp.md) — how the `xcsp/` directory consumes XCSP3
  instances: the `XCSPCallbacks` class, the intension tree walker, the
  cache-based test harness with ACE cross-checking, and the recipe for
  adding a new constraint binding.
- [Benchmarking](benchmarking.md) — the curated set of benchmarks for
  measuring the wall-time impact of a performance-sensitive change, the
  rationale for each pick, the harness pattern for comparing two builds,
  and what to capture. Use when quantifying a refactor's perf impact.
- [Frontend support matrix](frontend-support-matrix.md) — single source of
  truth for which gcs propagators each frontend (MiniZinc, XCSP3, CPMpy)
  exposes, plus where the solver-side gaps are tracked. Update when adding
  a propagator or a frontend binding.
- [Proof logging for `Cumulative`](cumulative-proof-logging.md) — concrete
  walk-through of the three-inference proof for the time-table propagator:
  the `pol`-over-`active=1`-flags idiom, the "extended-reason pinning"
  technique for hypothetical literals, and the chain-of-blocked-times
  structure that proves a bound push. The generic patterns are summarised
  in `constraints.md`; this doc spells them out for one concrete propagator
  and flags the bits that should carry across to `Disjunctive` and
  `BinPacking`.
- [Proof logging for `Disjunctive`](disjunctive-proof-logging.md) — companion
  to the cumulative writeup, focused on the new bridge pattern:
  keeping the OPB encoding declarative (pairwise non-overlap clauses
  only) and emitting the time-indexed `before` / `after` / `active`
  flags as proof scaffolding via `install_initialiser`. Covers the
  `recover_am1`-based pairwise at-most-one derivation that replaces
  cumulative's encoded `C_t`, and the third reusable proof-logging
  idea that comes out of the design.
- [Range ("in") literals](range_literals_spec.md) — the design specification
  for the interval-literal proof layer: reifying `[X∈[a,b]]` to its
  order-chain cuts, the always-covered partition invariant, interval-tree
  containment, and the P1/P2 (line-checkability vs replay-completeness)
  distinction that governs which linking clauses are load-bearing — with the
  W1–W5 witness suite as the regression defence against re-simplification.
  Read when touching range/interval reasons, branching, or `infer_not_in_range`.
- [View proof logging](view-proof-logging.md) — how the proof layer handles
  views (`ViewOfIntegerVariableID`): the V↔X link constraints that tie a view's
  proof variable to its underlying variable, and how literals over views are
  deviewed for emission. Read when touching view handling in proofs.
- [Proof logging for `Sort` / `ArgSort`](sortedness.md) — the fully-certified
  Mehlhorn–Thiel sortedness propagator proof: the permutation/root argument and
  the Hall-band pigeonhole over ranks. A worked companion to `constraints.md`.
- [Reasons rework (design)](reasons-improvement.md) — the rationale for the
  declarative `Reason` variant and lazy `materialise()` that replaced the eager
  `ReasonFunction` thunks. Read alongside `infer-redesign.md`.
- [Infer rework (implementation notes)](infer-redesign.md) — the as-built
  justification layer: `JustifyExplicitly` / `JustifyUsingRUP`, the mandatory
  `ThenRUP` enum, the pay-for-use `SimpleInferenceTracker`, and the typed
  per-constraint assertion hints (`gcs::innards::hints`).
- [SCP s-expression migration](scp_s_expr_migration.md) — how constraints expose
  themselves to the sub-constraint-proof (SCP) writer via `s_expr`, and the
  status of the per-constraint migration.
- [Workflow-2 / SCP chain testing](workflow2_testing.md) — the
  `glasgow_scp_solver` binary and the SCP chain test harness
  (`run_scp_chain.bash`, `scp_cases/`) for verifying constraint encodings
  against an external checker.

More documents will be added here as we build up coverage of other parts of
the codebase.
