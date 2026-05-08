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
- [Benchmarking](benchmarking.md) — the curated set of benchmarks for
  measuring the wall-time impact of a performance-sensitive change, the
  rationale for each pick, the harness pattern for comparing two builds,
  and what to capture. Use when quantifying a refactor's perf impact.
- [Frontend support matrix](frontend-support-matrix.md) — single source of
  truth for which gcs propagators each frontend (MiniZinc, XCSP3, CPMpy)
  exposes, plus where the solver-side gaps are tracked. Update when adding
  a propagator or a frontend binding.

More documents will be added here as we build up coverage of other parts of
the codebase.
