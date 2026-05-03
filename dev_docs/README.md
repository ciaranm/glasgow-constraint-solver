# Developer Documentation

This directory contains in-depth notes for developers (human or AI) working on
the Glasgow Constraint Solver. Each document covers one architectural area in
more detail than the top-level `README.md` does.

These docs are aimed at people changing the solver's code, not at users of the
library. For an introduction to *using* the solver, start with the top-level
`README.md`.

## Contents

- [Reification](reification.md) — how reified constraints are structured: the
  `ReificationCondition` static and `EvaluatedReificationCondition` runtime
  types, the `install_reified_dispatcher` helper, the OPB encoding pattern,
  and the conventions for writing new reified constraints.

More documents will be added here as we build up coverage of other parts of
the codebase.
