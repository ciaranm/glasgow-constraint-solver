# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```shell
cmake -S . -B build
cmake --build build
```

Run all tests (requires `veripb` installed):
```shell
cd build && ctest
```

Run a single test binary directly:
```shell
./build/equals_test
```

Run a single test with proof verification (uses `run_test_and_verify.bash`):
```shell
./run_test_and_verify.bash ./build/circuit_disconnected_test
```

Build with debug mode (disables -O3):
```shell
cmake -S . -B build -DGCS_DEBUG_MODE=ON
cmake --build build
```

Disable XCSP or MiniZinc support to reduce dependencies:
```shell
cmake -S . -B build -DGCS_ENABLE_XCSP=OFF -DGCS_ENABLE_MINIZINC=OFF
```

Format code with clang-format (all source is formatted this way).

## Architecture Overview

This is a C++23 constraint programming solver with a key focus on **proof logging** — every inference can be verified externally by VeriPB.

### Public API (`gcs/`)

- `gcs/problem.hh` — `Problem` class: create variables, post constraints, set objective
- `gcs/solve.hh` — `solve()` and `solve_with()` entry points; `SolveCallbacks` struct for solution/branch callbacks
- `gcs/current_state.hh` — `CurrentState`: read-only view of variable values in solution callbacks
- `gcs/integer.hh` — `Integer` type wrapper (use `0_i`, `100_i` literals)
- `gcs/variable_id.hh` — `IntegerVariableID` and related lightweight handle types
- `gcs/constraints/` — all user-facing constraint types (e.g. `LinearLessEqual`, `AllDifferent`, `Table`, etc.)
- `gcs/gcs.hh` — convenience header including the full public API

### Innards (`gcs/innards/`)

Not part of the public API. Key components:

- **`State`** (`innards/state.hh`) — holds all variable domains; uses algebraic types (`IntegerVariableConstantState`, `IntegerVariableRangeState`, `IntegerVariableSmallSetState`, `IntegerVariableSetState`) to compactly represent domains
- **`Propagators`** (`innards/propagators.hh`) — manages constraint propagators, triggers, and the propagation queue
- **`InferenceTracker`** (`innards/inference_tracker.hh`) — templated on `SimpleInferenceTracker` or `EagerProofLoggingInferenceTracker`; all domain modifications go through this
- **`ProofLogger`** (`innards/proofs/proof_logger.hh`) — writes OPB/VeriPB proof files

### Constraint Pattern

Each constraint in `gcs/constraints/` follows this pattern:
1. A user-facing struct/class (e.g. `NotEquals`, `AllDifferent`)
2. An `install` method that registers propagator(s) via `Propagators`
3. Propagators receive an `InferenceTracker &` and call `infer()` on it with a `Literal`, a `Justification`, and a `ReasonFunction`
4. If `Propagators::want_nonpropagating()` is true, the constraint must also define itself in OPB terms for proof logging

### Justification Types

Every inference must be accompanied by a justification:
- `NoJustificationNeeded` — assertion without proof
- `JustifyUsingRUP` — reverse unit propagation suffices
- `JustifyExplicitly{fn}` — callback that adds explicit VeriPB proof steps

### Testing Pattern

Constraint tests (e.g. `constraints/equals_test.cc`) use the `gcs::test_innards` utilities in `constraints/constraints_test_utils.hh`. The test pattern:
1. Generate all expected solutions using a pure C++ satisfiability check
2. Run the solver and collect actual solutions
3. Compare expected vs actual (optionally checking GAC at each search node)
4. Optionally run VeriPB on the proof output

Tests that call `run_test_and_verify.bash` run the test binary with `--prove`, then invoke `veripb` to check the proof. Tests using `run_test_only.bash` skip proof verification.

Some tests use Catch2 (linked with `Catch2::Catch2WithMain`); others are standalone programs.

### External Dependencies (fetched via CMake FetchContent)

- **Catch2** — unit test framework
- **fmt** — string formatting
- **nlohmann/json** — JSON parsing (MiniZinc support)
- **generator** — `<generator>` polyfill if compiler lacks it (C++23)
- **VeriPB** — external proof checker, installed separately via `cargo install`
