# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

Three build types are supported: `Release` (default), `Debug`, and `Sanitize`.
Use named presets from `CMakePresets.json` for convenience:

```shell
cmake --preset release  && cmake --build --preset release   # optimised (default)
cmake --preset debug    && cmake --build --preset debug     # -O0, full debug info
cmake --preset sanitize && cmake --build --preset sanitize  # ASan + UBSan
```

Or explicitly without presets (release equivalent):
```shell
cmake -S . -B build
cmake --build build --parallel $(nproc 2>/dev/null || sysctl -n hw.logicalcpu)
```

Use `--parallel N` for parallel builds. The expression `$(nproc 2>/dev/null || sysctl -n
hw.logicalcpu)` gives the CPU count on both Linux and macOS. Omitting the count causes
`make` to spawn unlimited jobs, which exhausts memory. If the build fails and the error
output is hard to read, re-run without `--parallel` to get clean sequential output.
For `ctest`, use `-j $(nproc 2>/dev/null || sysctl -n hw.logicalcpu)`.

Run all tests (requires `veripb` installed):
```shell
ctest --preset release      # with presets
cd build && ctest           # without presets
```

Run a single test binary directly:
```shell
./build/equals_test
```

Run a single test with proof verification (uses `run_test_and_verify.bash`):
```shell
./run_test_and_verify.bash ./build/circuit_disconnected_test
```

Disable XCSP or MiniZinc support to reduce dependencies:
```shell
cmake -S . -B build -DGCS_ENABLE_XCSP=OFF -DGCS_ENABLE_MINIZINC=OFF
```

Format code with clang-format (all source is formatted this way).

## Compiler and Standard Library Support

The codebase is built with both **GCC 15.2.0** and **clang 21**. Clang on macOS uses
**libc++** (Apple's standard library), not libstdc++. This matters for C++23 feature
availability: some features are in libstdc++ but not yet libc++.

Known unavailable in libc++ (clang 21):
- `std::views::enumerate` — use `util/enumerate.hh` instead; do not remove that file

Known unavailable in libstdc++ on the GitHub Actions Ubuntu 24.04 runner (GCC 13), which
we still support:
- `std::vector::append_range` — use `vec.insert(vec.end(), src.begin(), src.end())` instead

When adding a new C++23 feature, build with both compilers before committing.

## Code Style

### `using` declarations

The `using` declarations block near the top of each `.cc` file is sorted **alphabetically
by the full qualified name**. `std::ranges::` names sort under 'r', so they fall between
`std::pair` and `std::string`. Example:

```cpp
using std::pair;
using std::ranges::sort;   // 'r' < 's'
using std::string;
```

### Ranges algorithms

When replacing a classic algorithm with its `std::ranges::` equivalent:
- Remove `using std::foo;`
- Add `using std::ranges::foo;` in the correct sorted position
- Leave the call site **unqualified** — do not write `std::ranges::sort(v)` at the call site

### `using enum`

Place `using enum SomeEnum;` on the **first line inside the switch body**, indented one
level past the `switch` keyword, before the first `case` label:

```cpp
switch (x) {
    using enum SomeEnum;
case Value1:
```

This pattern is already used in the codebase; follow it consistently.

### `std::format` / `fmt::format`

Files that use `format()` for string building must use the conditional pattern:

```cpp
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
using std::format;
#else
#include <fmt/core.h>
using fmt::format;
#endif
```

Add `#include <format>` in the same `#if` block as `#include <print>` where both are
needed.

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
