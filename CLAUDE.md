# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

Three build types are supported: `Release` (default), `Debug`, and `Sanitize`.
All keep debug information, but scaled to purpose: `Release` uses `-g1` (`/Z7`
on MSVC) — function names plus line tables, enough for backtraces and the
`GCS_VERBOSE_LOGGING` stacktrace annotation — while `Debug` and `Sanitize` use
`-g3` for full interactive debugging. Use named presets from
`CMakePresets.json` for convenience:

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

Enable the view-wrap proof-verification sweep (~3000 extra tests, most
fail today; opt in when working on view proof logging):
```shell
cmake -S . -B build -DGCS_ENABLE_VIEW_WRAP_SWEEP=ON
```
The harness and `--view-wrap=N` / `--view-position=K` argv flags on each
test are always built; only the ctest registrations are gated.

By default the data-driven constraint tests run with generous per-solve
solution/recursion caps (`GCS_TEST_CAP_DEFAULTS=ON`) so a pathological
random instance can't dominate the parallel suite. A capped run checks
soundness and the partial proof only, **not** completeness — so when
working on a propagator, turn the caps off to get full enumeration
checking:
```shell
cmake -S . -B build -DGCS_TEST_CAP_DEFAULTS=OFF
```
See `dev_docs/constraints.md` (Testing) for details.

Format code with clang-format; all source is formatted this way. Use
**clang-format 21** to match CI (formatting output differs between major
releases). Format the whole tree with:
```shell
git ls-files '*.cc' '*.hh' | grep -v '^XCSP3-CPP-Parser/' | xargs clang-format -i
```
The `clang-format` CI workflow enforces this on every push and pull request. To
catch violations before CI, enable the tracked pre-commit hook once per clone
with `git config core.hooksPath .githooks` (see CONTRIBUTING.md).

## Compiler and Standard Library Support

The codebase is built with **GCC 15.2.0**, **clang 21**, and **MSVC (Visual Studio
2022)**. Clang on macOS uses **libc++** (Apple's standard library), not libstdc++.
This matters for C++23 feature availability: some features are in libstdc++ but not
yet libc++.

Windows/MSVC support is experimental (see README.md, Platform support), but the
`windows-2022` CI lanes gate every push and pull request just like the Linux and
macOS ones, so code must still compile there. In particular, do not use GCC/clang
extensions or Itanium-ABI-only headers (`<cxxabi.h>`, `abi::__cxa_demangle`, ...).

Known unavailable in libc++ (clang 21):
- `std::views::enumerate` — use `util/enumerate.hh` instead; do not remove that file

Known unavailable in libstdc++ on the GitHub Actions Ubuntu 24.04 runner (GCC 13), which
we still support:
- `std::vector::append_range` (and the other P1206 `*_range` container members) —
  `__cpp_lib_containers_ranges` is undefined there. Use
  `vec.insert(vec.end(), src.begin(), src.end())` instead. Reconfirmed unavailable on the
  Ubuntu 24.04 lane via CI on 2026-07-03; libc++ (macOS) and GCC 15 both have it.

Confirmed available on **all** supported toolchains (including GCC 13 and macOS libc++),
verified via CI on 2026-07-03 — prefer them where they read more clearly than a hand-rolled
`if`/ternary:
- `std::optional` monadic operations: `.transform()`, `.and_then()`, `.or_else()`, and
  `.value_or()`.

When adding a new C++23 feature, build with GCC and clang before committing, and check
MSVC availability (CI is the backstop there).

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

### `overloaded{...}` visitor blocks

Format `overloaded{...}` visitors like a `switch`: nothing after the opening brace, each
lambda starting on its own line at one indent level, all lambdas indented equally. Pin the
layout with an empty `//` comment straight after the opening brace:

```cpp
overloaded{//
    [&](const consistency::GAC &) {
        // ...
    },
    [&](const consistency::VC &) {
        // ...
    }}
    .visit(_level);
```

The pin is load-bearing. clang-format's penalty optimiser will otherwise pull the first
lambda up onto the `overloaded{` line whenever the content happens to make that layout
score better, and it re-mangles a previously-clean block when the lambda bodies change —
so an unpinned block that looks stable today is one edit away from being reflowed. When
you meet an already-mangled block, add the `//` and re-run clang-format rather than
re-indenting by hand. (Same trick as the trailing `//` that keeps cxxopts `add_options`
blocks one option per line.)

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
- `gcs/constraints/` — all user-facing constraint types (e.g. `LinearLessThanEqual`, `AllDifferent`, `Table`, etc.)
- `gcs/gcs.hh` — convenience header including the full public API

### Innards (`gcs/innards/`)

Not part of the public API. Key components:

- **`State`** (`innards/state.hh`) — holds all variable domains as `IntervalSet<Integer>` (a sorted sequence of disjoint closed intervals, with small-buffer optimisation for the common one-or-two-interval case). See `dev_docs/state-and-variables.md` for the full picture: the `IntegerVariableID` family, epoch-based backtracking, and the `change_state_for_*` inference paths.
- **`Propagators`** (`innards/propagators.hh`) — manages constraint propagators, triggers, and the propagation queue
- **`InferenceTracker`** (`innards/inference_tracker.hh`) — templated on `SimpleInferenceTracker` or `EagerProofLoggingInferenceTracker`; all domain modifications go through this
- **`ProofLogger`** (`innards/proofs/proof_logger.hh`) — writes OPB/VeriPB proof files

### Constraint Pattern

Each constraint in `gcs/constraints/` follows this pattern:
1. A user-facing struct/class (e.g. `NotEquals`, `AllDifferent`)
2. An `install` method that registers propagator(s) via `Propagators`
3. Propagators receive an `InferenceTracker &` and call `infer()` on it with a `Literal`, a `Justification`, and a `Reason` (a declarative reason, materialised on demand)
4. If `Propagators::want_nonpropagating()` is true, the constraint must also define itself in OPB terms for proof logging

### Justification Types

Every inference must be accompanied by a justification:
- `NoJustificationNeeded` — the inference needs nothing in the proof: it is neither justified nor asserted (the solver simply trusts it)
- `JustifyUsingRUP{}` — reverse unit propagation suffices (optionally `JustifyUsingRUP{hints::Foo{...}}` to carry a typed assertion hint)
- `JustifyExplicitly{emit, ThenRUP::Yes}` — `emit` is a `(const ReasonLiterals &) -> void` callback (or a named fat-witness struct, for a reification verdict) that writes explicit VeriPB proof steps. `ThenRUP` is mandatory: `Yes` RUPs the inferred literal after the steps, `No` lets the steps conclude it. An optional third argument is a typed assertion hint, shared with `JustifyUsingRUP`.

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
