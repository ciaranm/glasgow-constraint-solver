# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

Three build types are supported: `Release` (default), `Debug`, and `Sanitize`.
All keep debug information, but scaled to purpose: `Release` (with `/Z7` as the
MSVC equivalent) and `Sanitize` use `-g1` — function names plus line tables,
enough for backtraces, for the `GCS_VERBOSE_LOGGING` stacktrace annotation, and
for an ASan or UBSan report to name a function and a `file:line` — while `Debug`
uses `-g3` for full interactive debugging. `Sanitize` is `-g1` for size: every
test binary links the solver statically and so carries its own copy of the same
DWARF, which at `-g3` made a 93 GiB build tree and ran the CI runner out of
disk; at `-g1` it is 56 GiB. Build `Debug` when you are going to attach a
debugger. Use named presets from `CMakePresets.json` for convenience:

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

The per-configuration flags at the top of `CMakeLists.txt` are plain `set()` calls,
not `set(... CACHE ...)`, and must stay that way: a cached `set()` there is a silent
no-op, because `project()` has already created those cache entries. That is how the
Sanitize build spent months containing no sanitizers (issue #597). Do not "tidy" them
back into cache variables — `sanitizers_enabled_test` and a configure-time check will
both object, and `-DCMAKE_CXX_FLAGS_SANITIZE=...` on the command line has no effect
either way. `grep`ping `CMakeCache.txt` for these tells you nothing; check
`build-sanitize/gcs/CMakeFiles/*.dir/flags.make` instead.

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

There are two families of test binary, and they are proved differently. The
data-driven constraint tests have no `--prove` flag: they write and check their
own proofs, calling `veripb` in-process whenever it is on the `PATH`. Running
one directly, as above, therefore already verifies its proofs, which is why
ctest registers them through `run_test_only.bash` — a wrapper that only runs the
binary. Everything that *does* take `--prove` — the examples, benchmarks and
frontends, plus the proof-innards tests under `gcs/` — goes through
`run_test_and_verify.bash`, which runs the binary with `--prove`, checks the
proof with `veripb`, and reads back any `.scp` it wrote:
```shell
./run_test_and_verify.bash ./build/reification_test
```
A third wrapper, `run_test_and_expect_verify_failure.bash`, is the inverse of the
second: a mutation lane makes a test write a knowingly wrong proof, and the run
passes only if `veripb` *rejects* it. Mutation lanes are the exception to the
split above — a handful of constraint tests are driven through these two
wrappers with `--mutate=` and the wrapper's `--basename`, which is what names
the one proof the wrapper then checks.

Proof files are deleted once they verify. To keep them for inspection, set
`GCS_PRESERVE_PROOF_FILES` (see `dev_docs/constraints.md`); they are kept
automatically when verification fails.

Disable XCSP or MiniZinc support to reduce dependencies:
```shell
cmake -S . -B build -DGCS_ENABLE_XCSP=OFF -DGCS_ENABLE_MINIZINC=OFF
```

Enable the view-wrap proof-verification sweep — every wrap × every argument
position, for each constraint that participates. That is around 7200 extra
tests (400 without it, 7636 with, in a build with the frontends and executables
off), and they pass: every constraint registered in the sweep verifies under
every wrap. `SmartTable` is the one deliberate omission — it over-prunes under
views, tracked in issue #238. Opt in when working on view proof logging:
```shell
cmake -S . -B build -DGCS_ENABLE_VIEW_WRAP_SWEEP=ON
```
The harness and the `--view-wrap=N` / `--view-position=N|all|mixed` argv flags
on each test are always built, as is the single `--view-position=mixed` test per
constraint, which is part of the ordinary suite; only the per-wrap ctest
registrations are gated. See `dev_docs/view-proof-logging.md`.

Enable the large-domain guard, a development tripwire that turns work
proportional to a variable's domain width into a test failure (issue #833):
```shell
cmake -S . -B build-guard -DGCS_LARGE_DOMAIN_GUARD=ON
```
Off by default, and deliberately not user-facing: what protects a user is a
constraint having somewhere cheap to fall back to, not an exception thrown from
the middle of propagation. Turning it on also registers `large_domain_audit_test`,
which probes every constraint class over a `0..10^9` domain against a table of
expected outcomes. See `dev_docs/large-domains.md`.

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

## Releasing the Python bindings

`gcspy` (the pybind11 module in `python/`) is published to PyPI. The version
lives in `python/pyproject.toml`; a tag push matching `gcspy-v*` builds the
sdist plus macOS/manylinux wheels and publishes via the `release-gcspy.yml`
workflow. Full procedure, the compiler-floor wheel setup, and the one-time PyPI
Trusted Publishing configuration are in
[`dev_docs/releasing-gcspy.md`](dev_docs/releasing-gcspy.md).

## Compiler and Standard Library Support

Development happens with **GCC 15.2.0** and **clang 21**; **MSVC (Visual Studio
2022)** is the third supported compiler. The *oldest* supported compiler is **GCC
13**, which is what the `ubuntu-24.04` lane and the manylinux wheel build use.
Clang on macOS uses **libc++** (Apple's standard library), not libstdc++. This
matters for C++23 feature availability: some features are in libstdc++ but not
yet libc++.

CI runs on every push to `main` and every pull request, over `ubuntu-24.04`
(default GCC, test caps off), `ubuntu-26.04` (default GCC, test caps off, and the
one lane that builds with `-DGCS_WERROR=ON`, so a new compiler warning turns the
lane red), `ubuntu-26.04` with clang, `macos-15` and `macos-26`, plus a
`ubuntu-26.04` Sanitize lane and the `windows-2022` MSVC lanes. `main` has no
branch protection, so a lane reports rather than literally gating a merge.

Windows/MSVC support is experimental (see README.md, Platform support), but the
`windows-2022` lanes run on every push and pull request just like the Linux and
macOS ones, so code must still compile there. In particular, do not use GCC/clang
extensions or Itanium-ABI-only headers (`<cxxabi.h>`, `abi::__cxa_demangle`, ...).

Known unavailable in libc++ (the Apple Clang on the macOS lanes; last checked
against clang 21, so re-confirm on CI before relying on a change here):
- `std::views::enumerate` — use `util/enumerate.hh` instead; do not remove that
  file, which 46 files include

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
by name**, with the `std::ranges::` names in a group of their own **after** all the plain
`std::` ones, themselves alphabetical. Example:

```cpp
using std::pair;
using std::string;
using std::vector;
using std::ranges::any_of;
using std::ranges::sort;
```

Every one of the 57 files that names a `std::ranges::` algorithm does it this way, so
follow it rather than sorting `std::ranges::sort` under 'r' between `std::pair` and
`std::string` — which is what this section used to say and what nothing in the tree does.

The `#if defined(__cpp_lib_print)` block that picks `std::print`/`fmt::print` is a
separate block and stays where it is, below.

### Ranges algorithms

When replacing a classic algorithm with its `std::ranges::` equivalent:
- Remove `using std::foo;`
- Add `using std::ranges::foo;` to the `std::ranges::` group below the plain `std::` ones,
  in alphabetical order within that group (see `using` declarations, above)
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
- `gcs/constraints/` — all user-facing constraint types (e.g. `LinearLessThanEqual`, `AllDifferent`, `Table`, etc.), each one a directory plus an umbrella header of the same name
- `gcs/presolvers/` — the opt-in presolvers (`AutoTable`, `DifferenceLogic`, `CumulativeStrengthening`, `InferredCumulative`, `InferredDisjunctive`), in the same directory-plus-umbrella-header layout; the base class is `gcs/presolver.hh`
- `gcs/proof.hh` — `ProofOptions` and `ProofFileNames`: the `.opb` model, the `.pbp` proof, the variables map and the `.scp` s-expression definitions
- `gcs/search_heuristics.hh`, `gcs/restarts.hh`, `gcs/variable_weighting.hh` — branching, restart schedules, and dom/wdeg-style conflict weighting
- `gcs/gcs.hh` — convenience header for most of the public API. It does **not** pull in `presolver.hh`, `proof_strategy.hh` or `scp_reader.hh`, which have to be included directly

### Innards (`gcs/innards/`)

Not part of the public API. Key components:

- **`State`** (`innards/state.hh`) — holds all variable domains as `IntervalSet<Integer>` (a sorted sequence of disjoint closed intervals, with small-buffer optimisation for the common one-or-two-interval case). See `dev_docs/state-and-variables.md` for the full picture: the `IntegerVariableID` family, epoch-based backtracking, and the `change_state_for_*` inference paths.
- **`Propagators`** (`innards/propagators.hh`) — manages constraint propagators, triggers, and the propagation queue
- **`InferenceTracker`** (`innards/inference_tracker.hh`) — templated on `SimpleInferenceTracker` or `EagerProofLoggingInferenceTracker`; all domain modifications go through this
- **`ProofModel`** (`innards/proofs/proof_model.hh`) — writes the OPB model: each constraint's definition, emitted during the `define_proof_model` phase
- **`ProofLogger`** (`innards/proofs/proof_logger.hh`) — writes the VeriPB proof (`.pbp`) during search, tagging each line with a `ProofLevel` and placing it in either the core or the derived constraint set

### Constraint Pattern

Each constraint in `gcs/constraints/` is a subclass of `Constraint`
(`gcs/constraint.hh`). `Constraint::install()` is **not** virtual: `Problem`
calls it, and it runs up to three phases, which are what a constraint overrides.

1. `prepare(Propagators &, State &, ProofModel * const) -> bool` — argument
   validation, reading the initial domains, allocating auxiliary variables and
   backtrackable constraint state, and installing child constraints. It is the
   only phase holding the propagators, the mutable `State` and the model at
   once, so it is the only one that can allocate or install a child. Return
   `false` to say the other two phases must not run.
2. `define_proof_model(ProofModel &, const State &) -> void` — write the OPB
   definition, and nothing else. Run only when proofs are being logged. It is
   `const` because this phase must describe the constraint, never allocate.
3. `install_propagators(Propagators &) -> void` — register the propagator(s).

Two further overrides are not phases: `constraint_type()` is pure virtual and
gives the `.scp` keyword stem (`abs`, `lin_less_equal`, `array_min`, ...), and
`s_expr()` exposes the constraint to the sub-constraint-proof writer (see
`dev_docs/scp_s_expr_migration.md`).

A propagator receives an `InferenceTracker &` and calls `infer()` on it with a
`ProofLogger *`, a `Literal`, a `Justification` and a `Reason` (a declarative
reason, materialised on demand). `dev_docs/constraints.md` has the full pattern;
`dev_docs/reification.md` covers reified constraints.

### Justification Types

Every inference must be accompanied by a justification. Three of these are the
alternatives of `using Justification = std::variant<JustifyUsingRUP<NoHint>,
AssertRatherThanJustifying, NoJustificationNeeded>`; `JustifyExplicitly` is
dispatched by overload resolution rather than carried in that variant.
- `NoJustificationNeeded` — the inference needs nothing in the proof: it is neither justified nor asserted (the solver simply trusts it)
- `AssertRatherThanJustifying` — the inference is emitted under VeriPB's assertion rule and taken on trust rather than checked. This is also what every other justification degrades to when the logger is running at an `AssertionLevel` other than `Off`
- `JustifyUsingRUP{}` — reverse unit propagation suffices (optionally `JustifyUsingRUP{hints::Foo{...}}` to carry a typed assertion hint)
- `JustifyExplicitly{emit, ThenRUP::Yes}` — `emit` is a `(const ReasonLiterals &) -> void` callback (or a named fat-witness struct, for a reification verdict) that writes explicit VeriPB proof steps. `ThenRUP` is mandatory: `Yes` RUPs the inferred literal after the steps, `No` lets the steps conclude it. An optional third argument is a typed assertion hint, shared with `JustifyUsingRUP`.

### Testing Pattern

Constraint tests live beside the constraint they test (e.g.
`gcs/constraints/equals/equals_test.cc`) and use the `gcs::test_innards`
utilities in `gcs/constraints/innards/constraints_test_utils.hh`. The test
pattern:
1. Generate all expected solutions using a pure C++ satisfiability check
2. Run the solver and collect actual solutions
3. Compare expected vs actual (optionally checking GAC at each search node)
4. Prove and check: these tests write their own proofs and call `veripb`
   in-process whenever it is on the `PATH` (`can_run_veripb()`,
   `verify_proof_and_clean_up()`), so they need no `--prove` flag and no
   verifying wrapper — which is why ctest registers them with
   `run_test_only.bash`

`run_test_and_verify.bash` is for the *other* kind of test binary: those that
take `--prove` and leave the checking to the wrapper — the examples, benchmarks
and frontends, plus the proof-innards tests under `gcs/` (`reification_test`,
`invar_test`, the `range_witness_*` set, and so on).

Some tests use Catch2 (linked with `Catch2::Catch2WithMain`); others are standalone programs.

### External Dependencies

Fetched at configure time with CMake `FetchContent`:

- **Catch2** — unit test framework (only when `GCS_BUILD_TESTS`)
- **cxxopts** — command-line parsing for the executables and the MiniZinc frontend
- **nlohmann/json** — JSON parsing (MiniZinc support)
- **gch/small_vector** — the small-buffer vector that backs `IntervalSet`, and so sits on the solver's hottest path
- **fmt** — string formatting, only when the compiler has no `<format>`/`<print>`
- **pybind11** — only for the Python bindings (`GCS_ENABLE_PYTHON`, via `python/CMakeLists.txt`)

Not `FetchContent`:

- **generator** — `<generator>` polyfill if the compiler lacks it (C++23); fetched with `ExternalProject_Add`, headers only
- **XCSP3-CPP-Parser** — vendored in-tree, and excluded from clang-format
- **VeriPB** — external proof checker, not fetched by CMake at all: install it separately with `cargo install --path .` from a VeriPB checkout
