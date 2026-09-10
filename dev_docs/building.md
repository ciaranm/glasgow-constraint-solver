# Building, build options, and toolchains

`README.md` has what a *user* of the solver needs: dependencies, the three
presets, and how to run `ctest`. This document is the developer's side of the
same ground — why the build is configured the way it is, the full option
catalogue, which toolchains have to keep working, and which test wrapper runs
what. Read it before editing `CMakeLists.txt` or adding a build option.

## Build types

Three build types are supported: `Release` (default), `Debug`, and `Sanitize`,
with a named preset each in `CMakePresets.json` and its own build directory
(`build/`, `build-debug/`, `build-sanitize/`), so all three can coexist:

```shell
cmake --preset release  && cmake --build --preset release   # optimised (default)
cmake --preset debug    && cmake --build --preset debug     # -O0, full debug info
cmake --preset sanitize && cmake --build --preset sanitize  # ASan + UBSan
```

Or explicitly, without presets — this is the release build:

```shell
cmake -S . -B build
cmake --build build --parallel $(nproc 2>/dev/null || sysctl -n hw.logicalcpu)
```

### Debug information is scaled to purpose

All three keep debug information, but not the same amount. `Release` (with
`/Z7` plus linker `/DEBUG` as the MSVC equivalent) and `Sanitize` use `-g1`;
`Debug` uses `-g3`.

`-g1` is function names plus line tables — what GCC documents as "enough for
making backtraces". That is all `ProofLogger::log_stacktrace` needs for the
`GCS_VERBOSE_LOGGING` proof annotation, and all an ASan or UBSan report needs
to name a function and a `file:line`, so keeping it in Release means crash
reports and verbose proofs stay useful in optimised builds.
`stacktrace_logging_test` fails if a Release build ever drops it.

`Sanitize` is `-g1` for size, and that is a deliberate trade. Every test binary
statically links the whole solver, so each carries its own copy of the same
DWARF: at `-g3` the tree's 173 programs came to 84.6 GiB of a 93 GiB build
tree, which is more than a GitHub runner has — the Sanitize lane died mid-test
with "No space left on device" when the tests went to write their proof files.
At `-g1` the same programs come to 52.1 GiB and the tree to 56 GiB. What is
given up is macros and local-variable DWARF, and those want a debugger — which
is what the `Debug` configuration is for. Build `Debug` when you are going to
attach one.

### The per-configuration flags must stay plain `set()`

The `CMAKE_CXX_FLAGS_<CONFIG>` assignments near the top of `CMakeLists.txt` are
plain `set()` calls, not `set(... CACHE ...)`, and must stay that way.

`set(FOO "value" CACHE STRING "help")` is a *defaulting* operation: it does
nothing at all, without a word of warning, when the cache entry already exists.
By the time `CMakeLists.txt` runs, `project()` has already created a
`CMAKE_CXX_FLAGS_<CONFIG>` cache entry for every configuration — the standard
ones get CMake's defaults, and since CMake 4.2 the custom `Sanitize`
configuration gets an *empty* one. So every cached `set()` there was a no-op.
For Release and Debug that went unnoticed, because CMake's defaults are close
to what was wanted; for Sanitize it meant compiling with no flags whatsoever,
and a CI lane that reported "sanitize clean" for months without ever running a
sanitizer (issue #597).

So: do not "tidy" these back into cache variables. A configure-time check and
`sanitizers_enabled_test` will both object if the flags go missing again,
however that happens. The trade-off is that `-DCMAKE_CXX_FLAGS_SANITIZE=...` on
the command line does not reach the compiler — but it never did. To add flags
to every configuration, use `CMAKE_CXX_FLAGS`, which is applied ahead of these
and is unaffected; to change what a build type *means*, edit it there.

One consequence when checking a build: `CMakeCache.txt` still holds CMake's own
(for Sanitize, empty) entries, because nothing writes to the cache any more, so
grepping the cache tells you nothing about the flags actually in use. The build
files are the truth:

```shell
grep CXX_FLAGS build-sanitize/gcs/CMakeFiles/*.dir/flags.make
```

### Parallelism

Use `--parallel N`. The expression `$(nproc 2>/dev/null || sysctl -n
hw.logicalcpu)` gives the CPU count on both Linux and macOS. Omitting the count
lets `make` spawn unlimited jobs, which exhausts memory. If a build fails and
the error output is hard to read, re-run without `--parallel` for clean
sequential output. For `ctest`, use `-j $(nproc 2>/dev/null || sysctl -n
hw.logicalcpu)`.

## Build options

| Option | Default | What it does |
|--------|---------|--------------|
| `GCS_ENABLE_XCSP` | on at top level | XCSP3 frontend; needs libxml2 |
| `GCS_ENABLE_MINIZINC` | on at top level | MiniZinc / FlatZinc frontend |
| `GCS_ENABLE_PYTHON` | `OFF` | `gcspy` bindings; needs Python and pybind11. `python/pyproject.toml` turns it on |
| `GCS_ENABLE_EXECUTABLES` | on at top level | Everything that is a program rather than the library: `examples/`, `benchmarks/`, `verified_encodings/`, `scp/`, `minicp_benchmarks/`. Formerly `GCS_ENABLE_EXAMPLES`, which still supplies the default |
| `GCS_BUILD_TESTS` | on at top level | Build the tests, and fetch Catch2 |
| `GCS_ENABLE_DOXYGEN` | `OFF` | Adds the `docs` target |
| `GCS_NATIVE_ARCH` | `ON` | `-march=native` on Release. Turn off for redistributable binaries such as wheels |
| `GCS_WERROR` | `OFF` | `-Werror`. One CI lane only — see below |
| `GCS_ENABLE_VIEW_WRAP_SWEEP` | `OFF` | The full view-wrap proof sweep; see [view-proof-logging.md](view-proof-logging.md) |
| `GCS_LARGE_DOMAIN_GUARD` | `OFF` | Development tripwire for width-proportional work, plus the audit lane; see [large-domains.md](large-domains.md) |
| `GCS_TEST_CAP_DEFAULTS` | `ON` | Per-solve caps on the data-driven constraint tests; see [constraints.md](constraints.md) |
| `GCS_TEST_MAX_SOLUTIONS` | `300` | The solution cap those defaults apply |
| `GCS_TEST_MAX_RECURSIONS` | `1500` | The search-node cap those defaults apply |

Two of these change what the test suite *checks*, rather than merely what gets
built, and are the ones to reach for when working on a propagator:

```shell
cmake -S . -B build -DGCS_TEST_CAP_DEFAULTS=OFF      # full-enumeration completeness checking
cmake -S . -B build -DGCS_ENABLE_VIEW_WRAP_SWEEP=ON  # ~7200 extra view-wrap proof tests
```

A capped run checks soundness and a partial proof only, **not** completeness.
The caps exist so a pathological random instance cannot dominate the parallel
suite; turning them off is what makes the tests enumerate fully, as the two
default-GCC Ubuntu CI lanes do.

`GCS_WERROR` is a CI lane rather than a normal build setting: GCC's warning
baseline has been zero since #710, whereas clang and Apple Clang each still
have a few hundred pre-existing warnings, so only the `ubuntu-26.04` default-GCC
lane can afford `-Werror`. Build with it before pushing if you want to know
what that lane will say.

## Which wrapper runs which test

There are two families of test binary, and ctest drives them differently.

The **data-driven constraint tests** have no `--prove` flag. They write and
check their own proofs, calling `veripb` in-process whenever it is on the
`PATH`, so running one directly already verifies its proofs. ctest registers
them with `run_test_only.bash`, which only runs the binary:

```shell
./build/equals_test
```

**Binaries that take `--prove`** — the examples, benchmarks and frontends, plus
the proof-innards tests under `gcs/` (`reification_test`, `invar_test`, the
`range_witness_*` set) — leave the checking to `run_test_and_verify.bash`, which
runs the binary with `--prove`, checks the proof with `veripb`, and then reads
back any `.scp` it wrote with `glasgow_scp_solver --parse-only`, so that a
constraint whose keyword `read_scp` cannot handle is reported by the program
that posted it:

```shell
./run_test_and_verify.bash ./build/reification_test
```

`run_test_and_expect_verify_failure.bash` is the inverse, for mutation testing:
the binary writes a knowingly wrong proof and the run passes only if `veripb`
*rejects* it. Mutation lanes are the exception to the split above — a handful of
constraint tests are driven through these wrappers with `--mutate=` and the
wrapper's `--basename`, which names the one proof the wrapper then checks. See
[constraints.md](constraints.md) (Mutation testing).

The frontends have their own wrappers — `xcsp/run_xcsp_test.bash`,
`minizinc/run_minizinc_test.bash`, `minizinc/run_fzn_json_test.bash` — as does
the SCP chain harness, `verified_encodings/run_scp_chain.bash` (see
[workflow2_testing.md](workflow2_testing.md)).

All of them dispose of proof files through one `dispose_proof` in
`proof_file_disposal.bash` at the repo root, and all honour
`GCS_PRESERVE_PROOF_FILES`; [constraints.md](constraints.md) (What happens to
the proof files) has the policy.

## Compilers and standard libraries

Development happens with **GCC 15.2.0** and **clang 21**. **MSVC (Visual Studio
2022)** is the third supported compiler. The *oldest* supported compiler is
**GCC 13**, which is what the `ubuntu-24.04` lane and the manylinux wheel build
use, so a C++23 feature that GCC 13 lacks cannot be used unconditionally.

Clang on macOS uses **libc++** (Apple's standard library) rather than libstdc++,
which is the other axis of feature availability: some C++23 library features are
in libstdc++ but not yet in libc++, and vice versa.

Windows/MSVC support is experimental (see README.md, Platform support), but the
`windows-2022` lanes run on every push and pull request just like the Linux and
macOS ones, so code must still compile there. In particular, do not use
GCC/clang extensions or Itanium-ABI-only headers (`<cxxabi.h>`,
`abi::__cxa_demangle`, ...).

### Known gaps

Unavailable in libc++ (the Apple Clang on the macOS lanes; last checked against
clang 21, so re-confirm on CI before relying on a change here):

- `std::views::enumerate` — use `util/enumerate.hh` instead. Do not remove that
  file; 46 files include it.

Unavailable in libstdc++ on the GitHub Actions Ubuntu 24.04 runner (GCC 13),
which we still support:

- `std::vector::append_range` and the other P1206 `*_range` container members —
  `__cpp_lib_containers_ranges` is undefined there. Use `vec.insert(vec.end(),
  src.begin(), src.end())` instead. Reconfirmed unavailable on the Ubuntu 24.04
  lane via CI on 2026-07-03; libc++ (macOS) and GCC 15 both have it.

Confirmed available on **all** supported toolchains, including GCC 13 and macOS
libc++, verified via CI on 2026-07-03 — prefer them where they read more clearly
than a hand-rolled `if` or ternary:

- `std::optional` monadic operations: `.transform()`, `.and_then()`,
  `.or_else()`, `.value_or()`

Three features are probed at configure time rather than assumed, and a fallback
is fetched or disabled when absent: `<format>`/`<print>` (libfmt is fetched
instead), `<generator>` (a polyfill is fetched), and `<stacktrace>` (without it,
`GCS_VERBOSE_LOGGING` is unavailable). See [code-style.md](code-style.md) for
the `#if` pattern a file using `format()` must follow.

When adding a new C++23 feature, build with GCC and clang before committing, and
check MSVC availability — CI is the backstop there.

## CI

Every push to `main` and every pull request runs:

| Lane | Notes |
|------|-------|
| `ubuntu-24.04`, default GCC | GCC 13, the compiler floor; test caps off |
| `ubuntu-26.04`, default GCC | Test caps off, and the only lane with `-DGCS_WERROR=ON` |
| `ubuntu-26.04`, clang | clang + libstdc++, including the lifetime-annotation probe tests |
| `macos-15`, `macos-26` | Apple Clang + libc++ |
| `ubuntu-26.04` Sanitize | ASan + UBSan, through the `sanitize` test preset |
| `windows-2022` | MSVC: library and ctest, then the XCSP3 / MiniZinc / Python frontends, then VeriPB |
| `clang-format` | `--dry-run --Werror` over the whole tree |

Every lane that runs tests installs VeriPB with `cargo install` from a fresh
`--depth 1` clone of upstream, so CI tracks VeriPB's `main` rather than a pinned
version — which means an upstream change can turn a lane red without anything
here having moved. The lanes that exercise the MiniZinc frontend install it too
— the official bundle on Linux and Windows, brew on macOS — without which every
`minizinc-*` test skips rather than failing.

`main` has no branch protection, so a lane reports rather than literally gating
a merge — read the results, do not assume a red lane blocked anything.

## See also

- `README.md` — dependencies, user-facing build and test instructions
- `CONTRIBUTING.md` — clang-format, the pre-commit hook, what a contribution
  should pass before submission
- [code-style.md](code-style.md) — the conventions clang-format does not enforce
- [releasing-gcspy.md](releasing-gcspy.md) — cutting a Python bindings release
- [benchmarking.md](benchmarking.md) — measuring a performance change
