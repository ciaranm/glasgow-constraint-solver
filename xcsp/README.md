XCSP3 Support
=============

This directory provides an XCSP3 frontend for the Glasgow Constraint Solver.
It parses XCSP3 instances using the upstream
[XCSP3-CPP-Parser](https://github.com/xcsp3team/XCSP3-CPP-Parser), fetched via
CMake `FetchContent` into the build directory — no separate checkout needed.

Build the binary with:

```shell
cmake --build build --target xcsp_glasgow_constraint_solver
```

Disable the XCSP frontend at configure time with `-DGCS_ENABLE_XCSP=OFF`.

Testing
-------

Tests cross-check our solver against [ACE](https://github.com/xcsp3team/ACE),
the reference XCSP3 solver, by comparing either the full set of solutions
(CSP) or the optimum value (COP) on small hand-written instances. The
expected output for each test is cached:

- `tests/expected/<name>.sols` — one solution per line, alphabetised
  `name=value` tuples (CSP enumeration mode).
- `tests/expected/<name>.opt` — a single integer, the proven optimum
  (COP optimisation mode).

Day-to-day testing does not require ACE — the runner just diffs our
output against the cache. If neither cache file is present for a test,
it is **skipped** (ctest exit code 66) rather than failed.

ACE is needed only to (re)generate the cache. Run:

```shell
ACE_JAR=/path/to/ACE-2.6.jar xcsp/regenerate_expected.bash <testname>
```

This invokes ACE in enumerate mode (`-s=all -xe -xc=false`), parses the
streamed `<instantiation>` blocks, expands array shorthand (`s[]`,
`m[][]`, …) using the dimensions read from the instance XML, and writes
the canonical sorted output. Commit the file alongside the new test.

### Optional dependencies for adding new tests

- **JDK 11+** (required by ACE):
  ```shell
  sudo apt install -y openjdk-21-jdk-headless
  ```
- **ACE 2.6+**:
  ```shell
  git clone https://github.com/xcsp3team/ACE.git
  cd ACE && ./gradlew build
  # Resulting fat JAR: build/libs/ACE-2.6.jar
  ```
- **pycsp3 2.5+** (for instance generation and the official solution
  checker; install into a virtualenv, since `pipx` rejects pure libraries):
  ```shell
  python3 -m venv ~/.venvs/pycsp3
  ~/.venvs/pycsp3/bin/pip install pycsp3
  ```

<!-- vim: set tw=100 spell spelllang=en : -->
