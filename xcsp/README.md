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
the reference XCSP3 solver, by comparing the full set of solutions on small
hand-written instances. The expected solution set for each test is cached in
this repository, so day-to-day testing does not require ACE — the runner just
diffs our output against the cache. ACE is needed only when *adding* a new
test, or to *regenerate* the cache if a test instance changes.

The test infrastructure that consumes these tools is being added under
[#150](https://github.com/ciaranm/glasgow-constraint-solver/issues/150)
(Phase 4); the install recipes below are recorded here so contributors can
set up the environment ahead of time.

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
