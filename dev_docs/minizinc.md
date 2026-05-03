# MiniZinc bindings

This document explains how the Glasgow Constraint Solver plugs into the
MiniZinc / FlatZinc ecosystem, and how to add bindings for new
constraints. It is aimed at developers (human or AI) working on the
`minizinc/` directory; users who only want to *use* Glasgow as a
MiniZinc solver should read the "Using the MiniZinc Solver" section
of the top-level `README.md` instead.

## What MiniZinc bindings do

MiniZinc is a high-level modelling language; FlatZinc is its low-level
solver-input form. Glasgow participates via three pieces:

1. A standalone executable `fzn-glasgow` (built from
   `minizinc/fzn_glasgow.cc`) that reads JSON FlatZinc and posts
   constraints to a `gcs::Problem`.
2. Solver-configuration files (`*.msc`) that register `fzn-glasgow`
   as a MiniZinc solver.
3. A library (`minizinc/mznlib/`) of predicate overrides that redirect
   specific FlatZinc predicates to Glasgow-specific implementations.

When a user selects the Glasgow solver, MiniZinc compiles the model to
FlatZinc using our `mznlib/` for predicate definitions, then runs
`fzn-glasgow` on the result.

## The pipeline for one constraint

Take `lex_less(x, y)`:

1. **MiniZinc stdlib** (`lex_less.mzn`) — handles the trivial cases
   (length 0, length 1) inline, and for the general case calls
   `fzn_lex_less_int(...)`.

2. **Glasgow `mznlib/fzn_lex_less_int.mzn`** — overrides the stdlib's
   default decomposition to instead call `glasgow_lex_less_int(...)`,
   declared as an opaque solver predicate.

3. **MiniZinc emits FlatZinc JSON** containing a constraint with `id`
   `glasgow_lex_less_int` and the array arguments inlined.

4. **`fzn-glasgow`** parses the JSON, walks the `constraints` array,
   and for each `id` dispatches to a C++ branch that calls
   `problem.post(LexLessThan{vars1, vars2})`.

If we don't override a predicate in `mznlib/`, MiniZinc uses the
stdlib decomposition (typically a PB or boolean encoding), which
still works but doesn't reach our dedicated propagator.

## Solver configuration files

Three `.msc` files are checked in:

| File                          | Purpose                                                                        |
|-------------------------------|--------------------------------------------------------------------------------|
| `glasgow.msc`                 | end-user solver registration; expects `build/fzn-glasgow`                      |
| `glasgow-for-tests.msc`       | what ctest uses; expects `fzn-glasgow` on `PATH`                               |
| `glasgow-for-debugging.msc`   | declares the executable as `false` so MiniZinc never invokes it; useful when running `fzn-glasgow` under a debugger by hand |

All three reference `mznlib/` as the predicate library directory.

## Adding a new constraint binding

The general recipe (see `gcs/constraints/lex.cc` and the
`minizinc/{mznlib,tests,fzn_glasgow.cc}` changes that bound it):

1. **Find the right FlatZinc predicate(s) to override.** Look at the
   stdlib (in the `MiniZinc/libminizinc` repo under
   `share/minizinc/std/`) for the `fzn_*.mzn` files. There's often
   one per type and one per reified/non-reified variant; e.g.,
   `fzn_lex_less_int`, `fzn_lex_less_int_reif`, `fzn_lex_less_bool`,
   `fzn_lex_less_bool_reif`.

2. **Write `mznlib/fzn_<name>.mzn` files.** Each follows the pattern:

   ```minizinc
   predicate glasgow_<name>(...);
   predicate fzn_<name>(...) = glasgow_<name>(...);
   ```

   Declare your `glasgow_<name>` predicate with the same parameters as
   `fzn_<name>`, then redirect.

3. **Add a C++ dispatch branch** in `fzn_glasgow.cc`. Find the
   `else if (id == "...")` chain in the main loop and add yours
   alphabetically among the `glasgow_*` ids. Use the helpers
   `arg_as_var`, `arg_as_array_of_var`, `arg_as_array_of_integer`,
   and `arg_as_set_of_integer` to extract typed arguments from the
   JSON.

4. **Add small test instances** in `minizinc/tests/<name>.mzn`. Each
   should call the user-facing predicate (`lex_less`, not
   `fzn_lex_less_int`), `solve satisfy;`, and emit either an
   `ENUMSOL:`-prefixed enumeration line or an `OPTSOL:`-prefixed
   optimisation line. Keep the solution count small — see *Testing*
   below.

5. **Add `add_test` lines** in `minizinc/CMakeLists.txt`, one per
   `.mzn` test, all set to `SKIP_RETURN_CODE 66` (which means
   "MiniZinc isn't installed, skip").

## Testing

Each test is a small `.mzn` instance run twice by
`run_minizinc_test.bash`:

1. Once with `--solver glasgow-for-tests.msc` (Glasgow).
2. Once with the default MiniZinc solver (currently Gecode).

The harness extracts solutions matching `^ENUMSOL:` (or the last
`^OPTSOL:` for optimisation) from each run and diffs them. Any
divergence fails the test. If `veripb` is installed, the harness then
re-runs Glasgow with `--prove` and verifies the proof file. Tests
that don't need proof verification can pass `false` as the last
argument to the bash script.

### Solution counts

Be deliberate about how many solutions a test enumerates. The default
solver enumerates all of them, and divergent solvers can take many
seconds on instances with many thousands of solutions.

If you stack independent constraint instances (each with their own
fresh variable set) in a single test file, the solution count
multiplies across them: four independent length-2-vs-3 lex constraints
over `1..2` give around 65k solutions. Prefer keeping each test
focused on one constraint variant; if you need to exercise multiple
variants, share variables across them or split into separate test
files.

## Bool vs int

`fzn-glasgow` represents a `var bool` as an `IntegerVariableID` with
domain `{0, 1}` — see the `var_type == "bool"` branch in
`fzn_glasgow.cc`. So most C++ branches that handle int variants can
also handle their bool counterparts. Combine them with:

```cpp
else if (id == "glasgow_X_int" || id == "glasgow_X_bool") { ... }
```

You still need the separate `mznlib/` files because MiniZinc dispatches
on the type of the argument arrays before reaching `fzn-glasgow`.

## Semantic gotchas

### Standard semantics may not match your propagator

The stdlib decomposition is the de facto reference for what each
predicate means. Solvers that have their own dedicated propagators
must agree with it on every input — including corner cases the docs
don't mention.

A real example from this codebase: the C++ Lex propagator originally
ignored trailing elements of unequal-length arrays (treating
`min(|x|, |y|)` as the comparison length), so `lex_less([1,2],
[1,2,0])` returned false. The MiniZinc stdlib decomposition says it
should be true (longer wins on equal common prefix). Adding a MiniZinc
binding for Lex without first fixing the propagator would have caused
silent solver disagreement that only the cross-solver test diff would
have caught. Always think about: *what does the stdlib decomposition
do for unequal sizes / empty inputs / special values?*

### `lex_greater`, `lex_greatereq`, etc., never reach you

The MiniZinc stdlib defines `lex_greater(x, y) = lex_less(y, x)` and
`lex_greatereq(x, y) = lex_lesseq(y, x)`. These rewrites happen
*before* flattening, so the FlatZinc only ever contains `_less` /
`_lesseq` predicates with the arguments swapped. You don't need (and
can't) bind `fzn_lex_greater_*`. The same pattern applies to other
predicate families with one-sided FlatZinc forms — always confirm in
the stdlib which forms actually emit a `fzn_*` call.

### Unsupported types

`fzn-glasgow` doesn't support `var float` or `var set of int`, so
predicates that have float/set variants only need int (and bool)
overrides. Leaving the float/set ones to the default decomposition is
fine; if the user writes a model that needs them, MiniZinc will either
decompose or fail at flattening. Don't write empty `fzn_*_float.mzn`
overrides — that breaks the default decomposition path.

### Search annotations

`fzn-glasgow` understands `int_search`, `bool_search`, and
`seq_search` annotations and translates the `var_heuristic`,
`val_heuristic`, and `method` arguments into Glasgow's
`BranchCallback` constructors. Unknown heuristics get a warning and a
fallback. If you add a new branching strategy or value-selection
order, that's where to plumb it through.

## Where things live

```
minizinc/fzn_glasgow.cc                main FlatZinc → C++ dispatcher
minizinc/CMakeLists.txt                builds fzn-glasgow + ctest entries
minizinc/glasgow.msc                   solver definition for end users
minizinc/glasgow-for-tests.msc         solver definition used by ctest
minizinc/glasgow-for-debugging.msc     dummy executable for manual debugging
minizinc/mznlib/                       per-predicate overrides
minizinc/mznlib/redefinitions.mzn      include "nosets.mzn" entry point
minizinc/mznlib/redefinitions-2.0.mzn  per-MiniZinc-version overrides
minizinc/tests/                        per-test .mzn instances
minizinc/run_minizinc_test.bash        cross-solver diff + VeriPB harness
```

## Adding a new constraint binding: checklist

1. Identify the FlatZinc predicate(s) — usually `fzn_<name>_int`,
   often plus `_int_reif` and `_bool` and `_bool_reif`.
2. For each, add an override in
   `mznlib/fzn_<name>_<type>[_reif].mzn` that declares a
   `glasgow_<name>_<type>[_reif]` predicate and redirects `fzn_*` to
   it.
3. Add C++ dispatch branches in `fzn_glasgow.cc`. Coalesce int+bool
   variants when they map to the same C++ class.
4. Add small `.mzn` tests in `minizinc/tests/`. Keep solution counts
   small; one test per constraint variant rather than one test with
   all variants.
5. Add `add_test` lines in `minizinc/CMakeLists.txt` with
   `SKIP_RETURN_CODE 66`.
6. Run `ctest -R minizinc-<your-name>` to verify; check that the
   default-solver enumeration matches and the VeriPB proof verifies.
