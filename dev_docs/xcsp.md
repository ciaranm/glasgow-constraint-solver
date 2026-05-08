# XCSP3 bindings

This document explains how the Glasgow Constraint Solver consumes
[XCSP3](https://xcsp.org) instances, and how to add bindings for new
constraints. It is aimed at developers (human or AI) working on the
`xcsp/` directory; users who only want to *use* Glasgow on an XCSP3
instance should read the "Using the XCSP Solver" section of the
top-level `README.md` instead.

For implementing the underlying C++ constraint that a binding exposes,
see [constraints.md](constraints.md). For the cross-frontend picture
(which propagators each frontend reaches), see
[frontend-support-matrix.md](frontend-support-matrix.md).

The XCSP3-core specification (v3.2, August 2024) is at
<https://arxiv.org/abs/2009.00514>. Parser callbacks are documented
inline in the upstream
[XCSP3-CPP-Parser](https://github.com/xcsp3team/XCSP3-CPP-Parser)
(`include/XCSP3CoreCallbacks.h`).

## What XCSP3 bindings do

XCSP3 is an XML-based modelling format used by the annual XCSP3
competition. Glasgow participates via two pieces:

1. A standalone executable `xcsp_glasgow_constraint_solver` (built from
   `xcsp/xcsp_glasgow_constraint_solver.cc`) that parses an XCSP3 XML
   instance and posts constraints to a `gcs::Problem`.
2. The upstream
   [XCSP3-CPP-Parser](https://github.com/xcsp3team/XCSP3-CPP-Parser)
   library, fetched via CMake `FetchContent` into the build directory.
   The parser walks the XML tree and invokes virtual `buildConstraint*`
   callbacks on a user-supplied subclass of `XCSP3CoreCallbacks`.

When a user runs `xcsp_glasgow_constraint_solver instance.xml`, the
parser dispatches each constraint declaration to one of our overridden
callbacks, which builds the equivalent gcs constraint(s) and posts
them on the `Problem`.

## The pipeline for one constraint

Take `<allDifferent>`:

1. **The XCSP3 XML** has an element like
   ```xml
   <allDifferent>
       <list> x[] </list>
   </allDifferent>
   ```

2. **The parser** finds the `<allDifferent>` tag, expands the
   `<list>` (resolving array shorthand `x[]` from the variable
   declarations), and invokes
   `buildConstraintAlldifferent(id, list_of_XVariable_pointers)`.

3. **`xcsp_glasgow_constraint_solver.cc`** overrides the callback and
   posts `AllDifferent{vars}` on the `Problem`.

The same pattern applies to every supported constraint: a callback per
constraint family, with a body that translates parser-supplied
arguments into a `gcs::*` constraint and posts it.

## Code structure

The whole binding lives in one file, `xcsp/xcsp_glasgow_constraint_solver.cc`.
Internally:

- **`ManagedVariable`** (struct) — a parsed XCSP3 variable, with the
  underlying `IntegerVariableID` created **lazily on first use**
  (`need_variable`). XCSP3 allows declaring variables that never
  appear in any constraint; lazy creation avoids putting unused state
  into `gcs::Problem`. Domain is either a range (`lower`, `upper`) or
  an explicit value list (`values`).

- **`ExprResult`** (struct) — what the intension tree walker returns:
  the `IntegerVariableID` holding the expression's value plus the
  `lower`/`upper` bounds we computed for it. Bounds drive the size of
  any newly-created result variables further up the tree.

- **`report_unsupported(constraint, reason)`** — the centralised
  reporter that throws `UnimplementedException`. `main()` catches
  this and emits `s UNSUPPORTED` plus a comment line. Use this any
  time a callback hits a feature we don't (yet) implement, with a
  brief reason — the parser's default behaviour is to throw an
  uncaught `runtime_error` which terminates the process.

- **`XCSPCallbacks`** (class, derives from `XCSP3CoreCallbacks`) —
  holds the `_problem` reference, the variable map, the array-storage
  members for `Element`, and the `_most_recent_tuples` for the
  `extension` "as" form. The constructor sets the parser flags:
  `intensionUsingString = false` so we get the typed `Tree*` form,
  `recognizeSpecialIntensionCases = false` so all intension comes
  through one path, and `recognizeSpecialCountCases = true` so the
  parser pre-dispatches `atMost`/`atLeast`/`exactlyK`/`among` to
  dedicated callbacks.

- **`main()`** — sets up cxxopts, runs the parser, runs `solve_with`,
  prints solutions and statistics. In `--all` (CSP enumeration) mode,
  each solution is streamed as one `ENUMSOL: name=val name=val ...`
  line as the search runs (variables sorted alphabetically). In COP
  mode, each improving objective value is streamed as `o N`, with a
  final `s OPTIMUM FOUND` and a single-solution `<instantiation>`
  block.

## The intension tree walker

`<intension>` constraints contain an arbitrary algebraic expression
tree. The parser hands us the typed `Node*` AST (because of the
`intensionUsingString = false` flag); we walk it with two related
methods:

- **`walk_intension(Node *)`** — returns an `ExprResult`. For
  leaf nodes (`ODECIMAL`, `OVAR`) it returns the constant or variable
  directly. For operator nodes it recursively walks the children, then
  builds a fresh result variable, posts the appropriate gcs
  constraint, and returns the result. Boolean operators (`OEQ`,
  `OLT`, `OAND`, `OXOR`, …) reify to a 0/1 control variable using
  the corresponding `*Iff` constraint.

- **`post_intension_top_level(Node *)`** — entry point for an
  intension constraint. Top-level relational roots (`OEQ`, `ONE`,
  `OLT`, `OLE`, `OGT`, `OGE`, `OOR`, `OIN`, `ONOTIN`, `OAND`, `OXOR`,
  `OIMP`, `OIFF`) get posted directly without going through
  reification — e.g. `eq(x, y)` at the top level posts `Equals{x, y}`
  rather than reifying to a 0/1 variable and asserting it equals 1.
  Anything else falls through to `walk_intension` and gets asserted
  to be 1.

Two helpers reduce duplication:

- **`reify_binary<ConstraintT>(Node*, name)`** — used by `OEQ`,
  `ONE`, `OLT`, `OLE`, `OGT`, `OGE`, `OIFF` inside an expression
  context. Walks both children, creates a 0/1 control, posts the
  given `*Iff` reified constraint, returns the control.
- **`post_product(ExprResult, ExprResult, name)`** — used by `OMUL`
  (n-ary, left-fold), `OSQR`, and `OPOW` (constant exponent →
  product chain). Picks `WeightedSum` when one side is a constant,
  `Times` otherwise. The constant-detection logic in this helper is
  a workaround that should eventually move into the user-facing
  `Times` constructor — see #153.

## The `apply_count_condition` shape

Several XCSP3 constraints (`count`, `nValues`, `minimum`, `maximum`,
`knapsack`'s two conditions) reduce to "compute a result variable;
constrain it via an `XCondition`". The shared helper
`apply_count_condition(result, xc, ctx)` handles the dispatch on
`xc.operandType` (variable vs integer vs interval) and `xc.op`
(LE/LT/EQ/GT/GE/NE) and posts the corresponding direct constraint
(e.g. `Equals{result, rhs}`). When you add a callback that has the
same "result variable + condition" shape, lean on this helper instead
of writing a fresh switch.

## Element array lifetime

`Element` (and `Element2D`, etc.) takes a raw pointer to its array
and holds it through `clone()`, which is invoked during search. The
array therefore has to outlive every solver phase, not just the
parser callback. We can't pass a stack-local pointer (the original
binding had this latent bug).

The `XCSPCallbacks` class holds three vectors of `unique_ptr`s:

- `_element_arrays` — 1D variable arrays.
- `_element_2d_var_arrays` — 2D variable matrices.
- `_element_2d_const_arrays` — 2D constant matrices.

Each `allocate_element_*` helper builds a new `vector` on the heap,
moves it into the appropriate member, and returns the raw pointer for
the constraint. The unique_ptrs are released only when the
`XCSPCallbacks` instance is destroyed, which is after the `Problem`
is solved.

## Honest gaps

Four XCSP3-core constraint families have no propagator yet:
`noOverlap` (#146 — needs `Disjunctive`), `cumulative` (#147),
`binPacking` (#148), and `mdd` (#149). The binding overrides each of
their callbacks with a `report_unsupported` call so the parser's
default uncaught `runtime_error` doesn't terminate the process.
`main()` also catches `std::runtime_error` as a safety net for any
other unhandled callback the parser might throw on.

Constraint forms we *partially* support get the same treatment for
the unsupported cases — e.g. `precedence` with `covered=true`,
`channel` with the one-to-many shape, `nValues` with `<except>`.

## Testing

Each ctest is a small `.xml` instance run by `xcsp/run_xcsp_test.bash`:

1. Run the binding with `--prove` (and `--all` for CSP).
2. For CSP: extract the streamed `ENUMSOL: ...` lines, sort, and
   diff against the cached expected list at `tests/expected/<name>.sols`.
3. For COP: extract the last `o N` line and compare against the
   single integer in `tests/expected/<name>.opt`. Require
   `s OPTIMUM FOUND` in the output.
4. Run `veripb` on the proof artefacts.

If neither cache file exists, the test is **skipped** (ctest exit
code 66) rather than failed: caches are populated explicitly via
`xcsp/regenerate_expected.bash`, not silently as a side effect of
`ctest`. The harness is therefore decoupled from ACE — installing
ACE is only required to populate or refresh the cache.

### Cache format

CSP `.sols` files are one solution per line, with each solution as
alphabetised `name=value` tuples joined by spaces (e.g.
`x[0]=1 x[1]=2 y=0`). The whole file is sorted lexically so that
`diff -u` against the gcs solution stream is order-insensitive.

COP `.opt` files contain a single integer: the proven optimum.

### Regenerating

```shell
ACE_JAR=/path/to/ACE-2.6.jar xcsp/regenerate_expected.bash <testname>
```

The script runs ACE on the instance:
- For CSP, in enumerate mode (`-s=all -xe -xc=false`), parses the
  streamed `<instantiation>` blocks, expands array shorthand (`s[]`,
  `m[][]`) using dimensions read from the instance XML, and writes
  the canonical sorted output.
- For COP, in default mode, extracts ACE's `d BOUND <value>` line
  and writes that.

If ACE produces a different result from gcs, the diff during ctest
will fail loudly — that's the cross-check working. One known
disagreement is documented under #167 (circuit semantics).

## Adding a new constraint binding

1. **Find the parser callback.** Look in
   `XCSP3-CPP-Parser/include/XCSP3CoreCallbacks.h` (or in the
   already-fetched copy under
   `build/_deps/xcsp3_cpp_parser-src/include/`) for the relevant
   `buildConstraint*`. Many constraints have multiple overloads
   distinguished by argument types (`vector<int>` vs
   `vector<XVariable*>` for coefficients, etc.). Decide which
   overload(s) you'll override.

2. **Implement the override** in `XCSPCallbacks`. Use:
   - `need_variable(name)` / `need_variables(x_vars)` to materialise
     `IntegerVariableID`s lazily.
   - `find_variable(name)` to read a `ManagedVariable`'s bounds
     without creating the underlying gcs variable.
   - `apply_count_condition(result, cond, ctx)` for any constraint
     of shape "result variable + `XCondition`".
   - `report_unsupported(name, reason)` for forms you can't yet
     handle.

3. **Write a small test instance.** Hand-write a tiny XCSP3 XML
   under `xcsp/tests/<name>.xml` that exercises the constraint with
   a small, exhaustively-enumerable solution set.

4. **Regenerate the cache** with `regenerate_expected.bash`. Verify
   the count looks right by hand. If gcs and ACE disagree, you have
   either a bug in your binding or a real semantic mismatch like
   #167 — investigate before committing.

5. **Add `add_xcsp_test(<name>)` to `xcsp/CMakeLists.txt`**, in the
   alphabetical block.

6. **Update `dev_docs/frontend-support-matrix.md`** — flip the
   relevant row from "frontend gap" to ✓ (or note the partial
   support).

7. Run `ctest --preset release -R xcsp_<name>` to verify.

## Where things live

```
xcsp/xcsp_glasgow_constraint_solver.cc   the whole binding (callbacks + main)
xcsp/CMakeLists.txt                      FetchContent + add_xcsp_test() helper
xcsp/run_xcsp_test.bash                  ctest harness (CSP/COP, cache diff, veripb)
xcsp/regenerate_expected.bash            ACE-based cache populator
xcsp/tests/<name>.xml                    per-test XCSP3 instance
xcsp/tests/expected/<name>.sols          CSP enumeration cache
xcsp/tests/expected/<name>.opt           COP optimum cache
xcsp/README.md                           user-facing setup notes (ACE, pycsp3, JDK)
```

## Semantic gotchas

### Constraint semantics may not match the XCSP3-core spec

The gcs propagators were not designed against XCSP3-core; they have
their own conventions. Two real cases:

- **`circuit`**: gcs's `Circuit` requires a strict Hamiltonian cycle,
  but XCSP3-core allows isolated vertices via self-loops. The
  binding currently posts `Circuit` directly, so it imposes a
  stricter constraint than the spec. Tracked as #167.
- **`Times`/`Div`/`Mod`/`Power`**: the gcs propagators materialise the
  cross-product of operand domains and blow up memory on wide
  domains. The binding does some constant-folding upstream (in
  `post_product`), but the right fix is a friendlier user-facing
  C++ API in gcs that does the folding and dispatches to `MultBC`
  for the all-variables case. Tracked as #153.

When you bind a new constraint, always check the XCSP3-core spec's
semantics against gcs's propagator's behaviour, especially for
edge cases (empty inputs, singleton arrays, special values like
zero). A real semantic mismatch is best caught at binding time
rather than after a benchmark run.

### Array shorthand in solution output

ACE prints solutions using the array shorthand from the instance
(`<list> s[] </list>`), while gcs always emits individual indexed
names (`s[0] s[1] s[2]`). The regenerator script expands ACE's
shorthand using the instance's `<array size="...">` declarations.
If you write a test that uses unusual shorthand (multi-dim or
heterogeneous), check that the regenerator handles it cleanly.

### `recognizeSpecialCountCases = true`

The parser pre-dispatches `<count>` instances that match common
patterns (atMost/atLeast/exactlyK/among) to dedicated callbacks
rather than the generic `buildConstraintCount`. Our generic
`buildConstraintCount` would handle them too, but the dedicated
overrides bound `how_many` more tightly. If you change one, the
other still has to be correct — both code paths can be exercised by
a single user.

### Element start-index

XCSP3's `<element>` allows a non-zero `startIndex` (1-based, etc.).
gcs's 1-D `Element` constructor has a hardcoded zero offset, so the
binding posts an extra index-shift `WeightedSum` to translate.
`Element2D` does support a pair-form constructor with explicit
offsets, so we use that directly for matrix-form element. If the 1-D
`Element` is ever extended to support an offset, drop the shift.

<!-- vim: set tw=100 spell spelllang=en : -->
