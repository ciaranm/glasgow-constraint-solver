# Implementing a constraint

This document explains the structural pattern every constraint follows in
the Glasgow Constraint Solver: the class shape, how `install` is
organised, the propagator framework, the inference and justification
APIs, the OPB encoding side, and the testing pattern. It deliberately
does **not** go into the algorithmic details of propagation or the
specifics of OPB encoding for any particular constraint — both vary
hugely across constraints, from a one-line implication for `NotEquals`
to graph algorithms for `Circuit`.

For reified constraints, read this document first, then
[reification.md](reification.md) for the additional machinery on top.
For exposing a finished constraint to MiniZinc, see
[minizinc.md](minizinc.md).

## The big picture

A `Constraint` is a user-facing object posted on a `Problem`. When the
solver starts, each constraint's `install` method runs once. It does two
things:

1. Optionally describes the constraint in PB terms by calling
   `optional_model->add_constraint(...)` zero or more times. This
   block is guarded by `if (optional_model)` and is what VeriPB sees.
2. Registers one or more propagators with the `Propagators` object. A
   propagator is a callable that gets invoked at search time to enforce
   the constraint by tightening variable domains.

After install, the constraint object itself is gone — only the
propagators (with their captured state) and the OPB definition remain.

## File layout

For a constraint named `Foo`:

```
gcs/constraints/foo.hh        public class declaration
gcs/constraints/foo.cc        install method + propagator
gcs/constraints/foo_test.cc   enumeration tests
```

Then three places to wire it up:

- `gcs/CMakeLists.txt` — add `foo.cc` to the library sources, and
  `foo_test` to the test target list.
- `gcs/gcs.hh` — add `#include <gcs/constraints/foo.hh>`. **This is
  easy to forget**; downstream consumers (`fzn-glasgow`, examples) get
  the class via this umbrella header.

### Constraint families

Some constraints come in groups — multiple algorithms
(`gac_all_different`, `vc_all_different`), variants
(`AllDifferentExcept`, `AllDifferentExceptZero`), or shared
encoding/justify helpers (`encoding.cc`, `justify.cc`). When a new
constraint shares concepts with an existing one, put its files inside
the family's subdirectory:

```
gcs/constraints/all_different.hh                       public umbrella header
gcs/constraints/all_different/gac_all_different.hh     one variant's interface
gcs/constraints/all_different/all_different_except.hh  another variant
gcs/constraints/all_different/encoding.{hh,cc}         shared OPB helper
gcs/constraints/all_different/justify.{hh,cc}          shared proof helper
gcs/constraints/all_different/*_test.cc                tests
```

The umbrella `gcs/constraints/<family>.hh` just `#include`s every
variant's header (and may add a `using AllDifferent = GACAllDifferent;`
style alias). `gcs/gcs.hh` then only needs the umbrella, not each
variant.

Look for an existing family before adding a new top-level
`gcs/constraints/foo.{hh,cc}`: `all_different/`, `circuit/`,
`linear/`, `innards/`. A constraint that's genuinely standalone (no
shared concepts with any existing family) keeps the flat layout.

## The header

```cpp
namespace gcs
{
    /**
     * \brief One-line description of what the constraint enforces.
     *
     * \ingroup Constraints
     */
    class Foo : public Constraint
    {
    private:
        // Captured arguments (vars and constants).

    public:
        explicit Foo(/* arguments */);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(
            const innards::ProofModel * const) const -> std::string override;
    };
}
```

`install` is rvalue-qualified (`&&`) — it consumes the Constraint
object. `clone` produces a fresh independent copy (used by some search
strategies). `s_exprify` produces a textual dump of the constraint for
debugging.

## install: the entry point

The recommended shape splits `install` into three phases, each
override-able as a protected virtual on `Constraint`:

```cpp
auto Foo::install(Propagators & propagators, State & initial_state,
    ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Foo::prepare(Propagators &, State & initial_state,
    ProofModel * const) -> bool
{
    // Early-out for trivial cases; precompute state shared by the
    // next two phases. Return false to skip them.
    return /* not trivially satisfied */;
}

auto Foo::define_proof_model(ProofModel & model) -> void
{
    // OPB definition only. State precomputed in prepare() may be
    // referenced via private members.
}

auto Foo::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    // ... fill in trigger sets ...
    propagators.install(
        [/* captures, typically moving in member fields */](
            const State & state, auto & inference,
            ProofLogger * const logger) -> PropagatorState {
            // Propagation body.
            return PropagatorState::Enable;
        },
        triggers);
}
```

State that needs to flow between phases (filtered task lists, proof-flag
handles, cached line numbers) goes on the class as private members.
`all_equal.cc`, `count.cc`, and `cumulative.cc` are good references.

Older constraints (e.g. `Knapsack`) still inline everything in
`install()`; new code shouldn't follow that — the split form is the
target everything is moving toward.

The lambda runs once at the root and again whenever any of its triggers
fire. It returns `PropagatorState::Enable` to stay registered, or
`PropagatorState::DisableUntilBacktrack` once the constraint is
*entailed* — i.e., every remaining assignment consistent with the
current variable domains already satisfies the constraint, so no
further propagation can ever be useful. Disabling applies at this
search node *and* every descendant node; the propagator is re-enabled
on backtrack to a level above where it was disabled. Don't return
`DisableUntilBacktrack` just because there's nothing to propagate
*right now* — the propagator will be triggered again as soon as a
domain changes.

### Triggers

Three trigger kinds, applied to specific variables:

| Trigger             | Fires when                           |
|---------------------|--------------------------------------|
| `on_change`         | any value removed from the domain    |
| `on_bounds`         | the lower or upper bound changed     |
| `on_instantiated`   | the variable becomes single-valued   |

Pick the *coarsest* trigger that suffices — `on_bounds` is cheaper to
fire than `on_change`. If the propagator only inspects bounds, use
`on_bounds`. If it iterates the full domain, use `on_change`.

```cpp
Triggers triggers;
for (const auto & v : _vars)
    triggers.on_change.push_back(v);
```

### install_initialiser

For one-shot setup that only runs once at the root (e.g., emitting
proof-log scaffolding that doesn't depend on search state), use
`install_initialiser` instead of `install`:

```cpp
propagators.install_initialiser(
    [/* captures */](const State &, auto &, ProofLogger * const logger) -> void {
        // Setup that runs once.
    });
```

### Backtrackable propagator state

If a propagator needs incremental state across calls that must be
restored on backtrack, register it via `state.add_constraint_state`:

```cpp
auto state_handle = initial_state.add_constraint_state(MyState{});

propagators.install(
    [state_handle, /* ... */](const State & state, auto & inference,
        ProofLogger * const logger) -> PropagatorState {
        auto & my_state = std::any_cast<MyState &>(state.get_constraint_state(state_handle));
        // ...
    },
    triggers);
```

`Lex` uses this for its alpha pointer; `Circuit` uses it for incremental
graph state. Most simple constraints don't need it.

## Querying state

Inside the propagator body, the `State` parameter exposes:

- `state.bounds(v)` → `pair<Integer, Integer>` (lower, upper).
- `state.in_domain(v, val)` → bool.
- `state.has_single_value(v)` → bool.
- `state.each_value_immutable(v)` / `state.each_value_mutable(v)` →
  ranges over the current domain. Use `_immutable` if you only read;
  `_mutable` if you might infer a removal mid-iteration.
- `state.domains_intersect(v1, v2)` → bool. Does the variables' domains
  share any value? Walks both stored interval sets in merge order
  without copying for the common case. Use this instead of
  `for (auto val : state.each_value_immutable(v1)) if (state.in_domain(v2, val))`.

These are read-only — modifying the state goes through `inference`.

## Making inferences

The `inference` parameter is templated; treat it as exposing:

```cpp
inference.infer(logger, lit, justification, reason);
inference.infer_all(logger, {lit1, lit2, ...}, justification, reason);
inference.contradiction(logger, justification, reason);
```

`lit` is an `IntegerVariableCondition` (e.g. `v != 3_i`, `v < 7_i`,
`v == 5_i`). If the inference makes the domain empty, the framework
raises a contradiction automatically — you don't need to check first.

### Reasons

Every inference takes a `ReasonFunction` — a thunk that returns the set
of literals justifying the inference. The two helpers you usually want:

```cpp
auto reason = generic_reason(state, vars);  // each variable's current bounds
auto reason = bounds_reason(state, vars);   // bounds + extras
```

The reason is what goes into the proof's RUP step. Be honest about it:
list every variable whose state contributed to the inference.

## Justifications

The `justification` parameter tells the proof logger how to back the
inference. Four kinds:

| Justification                  | When to use                                                  |
|--------------------------------|--------------------------------------------------------------|
| `NoJustificationNeeded{}`      | Trivial axioms (almost never — usually a code smell)         |
| `JustifyUsingRUP{}`            | Inference is RUP-derivable from the OPB + reason             |
| `JustifyExplicitlyThenRUP{f}`  | Emit explicit proof lines via `f`, then close with a RUP     |
| `JustifyExplicitly{f}`         | Emit explicit proof lines via `f`; no RUP closure            |

The vast majority of inferences want `JustifyUsingRUP{}`. Use
`JustifyExplicitlyThenRUP` when VeriPB can't unit-propagate to the
inference on its own — typically for chains involving auxiliary flags
or longer inference paths.

The callback in `JustifyExplicitlyThenRUP` receives a `ReasonFunction &`
and can emit proof lines via `logger->emit_rup_proof_line_under_reason`,
`logger->emit(RUPProofRule{}, ..., ProofLevel::Temporary)`, and
similar. See `among.cc` and `lex.cc` for examples of varying
complexity.

**Debug aid only:** `AssertRatherThanJustifying` exists as a "trust me"
step that bypasses the justification. Use it temporarily during
development to isolate whether a VeriPB failure is in the OPB
encoding (still fails with `Assert*`) or the justification (passes
with `Assert*`, fails with the real one). Never commit code that uses
it.

### When RUP isn't enough: explicit `pol`

VeriPB's RUP unit-propagation can't combine the *coefficients* of a
linear OPB constraint with the *values* of unit literals on the same
variables — what feels like a one-step linear deduction is actually
two reasoning steps for VeriPB. When the proof needs to compute "the
load already pinned to 1 exceeds the bound", emit the arithmetic
explicitly as a `pol` (polish-notation reverse-polish-style
combination of existing constraint IDs):

```cpp
stringstream pol;
pol << "pol " << C_t_line;
for (auto & [line, weight] : scaled_units)
    pol << " " << line << " " << weight << " * +";
pol << " ;";
logger->emit_proof_line(pol.str(), ProofLevel::Temporary);
```

After the `pol`, the resulting constraint sits in the proof database;
a wrapping RUP can then close cleanly because the cross-coefficient
arithmetic is already done.

The `Cumulative` propagator uses this pattern in three places (one for
each inference); see [`cumulative-proof-logging.md`](cumulative-proof-logging.md)
for a concrete walk-through with PB-form line shapes.

### Pinning a hypothetical fact under "extended reason"

Sometimes the proof step needs a fact that's *not* in the reason — a
literal we're assuming for contradiction, not one we have a witness
for. The trick is to reify the inference under
`{reason ∪ ¬extended_lit}`, which in OPB terms means appending
`extended_lit` as an extra disjunct on the goal:

```cpp
logger->emit_rup_proof_line_under_reason(reason,
    WPBSum{} + 1_i * flag + 1_i * extended_lit >= 1_i,
    ProofLevel::Temporary);
```

VeriPB checks the RUP by negating both the flag and `extended_lit`,
which puts it in exactly the context where the underlying inference
holds. The closing wrapping RUP then supplies `¬extended_lit` from
its own negated goal.

`Cumulative`'s bound-push proofs use this for the task being pushed:
the literal "task `j` is at most/at least so-and-so" doesn't live in
the bounds reason, but it appears in the closing RUP's negation,
where it cancels against the extra disjunct.

**Tracing proof line provenance.** Set `GCS_VERBOSE_LOGGING=1` in the
environment before running a test. Every line written to the `.pbp`
will be preceded by a C++ stacktrace as comment lines (`% ...`), so a
VeriPB failure at `foo_test.pbp:N` can be traced back to the exact
emit site. Cheap to use and often faster than narrowing the failure by
inspection.

## The OPB encoding

Inside `if (optional_model) { ... }`, build PB constraints with `WPBSum`
and pass them to `add_constraint`. Two common shapes:

```cpp
optional_model->add_constraint(WPBSum{} + 1_i * v1 + -1_i * v2 <= 0_i);
optional_model->add_constraint(
    "Foo", "explanation",
    WPBSum{} + 1_i * v1 == 1_i * v2);  // equality: emits two PB lines
```

The `(name, rule)` form is preferred — it tags the constraint in the
OPB output so VeriPB error messages identify which constraint
generated which line.

### Auxiliary variables

Two flavours, both for proof-only use (the propagator never sees them):

- **`ProofFlag`**: a single Boolean flag.
  ```cpp
  auto seen = optional_model->create_proof_flag("seen");
  ```
- **`ProofOnlyIntegerVariableID`**: an integer variable.
  ```cpp
  auto pos = optional_model->create_proof_only_integer_variable(
      0_i, Integer{n}, "pos", IntegerVariableProofRepresentation::Bits);
  ```
  Use `Bits` for arithmetic-heavy use, `DirectOnly` for one-flag-per-value.

Use these to define encodings that are cleaner in OPB than the
constraint's raw semantics — `Lex` uses `prefix_equal[i]` flags;
`ValuePrecede` uses `pos[v]` integers. The OPB should read like the
spec, not like the propagator's algorithm.

### Half-reified constraints

A PB constraint can be "active only if these flags hold" via
`HalfReifyOnConjunctionOf`:

```cpp
optional_model->add_constraint(
    "Foo", "if cond",
    WPBSum{} + 1_i * v1 <= 0_i,
    HalfReifyOnConjunctionOf{{cond, other_flag}});
```

This emits "the conjunction → the constraint" rather than asserting it
unconditionally. The natural way to express conditional encodings.

### Fully reified flags

When you introduce a *new* `ProofFlag` whose meaning is "this
inequality holds", encode it as a full equivalence — both
`flag → ineq` and `¬flag → ¬ineq` — not just one direction. Use:

```cpp
auto gt = optional_model->create_proof_flag_fully_reifying(
    "gt", "Foo", "var greater than",
    WPBSum{} + 1_i * v1 + -1_i * v2 >= 1_i);
```

This creates `gt` and emits both halves of `gt ⇔ (v1 > v2)`. The
equivalent two-step form is
`add_two_way_reified_constraint(name, rule, ineq, flag)` if you've
already created the flag elsewhere. Both compute the reverse direction
by integer-negating the supplied inequality.

**Why full reif and not half reif?** A half-reified flag is left
UP-free by VeriPB: under any complete assignment to the real
variables, the flag could still be either 0 or 1, so any later
constraint that *requires* the flag to be a particular value
(e.g. an at-least-one selector sum `Σ sel_i ≥ 1`) will fail
verification on `solx`. Full reif lets unit propagation determine
the flag from the underlying variables, mirroring what `Count` and
`SmartTable` do.

**When half reif is still right.** If the flag is acting as a
*selector* — i.e. the reverse half is a *different* inequality, not
the integer negation of the forward — keep two `add_constraint`
calls. The classic example is `≠`, encoded as
`flag → v1 > v2` plus `¬flag → v1 < v2`: the second half is *not*
`v1 ≤ v2`, it's the strictly stronger `v1 < v2`, and using the
two-way API here would silently allow `v1 = v2`. `ReifiedEquals`
and the main `Equal` flag in `SmartTable` use this pattern.

## Testing

The standard pattern lives in
`gcs/constraints/innards/constraints_test_utils.hh`. A test:

1. Constructs an "expected" set by enumerating all variable
   assignments and filtering with a pure C++ check of the constraint's
   semantics.
2. Posts the constraint on a `Problem`, runs the solver, and collects
   actual solutions.
3. Diffs expected vs actual via `check_results`.
4. Optionally runs VeriPB on the proof.

```cpp
auto run_test(bool proofs, /* args */) -> void
{
    set<tuple<...>> expected, actual;
    build_expected(expected, [/* check */](/* args */) { ... }, /* domains */);

    Problem p;
    // ... create variables, post constraint ...

    auto proof_name = proofs ? make_optional("foo_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, /* vars */);
    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs);
    }
    return EXIT_SUCCESS;
}
```

`solve_for_tests_checking_gac` additionally asserts at every search
node that every value remaining in any domain is supported by some
solution — a strong correctness check, useful for constraints that
claim to achieve GAC. Use plain `solve_for_tests` for constraints
that are only bounds-consistent.

GAC on each of two constraints separately is *not* GAC on their
conjunction. So if your constraint is implemented as a composition
or decomposition of other GAC propagators, the resulting consistency
level is typically weaker than GAC on the constraint as a whole —
e.g., `Inverse(x, x)` (= symmetric all-different) is not GAC, even
though both AllDifferent and Inverse-channeling individually are.
Write at least one test case that probes the intersection: if it
passes `solve_for_tests_checking_gac`, you haven't found the gap
yet; once it fails, switch that case to `solve_for_tests` with a
comment explaining what GAC algorithm would close the gap.

The for-each over `{false, true}` runs every test case twice: once
without proof verification (always), once with `--prove` if `veripb`
is on `PATH`. The CMake test target points at `run_test_only.bash`
which handles this.

### Splitting a slow test for parallelism

If a test takes a long time, it becomes a parallelism bottleneck —
ctest runs each `add_test` entry as one process, so a 100-second
test serialises 100 seconds even if the rest of the suite is fast.

To split: take an `argv` parameter, dispatch on it, and add multiple
`add_test` entries that pass different arguments. See
`linear_test.cc`, `comparison_test.cc`, and `element_test.cc` for
examples — typically the split is per-operator, per-reif-kind, or
per-data-shape:

```cpp
auto main(int argc, char * argv[]) -> int
{
    if (argc != 2)
        throw UnimplementedException{};

    string mode{argv[1]};

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & data_row : data) {
            if (mode == "eq") {
                run_test_for_eq(proofs, mode, data_row);
            }
            else if (mode == "ne") {
                run_test_for_ne(proofs, mode, data_row);
            }
            // ...
            else
                throw UnimplementedException{};
        }
    }
    return EXIT_SUCCESS;
}
```

CMakeLists side:
```cmake
add_test(NAME foo_constraint_eq COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:foo_test> eq)
add_test(NAME foo_constraint_ne COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:foo_test> ne)
```

**The proof-file-name gotcha.** When the test binary is invoked
multiple times in parallel (one per ctest entry), each invocation
must write to a distinct OPB/PBP filename. If they all write to the
same file, parallel runs clobber each other's proofs mid-VeriPB and
fail intermittently — but pass when run solo, which makes the
failure mode confusing.

Thread the `mode` string into the proof file name:

```cpp
auto proof_name = proofs ? make_optional("foo_test_" + mode) : nullopt;
```

This was the failure mode we hit twice when first splitting
`comparison_test` and `linear_test`. Always verify the split with
`ctest -j N` (not just running each entry solo) before committing.

## Adding a new constraint: checklist

1. Header file with class declaration, Doxygen comments, the standard
   trio of virtual methods.
2. `.cc` file with constructor, `install` method (OPB block + propagator
   registration), `clone`, `s_exprify`.
3. Test file with the standard `for (bool proofs : {false, true})`
   loop and a `can_run_veripb()` gate on the proofs leg. Split into
   multiple ctest entries via an argv mode if the test gets slow.
4. Add the `.cc` to the library and the test target to
   `gcs/CMakeLists.txt` (alphabetically), plus an `add_test` entry.
5. Add the header to `gcs/gcs.hh` (alphabetically).
6. Build and run under `--preset sanitize` and `--preset release`. Run
   the wider test suite to confirm no regressions.
7. If the constraint should be exposed to MiniZinc, follow
   [minizinc.md](minizinc.md) — separate commit.

## See also

- [state-and-variables.md](state-and-variables.md) — the variable-ID
  family, the `State` class, `IntervalSet` domain storage, epoch-based
  backtracking, and the `change_state_for_*` inference paths your
  propagator's `inference.infer(...)` calls into.
- [reification.md](reification.md) — the additional machinery for
  reified constraints (`If`/`NotIf`/`Iff` forms, the
  `install_reified_dispatcher` helper, the `evaluated_reif` runtime
  types).
- [minizinc.md](minizinc.md) — exposing finished constraints via
  FlatZinc.
