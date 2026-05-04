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
        [[nodiscard]] virtual auto s_exprify(const std::string & name,
            const innards::ProofModel * const) const -> std::string override;
    };
}
```

`install` is rvalue-qualified (`&&`) — it consumes the Constraint
object. `clone` produces a fresh independent copy (used by some search
strategies). `s_exprify` produces a textual dump of the constraint for
debugging.

## install: the entry point

```cpp
auto Foo::install(Propagators & propagators, State & initial_state,
    ProofModel * const optional_model) && -> void
{
    if (optional_model) {
        // Emit OPB definition.
    }

    // Register propagators.
    Triggers triggers;
    // ... fill in trigger sets ...

    propagators.install(
        [/* captures */](const State & state, auto & inference,
            ProofLogger * const logger) -> PropagatorState {
            // Propagation body.
            return PropagatorState::Enable;
        },
        triggers, "constraint name");
}
```

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
    triggers, "...");
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
    run_all_tests(false);
    if (can_run_veripb())
        run_all_tests(true);
    return EXIT_SUCCESS;
}
```

`solve_for_tests_checking_gac` additionally asserts at every search
node that every value remaining in any domain is supported by some
solution — a strong correctness check, useful for constraints that
claim to achieve GAC. Use plain `solve_for_tests` for constraints
that are only bounds-consistent.

The test runs twice: once without proof verification (always), once
with `--prove` if `veripb` is on `PATH`. The CMake test target points
at `run_test_only.bash` which handles this.

## Adding a new constraint: checklist

1. Header file with class declaration, Doxygen comments, the standard
   trio of virtual methods.
2. `.cc` file with constructor, `install` method (OPB block + propagator
   registration), `clone`, `s_exprify`.
3. Test file with `run_all_tests(false)` always, `run_all_tests(true)`
   gated on `can_run_veripb()`.
4. Add the `.cc` to the library and the test target to
   `gcs/CMakeLists.txt` (alphabetically), plus an `add_test` entry.
5. Add the header to `gcs/gcs.hh` (alphabetically).
6. Build and run under `--preset sanitize` and `--preset release`. Run
   the wider test suite to confirm no regressions.
7. If the constraint should be exposed to MiniZinc, follow
   [minizinc.md](minizinc.md) — separate commit.

## See also

- [reification.md](reification.md) — the additional machinery for
  reified constraints (`If`/`NotIf`/`Iff` forms, the
  `install_reified_dispatcher` helper, the `evaluated_reif` runtime
  types).
- [minizinc.md](minizinc.md) — exposing finished constraints via
  FlatZinc.
- The "Constraints" section of the top-level `README.md` for the
  high-level rationale behind the design.
