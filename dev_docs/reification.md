# Reification in gcs constraints

This document explains how reified constraints work in the Glasgow Constraint
Solver. It covers the types involved, the helper functions used to implement
new reified constraints, the OPB encoding pattern for proof logging, and the
reasoning behind the design.

It is aimed at developers (human and AI) writing new reified constraints, or
modifying an existing one. Read [constraints.md](constraints.md) first for
the general structure of any constraint — this document only covers what
*additionally* applies when the constraint is reified. The runnable
examples are `gcs/constraints/comparison.cc`, `gcs/constraints/equals.cc`,
and `gcs/constraints/lex.cc`.

## What "reification" means

A *reified* constraint is one whose enforcement is conditional on the value of
a Boolean *reification literal*. For a constraint *C* and a literal *cond*:

| Form           | Semantics                       | Constructor                  |
|----------------|---------------------------------|------------------------------|
| `MustHold`     | *C* must hold (no condition)    | `Constraint(...)`            |
| `MustNotHold`  | *C* must not hold               | `NotConstraint(...)`         |
| `If(cond)`     | `cond → C`                      | `ConstraintIf(..., cond)`    |
| `NotIf(cond)`  | `cond → ¬C`                     | `NotConstraintIf(..., cond)` |
| `Iff(cond)`    | `cond ↔ C`                      | `ConstraintIff(..., cond)`   |

Note the asymmetry: there is no "reverse If" — the public-facing `Less` /
`Greater` / `Iff` etc. classes simulate it by swapping vars and/or negating
the cond literal at construction.

## Two halves of the type story

### Static: `gcs::ReificationCondition` (in `gcs/reification.hh`)

```cpp
namespace reif {
    struct MustHold     { };
    struct MustNotHold  { };
    struct If           { IntegerVariableCondition cond; };
    struct NotIf        { IntegerVariableCondition cond; };
    struct Iff          { IntegerVariableCondition cond; };
}
using ReificationCondition = std::variant<
    reif::MustHold, reif::MustNotHold, reif::If, reif::NotIf, reif::Iff>;
```

This is what the constraint *stores*. It captures user intent at construction
time and never changes for the lifetime of the constraint.

### Runtime: `gcs::innards::EvaluatedReificationCondition`

In `gcs/constraints/innards/reified_state.hh`:

```cpp
namespace evaluated_reif {
    struct MustHold     { Literal cond; };
    struct MustNotHold  { Literal cond; };
    struct Undecided    { IntegerVariableCondition cond; ... };
    struct Deactivated  { };
}
using EvaluatedReificationCondition = std::variant<
    evaluated_reif::MustHold, evaluated_reif::MustNotHold,
    evaluated_reif::Undecided, evaluated_reif::Deactivated>;
```

This is the *runtime* state of the reification given the current search state.
It is computed by:

```cpp
auto test_reification_condition(const State &, const ReificationCondition &)
    -> EvaluatedReificationCondition;
```

Mapping table (rows = static kind, columns = state of the cond literal):

|              | cond is TRUE | cond is FALSE | cond is undecided |
|--------------|:------------:|:-------------:|:-----------------:|
| `MustHold`   | `MustHold`   | (n/a)         | (n/a)             |
| `MustNotHold`| `MustNotHold`| (n/a)         | (n/a)             |
| `If`         | `MustHold`   | `Deactivated` | `Undecided`       |
| `NotIf`      | `MustNotHold`| `Deactivated` | `Undecided`       |
| `Iff`        | `MustHold`   | `MustNotHold` | `Undecided`       |

`Deactivated` means "the reification's branch has been killed off" —
e.g. an `If(cond)` whose cond is now `FALSE` does not enforce anything.
Constraints react to it by doing nothing (or returning
`PropagatorState::DisableUntilBacktrack`).

### The `Undecided` struct's contrapositive logic

When cond is undecided, the constraint may still be able to *infer* cond from
variable state. For example, with `Iff(cond)` and bounds that prove the
constraint must hold, we should infer `cond = TRUE`. The rules are:

| Static reif | constraint must hold ⇒ infer | constraint must not hold ⇒ infer |
|-------------|:----------------------------:|:--------------------------------:|
| `If`        | (nothing)                    | `¬cond`                          |
| `NotIf`     | `¬cond`                      | (nothing)                        |
| `Iff`       | `cond`                       | `¬cond`                          |

These rules are encoded by two methods on `evaluated_reif::Undecided`:

```cpp
auto cond_to_infer_if_constraint_must_hold()      const -> std::optional<Literal>;
auto cond_to_infer_if_constraint_must_not_hold()  const -> std::optional<Literal>;
```

Each returns the literal to infer, or `nullopt` if the static reif kind doesn't
license an inference for that verdict. Constraint code should use these methods
rather than poking at the underlying booleans (`set_cond_if_must_hold` etc.) —
the booleans exist as backing storage, but they're easy to misread.

## Implementing a reified constraint

There are two pieces: the OPB encoding (for proof logging) and the propagator.

### OPB encoding

Each reified constraint hand-rolls an `if (optional_model)` block that calls
`optional_model->add_constraint(...)`. The conventional pattern dispatches on
the static `ReificationCondition` and emits one or two PB constraints per
direction, half-reified on the cond literal as appropriate. Look at
`comparison.cc` and `equals.cc` for the simplest examples, and `lex.cc` for a
more complex one with auxiliary flags.

Key idea: each PB constraint can be *conditioned* on a conjunction of
literals/flags via the `HalfReifyOnConjunctionOf` parameter to
`add_constraint`. So `cond → C` becomes "add C, half-reified on cond".
For `Iff(cond)` you typically add both `cond → C` and `¬cond → ¬C` (the
latter often expressed as the negation of C in PB form, half-reified on
`¬cond`).

### Propagator

The recommended approach is to use the dispatcher helper:

```cpp
#include <gcs/constraints/innards/reified_dispatcher.hh>

auto install_reified_dispatcher(
    Propagators &, const State & initial_state,
    const ReificationCondition &,
    Triggers,
    auto enforce_constraint_must_hold,       // (state, inference, logger, cond_lit) -> PropagatorState
    auto enforce_constraint_must_not_hold,   // ditto
    auto infer_cond_when_undecided,          // (state, inference, logger, cond_var) -> ReificationVerdict
    const std::string & name) -> void;
```

You provide three callables, one for each non-trivial branch of
`EvaluatedReificationCondition`:

1. **`enforce_constraint_must_hold`** — the constraint is currently `TRUE`
   (or unconditional `MustHold`). Propagate the constraint, returning a
   `PropagatorState`. The `cond_lit` parameter is the literal to include in
   reasons (use it via `bounds_reason(state, vars, cond_lit)` or similar).

2. **`enforce_constraint_must_not_hold`** — the constraint is currently
   `FALSE` (or unconditional `MustNotHold`). Propagate the *negation* of
   the constraint. Same shape as above.

3. **`infer_cond_when_undecided`** — cond is still undecided. Inspect
   variable state and return a `ReificationVerdict` declaring what you've
   learned: `StillUndecided`, `MustHold`, or `MustNotHold`. The dispatcher
   will use the `Undecided` struct's `cond_to_infer_*` methods to decide
   whether (and which) cond literal to actually infer.

The `ReificationVerdict` variant lives in the same header:

```cpp
namespace reification_verdict {
    struct StillUndecided   { };
    struct MustHold         { Justification justification; ReasonFunction reason; };
    struct MustNotHold      { Justification justification; ReasonFunction reason; };
}
```

For `MustHold`/`MustNotHold`, you provide the justification and reason for
the cond inference. The dispatcher chooses the right cond literal (or skips
the inference if the reif kind doesn't license one) and feeds them into
`inference.infer(...)`. `PropagatorState` falls out of the visit:
`StillUndecided` → `Enable`, anything else → `DisableUntilBacktrack`.

### What the dispatcher does for you

- If the initial state is `Deactivated`, no propagator is installed at all.
- Otherwise one propagator is installed; on each call it re-evaluates
  `test_reification_condition` and routes to the appropriate callable.
- When the initial state is `Undecided`, the cond literal's variable is
  appended to `triggers.on_change` automatically, so the propagator wakes
  when cond changes.

### When *not* to use the dispatcher

The dispatcher takes one set of triggers shared across all verdicts. If the
constraint legitimately wants different triggers per verdict (e.g.,
linear_equality wants `on_bounds` for the equality propagation but
`on_change` for the not-equals propagation), you can either (a) pass the
*union* (the more permissive set) and accept some over-triggering, or (b)
fall back to a hand-rolled four-arm `overloaded{}.visit(test_reification_
condition(...))` like `linear_equality.cc` does. The hand-rolled form is
fine for outliers — it predates the dispatcher — but it duplicates the
MustHold/MustNotHold passes between the top-level dispatch and an inner
re-dispatch inside the Undecided arm.

## Worked example: `LessThan` (in `comparison.cc`)

A boiled-down outline of `ReifiedCompareLessThanOrMaybeEqual::install`:

```cpp
// 1. OPB encoding (one or two add_constraint calls per reif kind)
if (optional_model) {
    overloaded{
        [&](const reif::MustHold &) {
            optional_model->add_constraint(...) // unconditional v1 < v2
        },
        [&](const reif::If & cond) {
            optional_model->add_constraint(..., HalfReifyOnConjunctionOf{cond.cond});
        },
        [&](const reif::Iff & cond) {
            optional_model->add_constraint(...,  HalfReifyOnConjunctionOf{cond.cond});       // cond → v1<v2
            optional_model->add_constraint(..., HalfReifyOnConjunctionOf{! cond.cond});      // ¬cond → v1≥v2
        },
        // ... MustNotHold, NotIf
    }.visit(_reif_cond);
}

// 2. The three callables
auto enforce_must_hold = [...](state, inference, logger, cond) -> PropagatorState {
    // tighten v1 < v2.hi+1 (or v2.hi for or_equal), v2 ≥ v1.lo (or v1.lo+1), reasons include cond
};

auto enforce_must_not_hold = [...](state, inference, logger, cond) -> PropagatorState {
    // tighten the negation
};

auto infer_cond_when_undecided = [...](state, _, _, cond) -> ReificationVerdict {
    auto v1b = state.bounds(v1), v2b = state.bounds(v2);
    if (v1b.second < v2b.first)              return reification_verdict::MustHold{...};
    if (v1b.first  >= v2b.second)            return reification_verdict::MustNotHold{...};
    return reification_verdict::StillUndecided{};
};

// 3. Install
Triggers triggers{.on_bounds = {_v1, _v2}};
install_reified_dispatcher(propagators, state, _reif_cond, triggers,
    std::move(enforce_must_hold),
    std::move(enforce_must_not_hold),
    std::move(infer_cond_when_undecided),
    "reified compare");
```

## Where things live

```
gcs/reification.hh                              ReificationCondition + reif::*
gcs/constraints/innards/reified_state.hh        evaluated_reif::*, EvaluatedReificationCondition,
                                                test_reification_condition (free function),
                                                Undecided's cond_to_infer_* methods
gcs/constraints/innards/reified_state.cc        test_reification_condition definition
gcs/constraints/innards/reified_dispatcher.hh   ReificationVerdict, install_reified_dispatcher
gcs/innards/proofs/reification.hh               unrelated: HalfReifyOnConjunctionOf for the OPB side
                                                (despite the name, *not* about reified constraints)
```

The proofs/`reification.hh` filename collision is unfortunate — it's about
"reifying a PB constraint on a conjunction of flags", which is a different
notion of reification (on the proof side). The constraint-side reification
machinery lives entirely in `gcs/constraints/innards/`.

## Subtleties and gotchas

### Justifications can depend on the cond polarity

For most constraints, `JustifyUsingRUP{}` works regardless of which cond
literal the dispatcher decides to infer — the OPB encoding has the right
shape and PB unit propagation closes the gap. But if a constraint emits
*explicit* RUP scaffolding (e.g., `lex.cc`'s
`run_lex_undecided_detection`), the scaffolding's reason may need to
include `cond` or `¬cond` as a literal, depending on which direction is
being inferred. Lex currently only fully supports the Iff polarity for
its scaffolded inferences; the NotIf case is latent (and not exposed in
the public API).

### Capture-by-reference inside the install function

The three callables passed to `install_reified_dispatcher` are stored
inside the propagator's lambda (which lives until the constraint is torn
down). They must capture by *value* (not reference) anything from the
install function's local scope — the install function returns long
before the propagator first runs. Look for `[v1 = _v1, v2 = _v2, ...]`
init-capture style.

The justification lambdas inside a `JustifyExplicitlyThenRUP` are called
synchronously from within `inference.infer(...)`, which is called from
within the propagator's call. So they *can* capture the State and
ProofLogger by reference (via `[&state, logger, ...]`) — those references
live long enough.

### One callable per direction, not one per static reif kind

You don't need to handle `If` vs `NotIf` vs `Iff` differently in your
callables. The dispatcher (and the `cond_to_infer_*` methods) does that
for you. Your `enforce_constraint_must_hold` is the same code regardless
of whether we got there via an `Iff` whose cond is now true, an `If`
whose cond is now true, or an unconditional `MustHold`.

### The `ReificationVerdict` variant carries the inference materials,
### but doesn't carry `PropagatorState`

`StillUndecided` deterministically maps to `Enable`; `MustHold` and
`MustNotHold` deterministically map to `DisableUntilBacktrack`. The
dispatcher derives the `PropagatorState` from the verdict, so the
constraint can't get it wrong.

### `evaluated_reif::Deactivated` is reachable mid-search

If the initial state is `Undecided` and the cond literal later resolves
to a value that makes an `If(cond)` or `NotIf(cond)` vacuous, the
dispatcher will see `Deactivated` on a subsequent call and disable the
propagator. You don't normally need to think about this — the
dispatcher handles it.

### linear_equality and linear_inequality

`linear_inequality.cc` uses the dispatcher. `linear_equality.cc` does
not, because (a) its three verdicts want different triggers
(`on_bounds` vs `on_change`), (b) it has empty-sum corner cases that
fire one-shot inferences via `install_initialiser`, and (c) it has a
GAC mode that's a totally separate code path. The current plan is to
eventually allow propagators to change their triggers dynamically,
which would unblock linear_equality's adoption.

## Adding a new reified constraint: checklist

1. Public class hierarchy in your header — typically a base class storing
   `ReificationCondition` plus thin `Constraint` / `ConstraintIf` /
   `ConstraintIff` wrappers (mirror `comparison.hh`).
2. OPB encoding in `install` guarded by `if (optional_model)`. Decide
   per reif kind whether you need a constraint, its negation, or both;
   half-reify each on the appropriate cond polarity.
3. Define three callables.
4. Build a `Triggers` value with the variables your propagator depends on.
5. Call `install_reified_dispatcher`.
6. Tests should cover at minimum: unreified (MustHold), `If`-with-cond-true,
   `If`-with-cond-false, `Iff`-with-cond-true, `Iff`-with-cond-false, plus
   cases where the constraint state forces cond to be inferred.
