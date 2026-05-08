# State and variables

This document describes how variables and their state are represented inside
the solver. It covers the variable-ID family, the `State` class that owns
all per-variable storage, the underlying `IntervalSet` representation,
chronological backtracking via epochs, and the inference paths through
which propagators modify variable domains.

For the user-facing model API see `gcs/problem.hh` and the top-level
README. For how propagators are wired up, see [constraints.md](constraints.md).

## The design rule: variables are identifiers, state is separate

A user-facing "variable" is just a lightweight handle. All actual state
(the current domain, whether the variable has been instantiated, etc.)
lives inside a `State` object owned by the search. This is deliberately
unlike a typical OO constraint solver where each variable is an object
with its own member-stored domain.

The handle/state separation buys us four things:

- **Cheap copy and pass-by-value.** A variable handle is a small `struct`
  (one `unsigned long long` for the simplest case). It can travel through
  expressions, vectors, hash sets, lambdas, etc. with no lifetime worries.
- **No object-lifetime puzzles.** You never need to ask "who owns this
  variable, and what happens to it on backtrack?" because there's nothing
  to own — the handle is value-typed and the state is owned by `State`.
- **Multiple `State`s, one set of handles.** The search creates a `State`
  per node when needed; the handles carry no per-state context, so they
  remain valid across cloning.
- **Solution callbacks see one consistent surface.** `solve()` hands the
  user a `CurrentState`, which exposes only the read-only operations
  needed in a callback — avoiding the question "is this the same object
  I had at modelling time, and what can I do to it now?".

## The variable-ID family

`gcs/variable_id.hh` defines a small family of handle types related by
`std::variant`:

```
IntegerVariableID          = variant<SimpleIntegerVariableID,
                                     ViewOfIntegerVariableID,
                                     ConstantIntegerVariableID>
DirectIntegerVariableID    = variant<SimpleIntegerVariableID,
                                     ConstantIntegerVariableID>
```

The three concrete handles:

- **`SimpleIntegerVariableID`** — a genuine variable, indexed by an
  `unsigned long long` into `State`'s storage. Created by
  `Problem::create_integer_variable`.
- **`ViewOfIntegerVariableID`** — a non-owning offset view over a
  `SimpleIntegerVariableID`: a `negate_first` flag and a `then_add`
  offset. Created with `var + 5_i` or `-var`. Lets constraints write
  `state.bounds(x + 1_i)` without anybody needing to materialise a
  separate variable for `x + 1`.
- **`ConstantIntegerVariableID`** — a constant value masquerading as a
  variable. Holds an `Integer` directly; never indexes into `State`.
  Created with `42_c` or `gcs::constant_variable(42_i)`. Lets constraints
  uniformly accept "a variable" without needing constant-vs-variable
  overloads.

The two variant types:

- **`IntegerVariableID`** — the user-facing top of the family. A variant
  over the three above. Most public APIs accept this.
- **`DirectIntegerVariableID`** — used internally after a view has been
  resolved: a variant over `Simple` and `Constant` only. Constructed by
  `deview()` (see below).

Two concepts in `gcs/innards/variable_id_utils.hh` constrain templated APIs:
`IntegerVariableIDLike` (anything convertible to `IntegerVariableID`) and
`DirectIntegerVariableIDLike` (the same for `DirectIntegerVariableID`).

### `deview()`: from any handle to (actual variable, view offset)

Every operation that touches state starts by calling the file-local
`deview()` helper in `gcs/innards/state.cc`. It returns
`tuple<actual_var, negate_first, then_add>`:

| Input handle                | Returned `actual_var`                |
|-----------------------------|--------------------------------------|
| `SimpleIntegerVariableID`   | same `SimpleIntegerVariableID`       |
| `ViewOfIntegerVariableID`   | underlying `SimpleIntegerVariableID` |
| `ConstantIntegerVariableID` | same `ConstantIntegerVariableID`     |
| `IntegerVariableID`         | a `DirectIntegerVariableID` variant  |

The `negate_first` and `then_add` fields capture the view's offset (zero
for non-view inputs). After deview, callers either query/mutate the
actual variable in its own coordinate system and then transform the
result back via `(negate_first ? -v : v) + then_add`, or pass an
adjusted `value` argument computed the same way.

The `visit_actual()` helper in the same file is a set of three function-
template overloads. The `SimpleIntegerVariableID` and
`ConstantIntegerVariableID` overloads dispatch directly to the relevant
lambda; the `DirectIntegerVariableID` overload defers to `std::visit`.
Constants short-circuit the entire state lookup — nothing in `State::Imp`
is touched for a `ConstantIntegerVariableID` query.

## `State` storage

`gcs/innards/state.hh` declares the `State` class. The implementation in
`gcs/innards/state.cc` keeps all variable domains in a single member of
`State::Imp`:

```cpp
list<vector<IntervalSet<Integer>>> integer_variable_states;
```

The outer `list` is a stack of epochs (see below). The inner `vector` is
indexed by `SimpleIntegerVariableID::index`, and each element holds the
current domain of one variable.

`allocate_integer_variable_with_state(lower, upper)` appends a new
`IntervalSet<Integer>` with the single interval `[lower, upper]` to the
current top epoch's vector and returns its index as a
`SimpleIntegerVariableID`. There is no separate "I'm a constant" path
within `State` — `ConstantIntegerVariableID`s are handled entirely by
short-circuiting in the entry points and never reach storage.

### `IntervalSet` representation

`gcs/innards/interval_set.hh` defines `IntervalSet<Integer>` as a sorted
sequence of disjoint closed intervals. The set `{1, 2, 3, 4, 8, 9, 10}`
is stored as the two intervals `[1..4]` and `[8..10]`. This is the only
representation used for variable domains.

The underlying container is `gch::small_vector<pair<Int_, Int_>, 2>` —
inline storage for up to 2 intervals (the dominant case is a single
contiguous interval; one hole takes 2). Only fragmented domains spill to
the heap. The inline capacity is tuned for the workloads in
[benchmarking.md](benchmarking.md); see issue #134 for the rationale.

The class has the operations propagators care about: `lower()`, `upper()`,
`contains(value)`, `contains_any_of(other)`, `has_holes()`, `size()`,
`empty()`, plus mutators `erase(value)`, `erase_less_than(value)`,
`erase_greater_than(value)`, `clear()`, `insert_at_end(value)`. Iteration
is via `each()` (per-value) and `each_interval()` (per-interval pair).
For set-difference idioms (yield each maximal interval present in
`*this` and absent from another set), there's
`each_interval_minus(other)` — a merge walk that's strictly cheaper
than per-value membership testing. Yielded `(l, u)` pairs are *closed*
intervals, matching `each_interval()`'s convention. The corresponding
in-place set-intersection is `intersect_with(other)`, which retains
exactly the values present in both sets via the same merge walk.

`has_holes()` is allowed to over-approximate: a `false` return guarantees
no holes, but a `true` return doesn't guarantee any. The current
implementation happens to be exact (`intervals.size() > 1`), but code
must not rely on that.

## Epochs and backtracking

`State` supports chronological backtracking by snapshotting the entire
`integer_variable_states` vector on `new_epoch()` and restoring it on
`backtrack()`.

```cpp
auto State::new_epoch(...) -> Timestamp
{
    _imp->integer_variable_states.push_back(_imp->integer_variable_states.back());
    // ...
}

auto State::backtrack(Timestamp t) -> void
{
    _imp->integer_variable_states.resize(t.when);
    // ...
}
```

The push-back deep-copies every `IntervalSet` in the inner vector. With
the inline-2 small-vector this is cheap for the dominant cases (one or
two intervals copied by value, no heap touch) but becomes a real cost
for variables with many fragmented intervals.

`Timestamp` (returned by `new_epoch`, accepted by `backtrack`) records
the epoch index plus a count of guesses, so the guess list is also
restored on backtrack.

`on_backtrack(callback)` registers a callback to run when this epoch is
backtracked off; useful for constraints that need to undo non-domain
state. For longer-lived per-constraint state that should be restored
automatically on backtrack, use `add_constraint_state` — see the
"Backtrackable propagator state" section in
[constraints.md](constraints.md).

## Inference: `change_state_for_*` and the `NoChange` rule

Mutating a variable's domain goes through one of four entry points,
exposed via the public `infer_*` family:

- `infer_equal(var, value)` → variable must equal `value`
- `infer_not_equal(var, value)` → variable must not equal `value`
- `infer_less_than(var, value)` → variable must be `< value`
- `infer_greater_than_or_equal(var, value)` → variable must be `≥ value`

Each `infer_*` method:

1. Calls `deview()` to get the actual variable and view offset.
2. Adjusts the `value` argument into the actual variable's coordinate
   system (and swaps `<` and `≥` if `negate_first`).
3. Dispatches via `visit_actual` to either:
   - `change_state_for_*` for a `SimpleIntegerVariableID` (mutates the
     `IntervalSet`), or
   - `infer_*_on_constant` for a `ConstantIntegerVariableID` (read-only
     comparison).

Each call returns an `Inference`:

| Value                     | Meaning                                              |
|---------------------------|------------------------------------------------------|
| `NoChange`                | nothing was changed                                   |
| `BoundsChanged`           | the lower or upper bound moved                        |
| `InteriorValuesChanged`   | a hole was created without changing the bounds       |
| `Instantiated`            | the domain is now a single value (and changed to be) |
| `Contradiction`           | the requested change would empty the domain          |

### The `NoChange` invariant

`Inference::NoChange` is **load-bearing**. The propagation queue uses
the return value to decide whether to re-trigger watching constraints.
Returning anything stronger than `NoChange` when the domain didn't
actually move can cause infinite re-propagation.

The rule each `change_state_for_*` follows is:

1. Read the *before* state from the `IntervalSet` (`lower()`, `upper()`,
   `contains(value)`).
2. Decide `NoChange` or `Contradiction` from (1) **before** any mutation —
   return immediately if so.
3. If a mutation is going to happen, do it.
4. Decide between `Instantiated`, `BoundsChanged`, and
   `InteriorValuesChanged` from the post-mutation state combined with
   what was true before.

Concretely:

- **`infer_equal(value)`** → `NoChange` if the domain is already
  singleton equal to `value`; `Contradiction` if `value` is not in the
  domain; otherwise the domain becomes `{value}` and the result is
  `Instantiated`.
- **`infer_not_equal(value)`** → `NoChange` if `value` is already absent
  from the domain; `Contradiction` if the domain is the singleton
  `{value}`; otherwise the value is erased and the result is
  `Instantiated`/`BoundsChanged`/`InteriorValuesChanged`. The "already
  absent" test must be performed by an explicit `contains()` check
  before any mutation — checking `lower()/upper()` after-the-fact is not
  a substitute, since the value may legitimately fall in the interior.
- **`infer_less_than(value)`** → `NoChange` if `upper() < value`; else
  the domain is restricted, and we report `Contradiction` /
  `Instantiated` / `BoundsChanged` accordingly.
- **`infer_greater_than_or_equal(value)`** → mirror of less-than, on
  `lower()`.

Do not derive `NoChange` from "post-state has `lower() == upper()`".
That post-state is also true when the call instantiated the variable —
the right answer there is `Instantiated`, not `NoChange`. The
distinction is made by reading the before-state.

## `CurrentState`: the public read-only view

`gcs/current_state.hh` defines `CurrentState`, the read-only handle
that every entry in `SolveCallbacks` receives — `solution`, `trace`,
`branch`, and `after_proof_started`. It wraps a reference to a `State`
and exposes only the queries — `bounds`, `in_domain`,
`optional_single_value`, `each_value_*`, and the `operator()` that
returns the unique value (or throws) for an instantiated variable.
It cannot mutate the underlying `State`.

This is the type a typical user-supplied solution callback receives; in
the typical pattern you call `s(my_var)` to read out the value the
solver assigned.

## Public read-only queries

All of these accept any `IntegerVariableIDLike` and short-circuit on
constants:

- `lower_bound(var)`, `upper_bound(var)`, `bounds(var)`
- `in_domain(var, value)`, `domain_has_holes(var)`
- `optional_single_value(var)`, `has_single_value(var)`,
  `domain_size(var)`, `operator()(var)`
- `test_literal(literal)` — answers `DefinitelyTrue`, `DefinitelyFalse`,
  or `Undecided` for a `Literal` or `IntegerVariableCondition`. Useful
  in propagators that want to ask "do I already know the answer to this
  reified question?" without committing to enforce it.
- `each_value_immutable(var)`, `each_value_mutable(var)` — generators
  yielding each value in the domain. The two have a contract
  difference: `_immutable` requires the caller to leave the domain
  alone for the lifetime of the generator; `_mutable` permits mutation
  and guarantees the generator keeps yielding the pre-modification
  values. The current implementation snapshots in both cases (it copies
  the `IntervalSet` into the coroutine frame), so they are
  behaviourally interchangeable today — but `_immutable` callers must
  not rely on that, since it is allowed to be optimised in future to
  avoid the copy. `CurrentState` exposes a single `each_value` (forward)
  and `each_value_reversed` (descending) for callback-time consumers.
- `copy_of_values(var)` — full snapshot as an `IntervalSet<Integer>`.
- `domain_intersects_with(var, IntervalSet)` — does the variable's
  domain share any value with the given set? The common case
  (SimpleIntegerVariableID, no view offset) walks the stored interval
  set against the given set without copying either side. Cheaper than
  `set.contains_any_of(state.copy_of_values(var))`.
- `domains_intersect(var1, var2)` — same shape, but for two variables.
  The common case of two SimpleIntegerVariableIDs with no offsets walks
  both stored interval sets in merge order — no copy of either side.
  Useful in overlap-detection propagators (`Equals`, `Count`).

Each one applies the view offset (and bound-swap for `negate_first`)
after computing the answer in the actual variable's coordinate system.

## Things to be careful of

- **Don't conflate "is a constant" with "is instantiated".** A
  `SimpleIntegerVariableID` whose domain has been reduced to a single
  value is *instantiated*; it is **not** a `ConstantIntegerVariableID`.
  Test with `has_single_value` or `optional_single_value`, not with
  `holds_alternative<ConstantIntegerVariableID>` or `is_constant_variable`.

- **Don't return a stronger Inference than is true.** See the
  `NoChange` invariant above.

- **Don't keep references to `IntervalSet`s across calls that might
  mutate `State`.** `state_of(var)` returns a reference into the
  current epoch's vector; allocating a new variable can invalidate that
  reference (the inner `vector` may resize), and `new_epoch()` /
  `backtrack()` change the active epoch.

- **Pick `_immutable` vs `_mutable` by intent, not by what works.**
  Calling `each_value_immutable` with the intention of modifying the
  domain during iteration happens to work today (both variants
  snapshot) but is not guaranteed to work in future. Use `_mutable` if
  you intend to mutate, `_immutable` if you don't.
