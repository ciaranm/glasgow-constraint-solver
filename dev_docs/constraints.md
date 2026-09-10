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
[minizinc.md](minizinc.md). Presolvers are a different kind of object,
but they share this document's file layout — see
[Presolvers](#presolvers) below.

## The big picture

A `Constraint` is a user-facing object posted on a `Problem`. When the
solver starts, each constraint is installed once, in three phases:

1. `prepare` validates the arguments, reads the initial domains, and allocates
   whatever the other two phases need — auxiliary variables, backtrackable
   constraint state, child constraints.
2. `define_proof_model` describes the constraint in PB terms by calling
   `model.add_constraint(...)` zero or more times. It runs only when proofs are
   being logged, and is what VeriPB sees.
3. `install_propagators` registers one or more propagators with the
   `Propagators` object. A propagator is a callable that gets invoked at search
   time to enforce the constraint by tightening variable domains.

After installing, the constraint object itself is gone — only the
propagators (with their captured state) and the OPB definition remain.

Those three phases are what a constraint *is*. The order in which to build them
for a constraint that does not exist yet is a separate question, and an
important one: see Bringing up a new constraint, below, before starting.

## File layout

Every constraint lives in its own directory. For a constraint named
`Foo`:

```
gcs/constraints/foo.hh             public umbrella header
gcs/constraints/foo/foo.hh         public class declaration
gcs/constraints/foo/foo.cc         install phases + propagator
gcs/constraints/foo/foo_test.cc    enumeration tests
```

The top-level `gcs/constraints/foo.hh` is a thin umbrella that just
`#include`s `gcs/constraints/foo/foo.hh`. Consumers (`gcs.hh`,
`fzn-glasgow`, examples) always include the umbrella
`<gcs/constraints/foo.hh>`, so the public include path stays stable no
matter how the directory's internals are arranged. The class header's
include guard is directory-qualified (`..._CONSTRAINTS_FOO_FOO_HH`)
while the umbrella keeps the bare `..._CONSTRAINTS_FOO_HH`.

Then two places to wire it up:

- `gcs/CMakeLists.txt` — add `constraints/foo/foo.cc` to the library
  sources, and `foo_test` (built from `constraints/foo/foo_test.cc`) to
  the test target list.
- `gcs/gcs.hh` — add `#include <gcs/constraints/foo.hh>` (the
  umbrella). **This is easy to forget**; downstream consumers
  (`fzn-glasgow`, examples) get the class via this header.

### Constraints with several files

Some constraints come in groups — multiple algorithms
(`gac_all_different`, `vc_all_different`), variants
(`AllDifferentExcept`, `AllDifferentExceptZero`), or shared
encoding/justify helpers (`encoding.cc`, `justify.cc`). These all live
in the same directory, alongside the main class header:

```
gcs/constraints/all_different.hh                       public umbrella header
gcs/constraints/all_different/gac_all_different.hh     one variant's interface
gcs/constraints/all_different/all_different_except.hh  another variant
gcs/constraints/all_different/encoding.{hh,cc}         shared OPB helper
gcs/constraints/all_different/justify.{hh,cc}          shared proof helper
gcs/constraints/all_different/*_test.cc                tests
```

Here the umbrella `gcs/constraints/<family>.hh` `#include`s every
variant's header. `gcs/gcs.hh` then only needs the umbrella, not each
variant.

### Presolvers

Presolvers (`gcs/presolver.hh`, the `Presolvers` Doxygen group) are laid
out exactly the same way, one directory each, under `gcs/presolvers/`
instead of `gcs/constraints/`. For a presolver named `Foo`:

```
gcs/presolvers/foo.hh             public umbrella header
gcs/presolvers/foo/foo.hh         public class declaration
gcs/presolvers/foo/foo.cc         run() method
gcs/presolvers/foo/foo_test.cc    tests
```

The same rules apply, for the same reasons (issue #589):

- The umbrella keeps the bare guard `..._PRESOLVERS_FOO_HH` and does
  nothing but `#include <gcs/presolvers/foo/foo.hh>`; the class header's
  guard is directory-qualified, `..._PRESOLVERS_FOO_FOO_HH`.
- Consumers — examples, the frontends, other presolvers' tests — always
  include the umbrella `<gcs/presolvers/foo.hh>`, so the public include
  path stays put no matter how the directory's internals are arranged.
  The implementation `.cc` includes the class header directly; the
  `*_test.cc` includes the umbrella, matching what constraint tests do.
- `gcs/CMakeLists.txt` gets `presolvers/foo/foo.cc` in the library
  sources and a test target built from `presolvers/foo/foo_test.cc`.

Unlike a constraint, a presolver is **not** added to `gcs/gcs.hh`:
presolvers are opt-in, and a user asks for one by name.

A presolver whose implementation grows past one file — an enumeration
pass, a lifting pass, a proof helper — puts the extra files in its own
directory and, if they are part of its interface, `#include`s them from
the umbrella, exactly as the multi-file constraint families do above.
The Cumulative presolver family (issues #547, #548, #549) is the next
consumer of this layout.

Constraints that offer more than one consistency level or propagation
algorithm select it with a fluent `.with_*()` setter and the
`gcs/consistency.hh` tag types, not a constructor argument or a separate
public class (issue #299): the constructor takes only variables and data,
and the setter takes a `std::variant` over exactly the levels the
constraint supports, so requesting an unsupported one is a compile-time
error, as in
`problem.post(Multiply{x, y, z}.with_consistency(consistency::Tabulated{}))`.
`consistency::GAC` names a genuine algorithm that achieves the level; a
constraint that can only get there by enumerating a table takes
`consistency::Tabulated`, so the very different cost model is visible in
the signature. The arithmetic family (`Multiply`, `Divide`, `Modulus`,
`Power`, `Plus`, `Minus`) also accepts `consistency::Auto`, which
tabulates the relation for GAC when the domains involved are small (see
`gcs/constraints/innards/tabulation.hh`); the tag never changes the OPB
encoding, since the table is derived in-proof. Families that used to
expose several public classes behind a `using` alias — `AllDifferent`,
`GlobalCardinality`, `Circuit` — are now a single class each, the choice
moved onto the setter (`.with_consistency()`, or `.with_algorithm()` for
`Circuit`'s `circuit::SCC`/`circuit::Prevent`).

A compound constraint should emit one flat `@c[id][role]` OPB block and
install one propagator, reusing the exposed machinery (`mult_bc::
define_encoding` / `mult_bc::propagate`, the `linear_stages` helpers,
`propagate_linear`, `install_tabulation`) rather than installing child
constraint objects — see the arithmetic family for the pattern, and
issue #448 for why. Two contracts to know: `propagate_linear` signals
failure through the tracker's non-throwing path, so check
`inference.contradicted()` after each linear stage; and a constraint
that does install a child directly (`SeqPrecedeChain`'s `ValuePrecede`)
must give it an identity, or id-keyed proof flags collide across
instances (issue #449).

The `role` half of `@c[id][role]` must name **everything the surrounding
loops vary over**, not just the innermost thing. A role built from a
position index inside a loop over values gives every value after the
first the same labels as the first — several genuinely different rows
under one name, none of them citable unambiguously (issue #604, where
`ValuePrecede` spelled its upper-bound role `<i>ub` rather than
`<i>ub_<v>`). This is a hard error, not a first-wins pick:
`ProofModel::claim_labels` throws on a repeated label, so a role that is
missing a key fails loudly at model-definition time rather than becoming
an `.opb` with repeated names that nothing dereferences. It also means
you cannot work around a collision by ordering the emissions; fix the
role. The `role_le`/`role_ge` pair of the equality overload is covered
too, and claimed together, so passing the same role for both halves is
caught as well.

The check is confined to the `c[id][role]` namespace — it runs in the
`ConstraintID`-taking `add_labelled_constraint` overloads, which is what
every constraint uses. The variable-encoding namespaces (`@i[name][...]`
for a real variable, `@po[index][...]` for a proof-only one) are out of
scope deliberately: those rows may be deleted and re-emitted to keep the
proof database small, so a repeat there is by design.

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

        // The three install phases, in the order they run.
        virtual auto prepare(innards::Propagators &, innards::State &,
            innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &,
            const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Foo(/* arguments */);

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(
            const innards::ProofModel * const) const -> innards::SExpr override;
    };
}
```

`clone` produces a fresh independent copy (used by some search
strategies). `s_expr` returns the constraint's `.scp` entry as a structured
s-expression term `(name op args...)` (built with `innards::SExpr::list`/`atom`
and `NamesAndIDsTracker::s_expr_term_of`); `innards::write_scp` serialises it.

Whatever keyword `constraint_type` returns, **`gcs::read_scp` must have a case
for it**: the writer and the reader are meant to be inverses, and the
workflow-2 chain harness re-solves the `.scp` as its first step, so a keyword
the reader does not know fails the chain before `cake_pb_cp` is reached. Your
constraint's own test enforces this — `verify_proof_and_dispose` reads the
`.scp` back and fails on an unknown keyword. See
`dev_docs/workflow2_testing.md`. The keyword names the *constraint*, not the
propagator: an alternative propagator for an existing constraint writes the
existing keyword (all three `Regular` variants write `regular`).

## The three install phases

`Constraint::install` is not virtual and is not yours to write. It is
rvalue-qualified (`&&`) — it consumes the Constraint object — and all it does is
run the three phases:

```cpp
auto Constraint::install(Propagators & propagators, State & initial_state,
    ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model, initial_state);

    install_propagators(propagators);
}
```

A constraint overrides the phases it needs; each has a do-nothing default, so a
constraint with no OPB definition simply does not override
`define_proof_model`.

```cpp
auto Foo::prepare(Propagators &, State & initial_state,
    ProofModel * const) -> bool
{
    // Validate the arguments; read the initial domains; allocate auxiliary
    // variables and backtrackable constraint state; install child constraints.
    // This is the only phase holding all three of the propagators, the mutable
    // State and the model at once, so it is the only one that can allocate or
    // install a child. Return false to say the other two must not run --
    // whether because the constraint is trivially satisfied, because a
    // contradiction initialiser has been installed, or because the whole
    // constraint has been delegated to a child.
    return /* not trivially satisfied */;
}

auto Foo::define_proof_model(ProofModel & model,
    const State & initial_state) -> void
{
    // The OPB definition, and nothing else. The State is the *declared*
    // domains -- nothing at install time narrows one -- so an encoding whose
    // shape depends on them (bit widths, a row per value, a flag per tuple)
    // can read them here rather than having prepare() snapshot them first. It
    // is const because this phase must only describe the constraint, never
    // allocate.
}

auto Foo::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    // ... fill in trigger sets ...
    propagators.install(constraint_id(),
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
`all_equal/all_equal.cc`, `count/count.cc`, and
`cumulative/cumulative.cc` are good references.

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

In between the two sits `PropagatorState::EnableButIdempotent`: the
propagator stays registered, but this run reached its own fixpoint —
re-running it immediately, against the domains exactly as this run
left them, would infer nothing and not contradict — so the propagation
queue skips re-waking it from its own inferences (changes made by
other propagators wake it as usual). The claim is per-run, and only
correct for algorithms that process all their internal cascades in one
call *and* whose scope has no two positions aliasing the same
underlying variable; `Propagators::install` detects aliased trigger
scopes (including through views) and silently ignores claims from such
propagators, which relies on claiming propagators registering triggers
1:1 with their scope positions. A wrong claim silently under-propagates
or is unsound, so every adoption needs an audit note, and the test
harness sets `GCS_CHECK_IDEMPOTENT_CLAIMS` to re-run every honoured
claim and abort if it infers anything. When in doubt, return `Enable`:
the only cost is a possible wasted no-op run.

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

These wake the propagator on any change to a whole *variable*. A propagator that
instead cares about specific *literals* (`x = v`, `x >= k`, ...) on many variables
and is otherwise dormant can arm **refined per-literal watches** via
`Triggers::refined` and the `RefinedWatchContext` — see [Refined
triggers](refined-triggers.md). Most constraints want the coarse triggers above;
reach for a watch when the propagator's whole verdict turns on a literal and
`on_change` would therefore wake it for every *other* value too. `ReifiedEquals`
against a constant `c` is the small case — instantiation plus `x != c` is the
whole of what it reads, where `on_change` woke it once per value in `x`'s domain
(issue #889) — and the learned-nogood store is the large one.

A refined-watch literal puts its variable in the propagator's **scope** (so
degree and adjacency are unchanged) without arming a coarse trigger; use
`Triggers::scope_only` to declare scope for a variable that neither mechanism
mentions.

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
- `state.for_each_value_immutable(v, cb)` / `state.for_each_value_mutable(v, cb)`
  → call `cb(value)` for each value in the current domain, ascending. Use
  `_immutable` if you only read; `_mutable` if you might infer a removal
  mid-iteration. A `cb` returning `bool` stops iteration by returning `false`;
  one returning `void` runs to completion. **Prefer these anywhere that runs
  per wake** — see the note below.
- `state.each_value_immutable(v)` / `state.each_value_mutable(v)` →
  the same two contracts as ranges, for a `for (auto val : ...)` loop. They
  allocate a `std::generator` frame per loop and route each value through a
  `std::function`, which is real per-call cost in a propagator body: converting
  the three loops in `propagate_extensional` to the callback forms above was
  worth 1.4x end-to-end on every shape measured (PR #786), with nothing else
  changed. Reach for the range form when a propagator runs once, or when the
  loop genuinely reads better that way.
- `state.domains_intersect(v1, v2)` → bool. Does the variables' domains
  share any value? Walks both stored interval sets in merge order
  without copying for the common case. Use this instead of
  `for (auto val : state.each_value_immutable(v1)) if (state.in_domain(v2, val))`.

These are read-only — modifying the state goes through `inference`.

Every one of the value-iterating forms above costs time proportional to how
*wide* the domain is, and a declared domain of `0..1000000000` is an ordinary
input rather than a mistake — so a loop over one is a hang, not a slow path. Read
[large-domains.md](large-domains.md) before writing one: it says when the loop is
really an interval operation written out longhand (in which case
`IntervalSet::each_interval_minus()` and `InferenceTracker::infer_not_in_range()`
give you the same pruning in time proportional to the number of *intervals*), and
how to check your constraint with the `GCS_LARGE_DOMAIN_GUARD` build.

## Making inferences

The `inference` parameter is templated; treat it as exposing:

```cpp
inference.infer(logger, lit, justification, reason);
inference.infer_all(logger, {lit1, lit2, ...}, justification, reason);
inference.contradiction(logger, justification, reason);
```

`lit` is an `IntegerVariableCondition` (e.g. `v != 3_i`, `v < 7_i`,
`v == 5_i`, `v <= 7_i`, `v > 3_i`). The `<=` and `>` overloads desugar to
`v < val + 1_i` and `v >= val + 1_i` respectively — internally only `Less`
and `GreaterEqual` exist. If the inference makes the domain empty, the
framework raises a contradiction automatically — you don't need to check
first.

### Reasons

Every inference carries a `Reason`: a *declarative* description of the
literals that justify it, materialised on demand — only when proofs are
on — by `materialise(reason, state) -> ReasonLiterals`. The `Reason`
variant covers an explicit literal set (`ExplicitReason`), a set of
variables by full domain or by bounds (`GenericReasonOver` /
`BothBoundsReasonOver`), a single instantiated value (`ExactSingleValue`),
and lazily-computed forms (`LazyReasonOver`, `Narrowable*`). The two
builders you usually want:

```cpp
auto reason = generic_reason(vars);  // each variable's full domain (bounds + holes)
auto reason = bounds_reason(vars);   // each variable's lower/upper bounds only
```

Both take an optional trailing extra literal; `singleton_reason(lit)`
builds a one-literal reason. The reason is what goes into the proof's RUP
step. Be honest about it: list every variable whose state contributed to
the inference.

## Justifications

The `justification` parameter tells the proof logger how to back the
inference. The kinds:

| Justification                           | When to use                                                  |
|-----------------------------------------|--------------------------------------------------------------|
| `NoJustificationNeeded{}`               | Trivial axioms (almost never — usually a code smell)         |
| `JustifyUsingRUP{}`                     | Inference is RUP-derivable from the OPB + reason             |
| `JustifyExplicitly{emit, ThenRUP::Yes}` | Emit explicit proof lines via `emit`, then close with a RUP  |
| `JustifyExplicitly{emit, ThenRUP::No}`  | Emit explicit proof lines via `emit`; the steps conclude it  |

The vast majority of inferences want `JustifyUsingRUP{}`. Use
`JustifyExplicitly{emit, ThenRUP::Yes}` when VeriPB can't unit-propagate
to the inference on its own — typically for chains involving auxiliary
flags or longer inference paths. The `ThenRUP` argument is mandatory:
`Yes` RUPs the inferred literal after the explicit steps, `No` lets the
steps conclude it themselves.

The `emit` callback receives a `const ReasonLiterals &` and can emit
proof lines via `logger->emit_rup_proof_line_under_reason`,
`logger->emit(RUPProofRule{}, ..., ProofLevel::Temporary)`, and similar.
See `among/among.cc` and `lex/lex.cc` for examples of varying complexity.

**A `JustifyExplicitly` handed to `infer_all` justifies the whole batch,
once.** The `emit` is never told which literal it is justifying, so it runs
exactly once per `infer_all` call, before any of the literals are applied,
with the reason materialised once at that point. What each literal needs
after the steps is what `ThenRUP` says: with `ThenRUP::Yes` the steps are
shared scaffolding and every literal is RUPped under it; with
`ThenRUP::No` the steps must themselves derive **every** literal in the
batch, at `ProofLevel::Current` so the conclusions outlive the emit's
temporary scaffolding — nothing further is logged per literal. Never write
an `emit` that assumes it will be called once per firing literal, and never
pass a literal the steps do not conclude.

**Assertion hints (optional).** Both `JustifyUsingRUP` and
`JustifyExplicitly` take an optional trailing *typed assertion hint*, e.g.
`JustifyUsingRUP{hints::Foo{owner}}` or `JustifyExplicitly{emit,
ThenRUP::Yes, hints::Foo{owner}}`. The hint structs live per-constraint in
`gcs/constraints/<foo>/hints.hh` (namespace `gcs::innards::hints`) and only
annotate the step in *assertion mode* — an alternative proof mode, selected
by `AssertionLevel`, in which inferences are asserted under their reason for
an external justifier rather than fully justified. In normal proofs-off mode
the hint is inert and the output is byte-identical. See `abs/hints.hh` for
the minimal shape.

**Development scaffolding only --- never merge it:**
`AssertRatherThanJustifying` is a "trust me" step that bypasses the
justification entirely, emitting VeriPB's `a` rule, which adds the
constraint to the proof *without checking it*. An inference justified this
way is not verified, and a proof containing one verifies nothing about it.

It has two legitimate uses, both temporary. As a bisection aid, it isolates
whether a VeriPB failure is in the OPB encoding (still fails with `Assert*`)
or in the justification (passes with `Assert*`, fails with the real one). And
as stage 3 of Bringing up a new constraint, below, it lets a new propagator's
algorithm be developed and tested before any of its proofs exist.

Both are borrowed time. **Never commit code that uses it**, and be aware that
nothing will catch you if you do: `veripb` exits successfully on an asserted
proof, so the test suite stays green. The only signal is the `s UNDER
ASSERTIONS` line and the accompanying warning, which you have to go and read.

### When RUP isn't enough: explicit `pol`

VeriPB's RUP unit-propagation can't combine the *coefficients* of a
linear OPB constraint with the *values* of unit literals on the same
variables — what feels like a one-step linear deduction is actually
two reasoning steps for VeriPB. When the proof needs to compute "the
load already pinned to 1 exceeds the bound", emit the arithmetic
explicitly as a `pol` (polish-notation reverse-polish-style
combination of existing constraint IDs). Use `PolBuilder` rather than
hand-rolling the string:

```cpp
PolBuilder pol;
pol.add(C_t_line);
for (auto & [line, weight] : scaled_units)
    pol.add(line, weight);
pol.emit(*logger, ProofLevel::Temporary);
```

`PolBuilder::add(line)` pushes a line (and inserts the `+` separator
to combine with the running stack top after the first push);
`add(line, coeff)` pushes a weighted line; `saturate()`,
`multiply_by(n)`, and `divide_by(n)` are the stack-top modifiers; and
`add_for_literal(tracker, lit [, coeff])` dispatches over the
`variant<ProofLine, XLiteral>` that
`NamesAndIDsTracker::need_pol_item_defining_literal` returns. See
`gcs/innards/proofs/pol_builder.hh` for the full API.

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
inspection. Only frames in the solver's own source are shown, and
resolving them relies on the debug info the build keeps even in release
(`-g1` on GCC/Clang, `/Z7` on MSVC); `stacktrace_logging_test` guards
against a build dropping it. Not available where the standard library
lacks `<stacktrace>` (e.g. macOS libc++), where it silently does nothing.

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
  For verified-encoding (`cake_pb_cp` chain) work, an optional `CakeBitNaming`
  argument names the bits in cake's value-flag scheme (`v[id][…][annot]`) as a
  free bit-sum with no OPB bound lines, so the proof-only integer lines up with
  cake's own encoding — see `value_precede`, `sort`, and `arg_sort`.

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
    "gt", WPBSum{} + 1_i * v1 + -1_i * v2 >= 1_i);
```

This creates `gt` and emits both halves of `gt ⇔ (v1 > v2)`. The
equivalent two-step form is
`add_two_way_reified_constraint(ineq, flag)` if you've
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

### Runtime caps for pathological random instances

Splitting helps when *one constraint* is uniformly slow, but the
data-driven tests have a second, nastier failure mode: the random data
and random search order occasionally conspire to produce a single
instance with a huge number of solutions or a huge search tree. Since
every inference is proof-logged and checked by VeriPB, the proof for
that instance balloons and VeriPB dominates the whole parallel suite —
and because the data is unseeded, it happens only "every now and again".

Two optional per-solve caps in the harness bound this, read from the
environment so they apply suite-wide without editing each test:

- `GCS_TEST_MAX_SOLUTIONS=N` — stop a solve after collecting `N` solutions;
- `GCS_TEST_MAX_RECURSIONS=N` — stop a solve after visiting `N` internal
  search nodes.

When a cap fires, the solve stops early. The solver emits a partial but
still VeriPB-checkable proof (`conclusion SAT` if a solution was seen,
else `NONE` — the same mechanism `check_initialisation_only_for_tests`
uses), and `check_results` automatically weakens its check: instead of
`expected == actual` it verifies only that every solution the solver
*did* produce is genuinely satisfying (`actual ⊆ expected`), then runs
VeriPB on the partial proof. With neither variable set the behaviour is
exactly the historical full-enumeration check.

CMake bakes generous defaults into every registered test's environment
(`GCS_TEST_CAP_DEFAULTS=ON`, with `GCS_TEST_MAX_SOLUTIONS`/
`GCS_TEST_MAX_RECURSIONS` cache variables), chosen so the worst case
stays well under a minute of parallel wall time. The Ubuntu release CI
lane configures with `-DGCS_TEST_CAP_DEFAULTS=OFF` so it keeps doing full
completeness checking.

**When working on a propagator, build and test with the caps off.** A
capped run only checks *soundness* (no spurious solutions) and the
partial proof — it can no longer catch a propagator that *misses*
solutions or *over-prunes*, which is exactly the class of bug you are
most likely to introduce. Configure with:

```shell
cmake -S . -B build -DGCS_TEST_CAP_DEFAULTS=OFF
```

or, without reconfiguring, clear the variables for a single run:

```shell
GCS_TEST_MAX_SOLUTIONS= GCS_TEST_MAX_RECURSIONS= ./build/foo_test
```

The capped defaults are for keeping the *routine* parallel suite fast;
correctness work wants the full enumeration check.

### What happens to the proof files

`verify_proof_and_clean_up` runs VeriPB and then, **by default, deletes**
the `.opb`, `.pbp`, `.scp` and `.varmap` it just checked. This is not
merely tidiness: a `.pbp` for an enumeration test can reach hundreds of
megabytes, and a full parallel `ctest` that kept them all would hold
gigabytes at once — enough to exhaust the disk mid-run and make an
*unrelated* lane's proof write fail. Deleting each proof as it verifies
bounds the footprint to the lanes running concurrently.

Files are **always kept when verification fails**, whatever the policy.
Since a failed verification throws, and no test catches
`UnexpectedException`, the run stops at the first bad proof — so the
files left under the bare proof name are exactly the failing instance's,
identified by the test's own log line just above them. That is why the
default needs no counter.

`GCS_PRESERVE_PROOF_FILES` overrides the policy:

| Value | Behaviour |
|-------|-----------|
| unset, empty, `0` | delete once verified (the default) |
| any other value, e.g. `1` | keep, letting the next instance overwrite in place |
| `all` | keep every instance, renamed with a zero-padded per-basename counter |

Use `1` to inspect the proof a test just produced. Use `all` only when
harvesting proofs across instances — comparing proof bytes before and
after a change, say. A single test can write hundreds of proofs under one
basename (`equals_test` writes 284), so `all` combined with
`-DGCS_TEST_CAP_DEFAULTS=OFF` can fill a disk.

```shell
GCS_PRESERVE_PROOF_FILES=1 ./build/equals_test     # keep the last of each
GCS_PRESERVE_PROOF_FILES=all ./build/equals_test   # equals_test.0001.pbp, ...
```

The same variable is honoured by the shell test wrappers
(`run_test_and_verify.bash`, `run_test_and_expect_verify_failure.bash`,
`run_xcsp_test.bash`, `run_minizinc_test.bash`, `run_fzn_json_test.bash` and
`run_scp_chain.bash`), so a proof is disposed of the same way whether it is
checked inside the test binary or by the wrapper around it. Those wrappers run
their binary once, so there is nothing for the counter to disambiguate: they
treat `all` the same as `1`.

All six get it from one `dispose_proof` in `proof_file_disposal.bash` at the
repo root, which they source relative to their own `$0`. Changing what the
wrappers delete — adding a sixth proof artifact, say — means changing that one
file, and its extension list should stay in step with `proof_file_extensions`
in `constraints_test_utils.hh`.

### Mutation testing: showing a derivation is tight

A proof that verifies is necessary, not sufficient. If a propagator's
derivation has slack in it — a bound derived more weakly than claimed, a step
that happens not to matter — then a *wrong* proof verifies too, and every
"veripb accepted it" in the suite is saying less than it looks.

The check is to break the derivation on purpose and insist that veripb
notices. Give the constraint a test-only knob that corrupts one emitted step
(precedent: `CumulativeProofMutation` and `Knapsack::with_proof_strategy`),
have the test binary write that proof and stop, and register it with
`run_test_and_expect_verify_failure.bash`, which is
`run_test_and_verify.bash` with the verdict inverted: it passes only when
veripb rejects.

Two things make the difference between a mutation lane that tests something
and one that does not. Mutate on an instance whose margin is *one* — corrupt a
proof of a conflict that had three units of slack and the contradiction
survives the corruption, so veripb accepts and the lane is green for the wrong
reason. And check that the run being mutated really produced the inference at
all, or the harness is checking an empty proof. If a mutation verifies anyway,
that is a finding about the honest derivation.

Registering a **control** alongside the lanes is what makes them mean
something: the same instances, uncorrupted, and veripb must accept. A lane whose
instance does not verify honestly either is green for no reason at all. The
equals family's `--mutate=control` is the pattern (`equals_mutation_control`).

Mutating a **reason** rather than an emitted step has a trap of its own, and it
is not obvious. Dropping a literal from a reason is only a corruption when that
literal traces back to a *search decision*. Anything a propagator derived is
written into the proof as a clause in its own right, so the checker has it
whether or not the reason repeats it — which means a rule that fires during root
propagation has a reason that merely restates the database, and dropping from it
changes nothing veripb can see. Such a lane goes green on an empty corruption.
Arrange for the fact to arrive under a decision (a reified constraint whose
condition the search sets, say, with a fixed branching order so it is set first),
or mutate an emitted lemma instead. `equals_mutations.hh` records two instances
that accept the mutation for this reason before the third one bites.

## Bringing up a new constraint

The checklist below says what files a new constraint touches. This section says
what order to do the work in, which matters more: it is the difference between
one hard problem and three easy ones.

A finished proof-logged constraint has three things that can be wrong — the OPB
encoding, the propagation algorithm, and the justification of each inference —
and a VeriPB failure looks much the same whichever it is. So bring them up one
at a time, in that order, with a gate after each that can only be failed by the
piece you just added.

One warning up front, because it is the part of this method that can do real
damage if it is half-remembered. Stage 3 has you cheat — deliberately, with
`AssertRatherThanJustifying`, which puts unchecked claims into the proof — and
stages 4 and 5 exist to take every one of those cheats back out again. **Not a
single one of them may ever be merged**, and nothing in the test suite or CI
will stop you, so the discipline has to come from you. If you are going to
follow only part of this section, follow that part.

### Stage 1: the encoding, with a check-only propagator

Write `define_proof_model` and a propagator that does no pruning at all: it
waits until the variables its semantics need are assigned, checks the
requirement, and contradicts if it is violated. Every inference such a
propagator makes is `JustifyUsingRUP{}` — no `pol`, no explicit steps, because
a fully assigned scope is exactly the case unit propagation can close on its
own.

Then run the data-driven tests with proofs on.

**The gate: the whole suite verifies.** That is a much stronger statement than
it looks. It says the encoding is *definitionally correct* — its solutions are
the constraint's solutions, on every instance the test generates — and that it
is *strong enough* that RUP alone certifies every consequence reachable from a
complete assignment. Once it passes, the encoding is settled, and every later
failure is about propagation or justification rather than about the model. Both
of the worked examples below record reaching this point as the thing that
licensed building everything else without revisiting the encoding.

**The catch: a check-only propagator does not prune, so the solver enumerates.**
Search is exponential in the number of variables, and the proof grows with it.
Keep the instances at this stage very small — small domains, few variables — and
expect to shrink them further if a proof gets slow. This is the one stage where
the test data is chosen for the *search* rather than for coverage of interesting
cases; you get those back in stage 2, once there is a propagator to make them
cheap. Turning the caps off (`-DGCS_TEST_CAP_DEFAULTS=OFF`) is what makes the
gate mean "on every instance" rather than "on a prefix of every instance", so
this stage wants them off and wants instances that can afford it.

### Stage 2: state the consistency level in the tests

Before writing any pruning, change the tests to demand it: switch
`solve_for_tests` to `solve_for_tests_checking_gac` if the constraint is meant
to achieve GAC, or add the directed cases that pin the bounds you intend to
reach if it is bounds-consistent (see Testing, above).

The tests now fail. That is the point — they fail for the reason you are about
to fix, and they will keep failing until the propagator actually reaches the
strength you claimed, rather than until it stops crashing. Writing this rung
before the propagator is what stops "it passes" quietly becoming the definition
of the strength, and it is the same discipline as
[large-domains.md](large-domains.md)'s audit table: say what you promise, then
make a test hold you to it.

### Stage 3: propagate, with every inference cheated (temporarily)

Now write the real propagation, and justify every inference with
`AssertRatherThanJustifying`.

**Be clear about what that is: it is cheating.** It emits VeriPB's `a` rule,
which adds a constraint to the proof *with no check whatsoever* — the solver
says "this follows" and the checker writes it down and believes it. Every
inference so justified is unverified. This is temporary development
scaffolding, borrowed against work you have not done yet, and it is repaid in
stage 4. It is the one thing in this whole document that must never reach
`main`.

Used that way, it is genuinely valuable: the suite verifies *subject to the
cheats*, so you can develop and debug the algorithm without paying for a single
proof step, and a failure at this stage can only be the algorithm.

**The gate: the stage 2 tests pass, and VeriPB still accepts.** Passing means
the algorithm reaches the strength you claimed and prunes nothing it shouldn't;
the enumeration check catches unsoundness whether or not anything is proved.
What it deliberately does *not* tell you is whether any of it is justifiable —
that is stage 4's job, and separating the two is the whole point, because
"my propagator is wrong" and "my proof is wrong" want completely different
debugging.

Assert each inference's own unit consequence, not a whole node failure: one
assertion per propagator firing keeps the search-tree refutation honest RUP from
the start, so what you discharge later is one self-contained claim at a time.

**Nothing will catch a cheat you leave behind. That is why this is dangerous.**
`veripb` exits 0 whether or not the proof used assertions, and `run_veripb` only
looks at the exit status, so a green `ctest` is exactly as green with cheats in
it as without. No CI lane, no test, and no reviewer reading a test log will tell
you. The only oracle is the `s` line, and you have to go and look at it:

```
s VERIFIED COMPLETE ENUMERATION OF 8 SOLUTIONS               <- honest
Warning: The proof used unchecked assertions.
s UNDER ASSERTIONS COMPLETE ENUMERATION OF 8 SOLUTIONS       <- cheats remain
```

`s UNDER ASSERTIONS` is not a verification. It is the checker telling you it was
asked to take things on faith, and it says nothing about the inferences that were
asserted — nor, strictly, about a proof whose later steps were derived from them.
There is no `--force-...` flag to turn this into an error, the way
`--force-checked-deletion` exists for the analogous deletion problem. So watch
the `s` line whenever you run a test binary directly during stages 3 and 4, and
count what is left with `GCS_PRESERVE_PROOF_FILES=1` and
`grep -c '^a ' foo.pbp`.

### Stage 4: discharge the cheats, one at a time

Take each inference-producing site in turn and ask, in words, before writing any
proof steps:

> *Precisely what is the general nature of what is being inferred here, and why
> is it true?*

The answer has to be a general argument about the constraint — the kind of thing
you would say to a colleague — not a restatement of what the code does. Insist
on it being general: "because `D[a][b] < T` for every `b` still in `x_j`'s
domain" is an argument; "because the loop found no support" is the code. When
the answer comes out sharp, the proof usually falls straight out of it, because
a `pol` is a formal transcription of exactly this kind of argument and RUP is
what you use when the argument is "unit propagation can see it". When it does
not come out sharp, you have found the real work, stated as a question you can
go and answer — which is a far better position than staring at a rejected proof
line.

Replace one assertion, re-run, and only then move to the next. One at a time
keeps every failure attributable, and the burn-down (`grep -c '^a '`) is a
progress bar.

If an argument turns out to need something RUP cannot do — a cross-variable
linear combination, most often — that is When RUP isn't enough, above. If it
needs a fact that is true but not stated anywhere in the encoding, you have
found the one legitimate reason to reopen stage 1.

### Stage 5: zero assertions, and no exceptions

**`AssertRatherThanJustifying` must not appear in merged code. Ever, for any
reason.** Not behind a flag, not "just this one inference", not with a `TODO`
next to it, not in a mode nobody enables by default. Delete every one of them
before the pull request.

This is not tidiness, and it is not a style rule. This solver has exactly one
claim to make — that you do not have to trust it, because everything it infers
can be checked by something else. A merged assertion is that claim being false
while continuing to look true: the proof still ships, VeriPB still prints a
green-looking `s` line, and the one inference nobody has checked is the one
someone got wrong. It is worse than having no proof at all, because a
constraint with no proof logging is honest about it and this is not.

So the finished constraint's proofs say `s VERIFIED`, with no assertion
warning. Check it yourself, on a real run, and say so in the pull request
description — "zero assertions", as the min-distance and global-cardinality
work both did — because nothing in the test suite or CI will say it for you.

If one inference genuinely resists after stage 4 has been honest about it, the
answer is never to leave the cheat in. Weaken the *inference* to something you
can justify: prune less, say so in the class comment, and record what a stronger
propagator would need, so that someone can pick the gap up later. A constraint
that prunes less and tells the truth is worth having; one that prunes more and
lies is not.

`NoJustificationNeeded` is not a way round this either, and it is worth
understanding why it is nonetheless the *safe* one of the two. It puts nothing
in the proof at all, so any later step that depends on the unjustified inference
simply fails to verify — you get a loud, honest failure. An assertion puts a
line in that VeriPB accepts unconditionally, so everything downstream sails
through. That is the whole difference: one of them breaks when you are wrong.

### Worked examples

Two constraints have written this up from their own side, each in detail on the
stage that was hardest for them:

- [min-distance-proofs.md](min-distance-proofs.md), "Check-only first:
  validating the encoding" — stage 1 on `MinDistance`. Shows what a check-only
  propagator looks like (act only once a pair's endpoints are both assigned;
  tighten `z`; pin it exactly once everything is fixed), and states the gate in
  its strongest form.
- [sortedness.md](sortedness.md), "Proof logging plan" — stages 3 and 4 on
  `Sort` / `ArgSort`, where no certifying sortedness propagator existed and the
  proofs had to be designed from scratch. Records the question above in its
  original wording, and what it turned up: the permutation/surjectivity of the
  stable rank, and then a single Hall pigeonhole shared by every bound and the
  contradiction.

`CheckOnly` is not a shared facility — `MinDistance` has its own
`install_check_only_propagator` and a mode enum to select it, and that is the
pattern to copy rather than something to call. Keeping the mode after bring-up
is worth considering: `MinDistance` still ships it, and it is the encoding's
standing regression test.

## Adding a new constraint: checklist

1. Header file with class declaration, Doxygen comments, the phases it
   overrides, and `clone` / `s_expr` / `constraint_type`.
2. `.cc` file with constructor, the three phases (`prepare`,
   `define_proof_model` for the OPB block, `install_propagators`), `clone`,
   `s_expr`.
3. Test file with the standard `for (bool proofs : {false, true})`
   loop and a `can_run_veripb()` gate on the proofs leg. Split into
   multiple ctest entries via an argv mode if the test gets slow.
4. Add the `.cc` to the library and the test target to
   `gcs/CMakeLists.txt` (alphabetically), plus an `add_test` entry.
5. Add the header to `gcs/gcs.hh` (alphabetically).
6. Add a `read_scp` case for the keyword `constraint_type` returns, in
   `gcs/scp_reader.cc`, plus an `enumerate` and a write -> read -> write
   test in `gcs/scp_reader_test.cc`. The writer and the reader are
   inverses; the constraint tests fail if the keyword has no case.
7. Decide explicitly how the constraint behaves when the caller passes
   the same `IntegerVariableID` (or a view that resolves to the same
   underlying variable) in two argument slots, or twice within an
   array argument. Pick one of three patterns and cover it with a test
   case in the constraint's `*_test.cc`:
    - **Handle correctly** — the propagator and OPB both produce the
      right result on alias. Add a dup test case (mirror the existing
      `run_dup_*_test` helpers in e.g. `equals_test.cc`,
      `linear/linear_test.cc`, `cumulative_test.cc`). Use
      `solve_for_tests` (not `solve_for_tests_checking_gac`) on the
      dup leg: a GAC algorithm for distinct vars is generally not GAC
      under aliasing, and trying to recover consistency is usually a
      separate, harder problem.
    - **Detect and contradict at root** — when an alias makes the
      constraint trivially unsat but the user's intent is still well-
      formed (e.g. `BinaryEntry`-style table rows). The
      `AllDifferent` family is the precedent: it sorts the array, runs
      `adjacent_find`, and routes to a one-shot contradiction initialiser
      (see the `adjacent_find` site in
      `all_different/gac_all_different.cc` and
      `install_clique_duplicate_contradiction_initialiser` in
      `all_different/encoding.cc`).
    - **Throw `InvalidProblemDefinitionException`** at construction
      when alias has no meaningful semantics, the propagator path is
      unsafe, or the proof encoding can't tolerate it. The Bucket A
      family — `NotEquals`, `LessThan`, `GreaterThan`, `Circuit`,
      `Inverse`, `innards::MultiplyBC` (via `Multiply`), `SmartTable` `BinaryEntry` — uses this.
      By convention the check is gated on
      `! is_constant_variable(...)` so two slots pinned to the same
      constant remain a well-formed (if often trivially infeasible)
      model. Test with a `try { ... } catch (const
      InvalidProblemDefinitionException &) { ... }` block (see
      `circuit/circuit_dup_test.cc`,
      `smart_table_dup_test.cc` for the small-binary pattern).

   The threshold for "alias" depends on the constraint. For most
   constraints, the structural variant `operator==` is the right
   check — it matches the `AllDifferent` precedent and reflects what
   the user actually typed. For constraints that key on a deviewed
   form (e.g. `SmartTable`'s `build_forests` uses the underlying
   `SimpleIntegerVariableID`), the check needs to match that — see
   `smart_table/smart_table.cc`'s `deview_for_alias_check` helper.

   The discipline above was retro-fitted across the existing
   constraints in PRs #223–#234.
7. Build and run under `--preset sanitize` and `--preset release`. Run
   the wider test suite to confirm no regressions.
8. If the constraint should be exposed to MiniZinc, follow
   [minizinc.md](minizinc.md) — separate commit.

## See also

- [propagator-performance.md](propagator-performance.md) — making a
  *correct* propagator faster: triggers/idempotence, reusing reasons and
  scratch data structures, fast data structures, iteration order,
  incrementality, backtrackable state, and removing variant-dispatch
  overhead — plus the discipline that keeps a performance change from
  becoming a strength or correctness change. Read this only once the
  propagator works and its proofs verify.
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
