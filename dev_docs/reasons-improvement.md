# Reasons: incremental improvement (DRAFT for discussion)

**Scope:** improve *only* the reason mechanism. This deliberately does **not**
touch justifications. The justification side — and a unified rethink of the whole
`infer()` triple — is explored separately in `infer-redesign.md` and in PR #302
(*Annotated Assertions*). This doc is the low-risk, near-term slice that delivers
the performance win on its own and is a strict stepping stone toward the larger
redesign (the `Reason` type defined here is reused there verbatim).

Nothing here is on main yet; this is a proposal to react to.

## Motivation

Today a reason is built like this (`gcs/innards/reason.cc`):

```cpp
auto generic_reason(const State & state, const std::vector<IntegerVariableID> & vars, ...) -> ReasonFunction
{
    Reason reason;
    for (const auto & var : vars) { /* walk domain, push lits */ }
    return [=]() { return reason; };          // captures the already-built vector
}
```

`ReasonFunction = std::function<auto()->Reason>` *looks* lazy but is not: the
domain walk, the `small_vector` fill, and a `std::function` allocation all happen
**eagerly at the call site**, on every `infer()` — and `SimpleInferenceTracker`
(proofs off) then throws the result away. This eager-build-then-discard is
measured at ~20% of runtime on some benchmarks.

### Goals (and what this doc delivers)

- **G1 — cheap construction in the easy cases.** Building a reason becomes a
  handle + a tag, no domain walk, no allocation. ← *delivered here.*
- **G2 — no diverging call paths.** A propagator writes the same thing whether or
  not proofs are on. ← *delivered here.*
- **G3 — more declarative.** Common shapes expressed as data, not lambdas. ←
  *delivered here for the easy cases.*
- **G4 — defer-friendly lifetimes.** Reasons become storable specs that *can* be
  reconstructed later. ← *the reason-side prerequisite is delivered here* (the
  spec is cheap, copyable, storable); the actual lazy-conflict-analysis machinery
  needs the justification side too, so it lives in `infer-redesign.md`.

## Core idea

Separate two things that `ReasonFunction` conflates:

1. **`Reason`** — a *declarative description* of a reason. Cheap, copyable,
   storable. A variant over a handful of shapes.
2. **`ReasonLiterals`** — the *materialised* literal conjunction the proof log
   reifies under. This is today's `Reason` type, renamed.

```cpp
namespace gcs::innards
{
    // Was `Reason`. The materialised conjunction of facts.
    using ReasonLiterals = gch::small_vector<ProofLiteralOrFlag, 2>;

    // Owned / shared / borrowed handle, reusing gcs::ArrayParam (gcs/array_param.hh).
    // "Borrowed" is the unowned mode: a constraint that always reasons over the
    // same scope passes `&_vars` and allocates nothing.
    using ReasonVars = VectorArrayParam<IntegerVariableID>;

    // Escape hatch for the bespoke tail; reads state, appends to `out`.
    using LazyReasonFn = std::function<void(const State &, ReasonLiterals & out)>;

    struct NoReason {};                                              // explicit "none"
    struct ExplicitReason            { ReasonLiterals literals; };   // singletons, fixed lists, eager snapshots

    struct GenericReasonOver         { ReasonVars vars; std::optional<Literal> extra; };
    struct BothBoundsReasonOver      { ReasonVars vars; std::optional<Literal> extra; };
    struct LazyReasonOver            { ReasonVars vars; LazyReasonFn fn; };

    // Narrowable counterparts: same payload, different tag (see "Narrowable" below).
    struct NarrowableGenericReasonOver    { ReasonVars vars; std::optional<Literal> extra; };
    struct NarrowableBothBoundsReasonOver { ReasonVars vars; std::optional<Literal> extra; };
    struct NarrowableLazyReasonOver       { ReasonVars vars; LazyReasonFn fn; };

    using Reason = std::variant<
        NoReason, ExplicitReason,
        GenericReasonOver, BothBoundsReasonOver, LazyReasonOver,
        NarrowableGenericReasonOver, NarrowableBothBoundsReasonOver, NarrowableLazyReasonOver>;

    // The only place the domain walk happens. Called by a consumer that has
    // decided it needs the literals (proofs on). Stateless variants ignore `state`.
    [[nodiscard]] auto materialise(const Reason &, const State &) -> ReasonLiterals;
}
```

A call site becomes, e.g.:

```cpp
inference.infer(logger, result <= a_hi + b_hi, justify(...),
    GenericReasonOver{some_vars});                 // no walk, no alloc

inference.infer(logger, x != v, JustifyUsingRUP{},
    ExplicitReason{{cond, y == w}});               // already-known literals
```

`ReasonFunction` and the three `*_reason()` factory functions go away;
`generic_reason(state, vars)` is replaced by the value `GenericReasonOver{vars}`
(note: no `state` at construction — that is the point).

## Where materialisation happens: the InferenceTracker template

The eager-vs-off decision already lives in the `InferenceTracker` template
(`SimpleInferenceTracker` vs `EagerProofLoggingInferenceTracker`). Reason
materialisation rides the same axis:

- **`SimpleInferenceTracker`** (proofs off): does nothing with the reason. Cost =
  building the variant. **This is the G1 win.**
- **`EagerProofLoggingInferenceTracker`** (proofs on, today's behaviour):
  `auto lits = materialise(reason, _state);` immediately, then
  `logger->infer(lit, just, lits, ...)`. State is current, so non-narrowable
  reasons are correct.

`ProofLogger::infer` / `emit_*_under_reason` take `const ReasonLiterals &`, not a
callable. The `if (reason)` null-checks disappear: `NoReason{}` materialises to
empty, which is just an un-reified inequality.

## The "Narrowable" axis (forward-looking, no-op today)

A new per-caller distinction, included now so a future deferred mode needs no
second sweep of every call site:

- **Non-narrowable** (default, conservative): the reason must reflect the *exact*
  domain at the moment of inference.
- **Narrowable**: the constraint is equally happy being handed *tightened*
  domains, so it can be re-materialised lazily against whatever (narrower) state
  is current later, with no per-inference bookkeeping ("lazy explanation
  generation").

In eager proof-logging mode both behave identically (we always materialise now,
against the current state), so the tag is a no-op until a deferred tracker exists.
Settling it per constraint needs a dedicated pass with proof-soundness sign-off —
default everything to non-narrowable.

**Caution.** Known non-narrowable: anything whose *justification reads the reason
positionally* (`plus.cc:71-76`, `minus.cc`, `mult_bc.cc` — the
`JustifyExplicitlyThenRUP` callback does `reason().at(i)` and feeds a `PolBuilder`,
so content *and order* are load-bearing), and the structural propagators (Hall
sets, GCC flow cuts) whose reason depends on the exact live domain.

## P1 — generator audit summary

~120 standard-builder call sites + ~60 bespoke `Reason{...}` lambdas. Mapping onto
the variant (counts approximate):

| Bucket | ~N | Examples | Target |
|---|---|---|---|
| A. full-domain | ~58 | count, among, element, knapsack, disjunctive, linear_equality, negative_table, cumulative, circuit | `GenericReasonOver` |
| B. bounds-only | ~15 | lex, arg_sort (often `+ extra`) | `BothBoundsReasonOver` |
| C. single fixed literal | ~14 | smart_table, vc_all_different, all_equal, increasing, inverse | `ExplicitReason` |
| D. specific selected bounds over a known scope | ~50 | plus, minus, mult_bc, comparison, linear/propagate, abs, logical, parity | `LazyReasonOver` — or a declarative "picks" form (open) |
| E. structural | ~4–6 | gac_all_different (Hall), gac/bounds global_cardinality (flow), lex scaffold | `LazyReasonOver`, reads state |
| no reason | ~2 | all_different encoding/except | `NoReason` |

Bucket D is the interesting one: it is **not** `generic_reason` (it does not dump
the domain — it picks specific bound literals computed from snapshotted values),
and for plus/minus/mult_bc it is coupled to the justification via positional
access. Open question: give D a declarative form (best for G3) or sweep it into
`LazyReasonOver` closures (simplest).

## P2 — consumer audit summary

On main, reason consumption is **uniformly eager and never escapes `infer()`**:

- Only invokers of `reason()`: `ProofLogger::{infer, reason_to_lits,
  emit_under_reason}` and a few justification callbacks (plus/minus/mult_bc index
  into it; smart_table/circuit_scc/regular iterate it once to build a "short
  reason" proof flag, then locally swap in `singleton_reason`).
- Nothing stores a `ReasonFunction`; `_inferences` keeps only `(var, Inference)`,
  no reason attached.
- `ExplicitJustificationFunction` is `std::function<void(const ReasonFunction&)>`.
  Change to `std::function<void(const ReasonLiterals&)>`: the logger materialises
  once, hands the literals to the callback *and* reuses them for the trailing RUP.
  Removes the `reason().at(i)` awkwardness and the double-materialise.

## The seam, and coordination with #302

This change rewrites the `reason` parameter of every `infer*()`/`track_impl`
overload from `ReasonFunction` to `Reason`. PR #302 independently adds a
`std::optional<AssertionAnnotation>` parameter to the *same* overloads. They
collide textually on every signature, so the merge point is one agreed shape:

```cpp
auto infer(ProofLogger * logger, const Literal & lit,
           const Justification & why,
           const Reason & reason,                                   // this doc
           const std::optional<AssertionAnnotation> & hints = std::nullopt)   // #302
    -> void;
```

Beyond the signature, this doc does **not** depend on #302 and vice versa.
Whoever lands second rebases. (The deeper, structural relationship — where
reasons and justification hints share captured data — is the subject of
`infer-redesign.md`, not this doc.)

## Lifetime contract to preserve (from the #335 / RFC #315 stack)

None of #318→#346 is in main, and none edits `reason.{hh,cc}` /
`justification.hh` — no textual conflict. Two semantic dependencies must keep
working:

1. **#318** stores the contradiction's reason on the tracker
   (`_last_contradiction_reason`, today `std::optional<ReasonFunction>`) across
   the `throw TrackedPropagationFailed`, read at the catch site by
   `ConflictObserver::note_conflict(...)`. Here it becomes
   `std::optional<Reason>` (the cheap spec); `materialise(...)` is called at the
   catch site with the still-current conflict state if an observer wants
   literals. Today all observers *ignore* it; the future "Nogoods → wdeg
   attribution" knob is the first consumer, and it wants implicated *vars* — so
   add a cheap `vars_of(const Reason &)` that reads the handle without
   materialising.
2. **#330** nogood learning is decision-path + RUP based, reason-independent. No
   conflict.

## Open decisions

1. **Bucket D shape:** declarative "selected bounds" variant vs `LazyReasonOver`
   closures vs leave-as-is initially.
2. **Per-constraint narrowability:** needs a pass with proof-soundness sign-off.
   Default non-narrowable.
3. **Sequencing:** range-literals (#303) has merged; the remaining gate is
   coordinating the `infer()` signature with #302 before this lands.

## Schedule

Two tranches; tranche 1 is the whole perf win and can land alone.

**Tranche 1 — the reason rework (G1/G2/G3):**
1. Add `Reason` variant + `ReasonLiterals` rename + `materialise`; keep thin
   constructors so nothing breaks.
2. Move materialisation into the tracker; `ProofLogger` +
   `ExplicitJustificationFunction` take `ReasonLiterals`. *Here the eager cost
   disappears.* Verify proofs byte-identical on a sweep.
3. Convert call sites bucket-by-bucket (A, then B/C, then D, then E), each a PR
   with proof re-verification; D needs care around positional-justification
   coupling.
4. `NoReason{}` cleanup; delete `ReasonFunction` and the empty-`std::function`
   sentinel.

**Tranche 2 — reason-side G4 prerequisite (light):**
5. `_last_contradiction_reason` → `std::optional<Reason>`; add `vars_of`. That is
   all the reason side owes G4. Full lazy conflict analysis (storing reasons *and*
   justifications per inference and replaying only the conflict path) is the
   subject of `infer-redesign.md`.

## Relationship to `infer-redesign.md`

This doc is a strict subset of that one: the `Reason` variant, `ReasonLiterals`,
`materialise`, and the narrowable axis are identical and reused there. You can do
this doc and stop — it stands alone and delivers the performance win without
disturbing justifications. If the larger redesign later happens, none of this is
wasted; it is the reason layer of that design, already done.
