# Redesigning `infer()` (DRAFT — ambitious, exploratory)

**Scope:** rethink the *whole* inference triple — what is inferred, its reason,
and its justification — as one declarative, mode-driven mechanism. This subsumes
the reason-only change in `reasons-improvement.md` and generalises PR #302
(*Annotated Assertions*) from the justification side into the same model.

This is a north-star sketch, **not committed**. It is intentionally larger than
`reasons-improvement.md`; that doc is the safe first slice you can ship and stop
at. Read this for where `infer()` *could* go.

## The abstraction

Every inference has three layers with a strict one-way dependency:

```
(1) what is inferred   — the Literal. ALWAYS eager. Never optional, never lazy.
        │
(2) reason             — a function of (variable set, state). May be: none / eager / reconstruct-later.
        │  (a justification needs the reason; never the other way round)
(3) justification      — = justify(rule_id, reason_literals, witness). May be: none / eager / external-later / internal-later.
```

The key claim (point 3) is that a justification is **not** an opaque callback —
it is a *named rule* applied to *explicit inputs*:

```
justify( rule_id = (ConstraintID, sub-rule),     // ConstraintID already threaded (#317)
         reason_literals,                          // the materialised reason
         witness )                                 // "the extra information"
    -> proof steps
```

This is exactly the shape of #302's annotation (`hint_name` ≈ `rule_id`,
`hint_fields` ≈ `witness`), which is evidence the abstraction is right.

## The move that gives you G2: recipe at the call site, strategy by mode

A propagator should **never** branch on whether proofs are on / eager / external.
It always supplies the same declarative recipe. A *global mode* — a property of
the InferenceTracker / ProofLogger, exactly where `Simple` vs `Eager` already
lives — picks the strategy:

| mode | (1) what | (2) reason | (3) justification |
|---|---|---|---|
| proofs off | do it | ignored | ignored |
| eager proofs (today) | do it | materialise now | run `justify(...)` now |
| external / assertion (#302) | do it | materialise now (it is the reified LHS of the `a` line) | **don't run** — serialise `rule_id → hint_name`, `witness → hint_fields` |
| internal lazy (G4) | do it | store recipe | store `{rule_id, witness}`; run `justify(...)` later, only on the conflict path |

**The coupling matters:** whenever a justification is realised, the reason must be
too. So the reason's stance is not fully free:

- external justification ⟹ reason is eager (it is written into the assertion);
- internal-lazy justification ⟹ reason defers *with* it (re-materialise at
  conflict time if narrowable, else snapshot);
- eager justification ⟹ reason eager;
- reason-without-justification ⟹ the reason's laziness is the only independent case.

## API sketch

```cpp
// (1) the literal: eager, always. Unchanged.

// (2) the Reason variant, IDENTICAL to reasons-improvement.md
//     (NoReason / ExplicitReason / {Generic,BothBounds,Lazy}ReasonOver + Narrowable*).

// (3) justification as a typed `Data` witness (one hint_sexpr/emit overload pair
//     per hint, on #302's SExpr layer). The propagator names the Data type and
//     hands over the raw args to build it; it no longer *contains* the justifier.
//     Full mechanism in "Justification dispatch" below.
```

Call site — the propagator names the witness type and hands over the raw args:

```cpp
inference.infer(
    result <= a_hi + b_hi,                                      // (1)
    BothBoundsReasonOver{operands},                             // (2)
    justify_with<plus::BoundData>(sum_line, plus::Dir::ResultUB));  // (3) Data built only if proofs on
```

Mode handling lives in the tracker/logger, not the call site (off / eager /
assert-external / lazy-internal — see the dispatch section for what each does).

## Justification dispatch: typed `Data` on #302's `SExpr` layer

*(Reconciled with PR #302 as of commit `027780b6`, "Use s-expressions for hint
fields". An earlier draft of this section argued "tags, not a global enum"; #302
has since built most of the mechanism, so this is now a much smaller, additive
proposal on top of what is already there. The change in stance is deliberate —
see the note at the end of the section.)*

### What #302 already provides (build on it, don't replace it)

As of `027780b6`, #302's hint mechanism is no longer the early enum-plus-flat-
`vector<hint_field>`. It is:

- `AssertionHintName` — a small, central enum naming the rule/constraint family
  responsible (`AllDifferent`, `Abs`, `ReifiedEquals`, …) — *the one piece this
  redesign replaces; see "Why the central enum should go" below*;
- `hint_fields : std::optional<SExpr>` — the payload, where `SExpr` is the
  **existing** `.scp` proof-model type (`gcs/innards/s_expr.hh`), so the wire form
  is codebase-consistent and `format`/`parse_s_expr` round-trips;
- built by a `hint_sexpr(...)` **overload set** (one overload per leaf type:
  `AssertionHintIdentifier` keyword, `ProofLineLabel`, `ConstraintID`, `Integer`,
  `SExpr` pass-through; variables via `names_and_ids_tracker().s_expr_term_of`) and
  a variadic `hint_list(Ts&&...)` that folds `hint_sexpr` over a typed pack.

This is a good substrate. Two of its properties are exactly what the earlier draft
was reaching for: a missing `hint_sexpr` overload is a hard **compile error**
(typed at the leaves, no silent wrong pick), and dispatch is plain overload
resolution on the argument type. It also settles the "is this too much C++?"
worry empirically — a variadic template plus an overload set is precisely the
idiom, and it is already in the branch, written by hand.

### What is still missing: a per-hint *schema*

`hint_list(...)` is free-form. Nothing enforces that an `AllDifferent` hint carries
`{hall_vars, hall_values, owner}` rather than, say, just a `constraint_id`. The
*leaves* are typed; the *composition for a given `hint_name`* is by convention,
checked nowhere. So the external justifier still switches on `hint_name` and must
know, per name, what shape to expect — a uniform **parse**, but not a uniform
**interpret**, and no single place documents the contract.

The one addition this redesign makes is to give each structured hint a typed
`Data` struct and a single `hint_sexpr` overload that owns its schema:

```cpp
// --- next to all_different ---
struct HallData {
    small_vector<IntegerVariableID, 4> hall_vars;
    small_vector<Integer, 4>           hall_values;
    ConstraintID                        owner;
};

// the schema lives in ONE place: this overload. Slots straight into #302's layer.
auto hint_sexpr(const HallData & d) -> SExpr
{
    return hint_list(AssertionHintIdentifier::hall_vars,     d.hall_vars,
                     AssertionHintIdentifier::hall_values,   d.hall_values,
                     AssertionHintIdentifier::constraint_id, d.owner);
}
```

The call site moves from free-form

```cpp
.hint_fields = hint_list(AssertionHintIdentifier::constraint_id, constraint_id)   // today
```

to schema-checked

```cpp
.hint_fields = hint_sexpr(HallData{hall_vars, hall_values, owner})                // typed
```

— same wire format, same machinery, one extra overload. The `Data` struct **is**
the explicit "interface the justifier supports" that #302 wants its hint names to
define, made compiler-checked and local to the constraint instead of free-form and
documented only by the Rust decoder. So this is **additive, per-constraint, and
non-disruptive**: keep the `SExpr` representation; add a `Data` struct wherever a
hint carries more than one field whose roles matter (the lone `constraint_id` hint
needs no struct — flat `hint_list` over leaves stays right for genuinely flat
hints). The wire identifier moves *onto* the `Data` type (`static constexpr
std::string_view name`), retiring the `hint_name` enum — see "Why the central enum
should go".

### One `Data`, two consumers — and the G1 deferral

The `Data` struct is the single typed witness; two functions consume it, picked by
the mode (the tracker/logger property, not the call site):

- **AssertExternal (#302):** `hint_sexpr(const Data &) -> SExpr` — the schema-owning
  serialiser above. This is the *only* path that crosses to the external Rust
  justifier, which reimplements the same schema reading the `.scp` s-expression.
- **Eager / LazyInternal:** `emit_justification(const Data &, ProofLogger &, const
  ReasonLiterals &) -> void` — emits the real proof steps in C++. For `HallData`
  this body is the *existing* `justify_all_different_hall_set_or_violator`,
  unchanged. Eager runs it at inference time; LazyInternal parks the `Data` and
  runs the same function at backtrack, only on the conflict path.

Crucially, construct `Data` **only in the mode that consumes it**. A hint is built
wherever its justification path runs — including plain eager proof mode, which
emits the real justification and never looks at the hint — so building
`hint_list(...)` eagerly there is wasted, the same eager-build-then-discard
`reasons-improvement.md` removes on the reason side. The fix mirrors it: pass cheap
raw args and let a `gather(raw...) -> Data` step defer `Data` + `hint_sexpr` past
the mode check. For all-different it is nearly free anyway — the Hall set is the
propagation *result*, and the proof path is already gated — but the principle
matters for the cheap, ubiquitous infer sites (the bound-pushers).

### Capability tiers — which modes a hint supports

Whether a hint is deferrable is "does it have a `Data` struct plus the two
overloads?", detected by a concept on the `Data` type rather than a flag:

- **Witness-complete (tier 1):** has `Data`, `hint_sexpr(Data)`,
  `emit_justification(Data, …)`. All modes. The target and the majority (plus, abs,
  all-different, GCC, reified-linear).
- **Re-derivable (tier 2):** `Data` ≈ empty but `emit_justification` re-runs an
  algorithm from `(def, reason)` (knapsack DP). Lazy/external work *at compute cost*.
- **Eager-only (tier 3):** no liftable witness; stays an inline `JustifyExplicitly`
  closure exactly as today. In assert/lazy modes it **falls back to emitting real
  proof steps** — so the external tool never reimplements it, and lazy analysis
  just skips it. Graceful, not a blocker; the messy intertwining is allowed to stay
  precisely where it is necessary.

The `if constexpr (has Data overloads)` branch in the tracker is the only generic
spot. It parallels the `Deferrable` concept sketched earlier; the only change is
that the dispatch type is now the `Data` struct itself (which `hint_sexpr` already
keys on), so there is **no separate empty `Tag` type** — one fewer thing to define
per rule.

### `derivable_from` and the constraint ID

Two notes specific to #302's current shape:

- It hand-carries `(constraint_id <id>)` *as a hint field* — `027780b6` threads
  `ConstraintID` through `propagate_gac_all_different` into every caller for exactly
  this. That is compensating for `infer()` not knowing which constraint owns the
  inference. Under this redesign `rule_id = (ConstraintID, sub-rule)` is
  **structural** — part of the inference, not a field the propagator assembles — so
  the `constraint_id` hint field disappears and the owner is available to `emit` /
  the assertion for free.
- `derivable_from` is best a `ConstraintID` (stable across renumbering, portable);
  for most hints `emit` can reconstruct the specific lines from `(owner + Data)`, so
  it need not be a stored field. Keep explicit `ProofLineLabel`s only where an
  assertion leans on a *temporary* lemma line not tied to a definition.

### The one cost this does not remove

The typed `Data` relocates the schema into one compiler-checked place; it does not
delete the cross-language contract. The external Rust justifier still needs the
union of hint names, their `Data` schemas (now readable off the `hint_sexpr`
overloads), and their emit semantics, kept in sync by hand. What the typed layer
buys is that the C++ side of that contract is *one struct + one overload per hint*,
self-documenting and checked, rather than free-form `hint_list` calls scattered
across call sites. Hint names and the `AssertionHintIdentifier` keywords become a
proof-compatibility surface and want light versioning.

### Where the hint types live: a dedicated namespace

Put every hint `Data` struct **and** its `hint_sexpr`/`emit_justification`
overloads in one dedicated namespace — say `gcs::innards::hints`. This is logical
co-location, not physical: reopen `namespace gcs::innards::hints { … }` inside each
constraint's files, so `HallData` and its `emit` (which calls
`justify_all_different_hall_set_or_violator` and reaches `def` via the
`ConstraintID` — all_different-specific logic) still sit next to all_different. A
reasonable split is to declare the `Data` **structs** in small per-constraint
headers (the *schema*, i.e. the contract, all in headers under the namespace) and
keep the `hint_sexpr`/`emit` *definitions* in the `.cc` next to the logic.

This is what makes the cross-language contract above tractable, and it answers the
enum's one real virtue without the enum:

- **Single discoverable interface surface.** "What does the justifier support?" =
  "everything in `gcs::innards::hints`." That is the "interface in one place" the
  enum was wanted for.
- **Additive, distributed membership.** A new hint adds a struct from a new file;
  it does *not* edit a shared token. This is the precise difference from the enum —
  no central edit point, no merge-conflict magnet, no desync. So a namespace
  matches the enum on discoverability while beating it on locality.
- **Clean ADL.** All overloads live in the argument type's namespace, so
  `hint_sexpr(d, …)` / `emit_justification(…, d, …)` resolve with no scatter and no
  `using` gymnastics.
- **It enforces canonicality.** A `Data` that wanted a constraint-private type
  could not sit cleanly in the shared namespace — which is exactly when it would
  fail to serialise to the Rust side anyway. The namespace pressures `Data` to stay
  in the serialisable vocabulary (`ConstraintID`, `Integer`, `IntegerVariableID`,
  vectors) for free.

What this does **not** buy is automatic Rust codegen: without reflection (pre-C++26)
the cross-language mirror is still hand-maintained. But a namespace is the lightest
way to make the C++ side of that contract a single enumerable list — a grep or
doc-gen keyed on `gcs::innards::hints` produces the exhaustive set of `{name, Data
schema}` to mirror in Rust. (Automatic codegen is judged unlikely to be worth it;
enumeration-for-a-human is the realistic goal and a namespace delivers it.)

### Why the central enum should go

`AssertionHintName` is prototype convenience — easy to write while bootstrapping —
not a long-term asset. Once each structured hint has a typed `Data`, the enum
fails three ways:

1. **It is a redundant second identifier.** The `Data` type (`HallData`) already
   names the hint kind; the enum value (`AllDifferent`) is a parallel name for the
   same thing, hand-synced at the call site (`.hint_name = AllDifferent,
   .hint_fields = hint_sexpr(HallData{…})`) with **nothing checking they agree** —
   `.hint_name = Abs` over `HallData` compiles. That is exactly the unchecked
   coupling the typed `Data` removes from the fields, reintroduced on the key.
2. **It is at the wrong granularity.** It is per-constraint-family, but the
   justification *shapes* are finer. all_different tags both its Hall-violator
   contradiction (`gac_all_different.cc:423`, `prove_matching_is_too_small`) and
   its SCC deletions (`:591`, `prove_deletion_using_sccs`) as one `AllDifferent`;
   abs tags ~11 distinct inferences `Abs`. So it does not actually discriminate the
   rule — the real dispatch is in the fields/procedure already.
3. **It forces a non-local edit** (the enum, its `operator<<`, its `as_string`)
   distant from the hint logic, for every new kind.

The single thing the enum genuinely provides — a stable, cross-language wire
identifier — moves onto the `Data`/tag type as `static constexpr std::string_view
name = "all_different.hall"`. One source of truth: it is the dispatch key *and* the
wire string, cannot desync from the schema, is at the right (per-shape)
granularity, and lets us choose the wire spelling explicitly so renaming a C++ type
does not break old proofs.

This still serves Matthew's real goal — the hint set as a visible "interface the
justifier supports." The contract that matters is {stable `name`, field schema,
emit semantics} per shape, and with typed `Data` each is self-documenting and
correctly granular, and the dedicated `gcs::innards::hints` namespace (above) *is*
the single enumerable menu — derived from the tags, not a hand-synced parallel list,
and not the load-bearing dispatch key. The pro-enum cases do not hold up here: we never switch on it in C++
(dispatch is overload resolution on the `Data` type; lazy-internal uses a per-type
`emit` function pointer, so no runtime kind-switch), and a closed Rust mirror is
hand-maintained per new hint either way, so a string with a catch-all arm is no
worse.

## The witness is the whole ballgame — and the hard cases disagree about it

Two constraints we'd worry about most land in **different** places.

**all-different (GAC) is ~90% there already.** `find_hall_set_or_violator`
(`gac_all_different.cc:203`) returns `pair<JustifyExplicitlyThenRUP,
ReasonFunction>`, and the justifier closure is a one-line adapter over an
*already free function*: `justify_all_different_hall_set_or_violator(logger, vars,
hall_variable_ids, hall_value_nrs, value_am1_constraint_numbers)`. Decompose:
- `vars`, `value_am1_constraint_numbers` → **def** (the am1 numbers are proof line
  refs — serialisable);
- `hall_variable_ids`, `hall_value_nrs` → **witness** (finite, explicit, serialisable);
- the *reason* (`gac_all_different.cc:263`) is built from the **same Hall set**
  plus the `excluded` values.

So this is the poster child: the witness is exactly `HallData`'s `{hall_vars,
hall_values}`, and it feeds *both* the reason literals (`v != val`) and the
justifier.
"Capture the witness once, derive reason + justification" is not aspirational —
the code already computes them together; the refactor just stops reference-
capturing `&state`/`&logger` and names the data. Fully serialisable → the external
Rust justifier reimplements one function reading hall vars/values from `hint_fields`.

**knapsack is the genuine hard case — but not because of hidden state.** Its
justification (`knapsack.cc:240–453`) is a long sequence of
`emit_rup_proof_line_under_reason(generic_reason(state, reason_variables), …)` +
`PolBuilder` lemmas emitted *inline as the DP forward/backward passes walk the
layer graph*. There is no Hall-set-like witness to lift out. **But** the DP is
deterministic given the variable domains, and those domains are exactly what the
reason captures — so the justifier *is* re-derivable from `(def =
weights/capacities, reason = current domains)` with an essentially empty witness.
The cost is not hidden state; it is that **the justifier is a whole algorithm**,
and deferring/porting it means re-running that algorithm (a second C++ pass for
lazy mode, or a Rust reimplementation for the external tool).

That distinction is the answer to "is the intertwining necessary?". It splits
into two unrelated problems:

- **(a) Hidden-state capture** — the justifier reference-captures transient data
  never made explicit. *Mechanical to fix*: make the witness a named struct.
  all-different shows most constraints are close.
- **(b) Justifier-is-an-algorithm** — the derivation is interwoven with the
  propagation algorithm (knapsack DP, perhaps circuit SCC). *Not* about missing
  data; re-emitting requires re-running the algorithm.

## A capability spectrum, not all-or-nothing

The modes a justifier *supports* become a per-rule property:

1. **Witness-complete** (plus, abs, all-different, GCC, reified-linear): `justify`
   is a pure fn of `(def, reason, witness)`; the witness records the propagator's
   non-re-derivable *choices*. Supports **all** modes. The target and the majority.
2. **Re-derivable** (knapsack): witness ≈ empty, but `justify` re-runs an
   algorithm from `(def, reason)`. Supports lazy (re-run in C++) and external
   (re-run in Rust) **at compute cost**; likely default to eager and only port if
   the trimmer shows it pays.
3. **Eager-only** (the holdouts): needs live transient state that is neither
   recorded nor re-derivable; only eager mode. Stays exactly as embedded as today.
   No flag needed — a tag is eager-only precisely when it does *not* define
   `gather_justification`, detected by the `Deferrable` concept above, and
   `realise` auto-degrades it to real proof steps in the defer modes.

The crucial property: **tier 3 is a graceful fallback, not a blocker.** An
eager-only rule emits real proof steps even in assertion mode (it is never an
assertion, so the external tool never has to reimplement it) and is simply skipped
by lazy conflict analysis (it forgoes the trimming benefit). So the messy
intertwining is allowed to remain *precisely where it is necessary*, and the
refactor's payoff is incremental and per-constraint: each rule lifted 3→2→1 gains
trimmability, lazy replay, and Rust-portability, with no big-bang requirement.

## Deep relationship to PR #302

This redesign **is** the generalisation of annotated assertions. #302 already:
- emits the inference reified under the reason as an `a` line
  (`emit_under_reason(AssertProofRule{}, …, reason, annotation)`), and
- attaches `AssertionAnnotation { derivable_from, hint_name, hint_fields }`.

Map directly onto this model (see "Justification dispatch"): the hint identifier is
the `Data` type's `name` (replacing the `hint_name` enum), `hint_fields` =
`hint_sexpr(Data)`, `derivable_from` = the `ConstraintID`/line refs `Data` carries.
The external Rust justifier in the VeriPB trimmer codebase consumes exactly the
**witness-complete tier**: it reimplements each hint's `emit` reading the `Data`
back from the `.scp` s-expression. Two big-picture #302 goals fall
straight out:
- **(A) proof logging in other solvers**: another solver emits `(inference, reason
  literals, hint)` and never needs our C++ internals — the portable boundary is
  the *materialised* forms (`ReasonLiterals` + serialised `Data`), so our
  in-process `LazyReasonOver`/`emit` functions never cross it.
- **(B) trim then justify**: emit cheap assertions for everything, trim, then run
  the justifier only on survivors. Composes with G4 lazy analysis (which avoids
  *emitting* off-path inferences): trim what G4 emits.

So #302 and this redesign want the same per-inference record — `(reason spec, tag,
gathered Data)` — designed cheap and storable. Practically, #302 can be the
justification-side beachhead: land its assertion mode, then this redesign is
"replace the global hint enum with per-tag `emit`/`gather` and extract every
justifier into that shape." Adopting the tag mechanism *in #302 itself* is the
cheapest point to do it — before a flat-field decoder hardens.

## Cost / payoff (honest)

- **Cost:** a large, mostly-mechanical refactor — every embedded justifier becomes
  an ADL-found `emit`/`gather` pair plus a tag + `Data` struct, done constraint-by-
  constraint with proof re-verification at each step. Tier-3 holdouts excepted.
  Plus the per-tag `Data ⇄ flat fields` (de)serialiser, but only for tags that
  support `AssertExternal`.
- **Payoff per extracted rule:** trimmable (B), lazily replayable on the conflict
  path (G4), and reimplementable in Rust (A) — plus the call-site/perf wins from
  `reasons-improvement.md` come along for free since the reason layer is shared.
- **Synergy:** for many constraints the reason and the justification draw on the
  *same data* (all-different's Hall set), so the per-constraint audit table —
  `{ reason variant, narrowable?, tag name, gathered Data fields }` — is one
  artifact serving reasons, #302, and this redesign at once.

## Resolved by the tag design

- *Witness typing* — typed per-tag `Data` in C++, lowered to flat fields only on
  the `AssertExternal` wire; in-memory and lazy paths never flatten.
- *Sub-rule granularity / a global enum* — gone. Tags group by *argument shape*
  (Plus's 6 rules → one `BoundTag` with a direction field), each carrying its own
  local `name`; the external tool dispatches on `name`.

## Open questions

- **Re-derivable rules vs narrowability collide.** A re-derivable justifier
  (knapsack) re-runs over "the domains" — but lazily, the domains have narrowed.
  Narrowable ⟹ fine; non-narrowable ⟹ snapshot the domains into reason/`Data`,
  which for knapsack is potentially large, possibly collapsing tier 2 into tier 3
  in practice. Probe a real knapsack proof before believing tier 2 is populated.
- **What does a constraint stash at install time** for its `emit` (the `def` —
  coefficients, automaton, table, at-most-one line numbers), and how does the
  external Rust tool obtain the equivalent? Likely the OPB/definition lines it
  already emits — needs pinning down.
- **Serialisation mechanism.** Hand-written per tag (no Boost, no reflection
  before C++26), or a single aggregate-reflection helper? Only bites tags that
  support `AssertExternal`.

## Relationship to `reasons-improvement.md`

That doc is the reason layer of this one, shippable on its own. This doc adds the
justification layer and the mode machinery on top. Recommended path: do
`reasons-improvement.md` first (real perf win, low risk), let #302 land its
assertion mode, and only then decide whether to pursue this full unification —
by which point the per-constraint witness work will be far clearer.

## Appendix: worked examples against the real code

Two constraints, deliberately chosen because they sit at opposite ends — `plus`'s
justifier *reads* the reason and is new-ish code; `all_different`'s *ignores* the
reason and is already a free function we reuse almost verbatim.

*(Surface note: the `all_different` example below is in the current surface and
matches `de85b4c9`. The `plus` example still uses the earlier draft's empty `Tag`
struct with `gather_justification`/`emit_justification` overloads on it; map it onto
the current surface the same way — there is no separate `Tag`, the `Data` struct is
the dispatch type and carries the `static constexpr name`; `emit_justification(Data,
…)` is unchanged (eager/lazy C++ steps); the AssertExternal wire form is
`hint_sexpr(Data) -> SExpr`. The substance — witness, tiers, what `def` holds — is
unaffected.)*

### `plus` (today: `plus.cc:55–110`)

Today each of the 6 bound rules calls `inference.infer(logger, lit,
justify(Conclude::GE|LE), [=]{ return Reason{op1_bound, op2_bound}; })`, and the
`JustifyExplicitlyThenRUP` lambda captures `[c, sum_line, logger]`, picks
`sum_line.first`/`.second` by direction, builds a `PolBuilder` from that line plus
`reason().at(0)`/`.at(1)`, and emits at `ProofLevel::Temporary`.

```cpp
// --- in the plus namespace ---
struct BoundTag { static constexpr std::string_view name = "plus.bound"; };

struct BoundData { ProofLine pol_line; };   // the operand bounds come from the reason, positionally

// raw args -> Data. Returns nullopt when the relevant sum_line is unset, which today
// is the "no explicit step, RUP only" path (the `if (! sum_line_value) return;` guard).
auto gather_justification(BoundTag,
        const std::pair<std::optional<ProofLine>, std::optional<ProofLine>> & sum_line,
        bool conclude_le) -> std::optional<BoundData>
{
    auto line = conclude_le ? sum_line.first : sum_line.second;
    if (! line) return std::nullopt;
    return BoundData{*line};
}

// Data + reason -> the explicit lemma. (The trailing RUP under the reason is done by
// the infer machinery — this is the "ThenRUP" half, factored out.)
auto emit_justification(BoundTag, ProofLogger & logger, const BoundData & d, const ReasonLiterals & reason) -> void
{
    PolBuilder b;
    b.add(d.pol_line);
    for (std::size_t i = 0; i < 2; ++i) {   // the two operand bounds, positionally — see note
        auto lit = get<IntegerVariableCondition>(get<Literal>(get<ProofLiteral>(reason.at(i))));
        if (holds_alternative<ConstantIntegerVariableID>(lit.var)) continue;
        b.add_for_literal(logger.names_and_ids_tracker(), lit);
    }
    b.emit(logger, ProofLevel::Temporary);
}
```

Call site:

```cpp
inference.infer(result >= a_vals.first + b_vals.first,
    ExplicitReason{{a >= a_vals.first, b >= b_vals.first}},        // (2) two specific bounds, cheap, known now
    justify_with(plus::BoundTag{}, sum_line, /*conclude_le=*/true)); // (3)
```

Notes:
- **`emit` reads the reason positionally** (`reason.at(0/1)`), so this rule's
  reason is content- *and order*-coupled → **non-narrowable**, and the reason
  must be materialised whenever the justification is.
- The reason is two *specific* picks, not a full domain (bucket D). `ExplicitReason`
  builds the 2-element vector eagerly; negligible here, but if we wanted it lazy a
  "picks"-style `LazyReasonOver` is the bucket-D open question from
  `reasons-improvement.md`.
- `gather` returning `optional` is the general "sometimes there is no explicit
  step, just the trailing RUP" pattern (here, an absent `sum_line`).

### `all_different` GAC (today: `gac_all_different.cc`, `all_different/justify.{hh,cc}`; structured hints added in `de85b4c9`)

This is now grounded in real code: as of `de85b4c9`, the GAC propagator emits
structured hints for **three** distinct inference shapes — all currently sharing
one coarse `hint_name = AllDifferent`:

| shape | site | inference | hint fields built |
|---|---|---|---|
| matching too small | `prove_matching_is_too_small` | `FalseLiteral{}` (contradiction) | `constraint_id`, `hall_vars`, `hall_vals`, `justifier = hall_set_or_violator` |
| SCC deletion, hall set | `prove_deletion_using_sccs` (hall branch) | value deletions | *identical block to the above* |
| SCC deletion, trivial | `prove_deletion_using_sccs` (forced-value branch) | one deletion | `constraint_id` only |

Two things to notice in that commit. (1) The first two shapes **hand-build the same
four-field s-expr block, copy-pasted across the two functions.** (2) `hint_name =
AllDifferent` does not say which of the three a hint is, so a `justifier =
hall_set_or_violator` field was added to separate the hall shapes from the trivial
one — i.e. *the real rule name is being carried as a field because the enum is too
coarse* (the granularity point from "Why the central enum should go", now live in
the code).

Both fall straight out of the typed design. The two hall shapes share one witness
and one `name`; the trivial shape is its own tiny one:

```cpp
// --- in namespace gcs::innards::hints, reopened in the all_different source ---
struct HallData {
    static constexpr std::string_view name = "all_different.hall";   // == de85b4c9's `hall_set_or_violator` justifier
    small_vector<IntegerVariableID, 4> hall_vars;
    small_vector<Integer, 4>           hall_values;
    ConstraintID                        owner;        // handle to this constraint's proof `def`
};

// schema + wire form in ONE place — replaces BOTH hand-duplicated hint_list blocks in de85b4c9.
// Variable fields need the names tracker (de85b4c9 renders them with s_expr_term_of), so the
// serialiser for a Data containing variables takes it — the same dependency, made explicit.
auto hint_sexpr(const HallData & d, NamesAndIDsTracker & names) -> SExpr
{
    std::vector<SExpr> var_terms;
    for (auto v : d.hall_vars) var_terms.push_back(names.s_expr_term_of(v));
    return hint_list(hint_list(AssertionHintIdentifier::constraint_id, d.owner),
                     hint_list(AssertionHintIdentifier::hall_vars,     SExpr::list(std::move(var_terms))),
                     hint_list(AssertionHintIdentifier::hall_vals,     hint_seq(d.hall_values)));
}

// eager / lazy C++ steps: reach `def` via the owner, reuse the existing free fn, ignore the reason.
auto emit_justification(ProofLogger & logger, const HallData & d, const ReasonLiterals &) -> void
{
    auto & def = logger.constraint_proof_data<AllDifferentDef>(d.owner);     // { all_variables, value_am1_constraint_numbers }
    justify_all_different_hall_set_or_violator(logger, def.all_variables,
        {d.hall_vars.begin(), d.hall_vars.end()}, {d.hall_values.begin(), d.hall_values.end()},
        def.value_am1_constraint_numbers);
}

// the trivial SCC shape: no hall set, just the owner.
struct ForcedValueData { static constexpr std::string_view name = "all_different.scc_forced"; ConstraintID owner; };
auto hint_sexpr(const ForcedValueData & d, NamesAndIDsTracker &) -> SExpr
{
    return hint_list(hint_list(AssertionHintIdentifier::constraint_id, d.owner));
}
```

`HallData::name` is exactly the `hall_set_or_violator` discriminator `de85b4c9`
puts in a field; once it lives on the type, the `hint_name` enum entry is the
redundant coarse duplicate.

Call site (the reason and the justification draw on the **same** computed Hall set;
build the witness only in a consuming mode — `de85b4c9` already does this with its
`if (logger.get_assertion_level() != AssertionLevel::Off)` guard):

```cpp
inference.infer(vars[k] != val,
    LazyReasonOver{hall_vars, [excluded](const State & st, ReasonLiterals & out) {   // (2) generic over hall_vars + exclusions
        for (auto v : /*hall_vars*/) for (auto s : excluded) out.push_back(v != s);
    }},
    justify_with<all_different::HallData>(hall_vars, hall_values, owner_cid));        // (3) Data built only if consumed
```

Notes:
- **One witness serves both hall shapes.** The contradiction
  (`prove_matching_is_too_small`) and the SCC deletion (hall branch) build the
  identical `HallData`; the single `hint_sexpr`/`emit` pair replaces the duplicated
  `hint_list` blocks `de85b4c9` currently carries in both functions.
- **`emit` ignores the reason** — it derives everything from the Hall set + `def`.
  Contrast with `plus`. So whether a justifier consumes the reason is genuinely
  per-rule, and the uniform `emit(…, Data, reason)` signature carries the reason for
  those that want it and is ignored by those that don't.
- The body of `emit` is the *existing* `justify_all_different_hall_set_or_violator`,
  unchanged. The refactor is: stop reference-capturing
  `&logger`/`&value_am1_constraint_numbers`; carry the Hall set as `HallData`; reach
  the rest via `owner`.
- **This pins down the "what does a constraint stash" open question.** `def` here
  is not pure install-time data — `value_am1_constraint_numbers` is a
  `map<Integer, ProofLine>` *mutated during proof* (it lazily emits an at-most-one
  constraint per value and caches its line, `justify.cc:41`). So the logger holds a
  per-constraint, ConstraintID-keyed proof-data object that may include mutable
  caches. For the external Rust tool the same at-most-one lines live in the proof,
  so it rebuilds/looks them up; for in-solver lazy replay the cache persists with
  the constraint. The witness stays small (the Hall set); `def` is reached by id.
- Fully serialisable witnesses (`HallData`, `ForcedValueData`) → both are
  witness-complete (tier-1) rules: all four modes work.
