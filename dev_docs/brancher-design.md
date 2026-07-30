# Step 2 — the Brancher-API refactor: concrete, decided design

**Status: decided design, partly implemented — stages A, B and B' have landed
(#606, #607); B''–E have not.** "Migration staging", below, is the authority on
what each remaining stage owes, and tracking issue #612 indexes them.
This note is the single committed record of the step-2 design: it turns the
user-approved conceptual sketch in
[order-encoding-deletion.md](order-encoding-deletion.md) ("Design overview"
through "Implementation staging") into concrete C++ against the real code, folds
in the two objective follow-ups the owner attached (the improvement-constraint
`delc` + Top-eviction, and the objective-variable deletion exemption from the 2b
findings), and integrates the eq-atom sliding window that turns ascending and
descending eq branching into a win. Where a call needed the owner it has been
made; the five decisions are recorded up front. Where a claim needed a checker it
was validated against `veripb 3.0.2`, and the raw drivers are cited in
Provenance. The three remaining unknowns are implementation gates, not owner
calls, and are flagged as such.

Step 2 changes no model, no propagator, no search order. It is a proof-only
change and must be verified as one: search identical mode-off vs mode-on at every
stage, byte-identity where the byte-identity section promises it.

The supervisor reviews this before any code is written.

## Decisions (owner)

1. **Per-node object: a generator, not a virtual class.** Keep the coroutine
   `std::generator` the solver already uses and only widen its yield type; do not
   build the virtual `Brancher` class the sketch drew. Revisit "at least until it
   starts showing up in benchmarks as being the hotspot" — stage E watches
   brancher overhead explicitly.

2. **Accept the public yield-type source break.** Pre-0.1, there is no
   API-stability obligation; the implicit `IntegerVariableCondition →
   BranchDecision` conversion is the compatibility bridge and a permanent dual API
   is not worth its maintenance. No shim.

3. **Objective handling: Option A, both mechanisms composed, unconditionally.**
   The exemption owns the objective's `ge` residency (its delete/reintroduce churn
   goes away); the incumbent `delc` keeps exactly **one** improvement constraint
   resident and checked-deletes every superseded one. Do the `delc` unconditionally
   — "even if it rarely matters, because occasionally it will matter a lot."

4. **The value-order mapping (final).** `split_*` win by the bound *jump*;
   `smallest_first` / `largest_first` / `smallest_in` / `largest_in` win by being
   O(1)-resident via the eq window; `median` / `random` / `random_out` /
   `reject_random_interval` stay `Exclude`; `smallest_out` / `largest_out` stay
   `Exclude` but are recorded as likely foldable future work (see below). This
   supersedes the eq rows of the earlier sketch, which had the eq orders wrong.

5. **The eq window ships default-off for eq orders**, wired but gated, until the
   stage-E eq-heavy measurement settles the transient-for-permanent trade — the
   same measure-first discipline as the chain gate's default. The split family is
   likewise flag-gated.

Two of these (4, 5) supersede the "map the eq orders to `Exclude`, only split
wins" stance that an earlier iteration of this design held; the eq-atom window
(below) is what changed the calculus, and it is validated (8/8 in VeriPB 3.0.2).

## What is already committed, and what step 2 restructures

Done and committed on this branch (do **not** re-do):

- The **hoist primitive** — `ProofLogger::hoist_literal_to_{level,top}` over
  `NamesAndIDsTracker::hoist_order_literal_to_{level,top}` (definition move via
  `move_proof_lines_to_level` + re-stitch via `stitch_hoisted_order_literal`).
- The **Literals mode** (`OrderEncodingDeletion::Literals`): deletable interior
  `ge` defs at `Current`, forget-driven delete-and-stitch
  (`forget_order_literals_at_level`), reintroduction (`reintroduce_order_literal`),
  and the four hoist call sites (`backtrack`, `emit_learned_nogood`, `solution`,
  and the eq/invar `hoist_ges_named_by_top_atom`).
- The **chain-length gate** (`order_encoding_deletion_min_chain`, default 16;
  0 = off = the aggressive-testing mode).
- The **residency-cause diagnostic** (`OrderEncodingResidencyCause`,
  `GCS_ORDER_ENCODING_STATS`), currently stats-gated.

Today deletion is a **side-effect** of the existing branch/backtrack flow: a
guess literal happens to be emitted at `Current`, a backtrack `forget` happens to
delete it, and `backtrack()` / `emit_learned_nogood()` hoist the survivors. There
is **no explicit advance** — the verified guess-reasoned bound jump
(`order_jump_check`, the "verified foundation") is proven sound in isolation but
is not wired in.

Step 2 makes the advance a first-class, brancher-declared emission
(**consolidate → hoist → delete**), so the frontier is explicitly monotone and
deletion follows from the advance rather than from an incidental forget. It also
gives the branch layer the two things the flat machinery cannot express: a
**per-variable deletion-policy hook** (so the always-bound-tightened objective can
be exempted from churn) and an **objective-improvement lifecycle** (`delc`
superseded improvement constraints, evict their stale threshold from Top).

## Concrete types and signatures

### The decision and its backtrack advance

The sketch drew `BranchDecision { guess; on_refuted; }` with
`BacktrackAdvance = variant<LowerBound, UpperBound, Exclude, Custom>`. Grounded in
the real code (`gcs/variable_condition.hh`, `gcs/search_heuristics.hh`):

```cpp
namespace gcs
{
    namespace backtrack_advance
    {
        // The node's backtrack constraint tightens to a lower bound on `var`:
        // refuting this decision's subtree entails `var >= (next live threshold)`.
        // Emitted by the guess-reasoned bound-jump RUP; names ONE order literal.
        struct LowerBound final { IntegerVariableID var; };

        // Symmetric: refuting entails `var <= (next live threshold)` i.e. `var < t`.
        struct UpperBound final { IntegerVariableID var; };

        // The generic fallback: accumulate `! guess` into the node's excluded set.
        // Exactly today's `~(all guesses)` backtrack clause. Names a growing set,
        // so nothing is deletable for that variable. The default.
        struct Exclude final { };

        // Escape hatch: the brancher hands back the backtrack constraint it has
        // proven plus a callback that writes the advance. For exotic branchers only;
        // the callback still never writes raw guess/hoist/delete bookkeeping — it
        // hands the framework a WPBSum and a reason, and the framework emits.
        struct Custom final
        {
            std::function<auto(const CurrentState &)->WPBSumLE> constraint;
            // Reserved; not fleshed out until a use case appears.
        };
    }

    using BacktrackAdvance = std::variant<
        backtrack_advance::LowerBound,
        backtrack_advance::UpperBound,
        backtrack_advance::Exclude,
        backtrack_advance::Custom>;

    struct BranchDecision final
    {
        IntegerVariableCondition guess;   // what to branch on (unchanged type)
        BacktrackAdvance on_refuted = backtrack_advance::Exclude{};

        // Implicit bridge from a bare condition: an existing branch generator that
        // yields IntegerVariableConditions keeps compiling and, defaulting to
        // Exclude, keeps its proof byte-identical. This is the whole compat story
        // for hand-written branchers.
        BranchDecision(IntegerVariableCondition c) : guess(c) {}
        BranchDecision(IntegerVariableCondition c, BacktrackAdvance a) : guess(c), on_refuted(a) {}
    };
}
```

`BacktrackConstraint` — the node's *standing* fact, as opposed to a single
decision's advance — is the framework's internal fold of the advances seen so far,
and does **not** need to be a public type:

```cpp
namespace gcs::innards
{
    // The weakest constraint proven to hold at this node given every sibling tried
    // so far is refuted, under the current guesses. Folded from BranchDecision
    // advances as the framework refutes siblings. Lives at Current; a restart's
    // forget wipes it.
    struct BacktrackConstraint final
    {
        // Kind inferred from the advances: all-Exclude => ExcludedSet (today's
        // ~guesses); a Lower/UpperBound advance switches it to a monotone Bound on
        // that variable, carrying the current frontier threshold.
        std::variant<
            std::monostate,                                  // ExcludedSet (default / empty)
            std::pair<SimpleIntegerVariableID, Integer>>     // Bound: (var, frontier threshold)
            state = std::monostate{};
        bool is_lower = true;                                // meaningful only in the Bound arm
    };
}
```

### The per-node object: a generator, not a virtual class

The sketch drew `Brancher` as a virtual class with `next()` +
`initial_backtrack_constraint()`. The real per-node object today is a coroutine
`std::generator<IntegerVariableCondition>` (`search_heuristics.hh:63`,
`solve.hh:65`). Per Decision 1, keep the coroutine model and only widen its yield
type:

```cpp
namespace gcs
{
    // The per-node object. Yields the node's decisions, each carrying how the
    // node's backtrack constraint tightens if that decision's subtree is refuted.
    // A coroutine, exactly as today — no per-node vtable, no virtual dispatch in
    // the hot loop; a stateful brancher's state lives in the coroutine frame just
    // as it does now.
    using BranchCallback = std::function<std::generator<BranchDecision>(const CurrentState &, const innards::Propagators &)>;

    using BranchValueGenerator =
        std::function<std::generator<BranchDecision>(const CurrentState &, const innards::Propagators &, const IntegerVariableID &)>;
}
```

`initial_backtrack_constraint()` is not a separate method: the node's constraint
is *derived* by the framework from the advances it folds, so a generator that
yields only `Exclude` decisions reproduces today's ExcludedSet node byte-for-byte
with no extra protocol. This is strictly less machinery than a two-method virtual
class whose second method's answer is a function of the first, and it keeps
`Custom` expressible.

The one cost against the virtual-class alternative: the generator cannot be
*asked* its standing constraint out of band — it only tells the framework via the
decisions it yields. That is fine for Lower/Upper/Exclude (folded mechanically);
it only bites a hypothetical brancher that wants a node-level constraint
independent of any decision, which is exactly the `Custom` escape hatch. If such a
consumer ever lands, a virtual `Brancher` alias can be added alongside — the two
are not mutually exclusive. Ship the generator form now (Decision 1).

`branch_with`, `branch_sequence`, and every `variable_order::` / `value_order::`
factory keep their **exact signatures** — only the yield type inside
`BranchValueGenerator` / `BranchCallback` changes.

### Helpers

The sketch's `frontier_ascending()` / `bisect()` / `excluded_set()` are thin tags
applied inside the existing value_order coroutines. They are not new public entry
points; they are how each `value_order::` factory declares its advance:

```cpp
namespace gcs::value_order::detail
{
    // Tag a d-way / two-way ascending value branch: each refutation advances the
    // lower-bound frontier over the variable (jumping any holes) via the verified
    // guess-reasoned RUP. `var` is the branch variable.
    [[nodiscard]] auto frontier_ascending(IntegerVariableID var) -> BacktrackAdvance;   // = LowerBound{var}
    [[nodiscard]] auto frontier_descending(IntegerVariableID var) -> BacktrackAdvance;  // = UpperBound{var}

    // Bisection (split_*): the single order-atom split is a LowerBound (lower half
    // first) or UpperBound (upper half first) advance; identical to the above but
    // named for the split call sites.
    [[nodiscard]] auto bisect_lower(IntegerVariableID var) -> BacktrackAdvance;         // = LowerBound{var}
    [[nodiscard]] auto bisect_upper(IntegerVariableID var) -> BacktrackAdvance;         // = UpperBound{var}

    // The default: accumulate ~guess. Nothing new emitted.
    [[nodiscard]] auto excluded_set() -> BacktrackAdvance;                              // = Exclude{}
}
```

A new brancher is then: yield `IntegerVariableCondition`s as today, and where it
is a monotone bound, yield `BranchDecision{cond, bisect_lower(var)}` instead of
the bare `cond`. Everything else (consolidate, hoist, delete) is the framework's.

## Mapping the existing value orders

Which atom a value order branches on — the **eq atom** or the **order atom** —
decides how its advance deletes. There are two wins, and they are different
mechanisms: the split family wins by a bound *jump* over holes; the contiguous eq
family wins by being *O(1)-resident* via the eq window. Read against the real
`value_order` coroutines (`search_heuristics.cc`), the final mapping is:

| value_order (real code) | branches on | monotone frontier? | advance | deletable? |
|---|---|---|---|---|
| `split_smallest_first` (`var <= v` / `var > v`) | **order atom** `ge(v+1)` | yes (lower) | `LowerBound` — jump | **yes — one ge pin** |
| `split_largest_first` (`var > v` / `var <= v`) | order atom `ge(v+1)` | yes (upper) | `UpperBound` — jump | **yes** |
| `split_random` | order atom `ge(v+1)` | yes | `LowerBound` — jump [1] | yes |
| `smallest_first` (`==v`, ascending) | **eq atom** `eq(v)` | yes (lower) | `LowerBound` **+ windowed eq** | **yes — O(1) resident, via the window** |
| `largest_first` (`==v`, descending) | eq atom | yes (upper) | `UpperBound` **+ windowed eq** | **yes** |
| `smallest_in` (`==lb` then `!=lb`) | eq atom | yes (lower) | `LowerBound` **+ windowed eq** | **yes** |
| `largest_in` (`==ub` then `!=ub`) | eq atom | yes (upper) | `UpperBound` **+ windowed eq** | **yes** |
| `smallest_out` (`!=lb` then `==lb`) | eq atom | — (reject-first) | `Exclude` [2] | no |
| `largest_out` (`!=ub` then `==ub`) | eq atom | — (reject-first) | `Exclude` [2] | no |
| `median` (`==m` / `!=m`) | eq atom | no | `Exclude` | no |
| `random`, `random_out` | eq atom | no | `Exclude` | no |
| `reject_random_interval` (`not_in_range` / `in_range`) | **invar atom** | no (disjunctive) | `Exclude` [3] | no |

Why the eq family splits the way it does:

- **`LowerBound`/`UpperBound` + windowed eq** — `smallest_first`, `largest_first`,
  `smallest_in`, `largest_in`. Each refutes `x == frontier` and advances the
  frontier by one; the window applies exactly. There is *no gap to jump* in
  contiguous ascending eq (refuting `x == lb` moves the frontier from `lb` to
  `lb+1`, with only the two ges the eq atom already pins in between), and an eq
  atom's permanent Top definition pins **both** `ge(v)` and `ge(v+1)`
  (`hoist_ges_named_by_top_atom` → `EqHoist`; the measured 44.2% `eq_hoist` on
  seat-moving). The window does **not** try to jump gaps — it deletes *behind* a
  one-step frontier, evicting each `eq(v)`/`ge(v)` once the frontier has stepped
  past it, bounding the permanent proof objects per branched variable from
  O(domain-width) to O(1). That is the win, and it is driver-backed (see "The
  eq-atom window").

- **Stay `Exclude`** — `median` / `random` / `random_out` refute a *non-boundary*
  value, so the frontier does not move and there is no "behind" to delete;
  `smallest_out` / `largest_out` are reject-first and never establish the sibling
  refutation the advance needs; `reject_random_interval` mints an **invar** atom
  (partition machinery, `InvarHoist`) and is genuinely disjunctive.

Net: `LowerBound`/`UpperBound` are wired for `split_*` (jump) and for the four
contiguous eq orders (windowed); everything else is `Exclude`. This is the honest,
search-preserving mapping. The framework must **never** silently swap an eq guess
for an order guess to manufacture a win — that changes propagation strength and
therefore search.

Footnotes:

1. **Fixed upstream; the note is kept for history.** `split_random_value_generator`
   used to have *identical* then/else arms — both yielding `var > v` then
   `var <= v` regardless of the coin flip, making it effectively
   `split_largest_first`. That was filed as issue #568 and fixed upstream in
   `e8befc17` ("make split_random actually pick a random half"), which this branch
   picked up when it rebased onto `3800424f`. The mapping was unaffected either way:
   the advance is derived from the *yielded condition*, so both arms tag correctly
   whether or not they differ.

2. `smallest_out` / `largest_out` are **likely foldable**, but as their own small
   design, not this one: refuting the reject-first sibling (`x != lb` first)
   COMMITS `x == lb` rather than *advancing a frontier*, so the eq window's
   advance-and-evict does not apply directly. There is no known application, so
   this is recorded as deferred future work rather than built.

3. `reject_random_interval` is the natural first consumer of a future first-class
   `ExcludedInterval` / disjunctive advance kind (see Deferred / future work). Map
   it to `Exclude` for now.

## The eq-atom window

The mechanism that makes the four contiguous eq orders win. Audited (window closes
cleanly at assertion Off; one scoping caveat, eq⨯interval) and driver-validated
(8/8 in VeriPB 3.0.2, including the load-bearing eq-def-traversal control). The
advance is emitted by **the framework** (`solve.cc` + `ProofLogger`), never the
brancher — the same framework/brancher split the split family uses; branchers only
declare `LowerBound`/`UpperBound`, and the mode gate makes it inert under `None`.

Grounding facts the window rests on:

- For a Bits variable with **only** eq atoms, the sole Top-resident thing naming
  `eq(v)` is its two `red` def lines; the containment/partition pins are inert
  (they need a `containment_tree` / `interval_partition`, created only by
  `need_invar`). So the window closes cleanly for pure eq branching.
- The advance `rup <guesses> ge(v+1)` is RUP through `eq(v)`'s **reverse
  reification** and is genuinely load-bearing — driver control D2c rejects when
  that reverse def is deleted before the advance.
- VeriPB polices a stranded ge only at a **point of use** (D4c rejects, D4c-silent
  is tolerated), so ge-under-eq residency is a solver-side invariant, not a
  checker-enforced one.

### Mint-time lifetime tagging (the narrow API)

Today `need_direct_encoding_for` hardcodes the eq def at `ProofLevel::Top`
(`names_and_ids_tracker.cc:672`), unlike `need_gevar`, which already chooses
`Current` vs `Top` from `def_at_current`. The window gives the eq path the same
choice, **gated so ordinary `need_proof_name` callers are oblivious** — a scoped
RAII guard set by the branch layer around the guess mint only:

```cpp
// NamesAndIDsTracker — RAII, set by the branch layer around the guess mint only.
struct WindowedEqScope {                       // ctor sets _imp->minting_windowed_eq = true
    explicit WindowedEqScope(NamesAndIDsTracker &); ~WindowedEqScope();
};
```

`need_direct_encoding_for` reads `minting_windowed_eq` exactly where `need_gevar`
reads its residency inputs: when set (and Literals mode / `AssertionLevel::Off` —
the same pairing every existing Literals-machinery guard uses / real Bits var /
not a bound / not eq⨯interval — see the guard below) it emits the two eq def lines at
`ProofLevel::Current` and records the atom in a new live-eq index, instead of Top.
**Every other caller** — propagator reasons, reified constraints,
`need_pol_item_defining_literal` — runs with the flag clear and gets today's
byte-identical Top behaviour. This meets the owner's bar: only the guess/mint path
knows about lifetimes. (A tagged
`need_direct_encoding_for(id, v, Lifetime::Windowed)` overload is equivalent but
threads the tag through more call sites; the scoped guard keeps the surface to one
RAII object set in `solve.cc`'s branch loop, where the guess is made.)

### The per-iteration tidy sequence

For an ascending window step refuting `x == v` (standing bound `x >= v`), landing
at the sibling's backtrack level `L`; this order **verifies as `d1_main.pbp`** and
the marked orderings are load-bearing:

1. Mint frontier `ge(v+1)` (Current) + chain link to the current live lower
   neighbour (`make_pol_chain`).
2. Mint `eq(v)` (Current, windowed): **reverse reification first, then forward** —
   the reverse must exist when the forward's `red` witness is checked (fresh-atom
   order). **[ordering constraint 1]**
3. Emit the sibling refutation `~guesses | ~eq(v)` (the generalised
   `ProofLogger::backtrack`; in the solver this is RUP from the still-live child).
4. **Advance** `rup <guesses> ge(v+1)` — RUP through {standing `~g | ge(v)`,
   sibling `~g | ~eq(v)`, `eq(v)` reverse-reif}. Must come **after** steps 2/3 and
   **before** any deletion of `eq(v)`'s reverse reif. **[ordering constraint 2 —
   this is exactly what driver control D2c violates and VeriPB rejects.]**
5. **Hoist** the new frontier `ge(v+1)` to `L` (existing
   `hoist_live_order_literals_toward_level`), so the standing advance never names a
   to-be-deleted literal.
6. **Tidy** (all `del id`, derived/unchecked): the superseded previous advance
   `~g | ge(v)`; `eq(v)`'s two def lines; **the sibling `~g | ~eq(v)` — it named
   `eq(v)`, so it must go for the atom to be fully unreferenced** (this is *not* in
   the naive "delete eq def + ge def" list, and is required for full eviction; see
   the tidy note below); the stepped-over `ge(v)` def + its dangling chain link.
   Then **re-stitch** `ge(v+1)` to its surviving lower neighbour.

**[ordering constraint 3 — stitch vs delete]** re-stitch *after* deleting the
dangling links, at the surviving neighbour's level, exactly as
`forget_order_literals_at_level` already does for the ge case. In pure ascending
branching the surviving lower neighbour is always the true boundary `ge0`, so this
stitch is trivial (`rup 1 ge0 1 ~ge(v+1) >= 1`); a non-trivial `make_pol_chain`
stitch arises only around a *hoisted-out* interior ge (below).

Tidy note (**the sibling-clause deletion**): the tidy must delete the sibling
`~g | ~eq(v)` for full eviction, because it names `eq(v)`. The naive "delete eq
def + ge def" list omits it; it is confirmed necessary and safe in `d1_main.pbp`,
and is called out here so it is not forgotten in the implementation.

Steady state after each tidy is the design's target: **one boundary `ge0` + one
frontier `ge` + one standing advance clause live** (plus, mid-iteration, one eq
def). Descending (`largest_first` / `largest_in`) is the `UpperBound` mirror
(`x == ub`, advance `x < ub` i.e. `~ge(ub)`), mechanically symmetric; the driver
validated the ascending direction only (see Implementation gates).

### The hoist-out rule for permanent references

Unchanged from the design's deletion rule ("delete only when unreferenced; hoist
otherwise"), applied to eq atoms: if `eq(v)` acquires a **permanent (Top)
reference** — a solx blocking clause, a learned-nogood decision literal, or a
reified-constraint use that names `id == v` — then at tidy time `eq(v)` is **not
evicted**; instead it and the two ges it names are hoisted to Top, exactly as
`hoist_ges_named_by_top_atom` already does for the ges, plus a new
`hoist_eq_to_top`. The window then evicts `eq(v)`'s **neighbours** normally and
stitches the chain **around** the retained interior ges (the genuine
`make_pol_chain` case — driver D4, `ge3 -> ge2`). Detecting "has a permanent
reference" reuses the residency-cause bookkeeping the design already mandates for
the ge/soli case. VeriPB will not catch a wrongly-evicted referenced ge except at
a point of use (D4c vs D4c-silent), so this is a solver invariant, not something
the checker enforces.

### Bookkeeping mirrors

**The storage moved.** Since the rebase onto `3800424f`, `variable_conditions_to_x`,
`gevars_that_exist` and `eqvars_that_exist` are gone: conditions resolve through
per-variable `VariableAtoms` tables holding the atom literals (`eq` / `ge` / `in`,
**positive polarity only** — the negative op is the flip, resolved in `find_condition`)
alongside their defining lines (`eq_defs` / `ge_defs`), keyed by raw value. The one
remaining ordered structure is `Imp::gevar_values`, the per-variable set of ge thresholds
the chain walk iterates — distinct from `live_order_literals`, which is the *currently
resident* subset. An eq eviction mirrors the ge eviction's
`ge_defs` / `live_order_literals` / `order_literals_by_level` triple:

- `atoms_for(id).eq_defs.erase(v.raw_value)` — drop the **definition lines only**.
- **Retire `atoms_for(id).eq[v]` into a `retired_eq` table, mirroring what the ge side now
  does** (owner decision, 2026-07-29, revised the same day once the ge side proved it out).
  Do *not* leave the atom in place and track liveness separately, and do *not* erase it
  outright and let it re-mint.

  Retiring is what makes the naming rule self-enforcing: an atom absent from the lookup
  table makes `find_condition` return `nullopt`, which is exactly the trigger
  `xliteral_for_ensuring` already acts on, so no mode-specific special case is needed and
  the const `xliteral_for` throws rather than rendering a stale name. Keeping the retired
  `XLiteral` and taking it back on re-introduction is what keeps identity stable: a fresh
  `allocate_xliteral_meaning` would render as the same verbose name but as a different
  `x<n>` with `set_verbose_names(false)`, making proof semantics depend on a rendering flag.

  Follow the two traps the ge side hit (see
  [order-encoding-deletion.md](order-encoding-deletion.md), Implementation status):
  `eq_defs` keeps its entry and the re-introduction must `insert_or_assign` its refreshed
  line numbers, because `need_pol_item_defining_literal` resolves pol operands through
  them; and there is no aliased-atom exception to carve out, since #554's fix removed the
  aliasing that motivated one. A DirectOnly `{0,1}` variable's `eq_defs` entries do still
  hold `XLiteral`s rather than `ProofLine`s (`track_eqvar`), so an eq eviction must skip
  those, as the ge hoist does via `get_if<ProofLine>`.

  `reintroduce_eq_literal` is therefore **not** needed: `need_direct_encoding_for`'s
  existing guard becomes the re-introduction path for free, exactly as `need_gevar`'s did
  once `reintroduce_order_literal` was deleted.
- A DirectOnly `{0,1}` variable's eq entries hold `XLiteral`s, not `ProofLine`s
  (`track_eqvar`, from `proof_model.cc`), so eviction must skip them — exactly as the ge
  hoist filters on `get_if<ProofLine>` and `order_literal_aliased_to_bit` skips aliased
  re-introduction.
- Whatever the eviction does, it must not break the naming invariant recorded in
  [order-encoding-deletion.md](order-encoding-deletion.md) (Implementation status): every
  path that names a literal in an emitted line has to go through the re-introduction hook.
- **New `live_eq_literals` + `eq_literals_by_level`** (mirroring
  `live_order_literals` / `order_literals_by_level`): a per-level index of windowed
  eq defs, so a backtrack `forget` deletes the right eq def lines and an eviction
  can find and retag an atom. `forget_order_literals_at_level` gains an eq sweep
  (or a sibling `forget_eq_literals_at_level`), called from the same
  `forget_proof_level` funnel.

  **As implemented in B'**, with one deliberate asymmetry: these hold **only windowed
  (deletable) eq defs**. Absence means "permanent, resident forever", which is what every
  eq atom outside a window is — so both structures stay empty until something windows a
  variable, and the index costs nothing on the eq-heavy instances whose eq atoms are not
  branched on. (`live_order_literals` cannot do this: it records level-0 ge thresholds
  because the chain walk and the stitch need them.) `forget_eq_literals_at_level` and
  `forget_chain_lines_at_level` both hang off the same `forget_order_links_at_level`
  funnel, after the ge sweep — which is what emits the level's stitches, and those land at
  a *surviving* neighbour's level, never at the level being forgotten.

  The producer of a windowed def is a defaulted argument,
  `need_direct_encoding_for(id, v, EqAtomResidency::Windowed)`; `Permanent` is the default
  and what every caller in the solver passes, so B' changes no emission. The request is
  honoured only where a deletable def is meaningful (Literals, proof-time, assertions off,
  real variable) and, per **(i-static)** below, is refused for a variable that already has
  an interval partition or a containment tree — that half of the eq⨯interval guard is
  cheap enough to ship with the primitive rather than with the window. B'' replaces the
  argument with the variable's `WindowedEqScope` tag; until then it exists so
  `hoist_eq_to_top` and the eq forget sweep have a producer to be VeriPB-checked against
  (`order_evict_test`).

### WindowedFrontier vs FrontierExempt, and the chain gate

The chain gate (`order_encoding_deletion_min_chain`) keeps *short-chain
non-frontier* variables resident to avoid stitch churn with no win. A windowed eq
variable is a **frontier** variable by construction, so it must not be held
resident by the gate — or the window degenerates to the baseline (every eq stays
Top, O(width) again). The windowed-eq lifetime tag therefore takes **priority over
the gate** in `need_gevar`'s residency ladder: insert a new lowest-structural
reason `WindowedFrontier`, checked *above* the gate (so a windowed var's interior
ges are deletable regardless of chain length) but *below* the structural pins
(boundary / aux / view) and below a genuine permanent reference (hoist-out). The
gate keeps its job for the **non-frontier short-chain tail**
(crystal_maze / talent eq atoms that are *not* branched on), which the window
never touches.

This composes with payload 3's `FrontierExempt` (below) as its exact opposite:
`FrontierExempt` says "resident *despite* being frontier" (the churn-regime
objective); `WindowedFrontier` says "deletable *because* frontier" (the win-regime
eq branch). They are the two opposite frontier policies and only the frontier
owner (branch layer / objective owner) can pick which applies. They never apply to
the same variable, so they sit as sibling slots just above the gate.

### The one hidden pin — eq⨯interval (bidirectional guard)

A windowed eq variable that *also* receives an `in`/`not_in` interval literal has
its live eq atoms retro-pinned as `Top` partition singleton cells
(`init_interval_partition` / `define_plain_invar` walk the variable's `eq_defs` table),
holding the window open. Ascending eq branching alone never does this, but a
constraint on the same variable might. The guard must be **bidirectional**
(supervisor correction):

- **(i-static)** `WindowedEqScope` refuses to window a variable that already has an
  `interval_partition` — conservative: eq stays Top, correct, no win.
- **(i-dynamic)** if an interval literal is requested mid-search on a
  currently-windowed variable, `init_interval_partition` would build Top singleton
  cells naming eq defs that live at Current — a Top-discipline violation that
  rejects at the next backtrack — so the partition path must first **collapse the
  window** (hoist-out every live windowed eq def + its ges to Top, the existing
  hoist-out mechanism run wholesale) and only then build the partition; the
  variable is thereafter unwindowed.

Both are recommended for step 2, flagged as a future extension. The alternative —
the window managing partition coverings on evict — stays out of step-2 scope. This
is the single scoping caveat the audit surfaced.

## Ownership and lifecycle

- **`BranchHeuristic` (per-search setup)** — unchanged. `solve_with` calls it once
  after propagators are final (`solve.cc:351-353`) and reuses the returned
  `BranchCallback` at every node. `dom_wdeg`'s conflict-observer attachment, the
  RNG `shared_ptr` sharing, all unchanged.
- **The per-node generator (the "Brancher")** — created per node by
  `branch_callback(state.current(), propagators)` (`solve.cc:118`), lives for that
  node's branch loop, destroyed when the loop ends. Same lifetime as today's
  generator; its coroutine frame holds any per-node state (RNG draws, the split
  point). **No per-search or per-solve Brancher object** — the standing
  `BacktrackConstraint` is a stack local in `solve_with_state`, born and folded
  within one frame.
- **State across restarts** — nothing to carry. The `BacktrackConstraint` and the
  advance RUPs live at `Current`, so the restart `forget` wipes them and the next
  pass re-runs the generator and re-derives them. The only cross-restart coupling
  is learned nogoods (below).
- **The `guesses` vectors.** Two distinct vectors; step 2 must not conflate them:
  - `solve.cc`'s local `Literals guesses` (`solve.cc:97-111`) is the **propagation
    seed** only (this_branch_guess + the B&B objective bound). The brancher never
    touches it. Under the objective exemption the B&B bound still seeds propagation
    exactly as today.
  - `state.guesses()` — the full decision stack — feeds `backtrack()`
    (`solve.cc:263-265`) and nogood learning (`solve.cc:236-240`). Under `Exclude`
    this is unchanged. Under a `Bound` node, the frame's terminal lemma is the
    standing bound rather than `~(state.guesses())`.
  - The **reduced nld-nogood prefix** (`solve.cc:180-195`) and its negative-flip
    detection (`guess == ! *first_sibling`) operate on `BranchDecision.guess`
    (still an `IntegerVariableCondition`), so they are untouched: a split node's two
    siblings `var <= v` and `var > v` are still exact negations (`operator!`,
    `variable_condition.hh:245`), the flip is still detected, and the prefix still
    drops the second sibling.
- **The existing hoist call sites — which move, which stay:**
  - `ProofLogger::backtrack` (`GuessHoist`) — **stays**, generalised: under a
    `Bound` node the framework emits the advance-derived bound instead of the
    `~guesses` clause. Under `Exclude` it is verbatim today's code.
  - `ProofLogger::emit_learned_nogood` (`NogoodHoist`) — **stays verbatim**.
    Nogoods still hoist their decision literals to Top so they survive the restart
    forget.
  - `ProofLogger::solution` (`SoliHoist`) — **stays, and gains the payload-2
    lifecycle**: it still hoists the incumbent threshold to Top, and now also records
    the improvement-constraint id and, on the *next* incumbent, delcs the superseded
    one and evicts the stale threshold.
  - `hoist_ges_named_by_top_atom` (eq/invar, `EqHoist`/`InvarHoist`) — **stays
    verbatim**. Independent of branching. (`hoist_eq_to_top`, above, is its eq-atom
    sibling for the window's hoist-out.)
  - The **new** advance-RUP + frontier-hoist + delete-behind is the one genuinely
    new call site, driven from `solve_with_state`'s branch loop.

## The framework's proof duties

Per node, in `solve_with_state`'s branch loop (`solve.cc:182-207`). "The framework"
= `solve.cc` + `ProofLogger`; branchers never write raw VeriPB.

**Mode gating (load-bearing).** The advances are *declared* always but *acted on*
(proof-wise) only under `OrderEncodingDeletion::Literals`. Under `None` (the
default) a `Bound` advance is treated exactly like `Exclude`: no advance RUP, no
hoist, no delete — the frame emits `backtrack(state.guesses())` as today. This is
what keeps flag-off byte-identity true even after the bound advances are wired.

Per node, for each `BranchDecision d` the generator yields:

1. Guess `d.guess`, recurse (unchanged: `new_epoch` / `state.guess` / recurse /
   `state.backtrack`).
2. If the child subtree completed (was refuted), **fold the advance** into the
   node's `BacktrackConstraint`, and — under Literals, for a `Lower/UpperBound`
   advance only — perform **consolidate → hoist → delete**:
   - **Advance RUP.** Emit the guess-reasoned bound jump
     `rup <state.guesses()> (var >= H) >= 1` (resp. `var < L`), where `H` is the new
     frontier = the next live threshold above the refuted region. This is the
     verified foundation (`order_jump_check`); VeriPB re-derives the holes from the
     guesses and climbs the chain. One `.pbp` line. (For the windowed eq case the
     one-hole analogue climbs through `eq(v)`'s reverse reif, per the tidy sequence.)
   - **Hoist** the new frontier literal `ge(H)` to the advance's level (so the
     backtrack constraint never names a to-be-deleted literal), via
     `hoist_live_order_literals_toward_level`.
   - **Delete** behind the frontier: the ges the advance stepped over that no
     surviving constraint names. This is *already* what the child's
     `forget_proof_level(depth+1)` + `forget_order_literals_at_level` do; the new
     advance RUP is what lets those deletions keep exactly one hoisted frontier ge
     instead of relying on the incidental guess-hoist. The deletion rule is
     unchanged: delete only when unreferenced, hoist otherwise; the backtrack
     constraint's named literal is the one surviving reference.
3. When the generator is exhausted (`next() == nullopt`), the standing
   `BacktrackConstraint` is the node's refutation lemma:
   - **ExcludedSet** → emit today's `backtrack(state.guesses())` verbatim.
   - **Bound** reaching past the domain (`H > ub` / `L < lb`) → the bound is a
     contradiction under the variable's bound axioms, which is the refutation; it
     subsumes the `~guesses` clause (the frontier reaching `ub+1` IS the
     at-least-one closure). Emit the terminal advance RUP at the frame's backtrack
     level in place of `backtrack(state.guesses())`.

**The exact proof level of the advance RUP and the frontier hoist is the one
delicate mechanic.** The child frame has already emitted its own backtrack clause
at `depth+1` and forgotten `depth+2` before control returns; the advance must land
where it both (a) reasons from the still-live guesses and (b) survives to drive the
next sibling / close the node. The anchor is `order_jump_check` (verified at wide
gaps). The design does not pin the level here beyond "reasoned from
`state.guesses()`, landed at the sibling's backtrack level" — stage B validates it
empirically against VeriPB with `MIN_CHAIN=0` (see Implementation gates).

**The chain gate survives, with a narrowed role.** The gate was a *blanket*
no-harm floor: keep short chains resident so propagation-strong models pay no
churn. Post-refactor:

- The advance model makes a bound-branched variable's frontier explicitly monotone
  within the node, so there is no reintroduction churn along the advancing frontier
  itself.
- The 2b churn the flat gate could not kill — concentrated on the
  always-bound-tightened objective/cost — is removed precisely by the payload-3
  exemption (which the gate cannot express: it is length-based, and the objective's
  chain is only ~98 long, well inside any win-preserving gate).
- But the gate still guards the **long tail of short-chain non-frontier variables**
  on eq/small-domain models (crystal_maze, talent), where deletion emits stitch
  churn with no win and which no advance or exemption covers (they are not frontier
  variables). There the gate is the only thing that makes the feature
  strictly-no-harm (measured: gate 16 → crystal_maze byte-identical to `None`).

So the gate stays; its job narrows from "cover all churn" to "cover the non-frontier
short-chain tail," with the exemption taking the objective/cost churn it never
handled well. Gate, `FrontierExempt`, and `WindowedFrontier` compose as residency
reasons in `need_gevar` (the exemption and the windowed tag are both checked *above*
the gate).

## Objective handling

Two independent mechanisms, both under the Literals flag, both new in step 2, both
adopted per Decision 3.

### Where incumbent state lives

Today the objective is a `min:` line in the OPB (`proof_model.cc:626`); there is
**no** model-time improvement constraint. Each improving solution emits, in
`ProofLogger::solution` (`proof_logger.cc:227-237`), a permanent `Top` RUP
`~ge(incumbent) >= 1` (the improvement constraint) after the `soli`, and hoists
`ge(incumbent)` to Top (`SoliHoist`, `proof_logger.cc:211-217`). Over an
optimisation descent this accumulates **O(#incumbents)** resident unit clauses plus
O(#incumbents) Top-pinned thresholds. Payloads 2 and 3 convert this to O(1)
resident.

`solution()` gains a small **incumbent record** (in `ProofLogger::Imp`, or threaded
from the tracker):

```cpp
struct IncumbentRecord {
    Integer value;             // the incumbent objective value
    ProofLine improvement_line; // the Top RUP `~ge(value) >= 1` just emitted
};
std::optional<IncumbentRecord> last_incumbent;   // per objective, per solve
```

Today `emit_rup_proof_line(... id < value ...)`'s return is discarded
(`proof_logger.cc:235`); the `soli` improvement constraint lands in **core** at the
next sequential ID (`IDmax+1`), which is exactly the ID to capture here.

### Payload 2 — delc the superseded improvement constraint + evict its threshold

When solution `k+1` lands (value `v' < v`, minimisation), `solution()`:

1. Emit the new `soli`, hoist `ge(v')` to Top, emit the new improvement constraint
   `~ge(v') >= 1` (as today), and set `last_incumbent = {v', line'}`.
2. **Delc the old improvement constraint** `~ge(v) >= 1`. It is implied by the new
   one plus the resident order chain: `v' < v` gives the chain link
   `ge(v) → ge(v')`, so `~ge(v')` (the new unit) RUP-derives `~ge(v)` (the old
   unit).
3. **Evict `ge(v)` from Top** — the new evict-from-Top primitive (below), *iff* the
   residency bookkeeping says the `soli` pin was `ge(v)`'s **only** Top cause. If
   `ge(v)` is also pinned by an eq atom, an invar atom, a nogood, or the objective
   exemption, it stays resident and only the improvement constraint is delc'd.

**Ordering is load-bearing:** delc the old constraint (step 2) *before* evicting
`ge(v)` (step 3), because the delc's subproof needs `ge(v)` and its chain link still
resident. This delc-before-evict discipline is a **solver-side invariant** — see the
validated mechanics below.

`-n 1` / find-first optimisation: only one incumbent is ever produced, so
`last_incumbent` is set once and payload 2 never fires — a clean no-op. Full
optimisation: fires on every improvement after the first. No objective (`solx`
enumeration, `--all`): `solution()` takes the `solx` path,
`optional_minimise_variable_and_value` is `nullopt`, and the whole of payload 2 is
skipped — the `blocking_sum` / `SolxBlock` path is untouched.

Interaction with `solution()`'s existing hoist: unchanged for the *current*
incumbent (still `SoliHoist` to Top so the fresh improvement constraint does not
name a to-be-deleted literal); payload 2 only adds the *retirement* of the *previous*
incumbent's hoist. Measured benefit is TBD and stated honestly: this converts
O(#incumbents) resident constraints to O(1), matching the "shrink the resident DB"
thesis, but its verify-time payoff is unproven until the stage-E optimisation sweep.

#### Validated delc mechanics (veripb 3.0.2)

The `delc` syntax and its obligations are validated against `veripb 3.0.2` (9/9
driver checks, independently re-run by the supervisor; see Provenance):

- **Autoproof form (the one to emit): `delc <id> ;`** — succeeds via veripb's RUP
  shortcut for the weaker-from-tighter implication (the empty witness fires the
  shortcut).
- **Explicit-subproof form (on record if ever needed):**
  `delc <id> : <witness> : subproof <goals> qed ;` with an empty witness; the negated
  deleted constraint is goal premise `-1`, discharged by a one-line
  `pol <new_bound_id> -1 +`.
- The `soli` improvement constraint lands in **core** at the next sequential ID
  (delc-able); `delc` on a *derived* constraint is rejected outright, so it cannot be
  misapplied to ge defs by accident.

Two load-bearing caveats:

1. **A failed `delc` autoproof without `-c` downgrades rather than rejects — but the
   downgrade is enforced at exactly the right conclusions** (owner-corrected,
   source-read, and empirically confirmed). The downgrade clears veripb's
   `strong_solution_guarantees`; thereafter solutions do not update the valid-witness
   bookkeeping, so a `conclusion BOUNDS` whose upper bound cites a post-downgrade
   solution **rejects** (confirmed: "claimed upper bound of 8 mismatches the best
   recorded upper bound of 12", no `-c`), an `ENUMERATION_COMPLETE N` with
   post-downgrade exclusions **rejects** on count mismatch (confirmed), and strong
   `output` guarantees (EQUIOPTIMAL/EQUISATISFIABLE/EQUIENUMERABLE) reject outright.
   Only UNSAT / no-solution conclusions — where deletion-weakened refutations remain
   sound — tolerate the downgrade, and those tolerated cases are in fact sound.
   **Consequence: veripb's defaults are sound-by-construction; `-c` is NOT a soundness
   requirement.** Still run `-c` (`--force-checked-deletion`) in suites and gates from
   stage D on, for a different reason: it fails fast AT the delc site (precise line)
   and catches a broken implication in GCS's emission logic even on proofs whose
   conclusions happen to remain checkable without it.
2. **veripb does not police eviction ordering.** Deleting the ge defs while the old
   improvement constraint still names the atom also verifies (defs are derived and
   redundant over the bits; rejection happens only at a later point of use). The
   delc-before-evict ordering is therefore a **solver-side invariant** — VeriPB
   acceptance is not evidence the discipline held.

These are two instances of the same fact — **VeriPB polices order-encoding soundness
only at a point of use, not at deletion** — and the solver-side invariants it will not
police are:

- **Eviction ordering** (delc the improvement constraint before evicting its ge).
- **ge-under-eq residency** (do not evict a ge a live Top eq atom names; the eq
  window's hoist-out rule).
- **Chain-clause deletion on evict** (leave no clause naming an evicted threshold).
  Added in stage B' once it was measured: a leftover clause stays *valid*, so the proof
  verifies and the only loss is the shrinkage. See "The evict primitive" below.

Both are exactly why the always-on residency-cause bookkeeping (below) is mandatory,
not optional.

### The evict primitive — mirror of hoist

**Implemented in stage B'.** Hoist moves a def *to* a level and stitches it *in*.
Evict deletes it and stitches the chain *over* it. As shipped:

```cpp
// NamesAndIDsTracker
// Delete v's two reification def lines and every chain clause naming it, stitch its
// surviving immediate neighbours lo,hi with a skip link ge(hi) -> ge(lo) (the run-stitch
// of forget_order_literals_at_level, run for one literal on demand, landing at the deeper
// neighbour's level exactly as there), drop v from live_order_literals and its level
// index, release its Top pin, and RETIRE its atom -- so a later need_gevar re-introduces
// it as a deletable interior literal and takes the retired XLiteral back.
// Returns whether it was evicted; a refusal emits nothing and changes nothing.
auto evict_order_literal(const SimpleIntegerVariableID & id, Integer v,
    std::optional<OrderEncodingResidencyCause> expected_sole_top_cause) -> bool;
```

Three deltas from the sketch this replaces, each for a reason worth keeping:

- **It retires the atom** rather than "leaving the atom and its `ge_defs` slot". The
  sketch predates `a15d5757`, which made the naming rule structural on the ge side;
  eviction is a second deletion path and must enforce it the same way.
- **It returns a bool instead of asserting.** The precondition is *checked*, so a
  caller whose bookkeeping disagrees with the tracker's gets a safe refusal (the
  literal stays resident, costing only the win) rather than an abort. `nullopt` is the
  mid-level (window tidy) case: a deletable literal has no Top pin by construction, so
  naming a cause for one is refused too.
- **It handles any level, not just Top**, because the window's per-iteration tidy
  evicts Current-level defs. Hence the name loses `_from_top`.

It **required the residency-cause bookkeeping to become always-on under Literals**,
not stats-gated (`ge_top_pins`; `stats_ge_top_cause` stays as the diagnostic's
first-cause-wins map, layered on top and still covering the born-Top structural
causes that never hoist). It also required a **single-line deletion API**,
`ProofLogger::delete_proof_lines_at_level`, which drops the lines from the level's
bucket as well as `del`-ing them: `forget_proof_level` ends a bucket's final interval
with a bare `del id`, and VeriPB errors on a `del id` naming an already-deleted line
(only `del range` skips them), so a line evicted from a level that is later forgotten
would otherwise be deleted twice.

**A third thing VeriPB will not police.** A chain clause left naming an evicted
threshold is still a *valid derived constraint* — it was derived from definitions the
atom's stable identity lets a later `need_gevar` restore, and re-introducing that
definition **verifies with the stale clause present** (measured by mutation against
veripb 3.0.2: the negated half of the reification forces the neighbour's atom through
its own definition, so the leftover clause is implied under the witness). So a missed
chain-clause deletion is silent and costs exactly the resident-DB shrinkage the mode
exists for. `chain_clauses_naming(id, v)` exists to make that postcondition
observable, and `order_evict_test` checks it in C++ — the third solver-side invariant
listed above, alongside eviction ordering and ge-under-eq residency.

The evict primitive has **two consumers**: payload 2 (evict a superseded soli
threshold) and the eq window's per-iteration tidy (evict a Current-level eq/ge def +
re-stitch). Its hoist-out path needs the same always-on residency bookkeeping. So the
primitive and the bookkeeping promotion were a shared stage B' (below), rather than
payload 2 owning them.

#### The Top-pin bookkeeping, and its two counter-intuitive rules

`ge_top_pins`: per real variable, per ge threshold, a per-cause refcount of the
permanent references pinning it at Top. Both rules were found by getting them wrong
first (2026-07-29), and both are checked by mutation in `order_evict_test`:

1. **Count at the reference site, not inside the hoist.**
   `hoist_order_literal_to_level` early-returns when the def is already at the target
   level, and `hoist_order_literal_to_top_if_live` early-returns at level 0 — so a
   second permanent atom naming an already-Top ge does no hoisting at all, and would
   record no pin. This is not a corner case: `eq(v)` and `eq(v+1)` both name
   `ge(v+1)`. First-cause-wins is right for a diagnostic and *fatal* for an eviction
   precondition, which is exactly a count.
2. **Only a ge whose Top residency a hoist caused gets an entry.** A hoist never
   fires on a level-0 ge, so "level 0 with no entry" means structurally resident
   (model-time / boundary / aux / view / gate) — never evictable, and needing no
   record. That keeps the map proportional to hoists rather than to the resident
   majority, and it is load-bearing in the other direction too: recording pins for
   structurally resident thresholds would make a *boundary* literal — a permanent
   chain anchor — look evictable.

A `GuessHoist` to level 0 deliberately takes no pin (it targets a positive level and
is not a permanent reference), which leaves such a literal looking structurally
resident. Eviction then refuses it: a lost win at worst, never wrong.

### Payload 3 — objective / frontier deletion exemption

The 2b finding: seat-moving's residual 20 784 delete/reintroduce churn at gate 16 is
concentrated on the **always-bound-tightened objective (chain 98) and cost (76)**
variables, which any win-preserving flat gate leaves deletable, and which churn
*verify-neutrally* (OFF 126.2 s ≈ L16 121.2 s) for **zero** shrinkage. The fix is a
per-variable **deletion-exempt** policy hook, consulted in `need_gevar`'s residency
decision:

```cpp
// NamesAndIDsTracker — model/solve-time note, like note_order_encoding_stays_resident.
// A variable exempted from Literals-mode deletion: every ge def stays resident at
// Top (tagged level 0), never churned. Populated by the frontier owner.
auto note_deletion_exempt(const SimpleOrProofOnlyIntegerVariableID & id) -> void;
```

In `need_gevar` (`names_and_ids_tracker.cc:841-896`) the residency priority becomes
**boundary > aux > view > exempt > gate**, with the eq window's `WindowedFrontier`
as `exempt`'s opposite-signed sibling (both just above the gate). The exempt check
sits just above the gate (a new `OrderEncodingResidencyCause::FrontierExempt`),
because an exempt variable is resident regardless of chain length but below the
structural pins that already force residency for their own reasons.

Who populates it:

- The **framework** exempts the **objective** — `solve_with` (or `model->minimise`)
  calls `note_deletion_exempt(objective_var)`, because `solve.cc` owns the B&B
  bound-tightening step (`solve.cc:100-111`) that makes the objective a
  perpetually-re-tightened, backtrack-relaxed frontier. This is the primary, measured
  case.
- Optionally, a **brancher** may designate a frontier variable it does not want
  churned (a bound brancher whose variable is re-touched by another mechanism). The
  `BacktrackConstraint`'s Bound arm names the variable, so the framework can offer
  `note_deletion_exempt` for it — but **not by default**: exempting a bound-branched
  variable defeats the split win (the win *is* deleting its stepped-over chain). The
  exemption is opt-in, for the churn-regime where a variable is bound-frontier *and*
  re-touched such that deletion churns without winning — the objective being the
  canonical instance.

This is why it belongs in the branch layer and not the flat chain gate: the gate is
length-based and cannot tell a **win-regime long chain** (a weak-prop split variable
— delete it) from a **churn-regime long chain** (the always-tightened objective —
keep it resident). Only the frontier owner knows which is which.

**Composition with payload 2.** If the objective is exempt, its ges are resident by
`FrontierExempt`, so payload 2's *ge*-eviction never fires for them (soli is not the
only cause) — but payload 2's *improvement-constraint* delc still fires and still
matters (those O(#incumbents) unit clauses exist regardless of ge residency). So the
two compose cleanly: **payload 3 owns the objective's ge residency; payload 2 owns
the improvement constraints.** The measured objective chain (median a dozen, max 98)
is short, so keeping it resident is cheap and the ge-eviction half of payload 2 buys
little on the objective — its value is for a future long-objective-chain regime or a
non-exempt configuration. Per Decision 3, ship both.

## Byte-identity: exactly what must not move

- **`None` mode, forever:** a `Bound` advance is inert (treated as `Exclude`); the
  proof is byte-identical to pre-step-2. Enforced by the mode gate in the branch
  loop.
- **`Literals` mode, stage A only:** every value order maps to `Exclude`, so the
  proof is byte-identical to the *current* Literals proof (forget-driven deletion +
  guess/eq/nogood/soli hoists, no advance RUP). The Brancher types and the yield-type
  widening are pure plumbing at stage A.
- Stages B onward deliberately change the Literals-mode proof (advance RUPs, windowed
  eq, delc, eviction, exemption) and are gated on **VeriPB-verifies +
  search-identical**, not byte-identity — except stage B', whose primitives are
  unused and which is itself byte-identical.

## Public-API compatibility

**Keeps compiling unchanged** (all real user code): `branch_with`,
`branch_sequence`, every `variable_order::` and `value_order::` factory,
`SolveCallbacks::branch`, and every in-tree consumer — the 18 examples,
`minizinc/fzn_glasgow.cc` (`indomain*` → value_order at 990-1007), `xcsp`, and the
two `BranchValueGenerator` *variables* (`order_deletion_bench:304`, `fzn:989`, which
merely hold a factory result). They all go through the factories, which keep their
signatures, and run byte-identically at stage A.

**Changes shape but not source for factory users:** the yield type inside
`BranchValueGenerator` / `BranchCallback` becomes `std::generator<BranchDecision>`
instead of `std::generator<IntegerVariableCondition>`.

**Needs a mechanical one-line migration (internal only):**

- The scripted-branching tests `range_witness_w{1,2,3}_test.cc` construct a
  `BranchCallback` by hand returning `std::generator<IntegerVariableCondition>`.
  Change the two return-type annotations to `std::generator<BranchDecision>`; the
  bodies (`co_yield var != 0_i;`) are **unchanged** thanks to the implicit
  conversion. Behaviour byte-identical (Exclude default).
- `gcs/presolvers/auto_table.cc` consumes `*branch_iter` and does
  `state.guess(branch)`; change to `state.guess(branch.guess)` (one line). It
  maintains no `BacktrackConstraint`, so it takes the `Exclude` path and its
  `logger->backtrack(guesses)` call is verbatim today.

Per Decision 2, this small, well-contained source break is accepted: a user who
hand-wrote a `std::function<generator<IntegerVariableCondition>(...)>` (none exist
in-tree, but the type is public) must change their coroutine's declared return type
to `generator<BranchDecision>`; their `co_yield cond;` bodies keep working via the
implicit conversion. This is a source break, not a behaviour break, and is better
than a permanent dual API (two branch protocols and two deletion-driving code paths
to maintain). The rejected fallback — keep `generator<IntegerVariableCondition>` as
the public yield type and carry the advance in a parallel side-channel — reintroduces
the "keep value order and consolidation strategy mutually consistent" hazard the
Brancher is meant to abolish.

## Migration staging

Every stage that exercises deletion runs with **`MIN_CHAIN=0`** (the aggressive
mode; tiny test domains never cross a nonzero gate), caps-off. "search-identical" =
recursions / propagations / solutions unchanged mode-off vs mode-on.

- **Stage A — Brancher types + plumbing (byte-identical; independently committable).**
  Add `BranchDecision`, `BacktrackAdvance`, the implicit conversion, the
  `BacktrackConstraint` fold (folding only `Exclude` so far); widen
  `BranchValueGenerator`/`BranchCallback` yield to `BranchDecision`; port every
  value_order to `Exclude`; migrate the three scripted tests + `auto_table`.
  **Oracle:** `.opb`/`.pbp` **byte-identical** to pre-change across the whole caps-off
  suite, in each of {`None`, `Literals` gate 0, `Literals` gate 16}. No VeriPB
  behaviour may move.

- **Stage B — split-family bound advances + advance-RUP-driven deletion (flag-gated;
  committable after A).**
  Tag `split_smallest_first` / `split_largest_first` / `split_random` with
  `Lower/UpperBound`; wire the framework's consolidate→hoist→delete + the
  terminal-bound backtrack lemma, Literals-only. **Oracle:** VeriPB verifies +
  search-identical at `MIN_CHAIN=0` across the suite; flag-off byte-identity preserved;
  re-run the synthetic split/UNSAT sweep (`order_deletion_bench --problem pairwise
  --domain D --window D --tightness 90 --unsat`, D ∈ {250,1000,2000}) and confirm the
  win is preserved vs the current forget-driven numbers. **This is the stage that
  validates the advance-RUP proof level against VeriPB.**

- **Stage B' (shared prerequisite) — residency-cause bookkeeping + evict/hoist
  primitives, always-on under Literals. DONE.**
  Shipped: `ge_top_pins` (the always-on per-ge Top-pin refcount, counted at the
  reference sites — see "The Top-pin bookkeeping" above); `chain_clauses_by_level` (the
  chain clauses currently in the proof, bucketed by level then variable, which eviction
  needs and nothing previously recorded);
  `evict_order_literal` (any level, refusing rather than asserting, retiring the atom);
  `chain_clauses_naming` (its postcondition, made observable because VeriPB will not
  police it); `hoist_eq_to_top`; `live_eq_literals` + `eq_literals_by_level` +
  `forget_eq_literals_at_level` + `VariableAtoms::retired_eq` (the eq analogue of ge
  retirement, so a windowed def's atom is retired on backtrack and re-introduced with
  its identity intact); `EqAtomResidency` on `need_direct_encoding_for` as the minimal
  producer of a windowed def; and `ProofLogger::delete_proof_lines_at_level`.
  **No behaviour change**: nothing in the solver evicts, windows an eq atom, or passes a
  non-default residency, so every emission is unchanged.
  **Oracle (met):** caps-off suite in each of {None, Literals gate 0, Literals gate 16};
  `None`-mode byte-identity vs plain main; the flag-ON seed sweeps; and a new
  VeriPB-checked driver, `gcs/innards/proofs/order_evict_test.cc` (mode and gate set in
  code, so it does not depend on the environment — and in particular runs at gate 0,
  which the shipped default of 16 would make vacuous). It covers mid-level evict,
  evict-from-Top under a sole pin, the three refusals (no cause / wrong cause /
  two-eq-atoms-pinning-one-ge), the structurally-resident (boundary) refusal,
  `hoist_eq_to_top` across a forget of the window's level, the eq forget sweep and
  identity-preserving re-introduction, and the bucket-erasure shape that would otherwise
  double-delete. Each of those was confirmed discriminating by mutation (8 of 9 mutations
  caught; the ninth — erasing a chain clause's record without emitting its `del` — is
  invisible to both VeriPB and the tracker, and was checked by reading the emitted
  proof). This is the shared foundation for both the window (B'') and payload 2 (D).

  **Cost.** The stage emits not one different byte — re-confirmed by `cmp` on both the
  `.opb` and the 15 MB `.pbp` of the d1000 synthetic, stage-A/B build against stage-B' —
  so `veripb` time cannot move. The solver's own proof-writing time does: the
  chain-clause index takes an insert per chain clause. On the deletion-heaviest
  synthetic (`order_deletion_bench`, pairwise, d1000, gate 0, pinned and solo) that is
  **+4.1 %** — 68.8 ms → 71.7 ms, best of ten runs each. Keying that index by variable
  and then by threshold pair instead cost +12.0 %, which is why it is bucketed
  level-first and flat. In end-to-end terms at d1000 the solver is ~0.07 s against
  `veripb`'s ~0.51 s, so the stage costs well under 1 % of the pipeline.

  **What B'' still owes on top of it:** the `WindowedEqScope` tag (replacing the
  `EqAtomResidency` argument), the per-iteration tidy that actually calls
  `evict_order_literal`, the **eq-side eviction** (B' ships only the eq *forget* sweep and
  `hoist_eq_to_top`; taking a windowed eq def out on demand needs the same
  `delete_proof_lines_at_level` + retire pair, with the `get_if<ProofLine>` filter for a
  DirectOnly `{0,1}` variable's `XLiteral`-valued `eq_defs`), the hoist-out rule's
  *detection* of a permanent reference (`hoist_eq_to_top` is the action, not the trigger),
  the `WindowedFrontier` residency slot in `need_gevar`'s ladder, the **(i-dynamic)** half
  of the eq⨯interval guard, and tagging `smallest_first` / `largest_first` /
  `smallest_in` / `largest_in`.

- **Stage B'' — the eq-atom window.**
  The `WindowedEqScope` tag, `need_direct_encoding_for` Current-emission, the
  per-iteration tidy, the hoist-out rule, the `WindowedFrontier` residency slot, and
  the bidirectional eq⨯interval guard. Tag `smallest_first` / `largest_first` /
  `smallest_in` / `largest_in` with `Lower/UpperBound`. **Oracle:** VeriPB verifies +
  search-identical at `MIN_CHAIN=0`; flag-off byte-identity preserved; resident eq/ge
  count per branched var is **O(1) not O(width)**; the driver-analogue behaviours
  (D1–D4) hold on a real enumerated-domain instance. Ships **default-off for eq orders**
  (Decision 5). **This stage re-confirms the real-solver eq advance level** (see
  Implementation gates).

- **Stage C — objective / frontier exemption (payload 3; flag-gated; committable).**
  Add `note_deletion_exempt` + the `FrontierExempt` residency cause + the `need_gevar`
  priority slot (now reusing B''s residency ladder; `FrontierExempt` and
  `WindowedFrontier` are sibling slots); `solve_with` exempts the objective.
  **Oracle:** VeriPB verifies + search-identical; on seat-moving 2018 the
  objective/cost churn (~20.8k delete/reintroduce at gate 16) drops toward 0 at no win
  cost on the synthetic sweep (the exemption must not touch non-objective wins).

- **Stage D — objective-improvement delc + Top-eviction (payload 2; flag-gated;
  committable). Reuses B''s evict primitive** rather than introducing it.
  Add the incumbent record + the delc + the evict call. **Oracle:** VeriPB verifies,
  with **`-c` (`--force-checked-deletion`) in suites and gates from this stage on** —
  not for soundness (veripb's guarantee machinery already rejects deletion-endangered
  sat/enumeration conclusions) but as a **fail-fast discipline**: `-c` errors at the
  delc site, catching a broken implication in our emission even when the conclusion
  would still check. Plus search-identical on an optimisation instance with many
  incumbents (colour, knapsack, seat-moving); resident improvement-constraint count at
  proof end **O(1) not O(#incumbents)**; `-n 1` and no-objective paths proven inert.

- **Stage E — benchmark + cleanup.**
  Re-run the eq-free large-domain sweep and the optimisation sweep for the step-2
  numbers; **measure the eq window on the eq-heavy instances (crystal_maze, talent)
  and the ascending-eq large-domain case to decide whether it becomes the default for
  `smallest_first`** (Decision 5's transient-for-permanent trade). Remove the dormant
  `OrderEncodingDeletion::Links` mode; rename `forget_order_links_at_level` /
  `live_order_links` and the `_links_`-named machinery the tracker header flags as
  "left unchanged until the planned Brancher refactor renames it."

Stages A, B, B', B'', C have no external dependency and can land in sequence. Stage D
is the only one gated on work outside this task (the delc mechanics, now validated),
and can be prepared ahead (it reuses B''s primitives) and finished once wired.

## Implementation gates (not owner calls)

Three unknowns; all are validated empirically against VeriPB, not decided by the owner.
Two are now resolved by the stages that owned them, and the remaining one belongs to
B'':

1. **Advance-RUP proof level (stage B). RESOLVED.** The exact level at which the
   split-family advance RUP and frontier hoist land, given the child has already
   emitted-and-forgotten its own levels. *Resolution:* settled empirically when stage B
   landed — the caps-off suite verifies at `MIN_CHAIN=0` with the split families tagged,
   and the synthetic split/UNSAT sweep preserves its win. Nothing about the level was
   taken on trust; the gate was the suite, not an argument.

2. **Real-solver eq advance re-confirmation (stage B'').** The eq analogue of gate 1.
   The driver commits the sibling `~g | ~eq(v)` via an order-hole `red` witness because
   it has no child subtree; the *solver* emits it as `ProofLogger::backtrack`'s RUP
   clause from the still-live child. The two produce the identical clause, but the real
   path's RUP must be re-confirmed once wired — specifically that hoisting the frontier
   `ge(v+1)` to `L` before the child `forget` leaves the advance RUP at `L`. Validate
   against VeriPB at `MIN_CHAIN=0`, with `order_jump_check` + `d1_main.pbp` as anchors.
   (The descending direction — `largest_first` / `largest_in`, the `UpperBound` mirror
   — is expected to verify by symmetry but was not driver-tested; confirm before
   shipping the descending orders.)

3. **Residency-bookkeeping promotion (stage B'). RESOLVED.** Eviction's "sole Top cause"
   precondition needs always-on per-ge cause tracking under Literals. *Resolution as
   shipped:* `ge_top_pins`, a per-cause refcount counted at the reference sites and only
   for hoisted thresholds (see "The Top-pin bookkeeping" for why each of those two
   qualifiers is load-bearing); the diagnostic's `stats_ge_top_cause` layers on top,
   unchanged. Eviction *checks* it and refuses rather than asserting, so a disagreement
   costs a win instead of aborting.

## Deferred / future work

- **`smallest_out` / `largest_out` folding.** Likely foldable, but as their own small
  design (the reject-first sibling COMMITS `x == lb` rather than advancing a frontier).
  No known application; deferred.
- **`reject_random_interval` and a first-class disjunctive advance.** It mints an invar
  atom and is genuinely disjunctive — the natural first consumer of a future
  `ExcludedInterval` advance kind. `Exclude` for now.
- **eq⨯interval option (ii)** — the window managing partition coverings on evict —
  stays out of step-2 scope; step 2 uses the bidirectional (i-static)+(i-dynamic)
  guard instead.
- **Virtual `Brancher` alias** — build only if a `Custom` consumer appears
  (Decision 1).
- ~~**`split_random` duplicated arms**~~ — was issue #568; fixed upstream in `e8befc17`
  and picked up by the rebase onto `3800424f`. Nothing left to do.

## Provenance

The design drivers, raw findings, and validated `.pbp` scenarios were produced in an
`order-encoding-deletion-artifacts/` scratch directory, outside this repository and
**not carried between development machines** — so treat the list below as a record of
what was checked and how, not as a path you can open. Anything load-bearing that a
later stage needs must be re-derived (the drivers are small and the findings say what
each one asserts) or promoted into `gcs/` as a real test, which is what stage E
schedules for `order_jump_check` / `order_hoist_check`.

- **`brancher-design/`** — `design.md`, the working design record this note
  consolidates (concrete C++ against the real code; the five owner decisions folded in).
- **`eq-window/`** — the eq-atom window: `audit.md` (code audit — the window closes
  cleanly at assertion Off, plus the eq⨯interval scoping caveat), `findings.md` (the
  8/8 VeriPB 3.0.2 driver, D1–D4 + the load-bearing D2c control), the `.pbp` scenarios
  (`d1_main.pbp` … `d4c_silent.pbp`), and `design-revision-draft.md` (the revision this
  note merges inline).
- **`objective-delc/`** — the `delc` / eviction mechanics: `findings.md` (9/9 driver
  checks, both `delc` forms, the `-c`/downgrade correction, and the "veripb polices only
  at point of use" result), the `q*.pbp` scenarios, and `run.sh`.

The same applies to the two verified foundations `order_jump_check` (guess-reasoned
bound jump + its two must-fail controls) and `order_hoist_check`, which were never
committed, and to the phase-2 real-instance campaign that motivated the objective
exemption and the chain gate. The campaign's headline figures have since been
re-measured from scratch — see
[order-encoding-deletion.md](order-encoding-deletion.md), "Results" — so those stand on
their own. Background: McIlree PhD thesis,
Chapter 3 (integer-literal propagation properties); [variable-encodings.md](variable-encodings.md);
[reasons-improvement.md](reasons-improvement.md); the feature's standing dev-doc
[order-encoding-deletion.md](order-encoding-deletion.md).
