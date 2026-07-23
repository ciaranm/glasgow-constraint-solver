# Order-encoding deletion via consolidate-then-delete branching

**Status: implemented behind a flag (`GCS_DELETE_ORDER_ENCODING=literals`) and
measured; suite-safe; not committed; not default.** This note records the design
for shrinking the integer order-encoding that VeriPB carries, plus the measured
outcome and what is and isn't yet done. The full Brancher-API refactor (below) is
still a proposal; the current implementation wires deletion into the existing
branch/backtrack flow via hoisting.

## Results (measured)

VeriPB verify time, mode OFF vs ON, eq-free linear UNSAT, split branching, on a
tuned benchmark node (pinned, turbo off, hyperfine ≥5 runs; search identical, both
VERIFIED):

| domain | OFF | ON | speedup |
|---:|---:|---:|---:|
| 100 | 0.12 s | 0.055 s | 2.2× |
| 500 | 2.56 s | 0.28 s | 9.1× |
| 1000 | 10.96 s | 0.64 s | 17.2× |
| 2000 | 48.8 s | 1.6 s | 30.6× |
| 4000 | ~266 s | 4.4 s | ~60× |

The speedup **grows monotonically with domain**. ON proofs are ~+89 % larger yet
verify far faster: **resident chain length dominates VeriPB's cost far more than
proof line count** — the core justification for the whole approach.

## Implementation status

- **Done, suite-safe:** the full caps-off test suite passes with the flag on (0
  flag-induced VeriPB rejections; mode-off byte-identical; flag-off 525/525). The
  hoist primitive, guess/eq/partition-atom hoisting, and the aux/view dispositions
  below are all in `gcs/innards/proofs/{names_and_ids_tracker,proof_logger,proof_model}.*`.
- **Kept resident (not deletable), per the "delete only when unreferenced" rule,
  because their `ge`s are named by *permanent* Top constraints:**
  - divide/modulus in-proof-bit **aux-magnitude** variables (`register_state_variable_bits_in_proof`)
    — pinned by the product-justification caches;
  - **viewed** variables (underlying of a registered view) — pinned by the
    always-at-Top view-bridge `pol`s in `need_gevar`.
  These get no deletion win, but are correct. Making them deletable needs the
  bridge-lifetime redesign (Future work).
- **`soli` objective atom** is hoisted to Top when the objective-improvement
  constraint is emitted (latent optimisation-mode bug fixed defensively).
- **Not yet done:** the clean Brancher abstraction (below) — the current wiring
  hoists guess/eq/aux references directly; the abstraction generalises and tidies
  it. Also future: short-reason flag / deview-companion level-scoping (currently
  inert), and the bridge redesign.

## Next steps (prioritised)

**1. Real-instance benchmarking (do first).** The measured win is on the *synthetic*
eq-free `order_deletion_bench` driver, which is favourable by construction (large
domains, eq-free, split branching, UNSAT). Before any further implementation, confirm
the win generalises — and characterise good/neutral/bad — on real problems:
- MiniZinc-challenge / `minizinc-benchmarks/` instances and the `examples/`
  models, ideally ones with large-domain variables and bound/split branching.
- For each: `.pbp` size and VeriPB verify time, mode OFF vs ON, on the tuned node
  (pinned, turbo off, hyperfine ≥5 runs), asserting recursions/props/solutions
  identical off vs on and both VERIFIED.
- Expect *less* than the synthetic 2–60× on eq/value-heavy models (their viewed and
  eq-branched variables stay resident), and possibly neutral/worse where domains are
  small or branching is value-based. Report the distribution honestly; that decides
  whether the two redesigns below are worth it.
- Verification-only drivers `order_jump_check.cc` / `order_hoist_check.cc` and the
  raw hyperfine TSV are preserved (uncommitted) under
  `/cluster/ciaran/claude/order-encoding-deletion-artifacts/`; promote them to proper
  `gcs/` tests when convenient (they regression-check the two verified foundations).

**2. Brancher-API refactor** (the abstraction below) to generalise
consolidate-then-delete and tidy the current direct wiring — worth doing once the
benchmarks justify productionising the feature.

**3. Bridge-lifetime redesign** so viewed variables and divide/modulus aux magnitudes
become *deletable* rather than resident, recovering their share of the win for
view/product-heavy models. This is the larger proof-logging change; scope it only if
step 1 shows those models matter.

**Also:** decide productionisation (keep flag-gated vs default-on), and — cleanup —
the superseded dormant `Links` mode can be removed.

## The problem

Every integer variable is proof-encoded with order literals `ge(v)` ("x >= v"),
each defined by a reification against the variable's bits, plus **chain-link**
constraints `ge(v+1) -> ge(v)` between adjacent thresholds (see
[variable-encodings.md](variable-encodings.md)). Under the current (pre-this-work)
scheme all of this is emitted at `ProofLevel::Top` and kept for the entire search —
nothing is ever removed — so a large-domain variable accumulates a chain of every
threshold any subtree ever touched. Changing exactly that is the point of this note;
the rest of the document is about *when and how* the encoding can instead be deleted.

The chain links are 2-literal clauses, which VeriPB propagates first (2WL,
clausal priority) on every RUP check. Touching one end of a 1000-long chain makes
VeriPB chase the whole thing, and the bit<->order reifications fire more long
sequences. So the cost is **chain length**, and the lever is to **stop keeping the
entire order encoding of a large-domain variable resident when the proof is only
operating over a narrow range locally.** The goal is reduced VeriPB verification
time; proof size is a secondary signal.

## Why the obvious approaches don't work

Recorded so future work doesn't re-walk these.

- **Delete only the chain links, keep the literals.** Fails. It *fragments* the
  chain, and VeriPB RUPs rely on the chain being contiguous over the existing
  literals, including for closure-only reasoning about variables not named in the
  step. A fragmented chain breaks those RUPs. (The Ch.3 property of McIlree's
  thesis: at any point every integer literal must unit-propagate all known facts
  about its variable. A hole in the chain violates it.)

- **Delete literals and re-introduce on demand.** Deleting a literal and stitching
  its two chain links into one skip-link *coarsens* the chain (complete, fewer
  thresholds) rather than fragmenting it, which is sound. But re-introducing a
  literal later — re-emitting its `red` reification — **fails VeriPB** once the
  surrounding context has moved on: a live constraint pins the atom, and the
  reification's falsify-witness (`ge(v) := 0`) contradicts the pin, so the
  redundancy sub-goal can't be auto-proven. The dominant pins are **backtrack
  clauses**, which name the search's guess (branch-threshold) literals, so this
  bites in *every* searching proof, eq-free or not. An experimental
  `OrderEncodingDeletion::Literals` mode on this branch demonstrates the failure
  (see Provenance); it should be reworked into the design below.

The lesson: never delete-then-reintroduce. Advance a **monotone** frontier and
delete behind it, and when a surviving constraint still needs a literal, **hoist**
it rather than deleting-and-recreating.

## The verified foundation: guess-reasoned bound jumps

*Verified against VeriPB.* When a variable X has a lower bound `X >= L` and the
values `L .. H-1` have been eliminated as holes (each elimination derivable from
the current guesses), the bound can be jumped over the holes with a single RUP
whose reason is **just the conjunction of guesses**:

    rup <guesses> (X >= H) >= 1

This checks because RUP does full unit propagation: it re-derives every hole
`X != v` from the guesses over the (permanent) base constraints, then climbs
`X>=L -> X>=L+1 -> ... -> X>=H` through the eq-atom reverse-reifications. You do
**not** need the per-value reasons, nor "all reasons over all other variables" —
the guesses entail them and RUP rediscovers them. This is the same monotonicity
the final backtrack clause already relies on.

Checked at wide gaps (L,H differing in up to all 6 bits, e.g. 3->60, 17->46, 5->26)
with two controls that must fail and do: dropping a needed guess is rejected, and
over-jumping by one value is rejected. Small gaps can RUP by bit-coincidence, so
the wide-gap controls are what make the positive result trustworthy. (See
`order_jump_check` in Provenance.)

Two consequences that shape the design:

1. The jump climbs through the intermediate eq/ge atoms, so they must be **live at
   emit time**; afterwards they are deletable. That pins the ordering: **emit the
   jump, then delete behind it.**
2. The jump is one `.pbp` line but VeriPB does O(H-L) propagation to check it. So a
   jump doesn't make *that* check cheaper — the win is that after deletion the
   *resident* database is smaller, so every *other* RUP's closure shrinks.

## Design overview: consolidate -> hoist -> delete

A brancher maintains a compact **backtrack constraint** — the "what we'll use to
backtrack" fact, i.e. the weakest constraint it has proven must hold given every
sibling tried so far is refuted, under the current guesses. It tightens
monotonically as siblings fail. On each refutation the framework:

1. asks the brancher for the tightened backtrack constraint;
2. emits the guess-reasoned RUP that advances it (a bound jump, for the common
   case);
3. **hoists** the literals the new constraint names to the level where it lives;
4. **deletes** the encoding the advance stepped over that nothing else names.

Consolidate, hoist the frontier, delete the rest. Because the frontier is
monotone, we never delete-then-reintroduce.

## The backtrack constraint

Three kinds, declarative and extensible:

- **Bound** (`LowerBound(v)` / `UpperBound(v)`) — for split / ascending /
  descending value orders. Advanced by the bound-jump RUP; names **one** literal
  (the frontier). Maximally deletable.
- **ExcludedSet** — the generic fallback, accumulating `X != v`. This is exactly
  today's `~(all guesses)` behaviour. Correct, but names a growing set, so nothing
  is deleted for that variable. Used by genuinely unstructured orders.
- **Custom** — an escape hatch: the brancher supplies its own backtrack constraint
  plus a proof callback. For exotic branchers; not fleshed out until a use case
  appears.

## The Brancher abstraction

Replace the bare `BranchValueGenerator` (which yields a
`generator<IntegerVariableCondition>` and touches no proof state) with a small
stateful object that owns *both* the decision sequence and the backtrack
constraint:

    struct BranchDecision {
        IntegerVariableCondition guess;      // what to branch on
        BacktrackAdvance         on_refuted; // how the backtrack constraint tightens if this fails
    };
    // BacktrackAdvance = variant<LowerBound, UpperBound, Exclude, Custom>

    struct Brancher {
        virtual auto next(const CurrentState &, const Propagators &)
            -> std::optional<BranchDecision> = 0;
        virtual auto initial_backtrack_constraint(...) -> BacktrackConstraint = 0;
    };

`solve.cc` drives it: `next()` -> guess -> recurse -> on refutation apply
`on_refuted` (framework emits the advance RUP, hoists, deletes) -> repeat; when
`next()` returns `nullopt` the standing backtrack constraint is the node's
backtrack lemma, replacing the generic `~guesses`. A brancher that only ever emits
`Exclude` advances reproduces today's behaviour byte-for-byte.

Owning decisions and their proof consequence in one object is deliberate: it is
what lets a new brancher be written *correctly* without the caller having to keep a
separate "value order" and "consolidation strategy" mutually consistent.

## The hoist primitive

A general `ProofLogger` operation, foundational to the whole scheme:

    hoist_literal_to_level(lit, target_level)
    hoist_literal_to_top(lit)                 // = hoist to level 0, permanent

It is a **bookkeeping move**: it reassigns the literal's definition from its
current (deep) level bucket to a shallower one, so a later `forget` deletes it
later, or never. **It re-emits nothing.** That is precisely why it succeeds where
delete-then-reintroduce fails — there is no re-asserted reification and therefore
no witness to collide with a pin.

Caveat, load-bearing: hoisting a literal so it stays *referenceable* is not enough;
for it to keep unit-propagating (the Ch.3 invariant) at its new level it must be
chain-linked to its neighbours *at that level*. So hoisting is two steps — move the
definition **and** stitch the literal into the target level's chain (for
hoist-to-top, into the permanent boundary chain). This is the existing stitch
machinery run in the hoist direction. Doing only the first step reintroduces a
subtler version of the chain-fragmentation bug.

## The deletion rule

Stated once, cleanly:

> Delete a literal only when no surviving constraint names it. If a surviving
> constraint at level L names a literal currently at a deeper level, **hoist** the
> literal to L instead of deleting it.

The brancher's backtrack constraint and any live nogoods are the "surviving
constraints" that trigger hoists. A compact bound backtrack constraint names one
literal, so one is hoisted and the rest of the stepped-over range is deleted (the
win). An excluded-set constraint names many, so many are hoisted (no win, but
correct). Retention is therefore automatic and exactly as tight as the brancher's
backtrack constraint — there is no separate "retained set" to maintain.

## Mapping the existing heuristics

Helpers make each existing `value_order::` a one-liner:

| value_order                                   | backtrack constraint       | deletable        |
|-----------------------------------------------|----------------------------|------------------|
| `smallest_first`, `smallest_in`               | ascending `LowerBound`     | yes, O(1) pin    |
| `largest_first`, `largest_in`                 | descending `UpperBound`    | yes              |
| `split_smallest_first` / `split_largest_first`| `LowerBound`/`UpperBound`  | yes              |
| `median`, `random`, `random_out`, `reject_random_interval` | `ExcludedSet` | no (unchanged)   |

The orders people use for large domains (in-order, split) get the win; the
deliberately-random ones keep working unchanged.

## Restarts

Backtrack constraints and advance RUPs live at `Current` levels, so a restart's
`forget` wipes them and the next pass simply re-runs the brancher and re-emits
them — no special handling. The coupling is with learned nogoods: they are at
`Top` and name the decision (branch-threshold) literals, so those literals must
survive. They **hoist to Top**. Since nogoods are the reduced positive-decision
prefix, this hoists O(nogoods) literals, not O(domain).

## Last-value / phase saving

Falls out for free, and in fact motivates the hole-jumping. Trying a remembered
value `X==42` first: if it is refuted it becomes a hole `X != 42`; when the
ascending frontier later reaches 42 it jumps over it with the verified
guess-reasoned RUP. The backtrack constraint stays a clean bound; the saved value
is just a hole in its path. The d-way "last sibling is free" case is subsumed too:
the frontier reaching `ub+1` *is* the at-least-one closure, so there is no separate
last-value special case to carry.

(There is no in-tree phase-saving today; if one is added it slots in here as a
first decision that may become a hole.)

## Parallel search (future)

Planned parallel search runs independent search processes that sometimes share
restart-nogoods. A shared nogood is only usable by a receiving process if the
literals it names are stably, identically defined there — which is exactly what
**hoist-to-top** guarantees. So this design does not solve parallel *proof-logging*,
but the hoist-to-top hook is the thing that future work will want, and nothing here
precludes it. Restart nogoods hoisting to Top (above) is the same mechanism.

## Extensibility

A new brancher is: pick a variable, yield decisions, tag each with a backtrack
advance — or, for the common case, call `frontier_ascending()` / `bisect()` and get
the consolidation, hoisting and deletion for free. Unstructured branchers use
`excluded_set()` (correct, no win). `Custom` is the escape hatch, and even it never
writes raw VeriPB — it hands back a backtrack constraint and the framework emits the
RUP. Per the "don't design ourselves into a corner, but don't over-commit" steer, we
ship the internal helpers plus `Custom` and leave a polished power-user surface until
a real use case lands.

## Implementation staging

1. **Hoist primitive first.** It is foundational, independently testable, and needed
   by everything downstream. Build `hoist_literal_to_level` / `hoist_literal_to_top`
   (definition move + stitch into the target chain) and verify with VeriPB that a
   deep literal hoisted to Top / to a level still checks and the chain stays intact.
2. **Brancher abstraction.** Introduce `Brancher` + `BacktrackConstraint` +
   `BacktrackAdvance`, port the existing `value_order::` heuristics onto it via
   helpers (default `Exclude` = today's behaviour, byte-identical), keep `branch_with`
   working.
3. **Wire deletion.** Drive deletion from backtrack-constraint advances (consolidate ->
   hoist -> delete), replacing the experimental `OrderEncodingDeletion::Literals`
   mode. Gate behind the existing flag until it verifies across the suite.
4. **Benchmark.** Re-run the eq-free large-domain sweep (split branching, UNSAT) that
   the earlier attempt could not measure because its proofs did not verify.

Each stage gates on: VeriPB accepts, and recursions/propagations/solutions are
unchanged mode-off vs mode-on (a proof-only change must not perturb search).

## Open questions

- Backtrack-constraint expressiveness beyond bound/excluded-set/custom — deferred;
  revisit if a disjunctive (interval) brancher wants a first-class kind.
- Exactly how much chain context a hoist must carry to preserve the Ch.3 invariant
  cheaply (splice a single skip-link vs. rebuild a span).
- Whether hoist-to-top of nogood literals wants the full definition or a lighter
  "nameable at Top" form, once parallel proof-logging is designed.

## Provenance and artifacts

- Journey and findings: see the `gcs-order-encoding-deletion` project memory.
- Branch `delete-order-links-on-backtrack`: experimental `OrderEncodingDeletion`
  flag (`GCS_DELETE_ORDER_ENCODING=literals`) demonstrating the delete-then-reintroduce
  failure — to be reworked per this design.
- `examples/order_deletion_bench/` — scalable eq-free linear/cumulative driver
  (split branching, `--unsat`) for the benchmark.
- `order_jump_check` — the VeriPB verification of the guess-reasoned bound jump and
  its two controls.
- Background: McIlree PhD thesis, Chapter 3 (integer-literal propagation properties);
  [variable-encodings.md](variable-encodings.md); [reasons-improvement.md](reasons-improvement.md).
