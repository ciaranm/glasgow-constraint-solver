# Refined per-literal triggers

The coarse trigger system (see [Implementing a constraint](constraints.md)) wakes
a propagator whenever a *variable* it subscribed to changes: `on_change`,
`on_bounds`, `on_instantiated`. That is the right granularity for most
constraints, but it is too coarse for a propagator that cares about specific
*literals* on many variables and is otherwise dormant — the motivating case being
the learned-nogood store (see [Restarts, nogoods and
weighting](restarts-nogoods-weighting.md)), which subscribed to *every* variable
and rescanned its whole store on every domain change.

**Refined triggers** let a propagator instead arm watches on individual literals
(`x = v`, `x != v`, `x >= k`, `x < k`): it is woken only when one of *those*
literals becomes entailed, and is told exactly which fired. This document covers
the engine mechanism (`gcs/innards/propagators.{hh,cc}`) and its first real
client, the two-watched-literal `Nogoods` propagator
(`gcs/constraints/nogoods.cc`).

It is an *addition* to the coarse system, not a replacement: the two indexes live
side by side, and a propagator can use either or both. A propagator that uses
only coarse triggers is completely unaffected and pays nothing.

## The propagator-facing API

A propagation function can take an extra `const RefinedWatchContext &` parameter.
The wrapper forwards it only to functions whose signature accepts it, so existing
3-argument propagators are untouched:

```cpp
propagators.install(constraint_id(),
    [/* captures */](const State & state, auto & inference, ProofLogger * const logger,
        const RefinedWatchContext & ctx) -> PropagatorState { ... },
    triggers);
```

The context offers:

- `ctx.fired_payloads()` → `span<const uint32_t>` — the payloads of this
  propagator's watches that have fired since it last ran. A *payload* is an opaque
  small integer the propagator chose when arming the watch (the `Nogoods`
  propagator uses the clause index). A watch is **consumed when it fires**: if the
  propagator still wants to hear about that literal it re-arms a watch via
  `ctx.watch`.
- `ctx.watch(literal, payload)` — arm a refined watch: when `literal` next becomes
  entailed (`State::test_literal(literal) == DefinitelyTrue`), `payload` is
  appended to this propagator's fired set and it is woken. Watches armed while
  propagating are restored on backtrack (see below).
- `ctx.is_watching(var)` — whether this propagator currently watches any literal
  on `var`. Reads the (backtrack-consistent) index, so a propagator can recompute
  a watched set without tracking it itself.
- `ctx.watch_state(key)` / `ctx.set_watch_state(key, value)` — a per-propagator
  **backtrackable scratch** `uint64`, keyed by a small integer. See *Backtrackable
  bookkeeping* below.

Install-time base watches are declared on the `Triggers` struct alongside the
coarse triggers:

```cpp
struct Triggers {
    std::vector<IntegerVariableID> on_change, on_bounds, on_instantiated;
    std::vector<std::pair<Literal, std::uint32_t>> refined;   // (literal, payload)
};
```

`Triggers::refined` entries are armed at install and are the persistent baseline
(not undone on backtrack); watches armed later via `ctx.watch` are restored on
backtrack. (The `Nogoods` 2WL client arms everything at runtime via `ctx.watch`
and leaves `Triggers` empty — see below.)

## The engine mechanism

State, all in `Propagators::Imp`:

- `refined_watches_by_var[v]` — the watches currently armed on variable `v`. Each
  is `{literal, payload, owner, id, trigger_mask}`.
- `inbox_by_propagator[owner]` — the payloads delivered to `owner` since it last
  ran; handed to it as `fired_payloads()` and cleared after it runs.
- `refined_watch_edit_trail` — Added/Removed edits made while propagating.
- `watch_state_by_propagator` + `watch_state_trail` — the backtrackable scratch.

### Firing

`propagate()`'s `requeue(v, inf)` is called for each variable `v` that changed,
with the `Inference` granularity `inf` (`BoundsChanged` / `InteriorValuesChanged`
/ `Instantiated`). For each watch armed on `v`:

1. If `inf` is **not** in the watch's `trigger_mask`, skip it (see *Trigger
   masks*).
2. Otherwise test `state.test_literal(watch.literal)`. If `DefinitelyTrue`,
   **fire**: append the payload to the owner's inbox, wake the owner, trail the
   removal, and swap-remove the watch (consume).

The owner processes its fired set the next time it runs in the propagation queue
— firing and processing are *decoupled* (the owner is the schedulable unit). This
matters for one subtlety (*abandoned fires*, below).

### Trigger masks

A literal can only *become* entailed on certain kinds of change, mirroring the
coarse trigger masks:

| literal      | can be newly entailed by        | mask                          |
|--------------|----------------------------------|-------------------------------|
| `x == v`     | `x` becoming single-valued       | `{Instantiated}`              |
| `x >= k`     | a lower-bound rise               | `{BoundsChanged, Instantiated}` |
| `x < k`      | an upper-bound drop              | `{BoundsChanged, Instantiated}` |
| `x != v`     | any value removal                | all change kinds              |

`refined_watch_trigger_mask(literal)` derives this from the operator at arm time.
The firing loop tests `test_literal` only when `inf` is in the mask, so e.g. an
`x == v` watch is never tested on a mere bound move — `x == v` cannot have become
true there. This is **sound by the same granularity contract the coarse triggers
rely on** (`on_instantiated` fires iff a variable becomes single-valued, etc.),
and it is purely an efficiency gate: a watch outside its mask could not have
fired, so skipping its test changes nothing.

(`Instantiated` is in every mask, and the guess first-pass tags the decision
variable `Instantiated`, so all of a guessed variable's watches are tested on the
branch — the conservative thing. The masks pay off on the much more frequent
*propagation*-induced changes.)

### Restore on backtrack

Each `propagate()` snapshots the edit trails at entry and registers one
`on_backtrack` callback that truncates them in reverse. We replay our own trail
rather than registering a callback per edit, because `State` runs an epoch's
callbacks in registration order, which would compose per-edit undos incorrectly
(e.g. an add-then-consume of the same watch). Install-time base watches are
registered before search and sit below every snapshot, so they persist.

**Watches are restore-on-backtrack, not non-backtrackable.** Two consequences,
both load-bearing:

- *Abandoned fires.* A watch can fire (and be consumed) inside a `propagate()`
  that a *different* propagator's contradiction ends before the owner runs to
  process it. Because the consume is trailed, the following backtrack restores it
  — so the watch is not lost. A non-backtrackable ("no-change") scheme would lose
  it permanently and later miss an inference. This is why no-change watches were
  *not* used (a no-change two-watched-literal scheme was tried and the
  scan-vs-refined differential caught exactly this bug).
- *Per-level validity.* On backtrack the watches return to the state valid at that
  level, so a propagator does not have to maintain the SAT-style "the two watched
  literals are the last two falsified" invariant by hand.

### Backtrackable bookkeeping (`watch_state`)

A propagator that maintains its own per-watch bookkeeping — e.g. 2WL needs to know
*which two* literals of each clause it watches — has a problem: that bookkeeping
must stay consistent with the (restored) watches across backtrack, but a
propagator only sees `const State &` and cannot trail its own state.

`ctx.watch_state(key)` / `set_watch_state(key, value)` solve this: a per-propagator
`uint64` keyed by a small integer, written on `watch_state_trail` and replayed by
the *same* `on_backtrack` that restores the watch edits. So the bookkeeping moves
in **lockstep** with the watches — whatever the watches restore to, the bookkeeping
restores to the matching value.

This is deliberately *not* `state.add_constraint_state` (see
[constraints.md](constraints.md)): that snapshots the entire constraint-state
vector on every `new_epoch` (so per-clause bookkeeping would cost O(store) per
node), and its per-epoch granularity does not track the per-`propagate()` watch
restore (the root epoch sees several propagates across restarts). `watch_state` is
trailed (cost proportional to writes) and aligned with the watch restore.

## The `Nogoods` two-watched-literal client

`Nogoods` (`gcs/constraints/nogoods.cc`) is the first real client. It has two
paths, selected by a `bool _refined`:

- **scan** (`install_scan_nogoods`) — the original: coarse `on_change` on every
  nogood variable, rescan the whole store per wake. Kept as the differential
  oracle, and used by the growable-store constructor only when
  `GCS_LEARNED_NOGOODS_SCAN` is set.
- **refined** (`install_refined_nogoods`, the default) — two-watched-literal over
  refined watches.

### How 2WL maps onto refined watches

Each clause arms exactly two watches, on two non-entailed literals, both with
payload = the clause index. The two watched positions are stored in
`watch_state(ni)`, packed `(pos0 << 32) | pos1`.

- **Catch-up.** Watches are set up at a *root re-propagation* — the only time the
  propagator runs with an empty fired set (`propagate(nullopt)`, depth 0), which
  the restart loop re-enters once per pass. For the fixed store this happens once;
  for the growable store it picks up the nogoods learned since the last pass (a
  non-backtrackable `set_up` high-water marks how far it has got — sound because
  the arming/`watch_state` edits live in the persistent root epoch). A clause
  already unit/violated at this point (e.g. via an initialise-time entailment that
  never fires a watch) is resolved here.
- **On a fire.** Read `(p, q)` from `watch_state`; recompute which is entailed
  from the current state. Move a fired (entailed) watch to another non-entailed
  literal, updating `watch_state`. If there is no replacement the clause is unit
  (infer the survivor's negation) or, if none is non-entailed, a contradiction.

Because the watches restore on backtrack, the **unit case is trivial**: just
infer and leave the consumed watch to be restored. There is no need to keep a
watch on the just-falsified literal as classic non-backtrackable SAT 2WL does.

There is deliberately **no whole-store rescan** at the root (unlike the watch-all
scheme that preceded 2WL): catch-up handles clauses unit-at-setup, firing handles
every later entailment, and a root fact that persists across restarts was already
acted on (in the persistent root epoch) when it was first derived.

### Why 2WL, and the perf arc

A dump of the learned nogoods on a restart run showed they are *fans* of `x=v`
clauses sharing a common prefix — e.g. `{v0=0, v1=1, v2=2, v3=6, v4=k}` for many
`k` — so an early-decision variable appears in nearly every clause. Watching all
literals fires those prefix literals across the whole fan on each instantiation;
2WL watches each clause at only two literals, so an entailed prefix literal is not
one of a clause's watches and does not fire there. That is exactly the fan's
sweet spot.

Measured on `tsp --restarts=10000` (search identical throughout, ~4.29M
recursions, 1966 learned nogoods):

| scheme                          | solve time | overhead vs no-nogoods floor (55.6s) |
|---------------------------------|-----------:|--------------------------------------:|
| coarse scan                     |     190.6s | +135s                                 |
| refined watch-all               |     105.3s | +49.7s                                |
| watch-all + trigger masks       |      76.4s | +20.8s                                |
| two-watched-literal             |      58.4s | +2.8s                                 |

i.e. the learned-nogood machinery goes from a 3.4× tax to essentially free.

## Correctness invariants and pitfalls

For anyone changing this code:

- **Watches must be restore-on-backtrack.** No-change watches are unsafe here
  because of abandoned fires (above). If you ever add a no-change mode, it needs
  a separate mechanism to undo abandoned consumes.
- **`watch_state` and the watches must change together.** Every move that re-arms
  a watch must also update `watch_state`, in the same `propagate()`, so the
  lockstep restore keeps them consistent.
- **Trigger masks must over-approximate.** A mask must include *every* `Inference`
  granularity that could make the literal newly entailed; too narrow a mask drops
  a fire (a missed inference). The differential catches this.
- **Catch-up runs at root re-propagation only**, keyed off an empty fired set.
  That is where new clauses appear (after a restart unwind) and where the edits
  land in the persistent root epoch, keeping the non-backtrackable `set_up`
  counter in step.
- The conversion is **semantics-preserving**: scan and refined must explore the
  identical search tree and learn the identical nogoods.

## Testing

Two test vehicles, both driven by the *semantics-preserving* property — the
refined path must behave byte-for-byte like the scan oracle:

- `gcs/constraints/nogoods_test.cc` — a scan-vs-refined **differential** under a
  deterministic, degree-independent brancher (`variable_order::in_order`, so the
  trees can only differ through *propagation*), asserting identical recursions and
  solution counts over hand-picked and random backtrack-heavy instances; plus the
  per-node unit-propagation reference, the brute-force oracle, and VeriPB.
- `gcs/solve_test.cc` — a scan-vs-refined differential over restart runs (driven
  by `GCS_LEARNED_NOGOODS_SCAN`), asserting identical recursions / restarts /
  learned-nogood count / solutions.
- `gcs/constraints/mini_linear_test.cc` — a test-only `sum c_i x_i >= K` propagator
  that exercises the engine mechanism directly (the index, fired-watch inbox,
  consume, re-arm, restore, `is_watching`), with a coarse-vs-refined laziness
  comparison. Retired once refined triggers fold into the real `Linear`.

Each load-bearing piece has a **mutation test** recorded in the relevant PR:
inject the bug, confirm a differential catches it, before trusting the check.

## File map

- `gcs/innards/propagators.hh` — `RefinedWatchContext`, `RefinedWatchSink`,
  `Triggers::refined`.
- `gcs/innards/propagators.cc` — the watch index, firing, masks, restore trail,
  `watch_state`.
- `gcs/constraints/nogoods.cc` — `install_scan_nogoods` / `install_refined_nogoods`.
- `gcs/solve.cc` — installs the engine-owned learned-nogood `Nogoods` (refined by
  default; `GCS_LEARNED_NOGOODS_SCAN` forces scan).
