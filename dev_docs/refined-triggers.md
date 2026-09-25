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
(`x = v`, `x != v`, `x >= k`, `x < k`, `x in [lo, hi]`, `x not in [lo, hi]`): it
is woken only when one of *those*
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
- `ctx.clear_watches()` — remove every watch this propagator owns, trailed like
  `ctx.watch` so backtrack restores exactly the pre-wake set. For a
  clear-and-recompute client that re-arms a fresh watched set each wake rather
  than moving watches individually. Only variables in the propagator's declared
  scope (its triggers and `scope_only`) are searched, so watch only variables
  declared in scope — the intended usage in any case. `watch_state` is
  independent and left untouched; reset any of it the new watch set no longer
  matches.
- `ctx.watch_state(key)` / `ctx.set_watch_state(key, value)` — a per-propagator
  **backtrackable scratch** `uint64`, keyed by a small integer. See *Backtrackable
  bookkeeping* below.

Install-time base watches are declared on the `Triggers` struct alongside the
coarse triggers:

```cpp
struct Triggers {
    std::vector<IntegerVariableID> on_change, on_bounds, on_instantiated;
    std::vector<std::pair<Literal, std::uint32_t>> refined;   // (literal, payload)
    std::vector<IntegerVariableID> scope_only;                // in scope, arms no wake
};
```

`Triggers::refined` entries are armed at install and are the persistent baseline
(not undone on backtrack); watches armed later via `ctx.watch` are restored on
backtrack. (The `Nogoods` 2WL client arms everything at runtime via `ctx.watch`
and leaves `Triggers` empty — see below.)

`Triggers::scope_only` declares variables as part of the propagator's *scope* —
they raise variable degree (for dom_then_deg / dom-wdeg), appear in the
variable→constraint adjacency, and count for the idempotence-aliasing check —
without arming any wake. A propagator woken only by refined watches it arms
dynamically would otherwise have an empty scope and be invisible to degree-based
heuristics; list its variables here (as `NegativeTable` does).

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
2. Otherwise ask `state.literal_is_entailed(watch.literal)`. If it is, **fire**:
   append the payload to the owner's inbox, wake the owner, trail the removal, and
   swap-remove the watch (consume). (`literal_is_entailed` rather than
   `test_literal`, because the loop does not care whether an unfired watch is false
   or merely undecided, and finding that out is most of the cost — see
   propagator-performance.md.)

The owner processes its fired set the next time it runs in the propagation queue
— firing and processing are *decoupled* (the owner is the schedulable unit). This
matters for one subtlety (*abandoned fires*, below).

The round boundary replays the round's inferences through one of two variants:
`requeue`, or `requeue_unless_already_seen` when some propagator in the round
claimed `EnableButIdempotent`. **Both fire watches**, and the claim gates only the
coarse triggers. A claim says the claimant need not be re-woken by what it has
already seen, which for a coarse trigger costs at most a delay — the next change
wakes it anyway — but for a watch costs the wake outright, because each inference
is replayed exactly once and a watch not fired against it is never offered it
again. Getting this wrong is invisible in everything but the node count; see
issue #889, where it turned nmseq/100 from 767 nodes into 1,089,375.

**Whether to look at the index at all is decided once per boundary, not once per
inference.** A model that has armed no watch — most models — replays through
`replay_inferences_of_watchless_model`, a separate body that wakes the coarse
triggers and does nothing else: no firing block, and no test of an index that will
never have anything in it. A model that has armed one replays through the body
above, unchanged. The empty-index question is asked once, where the boundary picks
between them (issue #895).

Once per *boundary* is the load-bearing part. A propagator can arm the model's
first watch in one round and need it fired at the next boundary of the same
`propagate()` call, so an answer cached at entry to `propagate()` would drop that
watch — silently, since a lost wake costs only pruning. Within a single replay the
answer cannot go stale, because nothing can arm a watch while a replay is running:
only a propagator arms one, and no propagator runs between the start of a replay
and its end. The watchless path checks that rather than trusting it; see the
invariants below.

### Trigger masks

A literal can only *become* entailed on certain kinds of change, mirroring the
coarse trigger masks:

| literal      | can be newly entailed by        | mask                          |
|--------------|----------------------------------|-------------------------------|
| `x == v`     | `x` becoming single-valued       | `{Instantiated}`              |
| `x >= k`     | a lower-bound rise               | `{BoundsChanged, Instantiated}` |
| `x < k`      | an upper-bound drop              | `{BoundsChanged, Instantiated}` |
| `x in [lo, hi]` | both bounds moving inside the interval | `{BoundsChanged, Instantiated}` |
| `x != v`     | any value removal                | all change kinds              |
| `x not in [lo, hi]` | any value removal         | all change kinds              |

The two range rows follow from `State::test_literal`. `x in [lo, hi]` is
`DefinitelyTrue` only when `lower_bound >= lo && upper_bound <= hi` — both
conditions are about bounds, so removing an interior value cannot newly entail
it. `x not in [lo, hi]` becomes true when the domain stops intersecting the
interval, which a removal from the *interior* can do, so it needs the full
mask — the same one it would get from the conservative default.

Nothing arms a watch on a range literal today: every `ctx.watch(...)` in the
tree passes `>=`, `<=`, `<`, `==`, or a nogood literal, and a `Nogood` is a
`vector<IntegerVariableCondition>` of decision literals. Those two rows are
forward-looking, and this table is where a future caller would come to find out
what they do.

`refined_watch_trigger_mask(literal)` derives this from the operator at arm time.
The firing loop asks `literal_is_entailed` only when `inf` is in the mask, so e.g. an
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
`watch_state(ni + 1)`, packed `(pos0 << 32) | pos1`.

- **Catch-up.** Watches are set up at a *root re-propagation* — the only time the
  propagator runs with an empty fired set (`propagate(nullopt)`, depth 0), which
  the restart loop re-enters once per pass. For the fixed store this happens once;
  for the growable store it picks up the nogoods learned since the last pass. A
  high-water mark in `watch_state(0)` says how far it has got; it is kept there
  rather than beside the watches so that a backtrack that removes the watches
  also resets it (see the `AutoTable` pitfall below). A clause
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

## The `And` / `Or` clause client

The logical constraints (`gcs/constraints/logical/logical.cc`) are one
propagator, `Or` being `And` over the negated literals and reification. When
the `And` form's reification is decided false at install and the backward half
is wanted, all that is left is the clause "not every literal of the `And` form holds": an
unreified `Or` (FlatZinc's `bool_clause`), an `Or` whose reification is fixed
true, an `And` whose reification is fixed false, and an `OrIf` whose condition
is fixed true. A clause of at least `innards::default_clause_watch_threshold()`
literals (128, or `GCS_CLAUSE_WATCH_THRESHOLD`, or per constraint with
`with_watch_threshold()`) watches two of them, in `propagate_watched_clause`;
a shorter one keeps the scan (issue #1060).

It is the `Nogoods` scheme for one clause, with three differences:

- **The search for a new watch only goes forwards**, from after both watches,
  and never wraps. Every position before the later watch, other than the two
  watched, is entailed: that holds when they are armed, a move passes over only
  entailed literals, and on backtrack `watch_state` returns to positions that
  held it at that level, whose literals are still entailed. So there is nothing
  behind the watches to find, and a search that fixes the literals in order
  finds the next one at once. `Nogoods` and `NegativeTable` search from the
  front, which walks the fixed prefix on every move --- the very cost the issue
  was about.
- **A satisfied clause disables itself.** When a watched literal, or the one a
  move lands on, is already false, the propagator returns
  `DisableUntilBacktrack` without moving anything. Its watches go on firing
  while it is disabled, and are consumed and restored like any other fire; the
  inbox is dropped at the end of `propagate()`, and backtracking out of the call
  that disabled it restores the watches and re-enables it together. Without this
  a satisfied clause keeps waking until a watch happens to land on its true
  literal, and on the benchmark below the watched path lost at every length.
- **Whether it has armed at all is in `watch_state`**, as `Nogoods` and
  `NegativeTable` keep their high-water marks. See the pitfall below: the
  `AutoTable` presolver runs every propagator at the root of a search of its own
  and then backtracks out of it.

### Why a threshold

The issue's case was `network_50_cstr` (2024): one `bool_clause` over 2,774
Booleans, 75% of the model's propagation time. Most of that was not the rescan
itself but the scan never disabling a clause it had seen was satisfied: it
stopped at the second undecided literal, and so returned `Enable` whenever two
undecided literals came before a true one. Stopping at the first false literal
of the `And` form takes the `Or` calls on 20,443 nodes from 38,555 to 2,543,
with or without watches.

What is left for the watches is small on the corpus. Instructions at fixed
nodes, relative to the old scan (fataepyc-09, `GCS_BENCH_NODE_LIMIT` in a local
build of `fzn-glasgow`; identical nodes, failures and solutions in every arm):

| model                       | fixed scan | watch every clause | watch from 128 |
|-----------------------------|-----------:|-------------------:|---------------:|
| `network_50_cstr` 2024      |     1.690x |             1.731x |         1.731x |
| `sdn-chain` 2020            |     1.042x |             1.071x |         1.072x |
| `rubik` 2013                |     1.225x |             0.841x |         1.225x |
| `grid-colouring` 2011       |     1.132x |             1.072x |         1.132x |
| `valve-network` 2023        |     1.099x |             1.048x |         1.099x |
| `minimal-decision-sets` 2020 |    1.153x |             1.193x |         1.153x |

In user cycles, median of five, the watched clauses of `network_50_cstr` and
`sdn-chain` (1,543 literals) are worth another 1.9% each over the fixed scan,
whose own share is 1.53x and 1.06x. Watching a short clause costs more than it
saves, because a fire is dear next to a scan of a few literals: the firing loop
copies the whole watch, `Literal` variant and all, into the inbox and the trail
(the "watch carrying an `IntegerVariableCondition`" refactor in
propagator-performance.md is what would cheapen it).

The corpus has few clauses between 17 and 1,000 literals. Most of them are
`skill-allocation`'s 242 of 66 literals, and watching those saves 2.3% of its
instructions but nothing outside its run-to-run spread in cycles. So the
crossover comes from `benchmarks/clause_watch_bench`: a random set cover, each element's clause over
`--length` of the sets, a budget on the sets chosen, branching in order with
"leave it out" first, which is the scan's worst case. User cycles, scan over
watched (above 1 means watching is faster), mean of three seeds at 60,000
nodes, identical trees throughout:

| length                              |   32 |   48 |   64 |   96 |  128 |  192 |  256 |  384 |  512 |
|-------------------------------------|-----:|-----:|-----:|-----:|-----:|-----:|-----:|-----:|-----:|
| 200 sets, 400 elements, budget 40   | 0.74 | 0.79 | 0.84 | 1.08 | 1.39 | 1.63 |      |      |      |
| 600 sets, 300 elements, budget 120  | 0.95 | 0.92 | 0.94 | 0.94 | 0.98 | 1.18 | 1.44 | 1.89 | 2.19 |

(The first shape has 200 sets, so its clauses stop at 200 literals.) The
crossover moves with the instance, from under 96 to over 128; the default of 128
is where the worse of these two is back to about break-even.

Measuring this needs one precaution beyond benchmarking.md: pin glibc's malloc
thresholds, for instance
`GLIBC_TUNABLES=glibc.malloc.mmap_threshold=33554432:glibc.malloc.trim_threshold=4294967295`.
Without it, a large share of these runs is kernel page-fault handling for state
copies that malloc maps and unmaps at every node, and how much depends on the
heap's history. An early version of this change measured 2.06x *faster* on
`valve-network` with every clause watched, and 2.4x slower on
`products-and-shelves`, and both disappeared with the thresholds pinned.

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
- **Every replay path must fire watches, unless the model has none to fire.** A
  watch is a one-shot subscription and each inference is replayed once, so any path
  that walks the round's inferences and skips the watch index loses the wake
  permanently. There are two such paths and they are not interchangeable:
  `requeue_honouring`, instantiated on `HonourClaims_`, which fires watches, and
  `requeue_coarse_only`, which has no firing block at all and is reachable only
  when the index is empty. A new variant must be one or the other deliberately.
- **The watchless replay must only run against an empty index.** It was chosen
  against the index as it stood when the boundary started, and a watch armed on a
  variable it has already walked past would never be offered the inference that
  entails it. The boundary re-tests `refined_watches_by_var.empty()` after the
  watchless replay returns and throws if it is not, so an engine change that ran a
  propagator mid-replay fails loudly instead of silently losing pruning. The test
  is on that side of the branch only: a model with watches does not depend on the
  answer and pays nothing for the question.
- **Catch-up runs at root re-propagation only**, keyed off an empty fired set.
  That is where new clauses appear (after a restart unwind) and where the edits
  land in the persistent root epoch.
- **But the first run is not always at the real root.** The `AutoTable`
  presolver opens an epoch, runs `propagate()` with no guesses --- which enqueues
  every propagator, as the root does --- and backtracks out of it, all before
  the search's own root propagation. Watches armed there are removed by that
  backtrack, and so is anything in `watch_state`; a non-backtrackable marker
  saying that they were armed survives it, and the real root then arms nothing,
  leaving the constraint with no wakes at all. So keep any such marker in
  `watch_state`, which that backtrack restores along with the watches, as all
  three clients here do. `NegativeTable` and the fixed-store `Nogoods` once kept
  theirs in a `shared_ptr<size_t>`, and with an `AutoTable` attached both
  accepted a solution their constraint forbids (issue #1106).
- The conversion is **semantics-preserving**: scan and refined must explore the
  identical search tree and learn the identical nogoods.

## Testing

Two test vehicles, both driven by the *semantics-preserving* property — the
refined path must behave byte-for-byte like the scan oracle:

- `gcs/constraints/nogoods_test.cc` — a scan-vs-refined **differential** under a
  deterministic, degree-independent brancher (`variable_order::in_order`, so the
  trees can only differ through *propagation*), asserting identical recursions and
  solution counts over hand-picked and random backtrack-heavy instances; plus the
  per-node unit-propagation reference, the brute-force oracle, and VeriPB. The
  hand-picked instances, and half the random ones, run again behind an
  `AutoTable` presolver (#1106), as do some of `negative_table_test`'s.
- `gcs/solve_test.cc` — a scan-vs-refined differential over restart runs (driven
  by `GCS_LEARNED_NOGOODS_SCAN`), asserting identical recursions / restarts /
  learned-nogood count / solutions.
- `gcs/constraints/mini_linear_test.cc` — a test-only `sum c_i x_i >= K` propagator
  that exercises the engine mechanism directly (the index, fired-watch inbox,
  consume, re-arm, restore, `is_watching`), with a coarse-vs-refined laziness
  comparison. Retired once refined triggers fold into the real `Linear`.
- `gcs/innards/propagators_test.cc` — a watch must fire whether or not the round
  has an idempotence claimant. Neither vehicle above co-registers a claiming
  propagator, which is how the claim-path gap in the replay survived (#889), so
  this one is a pair of unit cases rather than a differential. A third case arms a
  watch *during* a round rather than at install, which is what says the empty-index
  question is re-asked at every boundary and not cached for the `propagate()` call
  (#895); every other test here arms at install, where the distinction is
  invisible.

- `gcs/constraints/logical/logical_test.cc` (`run_clause_set_test`) — random
  sets of clauses long enough for watches to move, in all four posted forms,
  against a brute-force oracle and VeriPB, with a watched-vs-scanned differential
  on recursions; then find-one with Luby restarts, and again with every solution
  blocked so that the search restarts many times proving there are none; each
  both with and without an `AutoTable` presolver. The `logical_constraint_watched`
  ctest lane runs the whole fixture with the threshold at 0.

Each load-bearing piece has a **mutation test** recorded in the relevant PR:
inject the bug, confirm a differential catches it, before trusting the check.

## File map

- `gcs/innards/propagators.hh` — `RefinedWatchContext`, `RefinedWatchSink`,
  `Triggers::refined`.
- `gcs/innards/propagators.cc` — the watch index, firing, masks, restore trail,
  `watch_state`.
- `gcs/constraints/nogoods.cc` — `install_scan_nogoods` / `install_refined_nogoods`.
- `gcs/constraints/logical/logical.cc` — `propagate_watched_clause`, and the
  threshold that chooses it over the scan.
- `benchmarks/clause_watch_bench` — the benchmark behind that threshold.
- `gcs/solve.cc` — installs the engine-owned learned-nogood `Nogoods` (refined by
  default; `GCS_LEARNED_NOGOODS_SCAN` forces scan).
