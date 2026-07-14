# Making a propagator faster

This is a companion to [constraints.md](constraints.md), which covers how to
*write* a correct, proof-logging propagator. This document is about how to make
one *faster* once it is correct. It is a checklist of the levers we have found
useful, roughly cheapest/safest first, plus the discipline that keeps a
performance change from quietly becoming a correctness or strength change.

Read [benchmarking.md](benchmarking.md) alongside this: it describes the curated
benchmark set and how to run a before/after comparison. This document is about
*what* to change; that one is about *how to measure* whether it helped.

## Ground rules

These come first because they are what stop performance work from going wrong.

### Correctness comes first

Do not start performance work until the propagator is finished: correct, with
wide test coverage (enumeration tests over varied instances, GAC-at-each-node
checks where applicable), and with proof logging that VeriPB accepts. A fast
propagator that is wrong, or whose proofs don't verify, is worthless, and a
half-built one is a moving target you can't benchmark. Optimise a thing that
works.

### Distinguish strength from performance

There are two completely different kinds of "the propagator got better":

- **Strength** — it prunes more (fewer search nodes). This is a change to *what*
  the solver does. It is a separate concern from this document and is usually
  out of scope for a performance pass.
- **Performance** — it does the same work faster (same search, less time per
  node). This is what a performance change should be.

Keep them apart. A pure performance change **must not change the search**:
`recursions` and the first integer of `propagations:` must be identical before
and after, on every benchmark. The benchmark harness prints both precisely so
you can diff them; treat any divergence as a correctness signal first and a
performance signal second (benchmarking.md, "What to capture"). If you find
yourself explaining a speedup by "well, it also prunes a bit differently now",
stop — you have conflated the two, and you need to re-evaluate the change as a
strength change (with its own soundness and proof review) rather than a free
win.

### Have good, varied benchmarks, and don't commit on a hunch

Propagator behaviour is extremely data-sensitive: large vs small domains, holey
vs contiguous domains, many vs few variables, tight vs loose constraints, and
search-heavy vs propagation-heavy instances can each flip which implementation
wins. A change that is 2× faster on one shape can be 2× slower on another. So:

- Measure on more than one instance shape before committing to anything
  complicated. The curated set in benchmarking.md is the baseline sanity check;
  supplement it with a shape that actually exercises *your* constraint.
- Don't commit a complicated change (incrementality, a bespoke data structure, a
  backtrackable cache) without evidence that it wins across the shapes you care
  about, not just the one you developed against.

There is one deliberate exception. A change that is *applied uniformly
everywhere* and is *generally sound as a principle* — the reason-reuse hoist
below is the archetype — gets a pass even if it doesn't measurably speed up some
individual constraint, as long as it never makes anything slower and the general
idea is worthwhile. Consistency has value: it removes a whole class of avoidable
work and makes the next propagator's default the good one. Don't use this as a
loophole for speculative single-constraint cleverness.

## Levers, cheapest first

### Better triggers and idempotence

The cheapest propagation is the one that never runs. Two mechanisms cut
unnecessary calls:

- **Triggers.** Register the propagator to wake only on the events that can
  actually change its output (`on_bounds` vs `on_change`, and only the variables
  it reads). Waking on changes you don't care about is pure overhead. See
  constraints.md, "Triggers".
- **Idempotence.** If a propagator reaches a fixpoint in a single call, it can
  tell the engine so (return the right `PropagatorState`, or claim idempotence)
  and avoid being re-queued to discover it changed nothing. Conversely, a
  propagator that reports `NoChange` when it *did* change state causes the
  engine to stop too early — see the `Inference::NoChange` note in the state
  docs.

Both are about not calling the propagator when there is nothing for it to do.
Get these right before micro-optimising the body.

### Reuse the reason instead of rebuilding it

A propagator that reasons over a fixed variable scope should build **one**
`Reason` and reuse it, not call `generic_reason(vars)` / `bounds_reason(vars)`
on every wake or at every inference site. Those factories take the scope
by-value (`ArrayParam`'s owning constructor), so each call copies the whole
scope vector into a fresh `shared_ptr` — and it happens even with proofs off,
where the reason is never materialised.

The `*_reason()` factories are *declarative*: they capture the variable scope
and defer reading domains to `materialise()` (see
[reasons-improvement.md](reasons-improvement.md)). So a reason over a fixed
scope is identical on every wake; the only per-call part is materialisation,
which the tracker does lazily and only when a proof actually needs it. That
means you can build the reason once — at install, as a capture-init, or captured
and threaded into a per-wake helper by `const Reason &` — and hand the same
object to every `infer()`.

```cpp
// once, at install:
auto all_vars_reason = generic_reason(all_vars);
propagators.install(id, [/* ... */, reason = std::move(all_vars_reason)](
    const State & state, auto & inference, ProofLogger * const logger) {
    /* ... */
    inference.infer(logger, lit, JustifyUsingRUP{...}, reason);   // reuse
});
```

This was applied across `count`, `n_value`, `at_most_one`, `value_precede`,
`linear_equality`, `linear_inequality`, `negative_table`, `regular`, and `sort`.
It is the archetype of the "uniform, generally-sound" change above: on some
constraints it's immeasurable, but it never hurts and removes an avoidable
allocation from every hot path.

The one thing to watch: this only applies to a reason that is genuinely fixed.
If the reason is materialised eagerly against the current state
(`eager_reason(reason, state)`), or its literal set depends on what changed,
it is per-call by nature and must not be hoisted. (`lex` is the in-tree example
that is *not* hoisted for exactly this reason.)

### Reuse data structures to avoid per-wake allocation

The same principle applies to scratch state generally: a propagator that
allocates working buffers (`vector`s, sets, maps) on every wake is paying malloc
and cache-miss cost per call for storage whose size it already knows. Allocate
once and reuse.

The model that makes this safe is: **each search gets its own clone of a
constraint** (`Constraint::clone()`), including if we ever run searches in
parallel threads. A propagator's captured state therefore belongs to exactly one
search on one thread. You do **not** need `thread_local` or any synchronisation
for reusable scratch — just hold it behind the constraint's own storage (a
`shared_ptr` to a scratch struct captured into the propagator lambda works
well, since the lambda's other captures are `const` inside a non-`mutable`
lambda) and reset (don't reallocate) it at the top of each wake.

`bin_packing`'s Stage 3 sweep is the worked example: it used to build three
`vector<unordered_set<long long>>` per bin per wake; replacing them with flat,
position-indexed bitmaps held in per-clone scratch (reset with `fill`, never
regrown) removed ~50% of its runtime that was pure hash-table allocation and
rehashing. See [bin-packing.md](bin-packing.md).

### Fast data structures for small collections

`std::set` / `std::map` (red-black trees) and `std::unordered_set` /
`std::unordered_map` (hash tables) have poor constant factors for the small
collections that dominate propagator inner loops: node-per-element allocation,
pointer chasing, and (for the hash containers) rehashing. For the sizes we
typically see — a handful to a few hundred elements, rebuilt constantly — a flat
`std::vector` (or `gch::small_vector`, which keeps the common small case off the
heap entirely) is usually much faster, even when an operation becomes O(n)
instead of O(log n) or O(1): the n is small and the memory is contiguous.

There is a real readability trade-off. A `set` membership test reads better than
a sorted-vector `binary_search`, and an `unordered_map<K,V>` lookup reads better
than a parallel-array scan. Reach for the flat structure when the collection is
small and hot (a profile says so, or it's rebuilt every wake); keep the
associative container when the code is cold or the collection is genuinely large
and the clarity matters more than the constant. `small_vector` is often the
sweet spot: vector performance, and it still reads like a vector.

### Iteration order in "for each value" loops

When you iterate a variable's domain, the order you visit values in can matter,
because it can let you use a faster `IntervalSet` primitive or exit early. The
domain is stored as an `IntervalSet<Integer>` — a sorted run of disjoint
intervals with a small-buffer optimisation for the common one-or-two-interval
case (see [state-and-variables.md](state-and-variables.md)). Operations that
work *with* that representation (interval-at-a-time, ascending/descending
sweeps, `domain_intersects_with` against another `IntervalSet`) are much cheaper
than ones that force a value-by-value materialisation or a copy.

Prefer the non-copying primitives: `for_each_value_immutable` /
`for_each_value_mutable` (which iterate without the coroutine/allocation cost of
the older `each_value_*`), and `domains_intersect` /`domain_intersects_with`
instead of building a set of one domain and testing membership. If an algorithm
is free to choose the order it processes values or variables, choosing the one
that matches the interval structure — or that lets it stop as soon as it has its
answer — can be a real win for free.

### Incrementality

If most of a propagator's work is recomputing something that changed only
slightly since the last wake, compute the delta instead of the whole thing. This
is the most powerful lever and also the most work and the most risk, so reach
for it only when a profile shows the recomputation dominating.

The subtlety in a backtracking solver is that "since the last wake" spans
descents *and* backtracks, and your cached state must stay consistent across
both. Two broad approaches:

- **Diff against cached inputs, recompute the affected range.** If the output is
  a pure function of some per-variable summary (e.g. per-item admissibility
  flags), cache that summary alongside the output; each wake, diff current vs
  cached to find what changed and recompute only the dependent part. This is
  automatically correct across backtrack *without any trailing*, because a
  backtrack simply relaxes the inputs, which the diff sees as a change like any
  other. `bin_packing`'s incremental Stage 3 works this way.
- **Backtrackable state** (below) when you genuinely need to restore a data
  structure to its earlier value on backtrack.

Either way, an incremental propagator is much harder to test than a
recompute-from-scratch one: bugs hide in the "only on this backtrack pattern"
cases. Keep the from-scratch version around (even if only in comments or a test)
to differential-test against, and lean on enumeration + proof verification.

### Backtrackable state — but expensive state isn't always a win

The engine can hold per-constraint state that is saved and restored across the
search (`add_constraint_state` / `get_constraint_state`; constraints.md,
"Backtrackable propagator state"). This is the natural home for an incremental
data structure that must track the search: a watched-literal structure, a
cached matching, a dead-value cache.

But trailing is not free: every backtrackable field costs save/restore work at
every relevant search node, and a large or deeply-structured piece of
backtrackable state can cost more to maintain than the recomputation it
replaces. Before committing to it, weigh the trailing cost against the
recompute cost. Sometimes the winning design is *non*-backtrackable state that
is sound to leave stale on backtrack (`negative_table`'s watches are left where
they moved — a moved watch is still a valid watch as the state relaxes), or the
diff-against-cached-inputs approach above, which needs no trailing at all.

### Removing variant-dispatch overhead

`IntegerVariableID` is a variant (`SimpleIntegerVariableID` /
`ViewOfIntegerVariableID` / `ConstantIntegerVariableID`), and every generic
`State` read visits it. GCC and clang usually lower that visit to a plain
discriminant switch, so it is not automatically a problem — but in a hot enough
read path the per-read view arithmetic and dispatch can show up in a profile. If
it does, two tools help:

- **Known-subtype overloads in `State`.** The hot read accessors have
  `SimpleIntegerVariableID` fast paths that skip the view arithmetic and the
  variant machinery for the common no-view case (this was issue #513 / the
  `State::bounds` fast path). If you are adding a hot read primitive, giving it a
  concrete-subtype overload can pay off.
- **Compile the propagator once per variable-kind mix.** `as_homogeneous(vars)`
  (`gcs/innards/variable_id_utils.hh`) inspects a variable list and, when they
  are all the same concrete kind, hands back a vector specialised to that kind,
  so you can `std::visit` once at install and instantiate the propagator body
  over the concrete type — an "all simple variables" specialisation with no
  per-read dispatch, versus a mixed fallback. `element` uses this. It costs
  compile time and code size, so reserve it for propagators where reads
  genuinely dominate.

Both are profile-driven: don't pre-emptively specialise. Confirm the dispatch is
actually costing you first.

## Is it the propagator, the strength, or the search?

When a model is slow, "the propagator is slow" is only one of three
possibilities, and they have completely different fixes:

1. the propagator is slow **per call** (this document);
2. the propagator's **strength** is wrong for the problem — too weak (search
   explores too much) or too strong (propagation costs more than the nodes it
   saves);
3. the **search heuristic** is making bad decisions, so no propagator speed
   fixes the node count.

Comparing against **Gecode** and the **MiniCP benchmarks** is a useful way to
tell these apart: if we explore far more nodes than Gecode on the same model,
suspect strength or search, not per-call speed; if we explore *similar or fewer*
nodes but take longer, suspect per-call speed. But investigate before
concluding — matching node counts requires matching search order, propagation
strength differences change the tree, and "fewer nodes but slower" can be a
propagator that is correctly stronger and worth its cost. A node-count and
per-node-time comparison (which the benchmark harness gives you) is the evidence;
the framing above is just where to point it.

## Feeding back into the benchmark set

Use the benchmarking.md table as the standard before/after sanity check, and
treat improving the benchmark situation as part of the work:

- If you find a good new benchmark candidate — a problem that exercises a
  constraint the current set doesn't, or a data shape that flips a decision —
  consider adding it. The long-term goal is a set with a representative problem
  for **every** constraint, each running in roughly the one-second-to-one-minute
  range (long enough to measure, short enough to iterate). Ask the user before
  adding one, so the set stays curated rather than sprawling.
- Converting a MiniZinc Challenge instance into an `examples/` entry that posts
  the model through the API is sometimes the cleanest way to get a realistic,
  constraint-specific benchmark that isn't gated on the whole FlatZinc pipeline.

A performance change that also leaves behind a better benchmark for the next
person is worth more than one that doesn't.

## See also

- [benchmarking.md](benchmarking.md) — the curated benchmark set, the
  before/after harness, and the proof-shape benchmarking notes.
- [constraints.md](constraints.md) — writing the propagator in the first place:
  triggers, backtrackable state, reasons, justifications, testing.
- [reasons-improvement.md](reasons-improvement.md) — the declarative `Reason`
  design that makes reason-reuse sound (lazy materialisation, the tracker seam).
- [state-and-variables.md](state-and-variables.md) — `IntervalSet` domain
  storage, the `IntegerVariableID` variant, and the `State` read/inference
  paths this document tells you to be careful with.

<!-- vim: set tw=78 spell spelllang=en : -->
