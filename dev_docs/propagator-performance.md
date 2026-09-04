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
`recursions` must be identical before and after, on every benchmark. So must
the first integer of `propagations:` — *unless* the change is to when the
propagator runs at all (triggers and idempotence, the first lever below), in
which case fewer executions is the whole point, and `propagations` should
generally fall while `recursions` stays fixed. The benchmark harness prints
both precisely so you can diff them; treat any divergence you didn't set out
to cause as a correctness signal first and a performance signal second
(benchmarking.md, "What to capture"). If you find yourself explaining a
speedup by "well, it also prunes a bit differently now", stop — you have
conflated the two, and you need to re-evaluate the change as a strength change
(with its own soundness and proof review) rather than a free win.

Two caveats on the trigger exception. First, don't expect the drop in
`propagations` to be tidy: skipping a wake reorders the propagation queue, and
with other constraints in the model the work can redistribute — another
propagator may run more or fewer times, or pick up an inference the skipped
wake would have made — so the count can move in perverse directions,
occasionally even up. Second, what makes that reordering safe is
monotonicity: when every propagator infers at least as much from a smaller
domain, the queue reaches the same fixpoint in any order, and the search
cannot tell the difference. A propagator whose inferences depend on
scheduling order in a non-monotonic way loses that guarantee, so a trigger
change interacting with one can, in principle, change `recursions` — at which
point it must be re-evaluated as a strength change, exactly as above.

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

### Find out which constraint is spending the time, before optimising one

`GCS_PROPAGATOR_STATS=calls` adds a per-constraint-type block to the stats: how
many constraints of that type there are, how many propagators they installed,
and how many times those propagators were called, changed a domain, and
contradicted. `GCS_PROPAGATOR_STATS=time` adds the elapsed time in each,
totalled per type. It reaches `%%%mzn-stat:` lines from `fzn-glasgow -s`, `d PROPAGATOR CALLS ...`
lines from `xcsp_glasgow_constraint_solver` (which prints its `d` statistics
unconditionally), and the one-line summary from the default `operator<<` on
`Stats`, so a sweep harness can tabulate it without any per-constraint
plumbing.

Read the two rungs for what they are. `calls` is one increment per propagator
run, so a run with it on is comparable with a run without. `time` reads the
clock twice per run — 13% on `tpp_3_5_20_1`, and far more if the model's
propagators are individually tiny — so a timed run's own wall clock
and nodes-per-second are *not* comparable with an untimed one. Read shares and
per-call figures off a timed run, never throughput.

The reason this section comes before the levers is that the aggregate
`propagations:` count cannot tell you which constraint to look at, and the
answer is regularly not the one you would guess. Two examples, both from the
subcircuit families of the MiniZinc Challenge corpus (issue #788):

- **A propagator's per-node cost is `calls-per-node` times `cost-per-call`, and
  the two vary independently.** `SubCircuit`'s reachability arm looked free on
  `tpp` and crushing on `mario`, at comparable `n`, which read as a per-call
  cost that was not a function of `n`. It is not: per *call* it costs 7.4 µs at
  `n = 15` and 31.2 µs at `n = 30` on `mario`, which is very nearly `n²`, and
  7.7 µs at `n = 15` against 30.7 µs at `n = 35` on `tpp` — it is the most
  expensive propagator per call in that model. It is woken **676 times in
  a 7.5-million-node search** there, because `tpp` fixes its 15 successors in
  the first 15 levels and then spends the whole search below them on
  `purchaseLoc`. On `mario`, whose search *is* the successors, it is woken 1.5
  times a node. Optimising the body would have been the right call and the
  per-node figure alone said the opposite.
- **A propagator can be 50% of the time while pruning nothing at all.** On
  `tpp` the twenty `lin_not_equals` constraints are called 17.8 million times,
  remove a value **once** in the entire search, contradict 3.75 million times,
  and take half the propagation time. That is a propagator whose wake condition
  is far looser than the only situation it can act in, which is the first lever
  below and not a body optimisation.

So: get the per-type breakdown first, and pick the lever from it.

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
They are the one legitimate way to lower the `propagations:` count — see the
ground rule above for what must still hold, and its caveats. Get these right
before micro-optimising the body.

**What a removed wake is worth.** A wake the propagator no longer takes costs
tens of nanoseconds, so the payoff scales with the *scan* the wake skips, not
with the call count on its own. Moving `lin_not_equals` from `on_change` to
`on_instantiated` (issue #807) dropped 9.9M of 17.8M calls on the `tpp`
challenge model, whose flattened `int_lin_ne` has two terms, and moved the wall
clock by nothing measurable (three instances, min-of-3, −0.3% to +0.7% against
a ~1% run-to-run spread); the same change dropped 15.6M of 41.0M calls on a
ten-term not-equals and was a reproducible 6.9% there. Both had identical
`nodes` *and* identical `effectfulPropagations` — which is the shape to insist
on, and the one that says the fixpoint at every node is untouched.

**A `_micros` share is not necessarily wake cost.** `GCS_PROPAGATOR_STATS=time`
brackets the propagator call, so a contradiction's `throw
TrackedPropagationFailed` unwinds inside the sample. `lin_not_equals` on `tpp`
reported 6.23 s of the model's 12.41 s of propagation, and 6.03 s of that
survived removing 56% of its calls: it was 3.75M contradictions at ~1.6 µs
each, not 17.8M wakes. Read the `_contradictions` column before reading a large
`_micros` share as a trigger problem.

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

### Don't throw from a propagator that fails in bulk

`inference.contradiction(...)` signals failure by throwing
`TrackedPropagationFailed`, which the propagation loop catches. The throw and
unwind cost about **1.6 us**, against ~15 ns for a propagator wake — so for a
propagator that is the failure detector at a large fraction of nodes, the
reporting mechanism can cost more than everything else it does. Such a
propagator should use `contradiction_or_stop`, which does the same recording and
logging, sets the `_contradicted` flag the `infer_*_or_stop` family sets, and
returns the `PropagatorState` for the caller to return immediately:

```cpp
return inference.contradiction_or_stop(logger, JustifyUsingRUP{hint}, reason);
```

The loop tests `tracker.contradicted()` as soon as the propagator returns and
does everything the catch clause does — the counters, the conflict observers —
so nothing else changes. Converting `propagate_linear_not_equals`'s all-fixed
check (issue #820) was worth **21% to 29%** end-to-end on three `tpp` challenge
instances, at 1.58 us per contradiction avoided, with every count and the proof
byte-identical.

Pick the candidates off the `_contradictions` column of
`GCS_PROPAGATOR_STATS=calls`, not by eye: a propagator that contradicts a few
thousand times a search has nothing to gain, and the conversion is a control-flow
change in the propagator (it must now return immediately, which
`[[nodiscard]]` enforces) rather than a free win.

**Measure the unwinder by DSO, not by symbol name.** `perf report | grep -i
unwind` finds `_Unwind_Find_FDE` and `__gxx_personality_v0` and misses most of
the cost, because the bulk of `libgcc_s.so.1`'s unwinder has no symbol names in
the profile and appears as bare addresses. On `Dubois-017` a symbol grep says
8.8%; `perf report --sort dso` says **30.7% in `libgcc_s.so.1`**, plus another
10% in `libstdc++.so.6` — and that 40% is what converting the extensional
propagator was actually worth (1.69x measured). Read that way the profile
predicts the prize on every instance, including the ones with no prize in them:

| instance | `libgcc_s` before | after | speed-up |
|---|---|---|---|
| `Dubois-017` | 30.7% | 0.00% | 1.69x |
| `enum_func_k3_n20` | 11.6% | 0.00% | 1.24x |
| `srch_bin_d12_n25_s1` | 7.5% | 0.00% | 1.09x |
| `Crossword` | 1.3% | 0.00% | 1.00x |
| `enum_single_k10_t200k` | 0.0% | 0.00% | 1.00x |

Instruction counts say it more bluntly still: 42.6% of `Dubois-017`'s
instructions were in `libgcc_s` plus `libstdc++` before the change and 1.9%
after, which is 21.6G instructions down to 11.5G for the same search.

Take the zero in the "after" column as well as the speed-up: it says the
conversion caught every failure path the propagator actually uses.

The second lesson from that conversion is that **a propagator can have failure
paths it never actually takes**, and knowing which is what decides how much
there is to do. `propagate_extensional` can fail in two places: the empty live
set, and an `infer` that empties a domain. The second is unreachable for a table
whose variables are distinct -- a live tuple is its own witness that every
position still has a supported value -- so only the first was worth converting,
and the unwinding going to exactly zero is the evidence that the second never
fired.

The counter-example, so nobody re-does it: **`NegativeTable` is not a candidate**,
despite failing 55 497 times in a 3.5 s search of its own benchmark. `libgcc_s`
is **3.6%** there, because its propagator is woken twenty-five times per
contradiction and each wake does real work (`test_literal` alone is 18% of the
profile). The ratio that matters is contradictions per *call*, not per node: the
extensional propagator on `Dubois` contradicts on one call in six, the negative
table on one in twenty-five. `Element` is not a candidate either — 2.2% on `qap`
and 1.5% on `tsp`, despite `tsp` failing 4.3 million times, because most of
those failures already report through the non-throwing `infer_*_or_stop` path.

### The throw survey, and what it found

Rather than guess at the remaining candidates, all 285 MiniZinc Challenge models
(2008-2025, one instance each, capped at twenty seconds) were run with a counter
on each of the two ways a propagator reports failure by unwinding. The raw
material is in `tmp/throw-survey/`. Two things came out of it, and both are worth
knowing before doing this kind of work again.

**`contradiction()` is a solved problem: there are no more candidates.** Across
all 285 models it threw **219 918** times in total, and exactly one model
(`2019_kidney-exchange`) reaches even 1% of its runtime that way. The table
propagator was the outlier, not the first of many.

**The volume is all on the other path — an `infer*` that empties a domain —
which threw 19 457 165 times, eighty-eight times as often.** That is worth
10-22% of the run on six models, and it concentrates in a handful of
propagators. Counting throws by constraint type over the thirty worst models:

| propagator | throws | models |
|---|---|---|
| `count` | 5 954 685 | 7 |
| `or` | 5 629 563 | **19** |
| `disjunctive2d_strict` | 2 435 425 | 4 |
| `all_different_except` | 766 548 | 2 |
| `disjunctive_strict` | 348 160 | 1 |
| `equals` | 266 738 | 13 |
| `element` | 199 096 | 6 |
| `multiply` | 135 549 | 3 |

`count` and `or` are converted (`infer_*_or_stop` throughout `Count`; the clause
conflict in the shared `And`/`Or` propagator is a contradiction spelled as
`infer(FalseLiteral{})` and became `contradiction_or_stop`). On identical trees
that is **1.53x** on a completed `2015/grid-colouring`, and 1.17-2.65x of extra
throughput on the capped models. `libgcc_s` goes to 0.00% on all of them.

The rest are named above and left: `disjunctive2d_strict`'s two prunings sit
inside a lambda in a doubly-nested loop, so stopping has to be threaded out by
hand, and `all_different_except`'s failure is
`gac_all_different.cc`'s matching-too-small `infer(logger, FalseLiteral{}, ...)`,
which would need `propagate_gac_all_different` to return a verdict to its five
callers. Both are mechanical; neither is one line.

**Per-throw cost, measured on an identical completed search** (`gc_4_8`, 322 378
clause conflicts): 5.65G instructions and 1.85G cycles, i.e. **17 500
instructions and about 2.4 us** each. That is the number to multiply a
contradiction count by when deciding whether a conversion is worth it. One model
(`2011/roster`'s larger instance) came out far above that, at 2.65x throughput
for only 5% of cycles in `libgcc_s`, because there the throwing build also takes
**five page faults per node** that the non-throwing one does not; that mechanism
is not understood and is not the general case.

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

### Keep type-erased callables out of per-node and per-inference paths

`std::function` costs in three places: construction heap-allocates whenever
the callable's captures outgrow the small-buffer optimisation (two pointers,
typically), copies are deep and silent, and invocation is an indirect call
the compiler cannot inline through. None of that matters for a callback
built once and invoked on a cold path; all of it matters per node or per
inference. Concretely:

- **Take hot callbacks as template parameters**, not `std::function`.
  `State::for_each_value_immutable` and `JustifyExplicitly`'s `emit` are the
  patterns to copy: the concrete closure type reaches the call site, so it
  inlines and nothing allocates. (This also beats C++26 `std::function_ref`,
  which still costs an indirect call — when the C++26 wrapper types
  eventually arrive on all our toolchains they will improve the cold-path
  vocabulary, not change this rule.)
- **Watch for invisible copies.** Copying a `std::function` deep-copies
  every capture. The archetype was `solve_with_state`: the expression
  `callbacks.branch ? callbacks.branch : <default>` materialised a copy of
  the branch callback — and of everything the composed heuristics captured,
  including a vector of all the branch variables — at every search node, and
  rebuilt the entire default heuristic per node when no callback was set.
  The fix is the shape to reuse: resolve the callback once before search
  starts, then invoke the lvalue in the recursion.
- **Copy semantics are part of a closure's interface.** Because a
  `std::function` may be copied at any time, mutable state captured into one
  must sit behind a `shared_ptr` so every copy aliases it (the RNG sharing
  in `search_heuristics.cc` is the documented example). Capturing an RNG or
  a cache by value looks equivalent and is not: the first silent copy forks
  its state.
- An owning wrapper is still correct when the callable is **stored** and
  outlives the call that created it: `SolveCallbacks`, tabulation's
  `accept`, deferred proof lines, or a callable parameter a coroutine keeps
  in its frame across suspensions. A non-owning reference (a raw callable
  `&`, or an eventual `std::function_ref`) in any of those positions
  dangles.

`PropagationFunction` is bespoke erasure for a different reason: a
propagator must be invocable with either inference-tracker type, which means
two `operator()` signatures — beyond any `std::function`-family type. It is
constructed once at install time, so per-wake it costs the same single
virtual call either way.

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

**A worked example of confirming it, and of getting the confirmation wrong.** In
the extensional (table) propagator, `State::in_domain` is 34% of the profile: it
is called once per (live tuple, position) in the feasibility pass, through the
`IntegerVariableID` variant. That looks like the textbook case for specialising.
It is not, and three measurements say so:

- `perf annotate` on `in_domain` shows its hot block is `cmpq %rdx,%rcx` /
  `cmpq (%rax),%rcx` / `addq $0x10,%rax` — a linear scan over the `IntervalSet`'s
  interval array, sixteen bytes per step, with **no discriminant test and no
  indirect branch in it**. GCC had already lowered the visit away.
- Specialising the pass over a concrete `std::vector<SimpleIntegerVariableID>`
  moves 1971 of 1995 `in_domain` samples from the variant instantiation to the
  concrete one, and leaves the total unchanged.
- End to end it measures 1.0x on all 18 instances of the table benchmark matrix.

The 34% is the intrinsic cost of testing interval membership, and the ways to
move it are algorithmic — call it less, or find a cheaper test than a scan.

Two traps to avoid when running this experiment, both of which produced a
confident wrong answer first time:

- **A helper that takes `const IntegerVariableID &` silently un-specialises its
  caller.** Passing a concrete `SimpleIntegerVariableID` to it converts back into
  the variant at the call site, so `State::in_domain` is still the variant
  instantiation and the "specialisation" changes nothing. Check the profile for
  which instantiation the samples are actually in, rather than assuming the
  specialisation took.
- **Make sure the benchmark binary relinked.** If the harness does not depend on
  the solver library, a before/after comparison measures one build against
  itself and reports exactly 1.00x for everything. `md5sum` the two binaries when
  a change reads 1.00x across the board.

### Adding a second algorithm to a hot function slows down the first one

The table propagator later grew a compact-table path alongside the live-set one,
chosen per instance and dispatched on a bool at the top of
`propagate_extensional`. That should cost the live-set path one predictable
branch per call. It cost it far more than that, on instances that execute none
of the new code, and for three unrelated reasons — each worth checking for
whenever a second path lands in a function that was already hot. The three are
separate costs on different instances, not three explanations of one number.

- **The inner test stopped being inlined.** `perf record` showed
  `bitmap_feasible` — pass 1's membership test, previously inlined away — as a
  separate symbol at 27% of runtime. The function had not changed; the function
  it was called from had grown past GCC's inlining budget. `[[gnu::always_inline]]`
  on the test put it back, worth **10% on `srch_k5`** and 25% of the instruction
  count. The symptom to look for is a helper appearing in the profile that did
  not use to be there at all.
- **Instruction footprint, even from code that never runs.** Before the new pass
  was moved out of line with `[[gnu::noinline]]`, it cost 7% on `Dubois` — an
  instance whose propagator does almost nothing per call, so its cost is
  dominated by how much of the function is resident.
- **Constraint state is not free to declare.** Every slot added with
  `State::add_constraint_state` is deep-copied into every search node, so two
  extra integers per table cost `Dubois` 14% and `enum_shared` 24% before the
  second one was folded into the undo trail and the first was made conditional on
  the table being large enough to want it. A propagator that ends up not using
  the state still pays for it at every node.

The general shape: a second algorithm is not free for the first one even when it
is never executed, and the cost does not show up where you would look for it. Any
such change needs the *old* path measured against the *unmodified* build, not
just the new path measured against the old one.

## Is it the propagator, the strength, or the search?

When a model is slow, "the propagator is slow" is only one of three
possibilities, and they have completely different fixes:

1. the propagator is slow **per call** (this document);
2. the propagator is **called too often** for what it can infer (the triggers
   lever, and the first thing `GCS_PROPAGATOR_STATS` tells you);
3. the propagator's **strength** is wrong for the problem — too weak (search
   explores too much) or too strong (propagation costs more than the nodes it
   saves);
4. the **search heuristic** is making bad decisions, so no propagator speed
   fixes the node count.

The per-type breakdown separates 1 from 2, which the aggregate counts cannot:
divide the calls by the nodes for how often, and the time by the calls for how
expensive, and never read one of those off the other.

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
