# Difference logic: `DifferenceConstraints` and the `DifferenceLogic` presolver

`DifferenceConstraints` propagates a whole system of `x - y <= d` at once,
rather than one propagator per constraint. This note covers the graph
formulation, the two propagation directions, the round bound and why the
negative-cycle extraction is total, the canonicalisation rule and why it exists,
the two proof shapes with worked examples, half-reified edges
(`b -> x - y <= d`) and what they cost in the reason and in the proof, the
defects in the source paper's pseudocode, the presolver that lifts an
already-posted model into the same propagator, the root simplification stage,
the incremental algorithms and the invariants they rest on, and what is
deliberately deferred.

The source is Kletzander, Dekker, Schutt and Stuckey, *Global Difference
Constraint Propagation for Constraint Programming*, arXiv:2607.20022 — the
journal expansion of Feydy, Schutt and Stuckey (PPDP 2008). Issue #571 tracks
the whole effort; this document describes what the first propagator PR actually
does, which is a deliberately small slice of the paper.

## The graph

A system `C` of difference constraints is a weighted digraph `G_C`: one vertex
per variable, and one edge `x --d--> y` per constraint `x - y <= d`. Note the
direction — the tail is the constraint's left hand side.

Two classical facts (the paper's Theorem 1, from the Shostak / Dechter-Meiri-
Pearl lineage) are all the reasoning we need:

- `C` is satisfiable iff `G_C` has **no negative-weight cycle**;
- `C ⊨ x - y <= d` iff the **shortest path** from `x` to `y` weighs at most `d`.

The paper encodes variable bounds as edges to a dummy vertex `v0` fixed at 0
(`x >= l` is `v0 --(-l)--> x`, `x <= u` is `x --u--> v0`), which turns bounds
propagation into single-source shortest paths from `v0` (their Corollary 1).
`v0` is never materialised here: the seeding of the two Bellman-Ford passes
below *is* the `v0` edge set, expressed directly as the initial distance array.

## The two directions

Read one edge `x --d--> y`, i.e. `x - y <= d`, in both directions:

- as `y >= x - d`, so **lower bounds flow forwards**: `lb(y) >= lb(x) - d`;
- as `x <= y + d`, so **upper bounds flow backwards**: `ub(x) <= ub(y) + d`.

So the propagator runs two Bellman-Ford passes:

1. **Lower bounds**, over the graph as given, seeded with `lb(v)` for every
   node. Writing `dist(v) = -lb(v)` this is literally shortest paths from `v0`
   with `w(v0, v) = -lb(v)`.
2. **Upper bounds**, over the reverse graph, seeded with `ub(v)`.

The two passes are **independent**, which is what makes one pass each a complete
fixpoint rather than something that has to be iterated: each edge relates only
`lb(x)` to `lb(y)`, and only `ub(y)` to `ub(x)`, so the lower-bound closure
depends on nothing but the initial lower bounds and vice versa. Reaching that
closure is exactly what Bellman-Ford computes.

Infeasibility shows up two ways, and both are handled:

- a **negative cycle**, which is infeasibility of the difference system on its
  own, refuted directly (below);
- a pushed bound crossing the opposite bound, which the framework turns into a
  contradiction when the inference empties the domain.

One caveat on "one pass each is the fixpoint": it is the fixpoint of the
*bounds abstraction*. gcs domains can have holes, so an inferred bound can snap
past the value Bellman-Ford computed, which may license a further push. The
propagator therefore triggers on the bounds of every node it owns, returns plain
`Enable` rather than `EnableButIdempotent`, and is re-woken by its own
inferences until the state stops moving.

## Rounds, and why the extraction is total

With `n` nodes, a shortest path from `v0` is simple, and the seeding *is* the
`v0` edge set, so at most `n - 1` real edges remain and `n - 1` relaxation
rounds always suffice. The loop runs rounds `0 .. n - 1` — one more than needed
— and then round `n` purely to detect: a relaxation that still succeeds there is
sound evidence that the system has a negative cycle.

The extraction then walks `pred` back from the node just relaxed, marking as it
goes, and both things it needs are true.

**The walk never runs off the end of the forest.** Suppose it did: it visits
distinct nodes `v, a_1, …, a_k` with `a_k` having no predecessor, so `dist(a_k)`
has sat at its seeded value since before round 0. Those nodes are distinct, so
`k <= n - 1`, and `a_k ⇝ v` is a real path of `k` edges out of a source whose
distance never moved — which after `k <= n` completed rounds forces
`dist(v) <= dist(a_k) + w(a_k ⇝ v)`. But `pred` gives exactly the reverse:
`dist(v) = dist(a_1) + w_1` at the instant it was set, and
`dist(a_i) >= dist(a_{i+1}) + w_{i+1}` throughout (each was an equality when its
pointer was set, and the tail has only fallen since), so
`dist(v) >= dist(a_k) + w(a_k ⇝ v)` — *after* the strictly improving relaxation
that round `n` has just made. The two together say `dist(v) < dist(v)`. So the
walk must revisit a node, and the first repeat is on a cycle.

**Every cycle in the predecessor graph is a negative cycle.** A cycle comes into
existence at the moment its last pointer is set, say `pred[v_1] := (v_k, v_1)`,
the rest already being in place. Chaining the same inequalities from `v_1` round
to `v_k` gives `dist_new(v_1) = dist(v_k) + w_k >= dist_old(v_1) + W`, and
setting the pointer at all required `dist_new(v_1) < dist_old(v_1)`, so `W < 0`.
Its edges and weights never change afterwards — reassigning any of them destroys
the cycle — so whenever one is found it is still negative. Summing the edge rows
round it cancels every distance and leaves `0 > W`.

Neither argument is left to trust: the extracted cycle is re-checked
arithmetically before anything is emitted (below).

## Canonicalisation, and why

Every operand of every edge is reduced at construction to a bare
`SimpleIntegerVariableID` plus an offset, and the offsets are folded into the
weight:

```
V1 - V2 <= d,  V1 = X + c1,  V2 = Y + c2      ⇒      X - Y <= d - c1 + c2
```

Three cases fall out:

| Operands | Result |
|---|---|
| two distinct variables | a graph edge |
| one variable, one constant | a **static bound** on the variable (`X <= d` or `Y >= -d`) |
| the same variable twice, or two constants | `0 <= d`: vacuous, or a **root contradiction** |
| a negated view `-X + c` | **rejected**, `InvalidProblemDefinitionException` |

**Negated views are rejected because accepting them would be unsound, not merely
incomplete.** `V - W <= d` with `V = -X + c` is `-X - W <= d - c`, which is not
a difference constraint at all: both coefficients are negative, the graph
formulation does not describe it, and treating it as an edge would licence
inferences the constraint does not entail. This is the survey's section 2.6(e).

**The OPB rows are emitted over the canonical form**, not over the operands the
user handed in, and that is the load-bearing decision of the whole design.
`dev_docs/view-proof-logging.md` invariant 1: a `pol` only cancels a variable
when both lines express it in the *same* representation. A registered view `V`
of `X` has its own bit-vector, related to `BinEnc(X)` only by the link axiom, so
two edges that meet at "the same variable" through two different views would not
cancel at all and every derivation below would strand. Both proof shapes here
are cancellation-driven, so this is not a small risk — the survey ranks it as
the single most likely thing to go wrong, and it is the historical
`Abs`/`AllDifferent` bug class.

Emitting the deviewed row removes the problem by construction, and it is still
definitional: `X - Y <= d - c1 + c2` states exactly the posted `V1 - V2 <= d`,
just written in the bare variables' bits. Nothing else goes in the OPB — no
flags, no auxiliaries — and every inference the propagator makes is a
cutting-planes consequence of those rows alone. (The alternative, which
`linear/justify.cc` takes, is to emit in the user's operands and switch the
`PolBuilder` into deview mode. That is strictly more machinery for the same
result here, because this constraint owns both ends of every cancellation.)

One labelled row per **posted** edge, role `e<i>` with `i` the edge's index in
the list the user gave, so a proof line traces back to the edge that was
written. Rows are emitted even for edges that contribute no graph edge: an
aliased edge leaves the same variable in the sum twice with opposite
coefficients, and a two-constant edge leaves the sum empty, and both render as a
row whose left hand side is zero — which is what `0 <= d` says, and which VeriPB
reads as trivially true or directly false according to `d`'s sign. A false one
is a root contradiction that RUPs straight from the model, via
`Propagators::install_initial_contradiction`.

## Proof shape 1: negative cycle ⇒ contradiction

Sum the cycle's edge rows and nothing else. Each variable appears once with `+1`
(as some edge's head) and once with `-1` (as the next edge's tail), so every
`BinEnc` term telescopes away and what is left is `0 >= -W` with `W < 0`, i.e. a
constraint of positive degree over an empty left hand side. All multipliers are
`1`; there is no multiplication, division or saturation, and (by total
unimodularity of a node-arc incidence matrix) there never needs to be.

The reason is **empty** — no domain state is used at all.

Worked example, straight out of `examples/difference_chain --mode=refute
--variant=global -n 10 --prove`, whose model closes a negative cycle of weight
`-1` round a 13-edge chain. The entire `.pbp` is:

```
pseudo-Boolean proof version 3.0
pol @c[_1][e18] @c[_1][e19] + @c[_1][e9] + @c[_1][e75] + @c[_1][e29] + @c[_1][e10] + @c[_1][e11] + @c[_1][e12] + @c[_1][e13] + @c[_1][e14] + @c[_1][e15] + @c[_1][e16] + @c[_1][e17] + ;
rup >= 1;
...
```

12 lines, **independent of the domain size and of `n`**. The same model posted
as one `LinearLessThanEqual` per edge needs `1760k - 468` lines at `n = 10` for
`k >= 2`, where `k` is the domain multiplier — the per-constraint propagators
can only find the contradiction by crawling every bound up one unit at a time.
At `k = 64` that is 112,172 lines against 12. (`k = 1` is off the line at 294
lines: the domain `0..10` is too narrow for the crawl to get going before the
bounds cross.)

## Proof shape 2: bound push ⇒ one `pol` per edge

Inferences are made **per edge along the predecessor forest, not per path**.
After Bellman-Ford converges, the improved nodes are walked in an order
consistent with the predecessor relation (the forest's roots are exactly the
nodes whose bound did not improve), and each node's new bound is inferred citing
*its predecessor's already-inferred bound*. Each such inference is then a
single-edge push, and its proof is one `pol`:

```
pol  <edge row>  <definition row for the predecessor's bound literal>  + ;
```

For a lower-bound push across `x --d--> y` with the predecessor at `x >= L`:

```
  (edge row)          -BinEnc(x) + BinEnc(y)                >= -d
  (D+[x >= L])         BinEnc(x) + M·¬[x >= L]              >= L
  ────────────────────────────────────────────────────────────────
                       BinEnc(y) + M·¬[x >= L]              >= L - d
```

and the framework's closing reason-wrapped RUP then derives
`[x >= L] → [y >= L - d]`. Upper bounds are the mirror image, citing the
definition row of `[y < U + 1]` and concluding `[x < U + d + 1]`.

This is `justify_linear_bounds` for a two-term linear, which is no accident: a
single difference edge *is* a two-term linear, and the global propagator's only
extra power is that it chains the pushes. It is also the shape verified by hand
in `boundpush_hand.pbp` (see the survey directory) before any of this was
written.

Real output, from the four-variable chain in
`gcs/constraints/difference/difference_constraints_test.cc`:

```
red 1 i[_2][b0] 2 i[_2][b1] 4 i[_2][b2] 1 ~i[_2][ge1] >= 1 : i[_2][ge1] -> 0;
red -1 i[_2][b0] -2 i[_2][b1] -4 i[_2][b2] 7 i[_2][ge1] >= 0 : i[_2][ge1] -> 1;
...
pol @c[_1][e0] -3 + ;
rup 1 i[_2][ge1] 1 ~i[_1][ge0] >= 1;
```

Two properties worth naming:

- **Per-edge is `O(1)` proof lines per inferred bound**, where a per-path
  justification would be `O(path length)`. It also needs no intermediate atoms
  beyond the ones the inferences mint anyway.
- **The reason is already "lifted"** in the paper's section 4.3.3 sense. The
  weakest antecedent for `y >= L - d` across this one edge is exactly `x >= L`,
  so the `pol`'s degree comes out at exactly the pushed amount with no wasted
  slack, and the learned clause is magnitude-invariant. The paper measures its
  `Simple` explanation (cite the current bounds, whatever they are) as clearly
  the worst of its three; per-edge inference gets `Lifted` for free, without
  choosing to.

The `pol` is load-bearing, not decoration. RUP cannot compose across
constraints: transferring the predecessor's *order atom* into the edge row's
`BinEnc` terms is a linear addition of two constraints, which unit propagation
never performs (`view-proof-logging.md` invariant 3, and the same finding
`dev_docs/disjunctive-proof-logging.md` records for its single-edge pol).

## Half-reified edges: `b -> x - y <= d`

An edge may carry a reification condition. The semantics are deliberately
one-directional:

> **An edge with a condition participates in the graph exactly while that
> condition currently holds.** Nothing is ever inferred the other way — the
> propagator never fixes a condition because of what the graph says.

That second half is the paper's `IncImp`, and leaving it out is not laziness: it
is the paper's own most strongly supported configuration finding. On RCPSP/max
*every* configuration with `IncImp` on scored below *every* configuration with
it off. The proof shape for it is already understood (below), so it is a small
addition if it is ever wanted; the measurements say not to want it.

Three shapes fall out of the same canonicalisation as before:

| Canonical form | Unconditional | With condition `b` |
|---|---|---|
| two distinct variables | graph edge | graph edge, active while `b` holds |
| one constant operand | static bound | bound applied while `b` holds, citing `b` |
| `0 <= d`, `d < 0` | root contradiction | **`!b` is inferred** |

The last row is a soundness obligation, not a nicety. `b -> 0 <= -1` says `!b`,
and an implementation that quietly dropped the edge would return solutions in
which `b` holds and the constraint is violated. It is handled in the propagator
rather than by an initialiser (which is how the unconditional case is done),
because the row `M·¬b >= 1` saturates directly to the unit clause `¬b`, so plain
RUP against it suffices — and because a presolver has no initialiser available.

### The reason, which is the whole soundness question

**A negative cycle** cites the conditions of every conditional edge on it, and
nothing else. The unconditional case keeps its empty reason. The conditions are
deduplicated, because the same Boolean legitimately appears on more than one
edge — a disjunctive encoding makes that the normal case — and a reason listing
it twice would render a proof line with a repeated literal.

**A bound push** cites the predecessor's bound and *this edge's* condition, and
that is the part worth being careful about. It is not "every condition along the
path", and it does not need to be, because the inference is made **per edge
along the predecessor forest**, never per path (see proof shape 2). The
predecessor's bound was either already there when the call started, or was itself
inferred moments earlier carrying its own edge's condition in its own reason. So
the conditions along a whole path are cited by the *chain* of inferences, and
each individual link is a standalone entailment of exactly one OPB row — which
is what makes each link's RUP check on its own.

### The proof: one extra `saturate`, and that is all

A row emitted under `HalfReifyOnConjunctionOf` carries a big-M term on `¬b`. It
does not telescope. Everything else does, exactly as before, so summing a cycle
whose edges are conditional on `b_1 … b_k` leaves

```
    Σ M_i·¬b_i  >=  -W        (with -W >= 1)
```

and one `saturate` turns that into the clause `¬b_1 ∨ … ∨ ¬b_k` — the learned
clause. The emitted line is

```
pol  <edge row>  <edge row> +  <edge row> +  s ;
rup 1 ~b_1 1 ~b_2 >= 1;
```

which is verbatim the shape hand-verified against real gcs OPB output in
`reified.opb` / `reified_hand.pbp` (survey section 2.0a case 3) before any of
this was written, and verbatim what the propagator now emits — from
`difference_test reified negcycle_two_conds`:

```
pol @c[_1][e0] @c[_1][e2] + @c[_1][e1] + s ;
rup 1 ~i[_4][b0] 1 ~i[_5][b0] >= 1;
```

With one Boolean shared between all three edges the same line closes with
`rup 1 ~i[_4][b0] >= 1;`, which is the deduplication above showing up in the
proof.

Two honest notes on that `s`:

- **The reason is load-bearing; the `saturate` is not.** Dropping a condition
  from the reason fails VeriPB on the reified fixtures (confirmed by mutation).
  Removing the `saturate` does **not** — the closing RUP assumes every condition,
  which drives each `M·¬b` to zero and falsifies the unsaturated line just as
  well (also confirmed by mutation, every reified fixture still verifies). It is
  emitted anyway because it makes the derived line *be* the clause rather than a
  big-M encoding of it, which is what a reader, an assertion hint, or a
  longer-lived `ProofLevel` would want.
- **The bound push does not saturate.** Its residual is harmless under the
  closing RUP for the same reason, while saturating would clamp `BinEnc(v)`'s own
  coefficients against the degree for no gain.

Everything else is unchanged: no new OPB content, no flags, no auxiliaries. The
unconditional path is byte-identical — `.opb`, `.pbp`, `.scp` and `.varmap` all
compare equal before and after across `difference_test views`,
`difference_chain -n 6` in both modes and all three variants, and `rcpsp` in all
three variants. `tools/opb_snapshot.bash` also still matches `main` byte for byte
on the three `rcpsp` entries in the proof benchmark set.

### Triggers

The propagator already woke on every node's bounds. It now also takes
`on_change` on each distinct condition variable. That is the coarsest trigger gcs
offers that is guaranteed to catch a condition *becoming true*:

- `on_bounds` is not enough — `x != v` becomes true the instant `v` leaves the
  domain, which can be an interior removal;
- `on_instantiated` fires strictly less often still — `x >= v` can become true
  long before `x` is fixed.

There is no "becomes entailed" coarse trigger, and the refined per-literal
watches would need one arming per condition, so `on_change` is both the cheapest
correct choice and the simplest. Waking when a condition becomes *false* is not
needed at all — an inactive edge simply does not participate, and no inference is
lost by finding that out later — but `on_change` cannot distinguish the two
directions, and the extra wake is cheaper than machinery to avoid it. Condition
variables are deliberately not deduplicated against the node list: a variable
that is both a node and somebody's condition would otherwise have to give up one
of the two trigger kinds, and a duplicate wake is merely wasted work.

### The termination and extraction arguments still hold, verbatim

Both arguments above — the `n - 1` round bound, and the totality of the
predecessor walk — are statements about **one Bellman-Ford run over one fixed
edge set**. Neither mentions where the edges came from or whether the same set
will be there next time. So the only obligation half-reification adds is that the
edge set really is fixed for the duration of a call, and that is arranged
directly: the active edges are **snapshotted once** at the top of the call,
rather than re-tested as the passes go.

The snapshot also stays *correct* as inferences land during the call, which is
what licenses citing a snapshotted condition in a reason later on. A literal that
is definitely true holds for every value in the current domain, so it holds for
every value in any subset of that domain; all this propagator does is shrink
domains, and a domain shrunk to empty is a contradiction, which ends the call. So
a condition true at snapshot time is still true at every inference made from it.

Across calls the edge set does change — it grows as conditions become true down a
branch and shrinks on backtrack — and nothing needs to be trailed for that,
because nothing about the graph is stored between calls. This version recomputes
from scratch every wake anyway.

### Two things that cost 3× until they were measured

Both were found by benchmarking `examples/difference_chain --variant=global` at
`n = 640` against the table above, not by inspection, and both left the
propagation and recursion counts *identical* — so nothing but wall clock would
have caught either.

- **The condition must not live in the edge struct.** An
  `optional<IntegerVariableCondition>` is 64 bytes, which took the edge from 32
  bytes to 96. The relaxation loop scans the whole edge array once per round, so
  that is 3× the memory traffic in the innermost loop, and it cost exactly that:
  0.32 s → 0.93 s. `DifferenceGraphEdge` therefore stays the convenient
  *construction* type, with the condition attached to the edge it belongs to,
  and `install_difference_propagator` repacks it once into a 32-byte arc array
  plus a parallel condition array. The conditions are read when the active set is
  snapshotted (once per call) and when a reason is built (only when something is
  inferred) — never inside a round. A `static_assert` pins the arc size.
- **An unconditional system must not go through the snapshot.** Iterating
  `active_edges` rather than `0 .. m-1` is a level of indirection in the same
  innermost loop, worth another 45% (0.32 s → 0.47 s). When nothing is
  conditional the snapshot is not built at all and the arc array is scanned
  straight through; the branch sits *outside* the per-edge loop, so the
  conditional case pays nothing for the choice either.

With both, `--variant=global` at `n = 640` is 0.332 s against the 0.323 s
measured before half-reification existed, which is inside the noise.

### The completeness caveat, which is the paper's and not ours

The paper's section 4.1 claims its propagator is a *domain* propagator only
"under the assumptions that the domain `D` is a range domain and **no Boolean
variable appears twice** in the set of difference, bounds, and half-reified
difference constraints".

A disjunctive encoding violates that by construction: `b -> i before j` and
`!b -> j before i` put the same Boolean in two difference constraints, and that
is precisely the modelling this feature exists to support. So the claim does not
apply to the most important use case. Two things follow, and they are worth
keeping apart:

- **Soundness is unaffected.** Nothing above depends on a Boolean appearing at
  most once; each inference is an entailment of the rows it cites.
- **Completeness is not claimed.** This is a bounds-consistent propagator for the
  active sub-system, nothing more — which it already was, since gcs domains have
  holes where the paper's Theorem 2 assumes ranges (its section 4.1 caveat (vi)).
  `difference_test reified negcycle_shared_cond` pins the sound-regardless part.

## The self-check

Before emitting a cycle refutation the extracted cycle is verified
arithmetically: that each edge meets the next at the node it claims to, that the
walk closes, and that the total weight really is negative. That is `O(cycle)`,
negligible, and it turns a predecessor-walk bug into an exception at the right
place rather than a VeriPB failure hundreds of lines later. The same check is
applied to each bound push (the pushed value must equal the predecessor's bound
plus the edge weight).

This matters more than usual here because of an asymmetry the survey points out
(section 2.1): if the algorithm produces a **wrong** inference, the `pol` will
not verify and proof logging catches it; if it produces a **missing** inference,
proof logging cannot help at all, because a proof only ever certifies what was
derived. Hence also the cross-check in the test suite, which posts each system
twice — once as `DifferenceConstraints`, once as individual two-term
`LinearLessThanEqual` constraints — and requires the solution sets to be
identical. A soundness bug shows up there as a missing solution and an
over-pruning bug as an extra one, neither of which any proof would catch.

Solution-set equality still would not show that the *new* strength ever fired: a
propagator that inferred nothing at all would pass every one of those cases, just
by searching harder. So two tests assert behaviour directly rather than counting
solutions. `run_transitive_test` posts `x - y <= -3` and `y - z <= -4` over
`0..10`, propagates the root, and requires `z >= 7` and `x <= 3` — bounds that no
single edge implies, so they can only come from a chained push.
`run_negated_view_test` requires `InvalidProblemDefinitionException` for each of
`-x`, `-y` and `-x + 2` as an operand, and fails if no exception is raised rather
than passing silently. Both were confirmed by mutation: stubbing out
`infer_along_forest` fails the first, and dropping the `negate_first` check fails
the second.

## Defects in the paper's pseudocode

Two, catalogued so nobody transcribes them:

- **Algorithm 3 lines 15-16 use `γ(s)` after line 10 has set it to `+∞`.** The
  value intended is `wSP(v0, s)`, saved on line 9. Transcribed literally the
  relaxation test is always `+∞ < γ(t)`, which is false, and the algorithm
  never propagates anything. The paper's own Example 7 arithmetic disambiguates
  it.
- **The `δ→` / `δ←` notation is not self-consistent.** Section 3.1 defines
  `δ←_x(y) = wSP(x, y)` and `δ→_x(y) = wSP(y, x)`; Algorithm 3 line 11 then
  writes `δ→_{v0}(s) := wSP(v0, s) + π(s) - π(v0)`, which is `δ←` by that
  definition. Read Algorithm 3 throughout as "distance *from* `v0`". (Line 20
  also drops its argument, which is merely cosmetic.)

Two more from the paper that bear on this PR even though the algorithms they
belong to are not implemented yet:

- The `Do` gate in Algorithm 3 is against the *previous run's* bounds, not the
  current ones, and the paper never says what happens to `Do` on backtracking.
  Loosening it is always sound, tightening it silently loses propagation — and
  a lost propagation is invisible to proof logging. See "Incremental
  propagation" below, which is where this bites and where the answer is.
- **Section 5.4 describes half of what section 4.4 requires on edge addition.**
  Transcribing the during-search section alone loses every push a reification
  delivers. Also below.
- Theorem 2 assumes **range** domains. gcs domains have holes. The propagator
  stays sound (it only reads and writes bounds), but the theorem's completeness
  half only holds for the bounds abstraction — so this is a bounds-consistent
  propagator, and its tests use `solve_for_tests`, never
  `solve_for_tests_checking_gac`.

## Measurements

`examples/difference_chain` builds the paper's Example 8, whose root fixpoint is
`Θ(n³)` under one-propagator-per-constraint with an unlucky posting order and
`Θ(n²)` with a lucky one. `--variant=global` posts exactly the same edges as one
`DifferenceConstraints`. Medians of 3, `k = 2`, release build, no `--prove`:

| n | order | variant | propagations | recursions | time (s) |
|---:|---|---|---:|---:|---:|
| 40 | unlucky | decomposed | 37,102 | 43 | 0.00125 |
| 40 | unlucky | global | **87** | 83 | 0.00055 |
| 40 | lucky | decomposed | 3,601 | 43 | 0.00064 |
| 40 | lucky | global | **87** | 83 | 0.00043 |
| 160 | unlucky | decomposed | 2,126,002 | 163 | 0.0459 |
| 160 | unlucky | global | **327** | 323 | 0.0081 |
| 160 | lucky | decomposed | 52,801 | 163 | 0.0088 |
| 160 | lucky | global | **327** | 323 | 0.0073 |
| 640 | unlucky | decomposed | 132,305,602 | 643 | 3.542 |
| 640 | unlucky | global | **1,287** | 1,283 | 0.323 |
| 640 | lucky | decomposed | 825,601 | 643 | 0.199 |
| 640 | lucky | global | **1,287** | 1,283 | 0.269 |

The headline is not the speed-up, it is the **column that does not move**: the
global propagator's count is `2n + 7` for both orders, so the cost stops
depending on the sequence the edges were handed over in. Bellman-Ford visits
each edge a fixed number of times whatever order they are stored in; the
decomposed model's propagation queue does not.

Two honest caveats. First, `recursions` differs between the variants because the
default `dom_then_deg` brancher sees different variable degrees — one global
propagator gives every variable degree 1, where the decomposition gives `y_0`
degree `n + 1` — so this is a search-shape change as well as a propagation
change and the two columns have to be read together. Second, the table above was
measured before incremental propagation existed, so its `global` column is the
from-scratch route: on the *lucky* order at large `n` it is slightly slower in
wall time despite doing 640× fewer propagations, because every wake re-ran the
whole `O(rounds × |E|)` pass from the current bounds. That was a property of the
implementation and not of the approach, and the section on incremental
propagation below is where it goes away — 0.269 s → 0.057 s at `n = 640`.

Proof size, `--mode=refute` (the same system plus one edge closing a
negative cycle of weight `-1`), `n = 10`:

| k | decomposed `.pbp` lines | global `.pbp` lines |
|---:|---:|---:|
| 2 | 3,052 | **12** |
| 4 | 6,572 | **12** |
| 8 | 13,612 | **12** |
| 16 | 27,692 | **12** |
| 32 | 55,852 | **12** |
| 64 | 112,172 | **12** |

and against `n` at `k = 2`:

| n | decomposed | global |
|---:|---:|---:|
| 5 | 842 | **12** |
| 10 | 3,052 | **12** |
| 20 | 11,672 | **12** |
| 40 | 45,712 | **12** |

The decomposed figure is `1760k - 468` in the domain multiplier for `k >= 2`,
exactly linear; the global one is a constant, because the refutation is one
`pol`. (PR #583 reported `1760k - 481` for the decomposed model; the 13-line
difference is the posting-order change made here, which moves the cycle-closing
edge in front of the lower-bound bump so that both variants post identical edge
sequences.)

## The presolver

`DifferenceLogic` (`gcs/presolvers/difference_logic.hh`) scans a posted
`Problem` for difference-shaped constraints and installs the propagator above
over them, **alongside** the donors' own propagators. A model written as
ordinary two-term `LinearLessThanEqual`s does not have to be rewritten to get
the global propagation. It is off by default; the user opts in with
`problem.add_presolver(DifferenceLogic{})`.

The timing dictates the shape and is worth stating plainly. Presolvers run
*after* `create_propagators` and *after* the proof model is finalised
(`solve.cc`), so a presolver **cannot remove** the donors' propagators and
**cannot add OPB content** — `Presolver::run` is handed no `ProofModel *` at all.
That is the paper's §4.4 hybrid, and it is also what makes the proof trivial:
each donor already emitted its own labelled row, so the global propagator cites
*those* rows and derives nothing that is not a cutting-planes consequence of
constraints the model already contains.

### What is lifted, and what is not

The paper's **level 1**, restricted to what the propagator supports today: a
two-term linear with coefficients exactly `+1` and `-1` and two distinct variable
operands, each of which may carry a `+X + c` view offset. The reification
condition may be either of two kinds:

- **`reif::MustHold`**, giving a plain edge;
- **`reif::If`**, giving a half-reified one, `b -> x - y <= d`.

**Both forms are citable, and this was checked rather than assumed.**
`linear_inequality.cc` labels them identically — `add_labelled_constraint(id, "",
…)`, i.e. `@c[<id>]` with an *empty* role — and differs only in passing
`HalfReifyOnConjunctionOf{cond.cond}` for the `If` form. So the `If` row is
exactly the shape the propagator's proofs assume, unlike `Comparison`'s
unconditional rows, which go through the `void`-returning `add_constraint` and
carry no label at all.

The other three reification kinds are *also* difference constraints, and are
skipped only because each needs a **different row** of the donor's output than
the two above:

- `reif::MustNotHold` and `reif::NotIf` state the integer negation,
  `y - x <= -d-1`;
- `reif::Iff` emits its two halves under the roles `r` and `f` rather than under
  the empty role — and both halves are edges, one on `cond` and one on `¬cond`.

They are counted in `skipped_reified` rather than guessed at. Two exclusions
remain soundness requirements rather than mere incompleteness:

- **Negated views are refused**, for the reason given above.
- **Degenerate conditional donors are left to the donor.** A conditional
  `x - x <= -1` says `!b`, which the donor already infers from its own bounds;
  lifting it would duplicate that, and the presolver skips all degenerate shapes
  anyway.

**Half-reified donors are never retired**, however many of their edges were
lifted, and that is a rule rather than a preference. `disabling_lifted_donors()`
rests on the global propagator subsuming the donor, and for a half-reified donor
subsumption fails in one direction: `LinearLessThanEqualIf` also infers `!cond`
when its own bounds make the inequality impossible, and the global propagator
makes no inference about a condition at all. Retiring one would silently lose
that. Only unconditional donors go on the retirement list; the tripwire test
asserts both halves of this (something must be disabled when there is an
unconditional edge, nothing may be when there is not).

Degenerate edges — a constant operand, or the same variable at both ends — are
also skipped, and left to the donor. This is not just tidiness: a `0 <= d` with
`d < 0` is a root contradiction, which `DifferenceConstraints` reports with
`install_initial_contradiction`, and **initialisers have already run** by the
time a presolver is called. Declining to lift such an edge leaves it with the
donor, which handles it correctly.

**`Comparison` donors are the shape we most want and cannot yet have.**
`x <= y + d` over an offset view *is* a difference constraint, but
`ReifiedCompareLessThanOrMaybeEqual::define_proof_model` emits its unconditional
rows through the `void`-returning `add_constraint`, so they carry no `@label`
and no proof step can cite them. They are detected, skipped, and **counted**, so
what a later labelling PR would buy is measured rather than guessed at.
Labelling them touches the `cake_pb_cp` chain surface, hence the deferral.

### Deview mode is the one thing the shared propagator needed

`DifferenceConstraints` emits its own rows over the canonical bare variables,
which is why its pols telescope. A donor's row is emitted over the *user's*
operands, views and all. So the shared propagator cites every edge row through a
`PolBuilder` in **deview mode**, which substitutes the framework's already-derived
deview-form line (in `X`-bits) for the `V`-form one. For
`DifferenceConstraints`'s own rows this is a no-op — no view appears in their
left-hand sides, so no deview-form is registered and `deviewed_line_for` returns
the line unchanged — which is why the constraint's OPB and proof output is
byte-identical to before the sharing refactor. It is load-bearing for the
presolver: confirmed by mutation, removing it fails VeriPB on the
`view_negcycle_wide` fixture in the *shipping* hybrid configuration. Same
situation, and same fix, as `linear/justify.cc`.

### Turning the donors off, and why `DisableUntilBacktrack` could not be reused as is

The hybrid is what the paper measures as best and is the default, but the
redundant donors should be measurable, so `disabling_lifted_donors()` exists and
ships off.

gcs already has `PropagatorState::DisableUntilBacktrack`, and its **mechanism**
is exactly right: the propagator is swapped past `idle_end` in the queue, where
`enqueue_if_idle` will not find it, so skipping it costs nothing. Its
**lifetime** is the part that does not transfer, in two places:

- `propagate()` saves `orig_idle_end` on entry and restores it from that call's
  `on_backtrack`, so the boundary is scoped to one `propagate()` call;
- more decisively, the no-guesses path *rebuilds* `queue` and `lookup` from
  scratch and resets `idle_end` to the propagator count.

A presolver acts at the root, before the first root propagation, so a boundary
it set would be erased before it ever took effect. `Propagators::
disable_propagators_for_constraints` therefore reuses the partition and adds a
*second* boundary that nothing restores: the rebuild puts permanently disabled
propagators at the tail, past `idle_end`, and the enabled count is what
`enqueued_end` and `idle_end` are set to.

It takes a **batch** of `ConstraintID`s, not one at a time. Finding a
constraint's propagators means scanning the propagator list, so a per-constraint
entry point makes disabling `m` donors `O(m · propagators)`; on `difference_chain`
at `n = 160` that quadratic was 23× the entire rest of the solve.

Disabling is **not** removing. The constraint keeps its OPB row, its scope and
adjacency entries, and its contribution to every variable's degree, so the
branching heuristic sees an unchanged problem. That is what makes the option a
tripwire as well as a knob: the global propagator subsumes every donor's
single-edge push, so **solutions and recursions must come out identical** with
the donors on and off. They do, across the whole test corpus; if they ever did
not, the subsumption claim would be wrong.

### Why the tests assert on counts

The presolver is invisible from the outside. A version that silently lifted
nothing — because, say, `clone()` stopped flattening a posted
`LinearLessThanEqual` to `ReifiedLinearInequality`, so
`each_constraint_of_type<ReifiedLinearInequality>()` no longer matched it —
would pass **every** validation we would otherwise write: solution-set
equivalence (a no-op presolver preserves solutions), the OPB byte-diff
(byte-identical is the *expected* result), and VeriPB (there would be nothing
new to check).

So the presolver reports what it did in `DifferenceLogicStats`, and three
things guard it:

- `static_assert`s in `run()` pinning the class relationships the enumeration
  relies on, so a hierarchy change is a compiler error at the site that needs
  fixing;
- a **runtime cross-check** of the typed enumeration against
  `Constraint::constraint_type()`, which does not depend on the hierarchy at all:
  if more constraints report `lin_less_equal` than the typed enumeration
  yielded, the presolver throws;
- assertions on the counts, and the propagation-count differential below.

Every one of those failure messages names the invariant and says explicitly not
to update the expectation. Mutation-tested: asking for `LinearLessThanEqual`
instead of `ReifiedLinearInequality` — the exact regression being defended
against — trips the cross-check, and with the cross-check also disabled all four
test modes fail, each naming the presolver.

The cross-check is on unconditionally, rather than being an opt-in strict mode,
and it is deliberately *not* "throw if nothing was lifted". Lifting nothing is a
perfectly ordinary outcome — most models contain plenty of `lin_less_equal`
constraints and no two-term `+1`/`-1` ones — so that version would fire on
legitimate models and would have to be off by default, which is to say it would
never be on when it mattered. The condition that cannot legitimately hold is the
narrower one: a constraint reporting a donor family's `constraint_type()` that
the typed enumeration did not yield. That is exactly the regression, it is free
of false positives, and it costs one pass over the posted constraints per
solve.

### Gating

None, beyond declining to install over a single edge, which is a degeneracy (one
edge's global propagator computes exactly what that edge's own propagator does)
rather than a tuning decision. A minimum-edge-count or connectivity threshold was
considered and **not** shipped: the measurements below give no crossover to site
it at — the presolver is a large win on the unlucky order at every size measured,
and its cost on the lucky order is a roughly constant factor rather than
something that switches sign — and the presolver is opt-in already, so a second
gate the user cannot reason about would be guessing dressed as tuning.

### Measurements

`examples/difference_chain --variant=presolved`, `-k 2`, release, medians of 3.
First, **`--mode=refute`**, which is unsatisfiable at the root, so there is no
search and the columns compare propagation and proof directly:

| n | order | variant | propagations | time (s) | `.pbp` lines |
|---:|---|---|---:|---:|---:|
| 40 | unlucky | decomposed | 68,137 | 0.00185 | 45,712 |
| 40 | unlucky | presolved | 903 | 0.00063 | **40** |
| 40 | unlucky | presolved + donors off | 2 | 0.00067 | **18** |
| 40 | unlucky | global | 1 | 0.00013 | **12** |
| 40 | lucky | decomposed | 38,435 | 0.00132 | 26,935 |
| 40 | lucky | presolved | 903 | 0.00061 | **40** |
| 160 | unlucky | decomposed | 4,139,782 | 0.0845 | 720,352 |
| 160 | unlucky | presolved | 13,203 | 0.0113 | **40** |
| 160 | unlucky | presolved + donors off | 2 | 0.0108 | **18** |
| 160 | unlucky | global | 1 | 0.0025 | **12** |
| 160 | lucky | decomposed | 2,150,495 | 0.0492 | 414,835 |
| 160 | lucky | presolved | 13,203 | 0.0112 | **40** |

The proof-size result is the headline: the presolver recovers essentially the
whole of the global route's win, 720,352 lines down to 40, because the
refutation is one telescoping `pol` over the donors' own rows however big the
domains are.

Then **`--mode=fixpoint`**, which searches:

| n | order | variant | propagations | recursions | time (s) |
|---:|---|---|---:|---:|---:|
| 160 | unlucky | decomposed | 2,126,002 | 163 | 0.0473 |
| 160 | unlucky | presolved | 52,807 | 163 | 0.0157 |
| 160 | unlucky | presolved + donors off | 167 | 163 | 0.0148 |
| 160 | unlucky | global | 327 | 323 | 0.0085 |
| 160 | lucky | decomposed | 52,801 | 163 | 0.0097 |
| 160 | lucky | presolved | 52,807 | 163 | 0.0152 |
| 640 | unlucky | decomposed | 132,305,602 | 643 | 4.460 |
| 640 | unlucky | presolved | 825,607 | 643 | 0.459 |
| 640 | unlucky | presolved + donors off | 647 | 643 | 0.452 |
| 640 | unlucky | global | 1,287 | 1,283 | 0.333 |
| 640 | lucky | decomposed | 825,601 | 643 | 0.257 |
| 640 | lucky | presolved | 825,607 | 643 | 0.445 |

Four things to read out of this.

**The presolver buys order-independence, which is what the pathology was.** The
`presolved` propagation count is identical for both orders at every size, and
equal to the *lucky* decomposed figure: 132.3M → 825.6k at `n = 640`, a 160×
reduction and 9.7× in wall time.

**It does not reach the global route, and the reason is registration order.**
gcs has no runtime propagator priorities (issue #582), and a presolver's
propagator is registered last, so at every round the donors all run before the
global one gets its turn — and then the global one's inferences wake them all
again. The residual is Θ(|E|) per round where the global route is Θ(1), which is
why `presolved` sits at 825,607 against `global`'s 1,287. Priorities would remove
the extra sweeps but not the one-run-per-donor-per-round floor; only disabling
the donors does that, and it takes the count to 647.

**The redundant donors cost almost nothing in wall time here**, 0.459 s against
0.452 s at `n = 640`, even though they are 1,275× of the propagation count. So on
this family the hybrid is nearly free, which matches the paper preferring it.
That conclusion survives incremental propagation, which was the obvious thing to
check: with it on the same pair is 0.239 s against 0.231 s, so the redundant
sweeps go from 1.5 % to 3 % of the presolved route's wall time rather than
becoming visible. What incrementality *does* change here is the gap between
`presolved` and `global` — 0.410 s against 0.323 s before, 0.239 s against
0.056 s after — and that residual is the presolver's own `O(constraints)`
enumeration and the model carrying 205k posted constraints, not propagator
ordering.

**On the lucky order the presolver is a modest loss**, 0.257 s → 0.445 s at
`n = 640`: nothing was wrong with the propagation order to begin with, and the
extra global pass and the presolver's own O(number of constraints) enumeration
(about 200 ns per constraint per pass, three passes, two of them the tripwire's)
are pure overhead. That is the honest counterweight to the 9.7× on the unlucky
order, and the reason this ships off by default.

## RCPSP/max: the benchmark this was built for

Per Kletzander, Dekker, Schutt and Stuckey (arXiv:2607.20022), RCPSP/max is
where a global difference-logic propagator wins most: 550 → 586.55 on their
scoring, and average unsat-detection time 1.98 s → under 0.01 s. The reason is
structural. A *maximum* time lag is a negative-weight arc running backwards
along the precedence network, so the network has cycles, and a nearly-tight one
is infeasible-or-nearly-so in a way per-constraint bounds propagation can only
find by crawling.

`examples/rcpsp` reaches it with `--max-lag-density`, and `--variant` posts the
identical edge list, in the identical order, three ways. `--branch` defaults to
a static order, so `recursions` is an invariant across variants rather than a
confound: any row where the three disagree on recursions is a bug.

Measured on fataepyc-10, release, `taskset`-pinned, medians of 3, never with
`--prove`; proof numbers taken separately below.

### Feasible instances

`recursions` identical in every row, propagations 3–12× lower for the global:

| instance | status | recursions | props (dec) | props (presolved) | props (global) |
|---|---|---:|---:|---:|---:|
| `--size 14 --seed 9 --max-lag-density 0.4 --max-lag-slack 0` | optimal 17 | 35 | 447 | 314 | **55** |
| `--size 12 --seed 3 --max-lag-density 0.3` | optimal 14 | 61 | 749 | 576 | **140** |
| `--size 18 --seed 11 --max-lag-density 0.3` | optimal 22 | 102 | 2,669 | 1,530 | **227** |
| `--size 16 --seed 3 --max-lag-density 0.3` | optimal 14 | 296 | 1,271 | 859 | **256** |
| `--size 22 --seed 4 --max-lag-density 0.25` | optimal 32 | 10,512 | 109,199 | 82,726 | **32,682** |
| `--size 20 --seed 5 --max-lag-density 0.3` | unsat at root | 1 | 1,155 | 56 | **1** |

The `--size 22` row is the honest one: 3.3× fewer propagations, and **8 % slower**
in wall time (0.0771 s decomposed against 0.0828 s global). That is the
non-incrementality caveat under "Deliberately deferred" showing up on a real
model — every wake re-runs the whole Bellman-Ford pass. The presolved column
sits between the two throughout because it leaves the donor linears installed
alongside the lifted global unless they are explicitly retired.

### Negative cycles, against the horizon

The sharp result. A negative cycle of weight -1, resources off, horizon forced,
so the only thing varying is how far the bounds have to crawl:

| horizon | props (dec) | props (global) | wall dec (s) | wall global (s) |
|---:|---:|---:|---:|---:|
| 200 | 1,163 | **1** | 0.00035 | 0.00016 |
| 800 | 4,763 | **1** | 0.00073 | 0.00010 |
| 3,200 | 19,163 | **1** | 0.00324 | 0.00011 |
| 12,800 | 76,763 | **1** | 0.02397 | 0.00010 |
| 51,200 | 307,163 | **1** | 0.26282 | 0.00011 |

Exactly linear against a constant: 4× the horizon is 4× the propagations
decomposed, and one propagation regardless for the global.

### Proofs of that refutation

Separate runs, with `--prove`:

| horizon | dec lines | dec `.pbp` | veripb dec | global lines | global `.pbp` | veripb global |
|---:|---:|---:|---:|---:|---:|---:|
| 200 | 4,454 | 299,560 B | 0.068 s | **12** | **222 B** | 0.012 s |
| 800 | 18,254 | 1,417,961 B | 0.95 s | **12** | **222 B** | 0.012 s |
| 3,200 | 73,454 | 6,578,202 B | 21.0 s | **12** | **222 B** | 0.014 s |
| 12,800 | 294,254 | 29,769,564 B | **> 600 s, abandoned** | **12** | **222 B** | 0.013 s |

The refutation is 12 lines and 222 bytes whatever the horizon, because it sums
the cycle's edge rows once (proof shape 1 above). The decomposed proof grows
with the horizon and its verification grows faster still — the 12,800 row was
abandoned after ten minutes rather than being left to finish, so that figure is
a lower bound and is marked as one.

### Where the paper's headline does and does not reproduce

The cost claim reproduces cleanly. The *shape* claim does not: `recursions: 1`
in **both** columns on the negative-cycle rows, because gcs runs root
propagation to a fixpoint and a negative cycle always eventually empties a
domain. So the global propagator does not turn a search into a root refutation
here; it turns an expensive root refutation into a single propagation.

The paper's baseline searches because its disjunctive resources contribute
*half-reified* difference constraints, so the cycle only closes after Boolean
decisions.

### Switching that mechanism on: `--machine=difference`

`examples/rcpsp --machine=difference` posts the machine as the pairwise
disjunctive decomposition in conditional edges — one ordering Boolean per pair,
the two disjuncts as edges under it and its negation — so the network's edge set
now changes during search, which is the paper's modelling rather than ours.

Two things follow, and the second is not the flattering one.

**The search mechanism does reproduce.** On an infeasible instance the
refutation now genuinely requires Boolean decisions rather than falling out of
root propagation:

| instance | `--machine` | variant | recursions | propagations |
|---|---|---|---:|---:|
| `--size 10 --seed 5 --machine-fraction 0.7 --deadline 17` | pairwise | decomposed | 836 | 45,777 |
| | difference | decomposed | 689 | 36,145 |
| | difference | **global** | **6,353** | **11,321** |
| `--size 12 --seed 2 --machine-fraction 0.8 --deadline 18` | pairwise | decomposed | 316 | 11,498 |
| | difference | decomposed | 47 | 2,355 |
| | difference | **global** | **329** | **720** |

**And the global propagator loses that search.** Nine times the nodes on the
first instance, seven on the second, for a third of the propagations. The cause
is `IncImp`'s absence, stated above and now measured: the reified linear forms
infer their own condition — a violated `LinearGreaterThanEqualIf` fixes its
Boolean false — and `DifferenceConstraints` infers nothing about a condition at
all, so it explores orderings the decomposition has already refuted. Propagations
are the wrong metric here; nodes are what the model is paying.

This is the concrete argument for reconsidering `IncImp` for gcs specifically,
against the paper's own configuration study, which found every configuration with
it on scoring below every configuration with it off. Their baseline is a
lazy-clause-generation solver that learns from a failed ordering; gcs is not, so
what `IncImp` would buy here is not what it bought there.

Two consequences worth stating for anyone writing a model against this
propagator:

- **The condition variables must be branched on.** An edge whose Boolean is
  unfixed does not constrain, so leaving them out of the branch list does not
  merely slow the search down — it lets the solver report a schedule that
  violates the resource. `examples/rcpsp` puts them first in the branch list, and
  the cross-check that catches getting this wrong is that all four `--machine`
  spellings must agree on the optimum.
- **`recursions` stops being a cross-variant invariant.** On the unconditional
  temporal network the three variants search identically, which is what makes the
  tables above a clean comparison. With conditional edges they do not, and a
  table that reports only propagations would hide the regression above.

## Root simplification

The paper's section 5.2 runs a one-off pass over the graph before search, and its
section 6.3 measures that pass as most of the difference-logic win: 320.95 against
312.94 on the MiniZinc challenge set, 637.50 against 573.40 on `ProdCons`, and on
`RCPSP/max` an average unsatisfiability time *below 0.01 s* because "most of these
instances are identified during simplification". The section above on half-reified
resources argued, from measurement, that the RCPSP/max headline has to belong to
this stage rather than to `IncSat`/`IncLB`/`IncUB`. This section is that stage,
and the argument turns out to be right.

It is on by default and can be turned off from either entry point:

```cpp
problem.post(DifferenceConstraints{edges}.simplifying_at_root(false));
problem.add_presolver(DifferenceLogic{}.simplifying_at_root(false));
```

Both also take `reporting_simplification_to(shared_ptr<DifferenceSimplificationStats>)`,
which is how the tests and the example binaries tell "worked" from "did nothing".

### Where it runs, and why it is not an initialiser

It runs **inside the propagator, on its first call**. That is not where one would
first reach for. An initialiser would be the natural home for the posted
constraint — but a presolver runs *after* `propagators.initialise()`, so an
initialiser it installed would never fire, and `Presolver::run` is handed a
`State &` and a `ProofLogger *` but no inference tracker, so it cannot infer
anything itself either. Fixing a condition is an inference. So the only place
that works for both entry points is the propagator, and putting it there means
one implementation and one set of proof shapes rather than two.

Two guards make that safe:

- **it runs once**, latched by a flag in the propagator's own (mutable) state;
- **only if that first call is at the root**, tested by `state.guesses()` being
  empty.

The second is not decoration. Everything the stage concludes is *permanent* —
edges leave the internal graph and never come back, and no part of it is trailed
— so doing it under a decision would keep conclusions that hold only under that
decision. That would be a completeness bug in the general case and an
**unsoundness** in the case of an edge dropped because a conditional path implied
it, and no proof would ever complain, because losing propagation is invisible to
a proof. In practice the first call is always at the root (search begins by
propagating everything, before any decision), so the guard costs nothing and
buys the argument.

Not trailing is then justified, and by exactly the argument that puts the paper's
own section 5.3/5.4 boundary where it is: every conclusion drawn here is a
statement about the *graph*, and backtracking does not change the graph. The
stage reads no domain. The one thing that looks like a domain read — testing
whether a condition currently holds — is a read of a fact fixed at the root and
never undone.

### The four sub-steps, and which are here

Johnson's all-pairs shortest paths first: Bellman-Ford from the paper's imaginary
source `v0` (seeding every potential at zero *is* that source's edge set, exactly
as in the propagator's own passes), then one Dijkstra per node on the
reduced-cost graph. `O(n² log n + nm)`, paid once. The pass computes nothing that
needs certifying; only its four conclusions do, and only one of them turns out to
need anything at all.

**1. Redundant-edge removal — implemented, and no proof obligation whatsoever.**
An active edge `u --d--> v` goes when `d > D_uv`, i.e. when a strictly shorter
path already implies it. An implied (conditional) edge goes on the weaker test
`d >= D_uv`, since one that merely restates a distance the base graph already has
can never add anything even once its condition holds. Among parallel edges that
*attain* the distance exactly one is kept, because dropping them all would change
the distance.

The crucial point, and the one the issue framed as a model change: **the edge is
not removed from the model.** gcs separates `define_proof_model()` from
`install_propagators()`, and this is a decision about the second. The OPB keeps
every posted row, so there is nothing to certify, nothing to delete, and no
brush with VeriPB's checked-deletion rule (Hoen et al., CPAIOR 2024). It also
keeps workflow-2 chain verification intact, since `cake_pb_cp` re-derives the
`.opb` from the `.scp` and knows nothing about our internal pruning. Deleting
from the OPB instead would be sound for proving UNSAT and *unsound* for SAT and
for optimisation, for no benefit at all.

**2. Fixing a condition false — implemented, and the one real inference.** If
adding `u --d--(b)--> v` would close a negative cycle — `d + D_vu < 0` — then `b`
cannot hold. This is the sub-step that carries the paper's RCPSP/max result, and
it is the deliverable of this PR.

**3. Zero-weight-cycle unification — not implemented, but detected and counted.**
See below.

**4. Node removal — implemented, internal.** A node with no incident edge left
cannot send or receive a bound, so it is dropped from the relaxation loop and,
more usefully, from the round bound. In practice these are nodes that only ever
appeared in a static bound.

### The proof for condition fixing

Proof shape 1 with the candidate edge standing in for the missing link. Sum the
candidate's row and the witness path's rows: every `BinEnc` term telescopes away,
because consecutive edges meet at a node and every row is in the canonical
representation. What survives is the big-M residual of each *conditional* row,
and the candidate's is always one of them, so

```
pol @c[_1][e1] @c[_1][e0] + s ;
rup 1 ~i[_3][b0] >= 1;
```

is the whole thing, copied verbatim from the `fix_one` fixture: `e1` is the
candidate `b -> x - y <= -5`, `e0` is the unconditional `y - x <= 2` that is the
witness path, and `~i[_3][b0]` is the Boolean. That is the `reified_hand.pbp` shape verified by hand against
real gcs OPB output before any of this existed, with the roles of the conditions
swapped round: there the conditions were the residuals that survived into a
learned clause, here the surviving residual *is* the literal being inferred.

The witness path is taken from the shortest-path tree, so it may itself contain
conditional edges — an edge whose condition the model fixed, or one an earlier
round of this stage fixed. Their conditions are cited in the `Reason`,
deduplicated, exactly as a negative cycle's are.

Two mutation results, both measured:

* **the `saturate` is not load-bearing** — removing it leaves every fixture
  verifying, because the closing RUP assumes every condition and drives each
  residual to zero. It is emitted anyway so the derived line *is* the clause;
* **neither, here, are the path's conditions in the reason.** That is specific to
  running at the root: a path condition is definitely true only because it is a
  *globally derived* fact, so unit propagation recovers it and the RUP passes
  without being told. They are cited regardless, because the reason is also what
  the state and the nogood machinery see, and there a missing antecedent is not
  recoverable.

Emitted inside a `JustifyExplicitly` at `ProofLevel::Temporary`, like every other
justification here. Nothing is emitted at `ProofLevel::Top`, and nothing needed
to be: the inference itself is recorded by the inference tracker, and the
redundant-edge and node removals leave no trace anywhere. **No new OPB content
from either entry point**, which is enforced by byte-diff tests on both.

### The fixpoint, and how the refutation actually happens

Fixing a condition false makes its complement definitely true, which can put an
edge *into* the base graph, which can license further fixing. So the stage
iterates — the paper's section 5.3 — until a round fixes nothing. It terminates
because every round either fixes at least one condition (removing an edge) or
stops, and there are finitely many edges.

On RCPSP/max the refutation turns out to arrive more directly than that. Both
polarities of an ordering Boolean are separately impossible, so both are found
fixable in the *same* round: the first is inferred, the second contradicts it,
and the model is refuted before search starts. The counters then read one
condition fixed in one round, because the second fix is the contradiction and
unwinds before it can be counted — which is why they are published by a
destructor rather than at the end of the stage.

If instead the newly-activated edges jointly close a cycle, the next round's
Bellman-Ford sees it, the stage stops, and the propagator's own pass refutes it
with the cycle extraction and the telescoping `pol` that already exist. The stage
deliberately does not duplicate that machinery.

### This is `IncImp`, restricted to the root

Fixing a condition because its edge would close a negative cycle is exactly the
paper's `IncImp`, which its own configuration study says to leave off — on
RCPSP/max every configuration with it on scored below every configuration with it
off. That is not a contradiction: what the study measures is running it on **every
wake**, and what this is is running it **once**, at the root, where its cost is
`O(n² log n + nm)` in total rather than per propagation. The section above on
half-reified resources noted that `IncImp`'s absence shows up in gcs as a
*search-tree* cost, since `--variant=global` has no donors to infer `!cond` from
bounds; the root-only version removes most of that without paying the per-wake
price. Whether the in-search version pays for itself in gcs remains open.

### RCPSP/max: the headline reproduces

`examples/rcpsp --size 9 --machine-fraction 0.9 --max-lag-density 0.4
--max-lag-slack 0 --machine difference`, the shape the half-reified section
measured: a machine posted as conditional edges, on a network whose maximum lags
are already tight. Every seed below is infeasible, and infeasible only
*conditionally* — at the root no Boolean is fixed, so no conditional edge is in
the graph at all, which is why neither the decomposed model nor the global
propagator could see it.

| seed | decomposed | presolved, no simp. | presolved | global, no simp. | global |
|---:|---:|---:|---:|---:|---:|
| 1 | 3 | 3 | **1** | 3 | **1** |
| 2 | 5 | 5 | **1** | 5 | **1** |
| 3 | 5 | 5 | **1** | 5 | **1** |
| 4 | 77 | 77 | **1** | 121 | **1** |
| 5 | 1 | 1 | **1** | 1 | **1** |
| 6 | 1,525 | 1,525 | **1** | 4,149 | **1** |
| 7 | 55 | 55 | **1** | 75 | **1** |
| 8 | 5 | 5 | **1** | 5 | **1** |

(recursions; seed 5 was already refuted at the root by the temporal network
alone.) Two things to read off it. The no-simplification global column is
*worse* than decomposed in every row where the search is non-trivial — 4,149
against 1,525 on seed 6 — which is `IncImp`'s absence again. And the
simplification column is 1 everywhere, whatever the row above it was.

Proofs shrink accordingly, and all of them verify:

| instance | variant | `.pbp` lines | `.pbp` bytes | VeriPB (s) |
|---|---|---:|---:|---:|
| seed 4 | decomposed | 4,662 | 210,129 | 0.058 |
| seed 4 | global, no simplification | 897 | 60,715 | 0.026 |
| seed 4 | global | **60** | **1,548** | **0.018** |
| seed 4 | presolved | 131 | 6,575 | 0.020 |
| seed 6 | decomposed | 69,050 | 3,218,361 | 0.798 |
| seed 6 | global, no simplification | 39,451 | 3,323,224 | 0.474 |
| seed 6 | global | **32** | **769** | **0.018** |
| seed 6 | presolved | 51 | 2,052 | 0.022 |

So: **the paper's RCPSP/max unsatisfiability headline reproduces in shape, and it
reproduces here and nowhere else in this stack.** #587 established that the
decomposed model refutes at the root too, just expensively; #590 added
half-reified resources and established that the search reproduces but the root
refutation does not; this PR closes it. That sequence is the evidence for the
claim, made in the half-reified section, that the headline belongs to the
simplification stage rather than to the incremental algorithms.

### What it costs where it does not pay

`examples/difference_chain`, the paper's Example 8, is the opposite case and is
worth stating plainly. `--variant=global --order unlucky --mode fixpoint`:

| n | recursions | propagations | wall, no simp. (s) | wall (s) | Johnson's (s) | edges dropped |
|---:|---:|---:|---:|---:|---:|---:|
| 80 | 163 | 167 | 0.00167 | 0.00233 | 0.00050 | 79 |
| 160 | 323 | 327 | 0.00817 | 0.01135 | 0.00328 | 159 |
| 320 | 643 | 647 | 0.0477 | 0.0729 | 0.0234 | 319 |
| 640 | 1,283 | 1,287 | 0.312 | 0.474 | 0.164 | 639 |

`recursions` and `propagations` are identical down every column — which is the
point, since redundant-edge removal and node removal are propagation-neutral by
construction — and the entire wall-time difference is the Johnson's pass. It
drops `n - 1` edges out of `n(n+5)/2`, i.e. essentially nothing, and costs 30 to
50 % of the solve. `--mode refute` is the same, with the Johnson's pass accounting
for the whole of a 0.117 s → 0.239 s regression at `n = 640` and nothing at all
dropped.

The pure-temporal scaling curve says the same more precisely
(`--resources 0 --max-lag-density 0 --variant=global`, satisfiable, so Johnson's
runs to completion):

| n | nodes | edges | Johnson's (s) | solve (s) | recursions (both) |
|---:|---:|---:|---:|---:|---:|
| 100 | 101 | 230 | 0.00025 | 0.0028 | 12,834 |
| 200 | 201 | 478 | 0.00110 | 0.0145 | 47,093 |
| 400 | 401 | 957 | 0.00532 | 0.0910 | 188,322 |
| 800 | 801 | 1,930 | 0.0238 | 0.625 | 757,354 |
| 1,600 | 1,601 | 3,844 | 0.0989 | 4.51 | 3,082,344 |

Sparse and satisfiable, the pass is quadratic-ish in `n` and around 2 % of the
solve — cheap. Dense, as in `difference_chain`, the `nm` term dominates and it is
not. That is the honest shape of the trade-off, and it is why the option exists
and defaults on rather than being unconditional: the paper reports simplification
as a clear win on its benchmark families, and it is a clear win on ours too, but
"clear win" is a statement about scheduling models with conditional edges, not
about difference systems in general.

### Zero-weight-cycle unification, and why it is deferred

The fourth sub-step is not implemented. It *is* detected: reduced weights are
non-negative and a cycle's reduced weight is its real weight, so a cycle weighs
zero exactly when every edge on it has reduced weight zero, and the
strongly-connected components of that subgraph are the sets of variables the
system pins into fixed relative positions. Tarjan over it is `O(n + m)` on data
Johnson's has already produced, so the counters cost nothing and answer the
question the deferral raises.

They answer it in the affirmative, which is worth recording: on the
`--max-lag-slack 0` RCPSP/max instances above there is one zero-weight cycle
spanning **10 of the 11 nodes**, because exactly-tight maximum time lags are
precisely a zero-weight cycle. On `difference_chain` and on the slack RCPSP/max
instances there are none. So unification would fire, and hard, on the family this
stage is aimed at.

It is deferred for two reasons, neither of them about the proof.

The proof side is settled and easy, and this is the issue's open question
answered: the two directions of `x - y = d` are **pure `pol` consequences with
unit multipliers** — the edge itself gives `x - y <= d`, and summing the rest of
the cycle (weight `-d`) gives `y - x <= -d`. Aggregation, not redundance. **No
`red`, no `dom`.** Nor does anything need to be pre-derived at `ProofLevel::Top`:
the cycle's rows are already in the OPB, so a derivation that crosses a merged
node can just add them to its own `pol`, which is the "one extra addend" story of
`dev_docs/view-proof-logging.md` paid at `Temporary`.

What is not cheap is the model side. Survey section 5.2 item 2 is emphatic that a
`ViewOfIntegerVariableID` must **not** be retro-fitted onto an already-encoded
user variable: gcs views are a model-construction concept, and
`NamesAndIDsTracker::need_view` creates a view's own bit-vector and its
definitional link row, which cannot happen after the model is finalised — and by
the time this stage runs it has been. So the merged variables keep independent
domains, and that is where the cost lands:

- seeding the merged node means taking the maximum over its members' bounds, and
  recording *which* member achieved it, since that member's bound is what the
  reason must cite;
- every push on the merged node must be inferred on **every** member separately,
  each with its own `pol` carrying the zero-cycle path from the pushing edge's
  endpoint to that member.

So the graph gets smaller — which is the algorithmic win — but the number of
`infer()` calls does not, and the bound-push justification, which is currently
one row plus one literal, becomes one row plus one literal plus a path. That is a
substantial rework of the two `infer_along_forest` passes for a win that has not
been measured, and it is the only sub-step whose proof shape changes at all. It
is left for a separate PR, with the counters above as the evidence that the PR is
worth writing.

## Incremental propagation

Every wake used to redo the whole `O(rounds × |E|)` Bellman-Ford pass from the
current bounds. That is what the two honest caveats above were about: the
propagation counts and the proof sizes were dramatically better than the
decomposed model's, and the wall time was not. This section is the paper's
`IncSat` / `IncLB` / `IncUB`, which fix that.

It is on by default and can be turned off from either entry point, and from
both example binaries:

```cpp
problem.post(DifferenceConstraints{edges}.incrementally(false));
problem.add_presolver(DifferenceLogic{}.incrementally(false));
```

**The from-scratch version is not dead code and must not be deleted.** It is the
reference the incremental one is checked against, in two ways that nothing else
can supply — see "The two oracles" below.

### The three moving parts

**A potential function `π`**, maintained over the whole search, satisfying
`π(u) + d − π(v) >= 0` for every arc `u --d--> v` **currently in the graph, and
nothing else**. That makes every *reduced* cost `π(u) + d − π(v)` non-negative,
which is what lets Dijkstra replace Bellman-Ford. It is computed once at the
root by a single Bellman-Ford from an imaginary zero-weight source (seeding every
potential at zero *is* that source's edge set, exactly as elsewhere in this
file), and repaired by `IncSat` whenever an arc joins the graph.

Three things are true of `π` and all three are load-bearing:

- **it is never trailed**, because its invariant is a conjunction over the arcs
  in the graph and backtracking only ever *removes* arcs. This is the paper's
  section 4.1 remark, attributed to Wang et al.;
- **bounds must not appear in it.** `π(v0)` is a per-call temporary, computed
  over `Vl` only, and is never stored. (It turns out not to be able to break
  anything if it were — see the mutation table below — but it is free to do the
  right thing and the reason it is safe is a property of the priority queue
  rather than of the algorithm);
- **it decreases monotonically and is never reset**, which is why an arc that
  was fine when it was last active can need repair when it comes back. See
  "re-activation" below.

**`IncSat`** (the paper's Algorithm 1, from Cotton and Maler) repairs `π` when
one arc is added, or reports that the graph now has a negative cycle. It is a
Dijkstra-shaped relaxation of the *violation* `γ`, touching only the nodes it
has to, and it terminates either when nothing is violated any more or when the
repair reaches back round to the new arc's own tail — which is exactly a negative
cycle. It does not *extract* that cycle: on `false` the caller hands straight
over to the from-scratch pass, which already carries the extraction and the
telescoping `pol`, and re-verifies arithmetically that a cycle is really there.
A negative cycle ends the search, so the `O(n·m)` is paid at most once per
branch and buys a second implementation that does not have to be written or
trusted. The same hand-off covers a negative cycle in the *initial* potential
computation.

**`IncLB`** (Algorithm 3) processes every bound change since the last run in one
Dijkstra on the reduced-cost graph. `IncUB` is the same function applied to the
reverse graph with the potential, the bounds and the gate all negated:
`ub(x) <= ub(y) + d` is `−ub(x) >= −ub(y) − d`, which is the lower-bound relation
along the arc read backwards, and `−π` is a valid potential for it. One
implementation, two instantiations, and no second opportunity to mistranscribe
Algorithm 3.

### The `Do` array, which is where all the difficulty is

`IncLB` is gated by `Do`, "the bounds of variables the last time the propagator
was run". Two invariants have to hold at the entry to every call, and everything
below is about keeping them:

- **I1**: `Do(x) <= min D(x)` for every node;
- **I2**: `Do(t) >= Do(s) − d` for every arc `(s, t, d)` currently in the graph.

`Vl = { x | min D(x) > Do(x) }` seeds Dijkstra, and the *expansion* gate
(Algorithm 3 line 12) declines to relax out of a settled node `s` whose new bound
does not beat `Do(s)`. I2 is what makes that safe: if `−δ(s) <= Do(s)` then for
every arc out of `s`, `−δ(s) − d <= Do(s) − d <= Do(t) <= min D(t)`, and the same
argument chains along any path, so the whole sub-search is dead. Drop I2 and the
gate silently throws away propagation.

**At the end of a run, `Do` becomes the bounds the run propagated *from*, not the
bounds the state ends up holding.** For every node Dijkstra settled, that is
`max(Do(x), −δ(x))`; for every node it did not, `Do(x)` is unchanged. That
assignment re-establishes I2 (the settled-and-expanded case is Dijkstra's own
`δ(t) <= δ(s) + d`; the settled-but-not-expanded and unsettled cases fall back on
the old I2) and preserves I1 (a pushed bound was inferred, so `min D` is at least
it).

**Recording the state's bounds instead is a real bug and it is gcs-specific.**
gcs domains have holes, so `infer_greater_than_or_equal(x, 5)` on a domain with a
hole at 5 lands the state's lower bound at 6 or higher. Recording 6 makes
`min D(x) == Do(x)`, so on the mandatory self-re-wake `x ∉ Vl`, `Vl` comes out
empty, and the consequences of the snapped bound are never propagated. The
propagator returns `PropagatorState::Enable` precisely so that it is re-woken by
its own inferences; recording the snapped value neuters that. Neither the paper
(range domains) nor the survey mentions it, and `run_hole_snap_test` catches it
immediately.

### Backtracking: exact restoration, not a lazy clamp

`Do` and the record of which arcs the invariants have been established for both
have to be restored on backtracking, and **restored exactly**.

The tempting cheap alternative — clamp `Do(x) := min(Do(x), min D(x))` at the
next call rather than restoring it — is wrong. Guess `y >= 10`; the propagator
runs and records `Do(y) = 10`; the branch fails; `y >= 5` is restored; the
sibling guesses `y >= 7`. The clamp gives `Do(y) = min(10, 7) = 7`, which is
`min D(y)`, so `y ∉ Vl`, the gate never expands, and the consequences of
`y >= 7` — computed in a branch that has been thrown away — are simply gone.
Successive guesses tightening the same variable is the commonest branching
pattern there is, and no proof can see the loss. `difference_test incremental`
runs that scenario verbatim.

`State::on_backtrack` is not reachable from a propagator's `const State &`, so
the restoration goes through the trailed constraint state. Putting `Do` itself
there would make entering an epoch `O(n + m)`, since gcs copies the whole
constraint-state vector at every `new_epoch`. So what is trailed is **one
number**: the length of an undo trail that lives in the propagator's own
(untrailed) memory. Entering an epoch is `O(1)`; the next call after a backtrack
pops the trail down to the restored mark, which restores exact values. Doing that
lazily is safe precisely *because* the values are exact and do not depend on the
current domains — nothing reads `Do` between the backtrack and that call. The
trail's length is bounded by the current root-to-leaf path, not by total work,
because it shrinks again on every backtrack.

### Arc activation: the paper's section 5.4 omits half of it

`Do` says nothing whatsoever about an arc that has joined the graph since the
last run, and a reification becoming true can deliver one **with no node bound
changing anywhere**. `Vl` is then empty, `IncLB` does nothing, and the push the
arc delivers is lost.

The paper's section 4.4 gives the right recipe — on adding `(u, v, d)`, compute
the possibly-new bounds `lb(v) := lb(u) − d` and `ub(u) := ub(v) + d` and feed
them through `IncLB` / `IncUB` — but **its section 5.4, which is the
during-search description one would naturally transcribe, mentions only `IncSat`
and `IncImp`**. Transcribing section 5.4 alone builds a propagator that silently
loses every reification-delivered push.

Here that seeding is done by *forcing the arc's tail into `Vl` and forcing it to
be expanded* (and its head, for the upper bound pass), rather than by touching
`Do`: Dijkstra then carries that node's bound across the new arc and onwards to
everything downstream, and the `Do` update at the end re-establishes I2 for the
new arc as a side effect. Lowering `Do` instead would have needed a cascade, since
lowering `Do(s)` can break I2 for arcs *into* `s`.

**Re-activation after backtracking counts, every single time.** `π` is never
reset and drifts downwards over the whole search, so an arc whose reduced cost
was non-negative when it was last active can be negative when it comes back —
`π`'s invariant is only maintained for arcs that are *in* the graph. Nothing may
cache "this arc has been checked", which is why the activation record is trailed
alongside `Do`. A negative reduced cost is not a slow path but a wrong one: it
breaks Dijkstra's settle order.

### The two oracles

Both come from keeping the from-scratch pass compiled and runtime-selectable.
They exist because of the asymmetry this whole file keeps running into: a proof
certifies what *was* derived, so an inference that should have been made and was
not is invisible to VeriPB. Every way the machinery above can go wrong loses
propagation.

**The differential fixpoint audit** re-runs the from-scratch pass after *every*
incremental call, on the same starting bounds and the same active edge set, and
requires the two to agree node for node — plus that it finds no negative cycle
the incremental route missed. It is on for every fixture in
`difference_constraints_test.cc`, and `GCS_DIFFERENCE_AUDIT=1` turns it on for
every difference propagator in a process, so a whole corpus (or an example
binary) can be run under it without touching a model. It catches a completeness
failure **at the wake where it first occurs**, which is the only way to catch a
stale `Do`, a stale `π`, a missed activation seed or a wrong `π(v0)`.

**Search-shape equality.** Given I1 and I2 the incremental route reaches the
*identical per-call fixpoint*, not merely the same eventual one: a bounds closure
is the least fixpoint of monotone inflationary operators and is therefore unique.
So the search tree must be bit-identical. Intra-call inference *order* does
differ — Dijkstra settles in a different order from the predecessor forest — so
`propagations`, other propagators' wake order and proof bytes may legitimately
move; `recursions`, the solution sequence and every per-node domain may not.
`run_test` therefore solves every fixture both ways and requires the solution set
*and* the recursion count to match, with a failure message saying not to relax
the check. Treat a `recursions` divergence as a bug with certainty. (Voided by a
randomised or conflict-weighted heuristic; the default `dom_then_deg` and the
harness's seeded random brancher are both fine, because both runs use the same
one.)

### What actually went wrong, measured by mutation

Every row was produced by breaking the shipping code in exactly that way,
rebuilding, and recording which test modes failed. The last two rows are the
interesting ones.

| mutation | caught by |
|---|---|
| record end-of-call state bounds in `Do` | `incremental`, `basic` (the hole snap), `reified`, `cycles`, `views` |
| clamp `Do` lazily instead of restoring it | every mode, and the presolver |
| never unwind the trail at all | every mode, and the presolver |
| seed nothing on activation (section 5.4 only) | `incremental`, `reified`, `random_reified` |
| cache "this arc has been checked" across backtracking | `incremental`, `reified`, `simplify`, `random_reified`, presolver |
| `Vl` gate off by one | every mode |
| expansion gate off by one | every mode |
| Algorithm 3 lines 15–16 literally (`γ(s)` after the `+∞` reset) | every mode |
| **`π(v0)` not the maximum over `Vl`** | **nothing — and it cannot be** |
| **no expansion gate at all** | **nothing — and it should not be** |

The last two are worth stating properly, because one of them contradicts a
prediction and the other confirms the theory.

**`π(v0)` cannot break anything here, whatever it is.** It enters only as
`γ(v) = π(v0) − min D(v) − π(v)` and leaves as `−δ(v) = π(v0) − γ(v) − π(v)`, so
any change to it is a *uniform shift* of every key in the priority queue and
cancels exactly out of every bound the pass reports. A too-small `π(v0)` makes
some seeds negative, which is harmless for a binary-heap Dijkstra: Dijkstra needs
non-negative *edges*, and a multi-source search with differing (even negative)
initial distances is fine. It is still computed per call over `Vl` — that is the
cheapest correct thing and it costs nothing extra — but the predicted failure
mode does not exist in this implementation. It *would* exist under a monotone
bucket or radix priority queue, which assumes non-decreasing extraction, so this
is a fact about the queue rather than about the algorithm.

**Removing the expansion gate is sound and complete, just slower.** That is the
correct answer, and it is a useful negative control on the mutation harness:
over-expansion loses nothing, which is why every *tightening* of a gate above is
caught and the loosening is not.

### Measurements

`examples/difference_chain`, the paper's Example 8, `--variant=global
--simplify=off`, `k = 2`, release build, `taskset`-pinned, medians of 3, no
`--prove`:

| n | order | variant | recursions | propagations | time (s) |
|---:|---|---|---:|---:|---:|
| 40 | unlucky | decomposed | 43 | 37,102 | 0.00123 |
| 40 | unlucky | global, from scratch | 83 | 87 | 0.00043 |
| 40 | unlucky | global, incremental | 83 | 87 | **0.00028** |
| 40 | lucky | decomposed | 43 | 3,601 | 0.00056 |
| 40 | lucky | global, from scratch | 83 | 87 | 0.00042 |
| 40 | lucky | global, incremental | 83 | 87 | **0.00028** |
| 160 | unlucky | decomposed | 163 | 2,126,002 | 0.0455 |
| 160 | unlucky | global, from scratch | 323 | 327 | 0.0081 |
| 160 | unlucky | global, incremental | 323 | 327 | **0.0028** |
| 160 | lucky | decomposed | 163 | 52,801 | 0.0081 |
| 160 | lucky | global, from scratch | 323 | 327 | 0.0069 |
| 160 | lucky | global, incremental | 323 | 327 | **0.0028** |
| 640 | unlucky | decomposed | 643 | 132,305,602 | 3.654 |
| 640 | unlucky | global, from scratch | 1,283 | 1,287 | 0.323 |
| 640 | unlucky | global, incremental | 1,283 | 1,287 | **0.057** |
| 640 | lucky | decomposed | 643 | 825,601 | 0.212 |
| 640 | lucky | global, from scratch | 1,283 | 1,287 | 0.269 |
| 640 | lucky | global, incremental | 1,283 | 1,287 | **0.057** |

`recursions` and `propagations` are identical down every column, which is what
says the wall-time column is measuring propagation cost and nothing else. The
`n = 640` figures are the headline: `--variant=global` was the *slower* choice on
the lucky order at that size (0.297 s against the decomposed model's 0.199 s in
the table earlier in this file) and is now comfortably the faster one.

`examples/rcpsp`, the real family, `--variant=global --simplify=off`, same
protocol, maximum lags on:

| instance | status | recursions | prop (dec) | prop (global) | dec (s) | global, scratch (s) | global, incr (s) |
|---|---|---:|---:|---:|---:|---:|---:|
| `--size 20 --seed 5 --max-lag-density 0.3` | unsat | 1 | 1,155 | 1 | 0.000492 | 0.000153 | 0.000163 |
| `--size 12 --seed 3 --max-lag-density 0.3` | optimal | 61 | 749 | 140 | 0.000502 | 0.000429 | 0.000430 |
| `--size 18 --seed 11 --max-lag-density 0.3` | optimal | 102 | 2,669 | 227 | 0.001192 | 0.000770 | 0.000784 |
| `--size 22 --seed 4 --max-lag-density 0.25` | optimal | 10,512 | 109,199 | 32,682 | 0.0775 | 0.0855 | **0.0701** |
| `--size 15 --seed 0 --max-lag-density 0.3 --max-lag-slack 4` | unsat | 3,796,420 | 76,983,465 | 19,692,576 | 40.88 | 38.89 | **36.67** |

`recursions` is identical across all three columns on every row, which is what
says the time columns are measuring propagation cost and nothing else.

**The `--size 22 --seed 4` row is the one this PR exists for.** The RCPSP/max
section above measured it as the instance where the global propagator lost to
the decomposed model in wall time — 3.3x fewer propagations and 8 % slower — and
named non-incrementality as the cause. The from-scratch route is 10 % slower than
the decomposed model there; the incremental route is 10 % *faster*. The largest
row moves the same way, 38.89 s to 36.67 s against the decomposed model's 40.88 s.

The small rows are flat, and honestly so: at this size the from-scratch pass
early-exits after two or three relaxation rounds over a few dozen arcs, which is
already cheap. The asymptotic win needs `|E| >> n` (which is what
`difference_chain` is), long chains, or a search deep enough for the per-wake
cost to dominate.

Half-reified resources, `--machine=difference`, which is where the conditional
edges live and therefore where `IncSat` and the activation seeding are exercised
at all:

| instance | variant | recursions | propagations | time (s) |
|---|---|---:|---:|---:|
| `--size 12 --seed 2 --machine-fraction 0.8` | decomposed | 277 | 13,638 | 0.00343 |
| | global, from scratch | 2,091 | 3,640 | **0.01626** |
| | global, incremental | 2,091 | 3,640 | 0.01717 |
| `--size 11 --seed 4 --machine-fraction 0.9` | decomposed | 917 | 51,142 | 0.01102 |
| | global, from scratch | 10,471 | 17,087 | **0.08168** |
| | global, incremental | 10,471 | 17,087 | 0.08816 |
| `--size 10 --seed 5 --machine-fraction 0.7` | decomposed | 3,172 | 178,964 | 0.03569 |
| | global, from scratch | 28,138 | 44,369 | **0.21335** |
| | global, incremental | 28,138 | 44,369 | 0.23048 |

**This is the one family where incrementality loses, consistently, by 5 to
8 %**, and the reason is worth stating because it is not a bug and not a missing
optimisation.

A pairwise disjunctive encoding contributes `n(n-1)` conditional arcs against `n`
nodes, so `|E| ~ n^2` and every wake is dominated by the `O(|E|)` pass that tests
which conditions currently hold --- which *both* routes pay, and which was 19 %
of the profile in both. What the incremental route saves on top of that is the
relaxation, which is cheap here because only the arcs whose Booleans have been
fixed are active. What it adds is one `IncSat` per activation, and on this
modelling those repairs are nearly always real: `pi` is seeded from the
unconditional temporal network, and a disjunctive arc weighs `-p_i`, so its
reduced cost starts out negative essentially every time. Each repair is a
Dijkstra over a graph in which every node has `~2(n-1)` outgoing arcs.

So the trade is: pay one potential repair per Boolean fixed, to save a
relaxation that was not expensive. `--incremental=off` is there for exactly this,
and the default stays on because the two families the paper and this stack care
about most --- Example 8 and the unconditional temporal network --- both want it.
Note that root simplification refutes most of these instances outright anyway
(see above), which is where the real win on this family is.

Root simplification interacts with this, because #592 measured Johnson's pass at
30–50 % of the solve on dense `difference_chain`. Making the solve four times
faster does not make the pass any cheaper, so its *share* rises:

| n | incremental | simplify | recursions | Johnson's (s) | solve (s) | Johnson's share |
|---:|---|---|---:|---:|---:|---:|
| 160 | off | off | 323 | — | 0.0083 | — |
| 160 | off | on | 323 | 0.0032 | 0.0112 | 29 % |
| 160 | on | off | 323 | — | 0.0027 | — |
| 160 | on | on | 323 | 0.0032 | 0.0060 | **54 %** |
| 320 | off | off | 643 | — | 0.0514 | — |
| 320 | off | on | 643 | 0.0220 | 0.0728 | 30 % |
| 320 | on | off | 643 | — | 0.0123 | — |
| 320 | on | on | 643 | 0.0228 | 0.0359 | **63 %** |
| 640 | off | off | 1,283 | — | 0.352 | — |
| 640 | off | on | 1,283 | 0.165 | 0.515 | 32 % |
| 640 | on | off | 1,283 | — | 0.056 | — |
| 640 | on | on | 1,283 | 0.164 | 0.220 | **75 %** |

The pass itself has not changed and costs the same to the microsecond. What has
changed is everything around it: on this family the root simplification stage is
now **three quarters** of the solve, against the 30-50 % #592 measured. It still
drops `n - 1` edges out of `n(n+5)/2` here and buys nothing, so this is the same
trade-off as before, just with the losing side of it four times more visible.
Nothing about that is an argument for changing the default, which is a statement
about scheduling models with conditional edges and not about this one; it is an
argument for `--simplify=off` being easy to reach, which it is.

### What this does not fix

The per-wake cost is now `O(n + |Vl| log n + reachable arcs)` rather than
`O(rounds × |E|)`, but the `O(n)` term is unavoidable without advisors: `Vl` is
built by scanning every node's bounds against `Do`. The refined-watch inbox could
supply it directly, but `propagators.cc` drops undelivered payloads when a
contradiction cuts a round short, so it could only ever be an optimisation on top
of the scan and never the sole source of truth. On a small, sparse graph — 21
nodes and a few dozen arcs, which is what `examples/rcpsp` is at the smaller
`--size` values — that `O(n)` term
plus a heap is not much cheaper than a Bellman-Ford pass that early-exits after
two rounds, and the win is correspondingly modest. The win is large exactly where
the asymptotics say it should be: `|E| >> n`, or long chains.

## Deliberately deferred

- **`IncImp`** (implication checking, to disentail half-reified edges). It needs
  no new proof machinery — "shortest path `x ⇝ y` of weight `<= d'`" plus the
  candidate edge `y --(-d'-1)--(b)--> x` is a negative cycle, so it is proof
  shape 1 with `b` the sole surviving residual, and the `saturate` already in
  place produces exactly that unit clause — but the paper's own configuration
  study says to leave it **off**: on RCPSP/max every configuration with it on
  scored below every configuration with it off. **This is the one deferral the
  RCPSP/max measurement below now costs something visible**: without it, a system
  whose infeasibility depends on edges nobody has fixed yet is invisible at the
  root.
- **Lifting `Comparison` donors**, which needs their unconditional OPB rows
  labelled; see the presolver section above.
- **Lifting `Iff`, `NotIf` and `MustNotHold` linear donors**, which need the `r`
  and `f` rows and the integer-negation row respectively rather than the
  empty-role row the two supported kinds share.
- **Zero-weight-cycle unification**, the fourth of the root simplification
  stage's sub-steps. The other three are implemented; see the section on it
  above, which also reports how often a zero-weight cycle actually turns up.
- **Runtime propagator priorities.** The paper wants bound propagation at the
  lowest priority and Boolean propagation at the highest, as separate
  propagators. gcs has no runtime propagator priorities, only
  `InitialiserPriority`. Issue #582 tracks this, and the presolver measurements
  above are the concrete cost of not having them.

## See also

- [Implementing a constraint](constraints.md) — the structural pattern this
  follows.
- [View proof-logging support](view-proof-logging.md) — invariant 1 is why the
  OPB rows are canonicalised; invariant 3 is why the bound push needs an
  explicit `pol`.
- [Proof logging for `Disjunctive`](disjunctive-proof-logging.md) — its
  `before_{i,j} ⇔ s_i + l_i <= s_j` is a half-reified difference constraint, and
  its pairwise pols are proof shape 2 at chain length 1.
