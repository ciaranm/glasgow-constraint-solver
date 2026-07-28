# Difference logic: `DifferenceConstraints`

`DifferenceConstraints` propagates a whole system of `x - y <= d` at once,
rather than one propagator per constraint. This note covers the graph
formulation, the two propagation directions, the round bound and why the
negative-cycle extraction is total, the canonicalisation rule and why it exists,
the two proof shapes with worked examples, the defects in the source paper's
pseudocode, and what is deliberately deferred.

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
  a lost propagation is invisible to proof logging. Relevant when incrementality
  lands.
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
change and the two columns have to be read together. Second, on the *lucky*
order at large `n` the global propagator is slightly slower in wall time despite
doing 640× fewer propagations, because this version is not incremental: every
wake re-runs the whole `O(rounds × |E|)` pass from the current bounds. That is
the deferred work below, not a property of the approach.

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

## Deliberately deferred

- **Incrementality.** The paper's `IncSat` / `IncLB` / `IncUB` maintain a valid
  potential function `π` and run Dijkstra on the reduced-cost graph, processing
  all bound changes since the last run in one pass, in `O(n log n + m)`. `π`
  stays valid when edges are removed — validity is a conjunction over edges — so
  it needs no trailing, which suits backtracking well. None of that is here: this
  version recomputes Bellman-Ford from scratch on every wake, which is
  `O(n·m)` worst case. The wall-time caveat above is entirely this.
- **Half-reified edges** (`b -> x - y <= d`). These make the edge set change
  during search, which needs the trailed edge journal and the paper's `E'`
  machinery. The proof side is already understood and costs nothing extra: a
  half-reified row contributes `M·¬b` to the sum, the `BinEnc` terms telescope
  exactly as before, and one `saturate` turns the residuals into the clause
  `¬b_1 ∨ … ∨ ¬b_k`. `Disjunctive` already does this at `k = 1`.
- **`IncImp`** (implication checking, to disentail half-reified edges). It needs
  no new proof machinery — "shortest path `x ⇝ y` of weight `<= d'`" plus the
  candidate edge `y --(-d'-1)--(b)--> x` is a negative cycle, so it is proof
  shape 1 with `b` the sole surviving residual — but the paper's own
  configuration study says to leave it **off**: on RCPSP/max every configuration
  with it on scored below every configuration with it off.
- **The presolver** — detecting difference-shaped constraints already posted on
  a `Problem` and lifting them into a global propagator. This is the half the
  paper's measurements say is actually valuable (310.00 → 312.94 for the
  propagator alone on the MiniZinc challenge set, → 320.95 with simplification),
  and it depends on #546's typed constraint enumeration.
- **Root simplification** — Johnson's all-pairs shortest paths, then dropping
  redundant edges, fixing Booleans whose edge would close a negative cycle, and
  unifying variables on a zero-weight cycle. Note that dropping a redundant edge
  is a decision about which *propagators run*, not about what the model says: the
  OPB must always contain every posted constraint, so the removal has no proof
  obligation at all.
- **Runtime propagator priorities.** The paper wants bound propagation at the
  lowest priority and Boolean propagation at the highest, as separate
  propagators. gcs has no runtime propagator priorities, only
  `InitialiserPriority`.

## See also

- [Implementing a constraint](constraints.md) — the structural pattern this
  follows.
- [View proof-logging support](view-proof-logging.md) — invariant 1 is why the
  OPB rows are canonicalised; invariant 3 is why the bound push needs an
  explicit `pol`.
- [Proof logging for `Disjunctive`](disjunctive-proof-logging.md) — its
  `before_{i,j} ⇔ s_i + l_i <= s_j` is a half-reified difference constraint, and
  its pairwise pols are proof shape 2 at chain length 1.
