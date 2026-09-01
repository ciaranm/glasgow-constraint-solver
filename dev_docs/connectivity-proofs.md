# Connectivity: encoding and proofs

The design note for `Reachable` / `DReachable` (issue #637), the propagators
behind MiniZinc's `reachable`, `dreachable`, `connected` and `dconnected`.

The short version: connectivity is not hard to proof-log, but which encoding it
is logged *against* decides everything. Against a breadth-first unfolding of
reachability, every inference the propagator makes is a plain RUP, because unit
propagation over that encoding *is* the breadth-first search the propagator ran.
Against the stdlib's arithmetic distance labelling, none of them are. The price
of the unfolding is size: it is `O(nodes × edges)` rows, where the labelling is
`O(edges)`.

## What the constraint says

`dreachable(from, to, r, ns, es)` takes a fixed graph, a 0/1 variable per node
and per edge saying whether it is in the selected subgraph, and a root variable.
It holds when

* every selected edge has both endpoints selected (MiniZinc's `subgraph`);
* the root node is selected — so the subgraph is never empty; and
* every selected node is reachable from the root along selected edges.

`reachable` is the same with each edge followed either way. `connected` and
`dconnected` are these two with the root existentially quantified, which is
literally how the stdlib spells them, so they need no separate propagator — see
"The root is an argument" below.

## Why the stdlib encoding is the expensive one

`fzn_dreachable` encodes reachability as a spanning tree with distances:
`parent[n]` and `dist[n]` integer variables, with `dist[n] = dist[parent[n]] + 1`
and `parent[n]` constrained to be an in-neighbour along a selected edge.

That is compact, and it is a correct statement of reachability, but consider what
a checker has to do with it to conclude that some node is *unreachable*. Let `U`
be a set of nodes with no selected edge entering it from outside. If some `n ∈ U`
were selected, it would have a parent in `U` at distance `dist[n] - 1`, which
would have a parent in `U` one lower again, and so on — an infinite descent,
contradicted only because distances are bounded below. That argument is an
induction, and unit propagation does not do induction: it would have to case-split
over which node is the parent. So the inference is not RUP, and neither is
anything else the propagator would want to say.

This is not a hypothetical cost. `examples/hitori`'s `--connectivity decomposition`
reproduces exactly this encoding, and on the 5×5 Challenge instance `h5-1` it
searches 113 671 nodes and writes 815 MB of proof that takes 796 s to verify —
against 19 nodes and 98 KB for the same model with connectivity dropped
altogether. The connectivity scaffolding was not part of that benchmark; it was
essentially all of it.

## The encoding that makes it RUP

`define_proof_model` writes a breadth-first unfolding instead. With `n` nodes,
`levels = n - 1`, and one *arc* per direction an edge may be followed:

```
    reach[v][0]     ⇔  root = v                        (a fully reified flag)
    Σ_v reach[v][0] =  1
    reach[v][0]     →  ns[v] = 1                       (the root is selected)

    arc[a][k]       ⇔  es[edge(a)] = 1  ∧  reach[from(a)][k-1]
    reach[v][k]     ⇔  reach[v][k-1]  ∨  ⋁_{a into v} arc[a][k]

    ns[v] = 1       →  reach[v][levels]
    es[e] = 1       →  ns[from(e)] = 1  ∧  ns[to(e)] = 1
```

`levels = n - 1` because a walk in an `n`-node graph never needs more steps than
that, so the last level is reachability itself rather than an approximation of it.

The point of the level index is that it turns the fixpoint into an explicit
chain. Unit propagation over these rows, started from "the root is not any of
these nodes" and "these arcs are unusable", falsifies `reach[·][0]` for the nodes
outside the region, then `reach[·][1]`, and so on — which is breadth-first search,
one level per round. So whatever region the propagator's own search reached, the
checker reaches the same region, and the inference follows.

Note that this is the *same* labelling idea as the stdlib's, only unary instead of
arithmetic. The distance is spread across `levels` Boolean flags rather than packed
into one integer, and that is exactly what removes the induction.

### The root is an argument, and one-hot in the proof

`Reachable` takes the root as an ordinary problem variable. It does not allocate
one, because search only branches on variables created on the `Problem`, and
nothing determines a root by propagation; an internally-allocated root would sit
unfixed at a "solution". `connected` is therefore posted by creating a root
variable and posting `Reachable` against it, which is what `fzn_connected`'s
`let { var index_set(ns): r }` does anyway, and what `examples/hitori` and the
`mznlib/` overrides both do.

In the proof the root is *also* represented one-hot, as the `reach[v][0]` flags
with `Σ_v reach[v][0] = 1` over them. That row is what lets a proof step conclude
something from "the root has to be *somewhere*", and it holds whatever encoding
the root variable itself has — an integer variable wider than 0/1 is bits-encoded,
and unit propagation cannot enumerate a bits-encoded domain. `prepare` defines the
root's bounds to be node numbers (via `Propagators::define_bound`, so it is a row
in the OPB and a RUP at search start, not a precondition on the caller), which is
what that row stands on.

## The inferences, and what each one costs

Every rule below is one `rup` line whose entire content is its reason. The reasons
are cuts: the literals that shut the border of the region the propagator's search
reached, which is the smallest honest statement of why the search stopped there.

| inference | reason | cost |
|---|---|---|
| a selected edge's endpoints are selected, and an edge at an unselected node is not | the one literal | 1 line |
| the root is not an unselected node; a fixed root is selected | the one literal | 1 line |
| **the root is not `ρ`**, because selected node `m` cannot be reached from `ρ` | the literals shutting the border of "what can reach `m`", plus `ns[m] = 1` | 1 line, for *all* such `ρ` at once |
| **node `v` is not selected**, being unreachable from every candidate root | the literals shutting the border of the reached region, plus "the root is not any node outside it" | 1 line |
| two selected nodes in different components | none of its own — the root's domain empties one value at a time by the rule above, and the framework raises the contradiction | 1 line per candidate root |

The third rule is worth a note: it is stated by searching *backwards* from the
selected node rather than forwards from each candidate root. That is not just
cheaper — one search instead of one per candidate — it also makes the reason
independent of `ρ`, so every candidate root that fails is ruled out under the same
cut.

## What consistency this reaches

**The propagator is generalised-arc-consistent**, in both spellings, and the test
suite checks it: `reachable_test.cc` runs every case through
`solve_for_tests_checking_gac`, which asserts at every search node that every
value left in every domain has a support.

That did not come free, and the shape of what was missing is worth keeping. Write
`G` for the residual graph (live nodes, live edges), `M` for the selected nodes,
and `C` for the component of `G` that contains `M` and meets the root's domain.
Working out what each literal needs — remembering that a solution may select
*every* live edge inside the set it selects, so there is nothing tree-shaped to go
looking for — gives:

| literal | supported iff | rule |
|---|---|---|
| `ns[v] = 1` | `v ∈ C` | the unreachable-node rule |
| `es[e] = 1` | both endpoints in `C` | the same, through `subgraph` |
| `r = ρ` | `ρ ∈ C` | the root-filtering rule |
| `ns[v] = 0` | `M` lies in one component of `G − v` that still meets the root's domain | the cut-vertex rule |
| `es[e] = 0` | `M` lies in one component of `G − e` that still meets the root's domain | the bridge rule |

The first three were always there. The last two are the forcing rules, and they
are the *whole* of the difference: every other way of strengthening this
propagator is already subsumed. So **cut vertices and bridges are not a heuristic
strengthening on the way to GAC — undirected, they are exactly the rest of it.**

Undirected they are also cheap. One Tarjan pass over `C` yields the articulation
points and the bridges together, and "does removing it separate `M`" is a count of
selected nodes per DFS subtree in the same pass, so the whole thing is
`O(nodes + edges)` per call.

Two things make that less tidy than it sounds.

**It is the residual graph, not the input graph.** A 2-connected input becomes
1-connected as soon as search excludes a node, so this fires constantly rather
than only on graphs that look fragile. The `triangle` case in `reachable_test.cc`
is 2-connected and still failed a GAC check before the forcing existed: by the time
the check runs one of its three nodes is out, and the remaining edge is a bridge
between the other two.

**Directed is messier, and is not the dominator tree you would first reach for.**
The analogue of a cut vertex is a dominator, but the root is existentially
quantified, so GAC asks: for *every* candidate root `ρ`, does `v` lie on every
path from `ρ` to *some* selected node? The witnessing selected node may differ
from one `ρ` to the next. Adding a super-root with an arc to each candidate and
taking one dominator tree does **not** capture that — it asks for a single witness
good for all `ρ` at once, which is strictly weaker, and is usually vacuous anyway,
since every candidate root reaches itself. So there is no one-pass version, and
`Reachable` does not pretend otherwise: for the directed spelling it asks the
question directly, one search per candidate root per node and per edge. That is
exact, and it is why `with_cut_forcing()` exists as a switch rather than being
unconditional.

The proof side mostly follows the propagation side here: every removal is a single
RUP, and so is every forcing wherever the root is fixed. Only a forcing made while
the root is still open needs the case split of the next section — and that is the
one case where this gets expensive, measured below.

## What is not one RUP

A stronger propagator would also force *cut vertices* and *bridges*: if removing
node `j` would separate two selected nodes, `j` must be selected.

The shape of that proof is the obvious one, and it is worth saying what it is
*not*. It is not a counting argument. `CircuitSCC` compares the size of a
transitive closure against a number of steps because Hamiltonicity is a covering
property — the paths are still there, they just fail to hit everything, so
something has to be counted. Connectivity fails by there being *no* path, so the
proof is only ever "assume the node is out, show the constraint is violated,
conclude it is in": assume `ns[j] = 0`, let unit propagation walk outwards, and
have it arrive at a selected node it cannot reach. The step levels in the encoding
are there so that walk can happen at all, not to count anything.

Whether that is **one** RUP turns on one thing only: whether unit propagation has
somewhere to start. It starts at the root.

* **Root fixed** — one RUP, exactly as above. This is the whole of `dreachable`
  and `reachable` as MiniZinc usually calls them, where `r` is a constant, and it
  is also every `connected` once search has decided the root.
* **Root still open** — not one RUP, because "the constraint is violated" is now
  quantified over the root: for candidates on one side of `j` the far selected
  node becomes unreachable, and for those on the other side the near one does, and
  unit propagation cannot case-split to see it. The fix is the standard
  extended-reason pinning — one line per candidate root reifying "the root is not
  `ρ`" under the reason *plus* `ns[j] = 0`, then a closing RUP — so it costs
  `O(|dom(root)|)` lines, shrinking to one as search narrows the root.

Note that this is an artefact of anchoring the encoding at a root, not of
connectivity. A pairwise encoding has no root and would make both regimes one RUP;
it just costs `O(n³ log n)` to write down (see below).

All of this was measured rather than assumed, on a 3×3 grid against VeriPB 3.0.2:
the cut-vertex and bridge forcings verify as a single RUP with the root fixed on
either side of the cut, are refused as a single RUP with the root open, and verify
with the case split added. The same harness confirmed that four unsound variants of
the rules above are refused, so none of the acceptances are vacuous.

The rule is **not implemented**. `Reachable` today propagates the five rules in the
table, which is enough to be a checker at every leaf — a full assignment that
violates the constraint is always caught — and enough to cut `hitori`'s search by
three orders of magnitude. As the previous section says, adding cut vertices and
bridges would take the undirected spelling to GAC for one linear-time pass, and
the proof for each is a single RUP wherever the root is fixed — which is the
common case, and cheaper than this section first concluded. What is left to
measure is the open-root regime, where each forcing costs `O(|dom(root)|)` lines.

## The cost: encoding size

The unfolding is `O(nodes × edges)`. Measured on `examples/hitori`'s grid graphs,
where the whole `.opb` is dominated by this constraint:

| grid | nodes | edges | `.opb` |
|---|--:|--:|--:|
| 5×5 | 25 | 40 | 0.65 MB |
| 11×11 | 121 | 220 | 16.4 MB |

For a grid that is `O(n⁴)` in the side length, and it is the limit on where this
encoding is usable: 20×20, the largest `hitori` Challenge instance, would be a
couple of hundred megabytes of `.opb` before the search writes a line. The
stdlib's labelling is `O(edges)` and does not have this problem — it has the other
one.

There is no third option known to us that is both compact and unit-propagatable.
The pairwise "walk of length ≤ k" encoding that the Glasgow Subgraph Solver uses
for maximum common *connected* subgraph (`gss/innards/proof.cc`,
`create_connected_constraints`) builds transitive closure by repeated squaring and
also makes its connectivity inference a bare `rup`
(`not_connected_in_underlying_graph`) — but it is `O(n³ log n)`, which is fine at
the pattern sizes that solver sees and worse than the unfolding here.

## Measured against the decomposition

`examples/hitori --connectivity decomposition|propagator|propagator-no-cuts|none`
posts the same requirement four ways, so the comparison is one instance in
one binary. On `h5-1` (fataepyc-10, VeriPB 3.0.2):

| `h5-1` | `decomposition` | `propagator` | `propagator-no-cuts` | `none` (relaxation) |
|---|--:|--:|--:|--:|
| recursions | 113 671 | **24** | 38 | 19 |
| `.opb` | 1 038 149 B | 649 792 B | 649 792 B | 68 327 B |
| `.pbp` | 815 217 012 B | 246 783 B | **129 545 B** | 97 774 B |
| solve (with proof) | 12.46 s | 0.04 s | **0.04 s** | — |
| veripb | 796.28 s | 0.14 s | **0.09 s** | 0.01 s |

Against the decomposition that is 3 300× on proof size and 5 700× on verify time,
landing just above the `none` relaxation on both — the propagator has taken
connectivity from being the whole benchmark to being nearly free on this instance.
`none` is not a solving mode: it drops connectivity and reports objective 36 rather
than 17. It is in the table because it is the floor.

`propagator` against `propagator-no-cuts` is the cut-vertex and bridge forcing on
its own, and the two columns disagree about which is better. The forcing is a
straight win on search — 24 nodes against 38 here, and 1 932 against 4 920 on
`h11-1` — and a straight loss on proof: 1.9× the bytes here, **7.2×** on `h11-1`
(679 MB against 93.7 MB, and 1 485.3 s against 626.7 s to
check). The reason is entirely the open-root case split of the previous section: `connected` leaves the root existentially quantified, hitori's
branching decides it last, so essentially every forcing in this model is made in
the expensive regime and pays a line per candidate root.

The forcing is nevertheless **on by default**, because a propagator's default
should be what behaves best with proofs off, and there it is unambiguously better.
The proof cost is a thing to fix rather than a reason to propagate worse — and it
is a good specimen to fix things *with*: most of it is the large-database RUP
penalty measured below, which is exactly what VeriPB's forthcoming label groups
are meant to remove. `--connectivity propagator-no-cuts` keeps the control for
measuring that.

`h5-1` is small enough that the decomposition finishes at all. On `h11-1` it does
not solve inside **900 s even without proofs**, while the propagator solves it in
0.26 s (1 932 recursions), or 0.36 s and 4 920 without the forcing. Both settings
verify: 93.7 MB in 626.7 s without the forcing, 679 MB in 1 485.3 s with it — 7.2×
the bytes for 2.4× the check, so the lines the forcing adds are individually
cheaper than the average line of the smaller proof, though still a clear loss
overall. Proof-logging the decomposition here is not a comparison anyone can run.

That 626.7 s against 93.7 MB is worth noticing on its own, and the relaxation run
below makes the point cleanly, because it is the same instance and the same solver
with only the encoding taken away:

| `h11-1`, with proof | `.opb` | `.pbp` | veripb | s per `.pbp` MB |
|---|--:|--:|--:|--:|
| `propagator-no-cuts` | 16.4 MB, 141 506 rows | 93.7 MB | 626.7 s | 6.7 |
| `none` | 0.67 MB | **9.65 GB** | 779.9 s | **0.08** |

The relaxation's proof is 103× the size and takes only 1.24× as long to check. All
of that difference is the database every RUP is checked against: the unfolding's
141 506 rows make each proof line roughly eighty times more expensive to verify.
This is the `veripb_time = displacement × DB-tax` shape of
[`decision-diagram-proof-strategies.md`](decision-diagram-proof-strategies.md) with
the encoding's size as the tax, and it is why the `O(nodes × edges)` limit bites on
checking time well before it bites on disk. (`h5-1`, at 6 118 rows, checks at about
0.7 s per megabyte.)

**And `--connectivity none` inverts between the two instances, which matters for
how #637 was sized.** On `h5-1` the relaxation is the floor: 19 recursions and
98 KB, against the decomposition's 113 671 and 815 MB, which is what justified
"connectivity is very nearly the whole benchmark". On `h11-1` the same relaxation
takes **446 479 recursions, 86 s, and 9.65 GB of proof** (verifying, at 779.9 s,
for an objective of 323 against the real 232) — two orders of magnitude of proof
worse than solving the real problem with the propagator in its `-no-cuts` setting
(one order against the default's 679 MB). Dropping connectivity
makes hitori's *objective* much harder, because far more shadings become feasible,
and at `h11-1` that dominates whatever the connectivity encoding costs. So the
attribution argument is an `h5-1` fact, not a hitori fact: at that size
connectivity is pure overhead, and by `h11-1` it is load-bearing for search.

Two things that table does *not* say, and should not be read into it. The
propagator is not competing with the decomposition on strength alone: 24 recursions
against 113 671 is mostly the decomposition's distance labelling being a bad thing
to search over, not the propagator being clever — the rules it implements are the
straightforward ones. And `h5-1` is, as issue #637 says, a connectivity benchmark
wearing a puzzle costume; a model that also does other things will not see ratios
like these.

## See also

- [`constraints.md`](constraints.md) — the structural pattern, the reason and
  justification APIs, and the mutation-testing discipline the
  `reachable_mutation_*` lanes follow.
- [`minizinc.md`](minizinc.md) — the `mznlib/` overrides sit on
  `fzn_reachable_int` / `_enum` and `fzn_dreachable_int` / `_enum`, so `connected`
  and `dconnected` reach the propagator through the stdlib's own wrappers.
- [`proof-benchmarks.md`](proof-benchmarks.md) — `mzn_hitori` and the Group C
  decomposition-against-propagator controls.
