# `Reachable`: every selected node is reached from the root along selected edges

> **Maturity** production ·
> **Audited** 2026-10-09 at `86caad24` ·
> **Open issues** filed by this audit: #1305 (an empty node set in MiniZinc's
> int spelling is a solver error rather than unsatisfiable, shared with `tree`
> and `path`), #1316 (the directed forcing is a search per candidate root per
> node and per edge on every call), #1312 (each open-root pinned lemma carries
> the whole reason rather than its own piece's). Filed from the `dag` audit and
> touching this family: #1309 (installing a propagator is quadratic in its
> trigger count). Already open and touching it: #833 (the large-domain policy; only the root can be
> wide, and `define_bound` narrows it), #868 (cross-solver comparisons; this document gives one, by hand),
> #1006 (MiniZinc shape lanes). See [Next steps](#next-steps). Tracked under
> #871.

`Reachable(edges, root, ns, es)` and `DReachable(...)` say that the subgraph
picked out by the 0/1 variables `ns` (per node) and `es` (per edge) of a fixed
graph is reachable from a variable root, following each edge either way or only
forwards. They are MiniZinc's `reachable` and `dreachable`, and through the
stdlib's own wrappers `connected` and `dconnected`; `Tree`, `DTree`, `Path` and
`DPath` post them as a child. One propagator serves both spellings, and the
encoding is a **breadth-first unfolding** of reachability, `reach[v][k]` for
"node `v` is reached within `k` steps", chosen because unit propagation over it
*is* the breadth-first search the propagator runs, so every removal is a single
RUP whose whole content is its reason. Issue #637 and PR #784 brought it in, and
[`connectivity-proofs.md`](../connectivity-proofs.md) is the design note, shared
with [`dag.md`](dag.md).

Four things to know before touching it.

- **It is generalised arc consistent on `ns`, `es` and the root, in both
  spellings**, with the cut-vertex and bridge forcing on (the default). A
  brute-force check of the root fixpoint on 12,000 random instances per
  spelling, up to seven nodes, with self loops, parallel edges, constants and
  holey roots, found no unsupported value and no missed failure. With the
  forcing off, every value that loses support is an `ns = 0` or `es = 0`:
  the removals alone are GAC on the 1-values and the root.
- **The price is the encoding: `Θ(nodes × (nodes + edges))` rows.** Every
  node is carried at every level, edges or not: 136,395 rows and 14.0 MB for
  an 11-by-11 grid, and 80,402 of the family's rows for 200 nodes and no
  edges. Every proof line is checked against them, this family's or not.
  That is what limits the family's proofs on large graphs. The undirected
  propagator's detection is linear in the graph per call, plus `O(n)` per
  unreachable region for rule 6 and `O(n + |A|)` per piece holding a candidate
  for each forcing's reason: a bridge has at most two such pieces, a cut
  vertex up to its degree.
- **A forcing made while the root is open costs a line per candidate root.**
  With the root fixed, a cut vertex or a bridge is one RUP; with it open, unit
  propagation cannot case-split over the root, so the proof pins one lemma per
  candidate first. MiniZinc's `connected` leaves the root open and `hitori`
  decides it last, so on `h11-1` 212,458 of the proof's 289,750 lines are
  such lemmas, from 2,396 forcings, about 89 each, and they are 96.5% of its
  673 MB. Most of each lemma is the border of its own piece, which the lemma
  needs given that its reason is the closure's border (a smaller cut might
  do); narrowing each to that (#1312) removes 23.5% of the bytes and leaves the
  lemmas at 95.4%. `with_cut_forcing(false)` keeps the control: 80 MB, for 2.5
  times the search.
- **The directed forcing is a search per candidate root per node and per edge,
  on every call.** It is exact, and the only part of the family whose cost is
  super-linear in the graph whether or not anything is forced: on a 20-by-20
  grid with both arcs per adjacency it costs about 5 times the per-call time of
  the same propagator with the forcing off, and about 20 times the undirected
  spelling's. No corpus model posts `dreachable` or `dconnected`.

## What it is

### Semantics

```
Reachable(edges, root, ns, es)      DReachable(edges, root, ns, es)
```

Nodes are numbered `0 .. |ns| − 1`; `edges[e]` is a pair of node numbers, and
`es[e]` says whether edge `e` is selected. The constraint holds when

- every selected edge has both endpoints selected (MiniZinc's `subgraph`);
- the root is a node number, and that node is selected, so the selected
  subgraph is never empty; and
- every selected node is reached from the root along selected edges, each
  followed either way (`Reachable`) or only from `edges[e].first` to
  `edges[e].second` (`DReachable`).

`connected` and `dconnected` are these with the root existentially quantified.
There is no class for them: the root has to be a `Problem` variable, since
search only branches on those and nothing determines a root by propagation, so
a caller creates one over the node numbers and posts `Reachable` against it,
which is what `fzn_connected`'s `let { var index_set(ns): r }` does too
(`reachable.hh:94–100`).

- **The root may be declared wider than the node numbering.** `prepare()`
  defines its bounds as `0 .. n − 1` with `Propagators::define_bound`
  (`reachable.cc:125–126`), which writes a row to the OPB where the declared
  domain is wider and removes the rest at the root, with hint `initial_bound`.
  A root that is no node number is simply false, as in `fzn_dreachable`.
- **No nodes:** `prepare()` throws `InvalidProblemDefinitionException`
  ("Reachable needs at least one node", `reachable.cc:100–101`), where the
  constraint is simply unsatisfiable. Through MiniZinc's int spelling that is a
  solver error; see [Robustness](#robustness-and-limits) and #1305.
- **`ns` and `es` must lie in `0..1`**, else `prepare()` throws
  (`reachable.cc:113–118`); one `es` per edge, and every endpoint a node
  (`102–108`). The `.scp` reader and `fzn-glasgow` refuse a negative endpoint
  themselves (`scp_reader.cc:724–725`, `fzn_glasgow.cc:189–190`).
- **No edges, one node, self loops, parallel edges** are all accepted and mean
  what they say. A self loop never helps reach anything; two parallel edges each
  stop the other being a bridge.
- **A repeated variable** among `ns` (or `es`) means those nodes (edges) are
  selected together; the propagator and the OPB both read it that way, and
  consistency is not claimed (`reachable.hh:89–92`). See
  [Robustness](#robustness-and-limits).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Reachable` | ✓ `fzn_reachable` (int and enum spellings)[^mznreach], and `connected` through the stdlib's `fzn_connected` | `n/a`[^xcsp] | ?[^gcspy] | ✓ `reachable` | |
| `DReachable` | ✓ `fzn_dreachable` (both spellings), and `dconnected` | `n/a`[^xcsp] | ?[^gcspy] | ✓ `dreachable` | |
| either, reified | `unsupported`: the stdlib's `fzn_reachable_*_reif` doubles the edges into `fzn_dreachable_*_reif`, which aborts ("Reified dreachable constraint is not supported"), and `fzn_connected_reif` and `fzn_dconnected_reif` abort too, in 2.9.7 and 2.10.1 | `n/a` | `n/a` | `unsupported` | no reified class exists |

[^mznreach]: `minizinc/mznlib/fzn_reachable_{int,enum}.mzn` and
    `fzn_dreachable_{int,enum}.mzn` call `glasgow_reachable` /
    `glasgow_dreachable` (`fzn_glasgow.cc:955–967`). The enum spelling shifts the
    endpoints and the root by `min(index_set(ns))`, so a node index set need not
    start at one; the int spelling's nodes are `1..N` and it shifts by one. The
    undirected override goes straight to `glasgow_reachable` instead of doubling
    the edges as the stdlib's `fzn_reachable` does, which would give the
    propagator two edge variables aliasing one. The endpoints are parameters, so
    their shift is free; the root's costs one auxiliary: `r - offset` is a fresh
    FlatZinc variable tied to `r` by a two-term `int_lin_eq`. That does **not**
    lose the root's holes, unlike the shape #803 fixed for other globals:
    `fzn-glasgow` recovers a two-term unit-coefficient `int_lin_eq` as `Equals`
    (`fzn_glasgow.cc:639–702`), which intersects domains, so a value this
    propagator removes from the shifted root leaves `r` too (checked by the
    fact-check's probe, `Equals{r, x + 1}` with `Reachable` on `x`: a hole at
    `x = 2` appears in `r` at 3). Consistently, padding the node array with an
    unselectable node 0, so the offset is zero and the root goes in unshifted,
    gives the same 24 and 1,932 nodes on `h5-1` and `h11-1`
    (`tmp/fd-graph/reachable/hitori-mzn/hitori_pad.mzn`).

[^xcsp]: XCSP3-core defines no reachability or connectivity constraint
    (#637), and `xcsp/` binds nothing here.

[^gcspy]: `gcspy` binds nothing in this family (`python/gcspy.cc` has
    `Circuit` and no other graph constraint), and no issue tracks it. Whether
    CPMpy itself has a vocabulary for it was not checked, and no decision about
    binding it is documented, so the cell stays `?`.

**Differential checks.** Solution sets from `fzn-glasgow` agree with Gecode's
(on the stdlib decomposition) on eleven models, under MiniZinc 2.9.7 and
2.10.1 alike: the int spelling of both constraints over four nodes, the
`reachable` one with its root declared over `0..6`; node index sets starting at −2 and at 3, with edge index
sets starting at 5 and 0, and a holey root; enum-typed nodes and edges, for
`dreachable` and `dconnected`; `connected` over negated Booleans with derived
edges, which is `hitori`'s shape; one variable for two nodes, a constant node,
a constant edge, a self loop and a parallel edge; no edges; and one node with a
self loop (`tmp/fd-graph/reachable/frontend/`, `run.sh`; 2 to 100 solutions
each, and every one of the 44 runs ends in `==========`, so each enumeration was
complete and none was an `=====ERROR=====`). The empty node set is the one disagreement: the int spelling is
`=====ERROR=====` against Gecode's and Chuffed's `=====UNSATISFIABLE=====`
(#1305); the enum spelling and `connected` reach `=====UNSATISFIABLE=====`
only because `min` of an empty index set is undefined and MiniZinc flattens the
constraint to `false`, with a warning.

**`.scp`.** `read_reachable` (`scp_reader.cc:710–735`) resolves the root and
every `ns` and `es` entry with `resolve_variable`, which accepts atoms only, so
a model with a view anywhere in this constraint writes a `.scp` the solver
cannot read back (`S-expression error: expected an atom, found a list`). That
is the reader's general limitation, recorded in [`in.md`](in.md) and
[`all_equal.md`](all_equal.md), not this family's. With plain variables the
round trip enumerates the same 100 (undirected) and 27 (directed) solutions as
the C++ model and both proofs verify (`tmp/fd-graph/reachable/views/`, mode
`wide`). The writer does not record `with_cut_forcing`, so a model posted with
the forcing off propagates more strongly when read back.

### Options

**`with_cut_forcing(std::optional<bool> = true)`**, default on: force in the
nodes and edges every remaining solution must use (rules 7 to 10). It does
**not** change the OPB; it changes only propagation, and so the proof. On by
default because a propagator's default is what behaves best with proofs off,
and on undirected `hitori`, the only corpus use measured (`surface-based-tsp`
reaches the family through `Tree`), the forcing is better there (24
nodes against 38 on `h5-1`, 1,932 against 4,920 on `h11-1`). For the directed
spelling, which the same default governs, it is shown on `DPath` grid searches
(`path.md`'s A/B with the child's forcing off: 296,234 nodes in 29.4 s against
5,686,456 in 218.2 s on a 6 × 6 grid), not on any corpus model; and per call
it is dear: on the 20 × 20 grid probe here the forcing costs 3.3 ms a call
against 0.6 ms with the root open, about 4.3 s against 0.8 s for the same 200
solutions, an enumeration in which it saves almost no nodes with the root
open (1,160 against 1,193 recursions); with the root fixed it does save nodes,
1,196 against 1,629 at 20 × 20 and 599 against 1,056 at 10 × 10 (see [CPU
performance](#cpu-performance)). The header's comment that the switch has "no
effect on the directed spelling" (`reachable.hh:54–55`) is stale: rules 9 and 10
run under it, and brute force shows `DReachable` is GAC with the forcing and not
without. Turned off, the undirected spelling is still a
checker at every leaf, and the removals keep the 1-values and the root GAC.
`examples/hitori --connectivity propagator-no-cuts` is the control; no frontend
exposes the switch, and `Tree` and `Path` post their child with it on.

**`with_proof_mutation(ReachableProofMutation)`**, testing only: drops one part
of every reason of one kind, for the mutation lanes. See
[Tests](#tests).

There is no consistency tag.

### Variable kinds and views

Plain variables, constants and views of either sign, for the root and for every
`ns` and `es` entry, so long as each `ns` and `es` is within `0..1`. The
propagator reads `optional_single_value`, `in_domain` and the root's values
only. The proof handles views: the encoding's rows are written over
`ns[v] == 1`, `es[e] == 1` and `root == v` literals, which the view layer
spells over the underlying variable. Checked by enumeration with proofs, both
spellings, on a five-edge graph: `ns` and `es` as negated views `1 − x`, the
root as `r + 3`, and the root as `r − 10⁹` over `0 .. 2·10⁹`; every proof
verifies and the counts match brute force (`views.cc`, modes `neg` and
`widev`). `reachable_test` posts no view.

### Reification

None, and none wanted: no corpus model reifies it, and the stdlib's own reified
forms abort.

### Relation to other families

- **Decomposes into it:** MiniZinc's `connected` and `dconnected`, through the
  stdlib's wrappers; `tree`, `dtree`, `path`, `dpath` and everything riding them
  (`steiner`, `dsteiner`, `bounded_path`, `bounded_dpath`, both
  `weighted_spanning_tree` spellings), through `Tree` and `Path`.
- **Child constraints:** none of its own.
- **Posted as a child:** `Tree` and `DTree` (`tree.cc:65–73`), `Path` and
  `DPath` (`path.cc:64–72`) post `Reachable` or `DReachable` under their own
  constraint ID, so its rows are labelled with the parent's ID and its
  assertions carry hint `reachable` with the parent's ID: under a `Tree`, 22 of
  the 23 hinted assertions on a three-node enumeration say `::reachable:((constraint_id _2))`,
  `_2` being the `Tree`. The forcing is on there, and nothing passes it through.
  [`tree.md`](tree.md) and [`path.md`](path.md) own those classes and their
  counting rows; this document owns everything the child does.
- **Shares code:** none. `Reachable`, `Subgraph` and `Dag` each carry their own
  copy of the two subgraph rows per edge (`sgf<e>`, `sgt<e>`) and of the two
  subgraph rules (here `reachable.cc:140–145`, `226–240`; `subgraph.cc:90–93`,
  `118–131`; `dag.cc`), and each family's document records its own copy;
  [`subgraph.md`](subgraph.md) and [`dag.md`](dag.md) own theirs. `Dag` also
  writes the unfolding idea with the root taken out, as its own code. The
  design note covers all three. Nothing in `gcs/constraints/innards/` is called
  from here.
- **Presolvers:** none reads it.
- **Frontend-only reach:** `connected` and `dconnected` have no class, and reach
  the propagator only through `reachable` / `dreachable`.

## The proof model

### OPB encoding

With `n` nodes, `levels = n − 1`, and one *arc* per direction an edge may be
followed (two per edge for `Reachable`, one for `DReachable`), so `|A| = 2|E|`
or `|E|`:

```
for each edge e = (u, w):
  sgf<e>:   es[e] = 1  ⇒  ns[u] = 1
  sgt<e>:   es[e] = 1  ⇒  ns[w] = 1
for each node v:
  x[id][v][root]          ⇔  root = v                      (fully reified flag; reach[v][0])
  rootin<v>:  x[id][v][root]  ⇒  ns[v] = 1
root1le, root1ge:  Σ_v x[id][v][root] = 1
for k = 1 .. levels:
  for each arc a = (from → to) of edge e:
    x[id][a_k][arc]       ⇔  es[e] = 1  ∧  reach[from][k−1]       (fully reified)
  for each node v:
    x[id][v_k][reach]     ⇔  reach[v][k−1]  ∨  ⋁_{a into v} arc[a][k]   (fully reified)
for each node v:
  reached<v>:  ns[v] = 1  ⇒  reach[v][levels]
plus, from prepare(), unlabelled:  root ≥ 0,  root ≤ n − 1   (where the declared domain is wider)
```

`levels = n − 1` because a walk in an `n`-node graph never needs more steps, so
the top level is reachability, not an approximation of it.

**It is definitional:** every flag is defined by a fully reifying pair, the
subgraph, root and reached rows are the constraint, and nothing is added for
the propagator's sake. The one-hot root (`root1le`, `root1ge`) is how the
proof concludes something from "the root is *somewhere*" whatever the root's
own encoding is; it is a consequence of the flag definitions, kept because the
open-root forcing's closing step needs it as a row.

**Size.** Counted from `define_proof_model` (`reachable.cc:131–198`), the rows
labelled with the constraint's ID number exactly

```
2|E| + 4n + 2 + 2(n − 1)(|A| + n)
```

`2|E|` for `sgf` and `sgt`; `4n + 2` for the two reifying rows of each root
flag, `rootin`, `reached`, and `root1le` / `root1ge`; and per level, two
reifying rows per arc flag and per reach flag. The flags are about half as
many as the rows. The level term has a node part as well as an arc part,
because every node gets a reach flag at every level whether or not an edge
touches it. So the encoding is `Θ(n(n + |E|))`, which is `Θ(n · |E|)` only when
the graph has at least about `n` edges, as any connected one does. The formula
matches the `.opb` exactly at every point measured (`size.cc`: distinct free
`ns` and `es`, the root over `0..n − 1`, stopped at the first solution; each
root proof verifies):

| graph | nodes | edges | spelling | family rows | whole `.opb` rows | bytes |
|---|--:|--:|---|--:|--:|--:|
| no edges | 10 | 0 | either | 222 | 276 | 19 KB |
| no edges | 50 | 0 | undirected | 5,102 | 5,356 | 398 KB |
| no edges | 100 | 0 | undirected | 20,202 | 20,706 | 1.5 MB |
| no edges | 200 | 0 | undirected | 80,402 | 81,406 | 6.3 MB |
| path | 100 | 99 | undirected | 59,604 | 60,207 | 5.7 MB |
| path | 100 | 99 | directed | 40,002 | 40,605 | 3.6 MB |
| complete | 30 | 435 | undirected | 53,192 | 53,781 | 5.6 MB |
| complete, one arc per pair | 30 | 435 | directed | 27,962 | 28,551 | 2.9 MB |

*Release build of `86caad24`, fataepyc-10, 2026-10-09
(`tmp/fd-graph/codex/reachable/size/`).* With no edges the family's rows are
`2n² + 2n + 2`, where `n · |E|` is zero. On grids (`gridprobe.cc` on a `k × k`
grid, all variables free, the `.opb` of a one-solution run):

| grid | nodes | edges | spelling | rows | bytes |
|---|--:|--:|---|--:|--:|
| 3 × 3 | 9 | 12 | undirected | 651 | 56 KB |
| 5 × 5 | 25 | 40 | undirected | 5,391 | 512 KB |
| 7 × 7 | 49 | 84 | undirected | 21,531 | 2.1 MB |
| 9 × 9 | 81 | 144 | undirected | 60,207 | 6.1 MB |
| 11 × 11 | 121 | 220 | undirected | 136,395 | 14.0 MB |
| 11 × 11 | 121 | 440 | directed, both arcs | 137,055 | 14.1 MB |

*Release build of `86caad24`, fataepyc-10, 2026-10-09
(`tmp/fd-graph/reachable/grid/opb/`).* For the undirected 11 × 11 grid the
level rows are `120 × (880 + 242) = 134,640`, plus 926 other family rows, which
is 135,566 rows labelled with the constraint's ID; the remaining 829 are the
variables' own encodings. Rows here are constraint rows: the `.opb`'s
`preserved:` header line is not counted, as in [`tree.md`](tree.md).
`Θ(n(n + |E|))`, so `Θ(k⁴)` in a grid's side, `Θ(n³)` on a dense graph, and
`Θ(n²)` however few the edges. The unfolding is independent of domain width;
the root's own encoding is not. It is a bit sum logarithmic in the root's *declared* width, and `define_bound`
adds two clamp rows rather than re-encoding it: on a three-node path the `.opb`
is 67 rows and 4,674 bytes with the root over `0..2`, and 69 rows with
6,620 bytes at `±10³`, 12,028 at `±10⁹` and 22,840 at `±(2⁶⁰ − 1)`
(`tmp/fd-graph/reachable/width/w.cc`); `tree.md` measures the same.

### Labels

None load-bearing. Every inference is a RUP with no antecedent list, so no
justification cites a row. The labels exist and are stable, which is what an
external tool would search for: `c[id][sgf<e>]`, `c[id][sgt<e>]`,
`c[id][rootin<v>]`, `c[id][root1le]`, `c[id][root1ge]`, `c[id][reached<v>]`,
and the flags `x[id][v][root]`, `x[id][a_k][arc]` (arc index `a`, level `k`) and
`x[id][v_k][reach]`. Under `Tree` and `Path` the `id` is the parent's.

### Cake conformity

None. `cake_pb_cp` has no `reachable` or `dreachable` rule (its binary's only
graph keyword is `circuit`), so no SCP chain case exists, and the writer's
`reachable` / `dreachable` terms are read by the solver's own `.scp` reader
only. There is no divergence to name, because there is nothing to diverge
from; a cake rule would most naturally adopt this encoding, since it is the
one that makes the inferences RUP.

### Proof-time state

- **At the root:** nothing of this family's beyond the OPB, and the
  `initial_bound` RUPs that cut a wide root. Every flag above is in the OPB,
  created in `define_proof_model`, not introduced in the proof.
- **During search:** one `rup` per inference, at `ProofLevel::Current`, so
  deleted when search backtracks past it. The only lines at
  `ProofLevel::Temporary` are the open-root forcing's pinned lemmas (rules 7 to
  10), deleted by `del range` as soon as the inference is derived. Nothing a later step depends on is deleted: no inference cites
  another's lines.
- **Naming:** the labels and flag names above.
- **Proof-only auxiliaries determined on a solution:** yes. On a full
  assignment, the root flags follow from the root's equality literals, then
  each level's arc and reach flags from the level below and `es`, in one
  direction, by their fully reifying rows.
- **Nothing dangles with proofs off:** `define_proof_model` is not called, and
  the propagator keeps no proof-only data.

## The implementation

### Initialisation and global data

`prepare()` checks the shape and the 0/1 bounds and defines the root's bounds;
nothing else. `install_propagators` builds the arc list and an adjacency index
(arcs leaving and entering each node), `O(n + |E|)`, once, and captures them in
the propagator. There is no initialiser of the family's own; the root's
`define_bound` installs one. `define_proof_model` writes the `Θ(n(n + |E|))`
rows, with proofs on. With proofs off too, installing the propagator is
quadratic in its trigger count, `n + |E| + 1`: `Propagators::install_returning_id` builds the
scope with a linear `contains` per trigger (`propagators.cc:724–748`), and then
unions it into the constraint's scope with another linear `contains` per scope
variable (`765–769`), so fixing the first loop alone leaves it quadratic. The
`dag` audit measured this as about two thirds of the 11 s to the first node on
a 100,000-node path (#1309).

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| reachability | `on_change`, every `ns`, every `es`, and the root | derived: every `ns` and `es` (vacuously, being `0..1`) and **the root** | 1–6, and 7–8 (undirected) or 9–10 (directed) | always; 7–10 only with `with_cut_forcing` | never claims | never: returns `Enable` on every path |
| `define_bound` initialiser (root) | — | — | root bounds | a root declared outside `0..n−1` | — | — |

**The root's `on_change` is honest.** Rules 3, 5 and 6 and the forcing read the
root's values one at a time, as the set of candidate roots, so removing an
interior value of the root really can give this propagator an inference, and a
`Reachable` on a root variable is a legitimate reason for another family's
interior pruning of it to stay on.

**Idempotence.** Not claimed. Rules run in a fixed order within a call, each
reading the state the previous ones left, and the forcing reads counts taken
before its own first forcing, so a forcing can enable more on the next call.
Whether a second call ever changes anything after a full one was not checked.

### Mutable state and incrementality

None. The propagator has no `add_constraint_state` and no member state; every
call rebuilds the residual graph (`node_out`, `arc_out`, `O(n + |A|)`) from the
domains, and runs its searches from scratch. Each search allocates its own
`seen` vector and stack. A dynamic-connectivity structure could maintain the
residual graph and its components across calls, at the cost of backtracking
it; nothing measured here says the per-call rebuild is the bottleneck on the
undirected spelling (its detection is linear in the graph; each forcing then
pays `O(n + |A|)` per piece holding a candidate for its reason), and the directed forcing's cost is in its
algorithm, not in rebuilding.

### Interior values and optional pruning

**Offers.** `None.` The propagator is GAC and has one arm.

**Observes.** **The root, and only the root.** `ns` and `es` are `0..1`, so they
have no interior. The root's interior is read value by value, as the set of
candidate roots, and its `on_change` trigger says so, which is the truth: a
removed interior value is a candidate that can no longer be the root, and that
can change rules 5, 6 and the forcing.

### Robustness and limits

**Unbounded domains.** Only the root can be wide, and `define_bound` cuts it to
`0..n−1` before the propagator first runs. A root over `±10⁹`, plain or as an
offset view, enumerates in 0.01 s and verifies (`views.cc`). See [Interval
efficiency](#interval-efficiency).

**Negative values and zero.** A negative root value is not a node, so it is
removed with the rest of the out-of-range values (`reachable_test`'s
`path3_wide_root` declares the root over `−1..4`). `ns` and `es` must be in
`0..1`.

**Degenerate shapes.**

- *No nodes:* refused at `prepare()` with `InvalidProblemDefinitionException`
  where the meaning is "unsatisfiable". Through MiniZinc, the int spelling
  `reachable(0, 0, ...)` and `dreachable(0, 0, ...)` print
  `=====ERROR=====` where Gecode and Chuffed print `=====UNSATISFIABLE=====`,
  on 2.9.7 and 2.10.1. `Tree`, `Path` and their directed forms, and the
  `dsteiner` and `d_weighted_spanning_tree` wrappers, error the same way
  (`tree.md`, `path.md`); `Path` throws before its child is installed, so it
  needs its own fix (#1305, which covers all three). `dag` and four-argument `subgraph` have
  a different defect with the opposite answer: an empty instance is
  satisfiable and the mznlib flattens it to a wrong UNSAT (#1303). No test posts an empty node set.
- *No edges, one node, self loops, parallel edges:* handled, and covered by the
  random checks below and by `reachable_test`'s `single` case.
- *A repeated variable in `ns`:* sound, not GAC, and not even failure-complete
  at the root. 3,000 random aliased instances per spelling (`reachcheck`,
  `alias`, seed 3): no solution lost, but 312 undirected and 296 directed
  instances are unsatisfiable at a root fixpoint that does not fail, and 410
  and 401 leave an unsupported value. The smallest: two nodes, no edges, one
  variable for both; the root has to be one of them and then the other is
  selected and unreachable, but no rule sees that the two `ns` are one. The
  header says consistency is not claimed under aliasing, and `reachable_test`'s
  `dup` runs check the solutions only. 600 aliased instances with proofs all
  verify (`proofsweep.cc`).
- *A repeated variable in `es`:* this audit's probes alias `ns` only. The
  fact-check's did both (`tmp/fd-graph/factcheck/reachable/strength/`, six
  nodes, up to nine edges, 3,000 per spelling with `es` aliased): sound and no
  missed failure, but not GAC, with an unsupported value in 104 undirected and
  117 directed instances, of every kind (`es` and `ns` either way, and the root
  when directed); and 600 enumerations with `ns` and `es` both aliased verify,
  with counts matching brute force (`psweep/`).
- *A constant operand:* a constant root, `ns` or `es` is fine (covered by the
  random checks); a constant root behaves as a fixed one, so every forcing is
  one RUP.

**Overflow.** Nothing to guard. No arithmetic is done on values: the root's
values are compared with `0` and `n` and cast to a node index only when inside
them (`reachable.cc:243–244`); the bounds `0` and `n − 1` are `size_t` counts.
The root's declared domain is subject to #1214's `±(2⁶⁰ − 1)`, like any
variable's.

### Interval efficiency

**Fine at any width.** The only variable that can be wide is the root, and it
is cut to the node numbers before any of this runs.

1. **The propagation side.** `state.for_each_value_immutable(root, …)` once
   for rule 3, once per search in rule 5, once for rule 6's candidate list and
   once for the forcing's (`reachable.cc:247`, `361`, `376`, `429`), plus `in_domain(root, σ)` for every
   node `σ` in the open-root forcing (`489`). All are bounded by the number of
   nodes, since the root's domain is inside `0..n−1`. Every other loop is over
   nodes, arcs or edges. The cost that matters is graph-shaped, not
   width-shaped; see [CPU performance](#cpu-performance).
2. **The reason side.** Rules 1 to 4 have one-literal reasons. Rule 5's is the
   border of a region, rule 6's the border plus one `root ≠ u` per node `u` of
   the region, and the open-root forcing's adds `root ≠ σ` for every non-candidate
   node: per node, never per value. Assembly is **not** guarded on
   `want_reasons()`: every inference builds its reason eagerly
   (`ExplicitReason{lits}`), with proofs off too: `O(n + |A|)` for rules 5
   and 6 per search, and for a forcing `O(n + |A|)` **per piece** holding a
   candidate, since each search allocates `seen(n)` and each border scan walks
   all `n` nodes whatever the piece's size (`reachable.cc:288`, `316–317`), plus
   an `O(n)` loop over the root's values. So a bridge costs `O(n + |A|)` (at
   most two pieces), a cut vertex `O(p · (n + |A|))` with `p ≤ min(deg v,
   |candidates|)`, and a directed forcing `O(|candidates| · (n + |A|))`, one
   search per candidate (`reachable.cc:449–491`). On a star whose centre is
   forced with the root open over the leaves, the forcing's cost (open minus
   fixed root) roughly quadruples per doubling of the leaves: 30 and 116 ms at
   4,000 and 8,000 (the fact-check's `star.cc`, re-run;
   `tmp/fd-graph/factcheck2/reachable/`). That is a
   per-inference cost proportional to the graph, not to a width.
3. **The proof side.** One `rup` line per inference; the open-root forcing adds
   one pinned lemma per candidate root, a count of nodes. No form is chosen by
   width or by kind. The one width effect is in the OPB: the root's bit-sum
   encoding is logarithmic in its declared width (see [OPB
   encoding](#opb-encoding)). What a line *costs to check* is proportional to the
   encoding, `Θ(n(n + |E|))` rows, which is the family's real proof cost; see
   [Proof performance](#proof-performance).
4. **The audit lane.** Two rows, `Reachable` and `DReachable`, pinned
   `NoWidePosition`: a path of three nodes, `ns` and `es` `0..1`, and a root over
   `0..2` (`large_domain_audit_test.cc:822–831`). They vary nothing: the root is
   never declared wide, never a view, never holey. The wide root is this audit's
   probe: `views.cc`, modes `wide` (a root over `±10⁹`) and `widev` (an offset
   view over `0 .. 2·10⁹`), linked against a `GCS_LARGE_DOMAIN_GUARD` build
   (limit 100,000; `gcs-fd-small-am1-patch-wt/build-guard`, at `c9ceea25`, where
   `gcs/constraints/reachable/` is identical to `86caad24`'s), enumerates both
   spellings with proofs and does not trip
   (`tmp/fd-graph/reachable/guard/`). At `86caad24` the rows are pinned
   `NoWidePosition`. PR #1302 (open) pins them `Clean`, as the safer choice,
   with wide-declaration rows for every index-valued position, this root
   among them, and its guarded run trips nothing. The lane is registered as a ctest
   only under `-DGCS_LARGE_DOMAIN_GUARD=ON` (`gcs/CMakeLists.txt:212–214`), which
   no CI lane sets (#920).

## Inference catalogue

Ten rules. Rules 1 and 2 are `subgraph`; 3 and 4 tie the root to `ns`; 5 and 6
are the reachability removals; 7 and 8 are the undirected forcing, 9 and 10
the directed one, all four only with `with_cut_forcing`. One propagator runs
them all, in that order, per call (`reachable.cc:224–633`).

Five facts hold for all ten.

**There is no explicit contradiction.** The code never calls `contradiction()`.
A conflict is always an ordinary inference whose literal is already false, and
its assertion is `attempted literal ∨ ¬reason`. The commonest is two selected
nodes in different components: rule 5 removes the root's candidates one at a
time and the last removal fails. Measured at `Inferences`, two pieces `0–1` and
`2–3` with `ns[0]` and `ns[2]` selected (`rules.cc`, case `conflict`): rule 5
asserts `root ≠ 2` and `root ≠ 3` under `ns[0] = 1`, then `root ≠ 0` and
```
a 1 ~i[root][eq1] 1 ~i[n2][eq1] >= 1::reachable:((constraint_id _1));
```
which is the failing one.

**One hint, no subhint.** Every assertion carries `hints::Reachable`,
`(constraint_id <id>)` on the wire, with `<id>` the parent's under `Tree` and
`Path`. Nothing says which rule fired; the clause's shape does (one literal of
reason, a border, a forcing). Every assertion carries its reason: none is a bare
unit clause, unlike the SCC propagator and `SmartTable` at the assertion levels.

**No published justification procedure covers rules 5 to 10.** Rules 1 to 4
are a row or a two-row chain. Rules 5 to 10 are ours: the procedure is "unit
propagation over the unfolding replays the propagator's breadth-first search",
which the design note argues and which no JP in McIlree's thesis states.
Each step it takes is a clause or a fully reifying pair, so the facts it rests
on are Theorem 2.6 (a step under a reason reduces to its consequent) and the
flag definitions; the induction that the stdlib's distance labelling would need
is replaced by `n − 1` explicit levels, one round of propagation each.

**The search, and so the reason, is over the residual graph.** A node is *out*
when `ns[v]` is fixed to 0, an arc when its edge is fixed to 0 or either
endpoint is out. Every reason names, for each arc crossing the border of the
region it is about, the literal that shut it: `es[e] = 0` if the edge is fixed
out, else `ns[w] = 0` for the outside endpoint (`border_reason`,
`reachable.cc:314–342`). That is sufficient, but not minimal: it is the border
of the whole closure, not a minimum cut. The `border` mutation lane shows only
that the last literal of one rule 6 reason on its fixture is needed.

**Checking a RUP walks the unfolding.** A rule 5, 6 or forcing line is one line,
but VeriPB's propagation reaches up to all `n − 1` levels of the region it is
about, `O(n · (n + |A|))` rows at worst. That is why proof size and checking
time move apart here; see [Proof performance](#proof-performance).

### Rule: edge-selects-endpoints

- **Infers** — `ns[u] = 1` and `ns[w] = 1` for a selected edge `(u, w)`.
- **Fires when** — `es[e]` is fixed to 1 and an endpoint is not yet fixed to 1
  (`reachable.cc:228–232`).
- **Strength** — `partial`: it and rule 2 make the `ns` and `es` of each edge
  consistent with its `sgf` / `sgt` rows; with the other rules of its spelling the
  propagator is `GAC`.
- **Algorithm** — one pass over the edges, `O(|E|)` per call.
- **Why it is true** — `subgraph`: a selected edge has both endpoints selected.
- **Proof technique** — `RUP`, by Theorem 2.6 over a row whose terms are 0/1
  literals: the conclusion is the `sgf<e>` or `sgt<e>` row itself, a clause.
- **Reason** — `es[e] = 1`. Minimal. Unguarded, one literal.
- **Assertion** — `ns[u] = 1 ∨ ¬(es[e] = 1)`. Measured at `Inferences`
  (case `endpoint`):
  ```
  a 1 i[n0][b0] 1 ~i[e0][eq1] >= 1::reachable:((constraint_id _1));
  ```
- **Hint** — `hints::Reachable`: `originator`, the `ConstraintID`.
- **Offline reconstructibility** — `offline`: the clause is an OPB row.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No lane breaks a one-literal reason.

### Rule: unselected-endpoint-drops-edge

- **Infers** — `es[e] = 0` for an undecided edge at an unselected node.
- **Fires when** — `es[e]` is not fixed and an endpoint is fixed to 0
  (`reachable.cc:233–239`).
- **Strength** — `partial`, as rule 1.
- **Algorithm** — as rule 1, the same pass.
- **Why it is true** — the contrapositive of rule 1.
- **Proof technique** — `RUP`, by Theorem 2.6, the same row read the other
  way.
- **Reason** — `ns[w] = 0`. Minimal.
- **Assertion** — `es[e] = 0 ∨ ¬(ns[w] = 0)`. Measured (case `edgeout`):
  ```
  a 1 ~i[e0][b0] 1 ~i[n0][eq0] >= 1::reachable:((constraint_id _1));
  ```
- **Hint** — `hints::Reachable`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: root-not-unselected

- **Infers** — `root ≠ ρ` for a node `ρ` fixed out.
- **Fires when** — `ns[ρ]` is fixed to 0 and `ρ` is in the root's domain
  (`reachable.cc:246–252`).
- **Strength** — `partial`: the root, against `ns` fixed to 0; with the other rules
  of its spelling the propagator is `GAC`.
- **Algorithm** — one walk over the root's domain, at most `n` values.
- **Why it is true** — the root is selected.
- **Proof technique** — `RUP`: `ns[ρ] = 0` falsifies the root flag through
  `rootin<ρ>`, and the flag's reification falsifies `root = ρ` (Theorem 2.6 for
  the reason).
- **Reason** — `ns[ρ] = 0`. Minimal.
- **Assertion** — `root ≠ ρ ∨ ¬(ns[ρ] = 0)`. Measured (case `edgeout`):
  ```
  a 1 ~i[root][eq0] 1 ~i[n0][eq0] >= 1::reachable:((constraint_id _1));
  ```
- **Hint** — `hints::Reachable`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per removed value.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: fixed-root-selected

- **Infers** — `ns[r] = 1` once the root is fixed to `r`.
- **Fires when** — the root is fixed to a node and `ns[r]` is not yet 1
  (`reachable.cc:254–258`).
- **Strength** — `partial`: the root's `ns`, once the root is fixed; with the other
  rules of its spelling the propagator is `GAC`.
- **Algorithm** — `O(1)`.
- **Why it is true** — the root is selected.
- **Proof technique** — `RUP`: `root = r` sets the flag, and `rootin<r>`
  selects `r`.
- **Reason** — `root = r`. Minimal.
- **Assertion** — `ns[r] = 1 ∨ root ≠ r`. Measured (case `rootsel`):
  ```
  a 1 i[n1][b0] 1 ~i[root][eq1] >= 1::reachable:((constraint_id _1));
  ```
- **Hint** — `hints::Reachable`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: root-cannot-reach-selected

- **Infers** — `root ≠ ρ`, for every candidate root `ρ` from which some
  selected node `m` cannot be reached.
- **Fires when** — for each selected node `m`, a backwards search from `m`
  over the residual graph finds the nodes that can reach it; every candidate
  outside that set is removed, all under one reason (`reachable.cc:347–372`).
  Undirected, the set is `m`'s component, so every other selected node in it is
  skipped as already covered; directed, every selected node gets its own search.
- **Strength** — `partial`: with rules 3 and 6, every root value left has a
  support (checked by brute force); a candidate `ρ` survives
  only if it reaches every selected node, and then the union of paths from `ρ`
  supports it. Checked by brute force with the rest; see rule 7.
- **Algorithm** — undirected, one search per component holding a selected node,
  `O(n + |A|)` per call in all; directed, one per selected node,
  `O(|M| · (n + |A|))` for `M` the selected nodes. Plus one walk of the root's
  domain per search.
- **Why it is true** — the root reaches every selected node; a node outside the
  set that can reach `m` cannot.
- **Proof technique** — `RUP`, **no published procedure**. Under `root = ρ`,
  the one-hot row falsifies every other root flag, so every node of the region
  that can reach `m` starts with `reach[·][0]` false (`ρ` is outside it). Every
  arc into the region from outside is shut by a reason literal, directly
  (`es[e] = 0` falsifies the arc flag) or through `sgf` / `sgt` (`ns[w] = 0`
  forces `es[e] = 0`). Arcs inside the region start from a falsified flag. So
  each level's reach flags in the region are falsified from the level below, and
  after `n − 1` rounds `reached<m>` contradicts `ns[m] = 1`. One RUP per removed
  candidate, the same reason each time.
- **Reason** — the border literals of the region that can reach `m`, plus
  `ns[m] = 1`. Independent of `ρ`, which is why one search serves every
  candidate. Not minimal (the whole closure's border, not a minimum cut).
  Unguarded, `O(border)`.
- **Assertion** — `root ≠ ρ ∨ ¬border ∨ ¬(ns[m] = 1)`. Measured (case
  `rootreach`: a path `0–1–2–3` with edge `1–2` fixed out and `ns[0]` selected):
  ```
  a 1 ~i[root][eq2] 1 ~i[e1][eq0] 1 ~i[n0][eq1] >= 1::reachable:((constraint_id _1));
  ```
- **Hint** — `hints::Reachable`.
- **Offline reconstructibility** — `offline`: the clause is RUP against the
  database as it stands; the procedure is plain RUP.
- **Proof size** — one line per removed candidate; checking it propagates up to
  `n − 1` levels of the region.
- **Gaps** — `None.`
- **Tightness** — `reachable_mutation_{undirected,directed}_mandatory` drops
  `ns[m] = 1` from this rule's reason, and VeriPB refuses the first such line
  (line 54 of the fixture's proof, `rup 1 ~i[root][eq6] 1 i[e3][b0] 1 i[e5][b0]
  >= 1` undirected). The `border` lane also corrupts this rule's border, but
  VeriPB stops at an earlier rule 6 line, so this rule's border literal is not
  shown separately.

### Rule: unreachable-node

- **Infers** — `ns[u] = 0` for every live node `u` that no candidate root can
  reach.
- **Fires when** — a forward search from every candidate root at once marks the
  reached nodes; for each unreached live node `v` not yet handled, a backwards
  search from `v` gives the region of nodes that can reach it, and every
  unreached live node in that region is ruled out under one reason
  (`reachable.cc:374–411`).
- **Strength** — `partial`: with rules 1 to 3 and 5, every `ns = 1` and `es = 1`
  left has a support; `ns[v] = 1` is kept exactly when `v` is reachable from a surviving candidate, which
  reaches every selected node, so the union of paths supports it; `es[e] = 1`
  follows through rule 2 once an endpoint is out.
- **Algorithm** — one forward search `O(n + |A|)`, then one backwards search
  per unreached region plus an `O(n)` scan of it. Undirected, the regions are
  components, disjoint, so the searches total `O(n + |A|)` and the scans
  `O(n · regions)`; directed, regions can overlap, `O(n · (n + |A|))` at worst.
- **Why it is true** — `u` can be reached from no candidate root, and every
  selected node must be reached from the root.
- **Proof technique** — `RUP`, **no published procedure**, as rule 5 with the
  roles swapped. Under `ns[u] = 1`, the reason's `root ≠ w` literals falsify the
  root flag of every node `w` in the region, the border literals shut every arc
  into it, and the levels fall as in rule 5 until `reached<u>` contradicts. The
  region of `u` is inside the region of `v`, since whatever reaches `u` reaches
  `v` through it, so `v`'s reason serves every `u` it covers.
- **Reason** — the border literals of the region, plus `root ≠ w` for every node
  `w` in it (per node). The second half is what says none of the region's nodes
  is the root; it is the region's size, not the graph's, which is the point of
  stating it per region (`reachable.cc:382–393`). Not minimal.
- **Assertion** — `ns[u] = 0 ∨ ¬border ∨ ⋁_{w ∈ region} root = w`. Measured
  (case `rootreach`, after rule 5):
  ```
  a 1 ~i[n2][b0] 1 ~i[e1][eq0] 1 i[root][eq2] 1 i[root][eq3] >= 1::reachable:((constraint_id _1));
  ```
- **Hint** — `hints::Reachable`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per ruled-out node.
- **Gaps** — `None.`
- **Tightness** — two lanes, both spellings.
  `reachable_mutation_*_border` drops the last border literal of every reason;
  VeriPB refuses line 33 of the fixture's proof, a rule 6 line
  (`rup 1 ~i[n6][b0] 1 i[root][eq6] >= 1`, its `es[6] = 0` gone).
  `reachable_mutation_*_rootdomain` drops the `root ≠ w` literals; VeriPB
  refuses the same line (`rup 1 ~i[n6][b0] 1 i[e6][b0] >= 1`). The fixture is
  seven free nodes, a path into a triangle with a spur, which the test's comment
  explains was built so that neither a model-pinned literal nor an enumeration's
  solution-exclusion clause can re-supply a dropped one
  (`reachable_test.cc:176–206`).

### Rule: cut-vertex

- **Infers** — `ns[v] = 1`, for a node every remaining solution must use
  (undirected).
- **Fires when** — `with_cut_forcing`, the undirected spelling, at least one
  selected node and one candidate root, and every selected node and candidate in
  one component. One depth-first pass from a selected node computes
  articulation points, bridges, and per subtree the number of selected nodes and
  candidates below it. A live, unselected node `v` is forced if no piece of the
  component left by removing it holds every selected node and a candidate
  (`reachable.cc:541–623`).
- **Strength** — `partial` on `ns`, alone; with rules 1 to 6 and 8 the
  undirected propagator is `GAC`.
  `ns[v] = 0` has a support exactly when the selected nodes lie in one component
  of the residual graph minus `v` that still meets the root's domain, and the
  forcing tests exactly that. Checked by brute force at the root fixpoint
  (`reachcheck.cc`): 10,000 instances up to five nodes (seeds 1 and 2) and 2,000
  up to seven (seed 4), with self loops, parallel edges, constants, fixed values
  and holey roots over `−1..n`; no unsupported value and no missed failure.
  Without the forcing, 365 of the 10,000 five-node instances keep an
  unsupported value, and all 536 such values are `ns = 0` or `es = 0`
  (`out_u_nocuts_s*.txt`). `reachable_test` also checks GAC at every node.
- **Algorithm** — Tarjan's articulation points and bridges in one pass,
  `O(n + |A|)`, plus `O(n + |A|)` per piece holding a candidate for each
  forcing's reason, so `O(p · (n + |A|))` for a cut vertex with `p` such
  pieces, `p ≤ min(deg v, |candidates|)`. Tarjan, *Depth-first
  search and linear graph algorithms*, SIAM J. Comput. 1(2), 1972.
- **Why it is true** — with `v` out, no piece holds every selected node and a
  candidate root, so no solution has `v` out.
- **Proof technique** — two forms, picked by whether the root is fixed.
  - **Root fixed:** `RUP`, **no published procedure**. Under `ns[v] = 0`, the
    reason's `root = ρ` starts the levels at `ρ`; the piece reached from `ρ`
    without `v` is sealed by its border literals and by `ns[v] = 0` itself
    (through `sgf` / `sgt`, then the arc flags), and a selected node `m` outside
    the piece fails `reached<m>`.
  - **Root open:** `RUP sequence` of `c + 1` steps, where `c` is the number of
    candidates other than `v`: one pinned lemma `goal ∨ root ≠ ρ` per
    candidate, each an `extended reason` step (the same RUP as the fixed-root
    form with `root = ρ` pinned), at `ProofLevel::Temporary`; then the
    conclusion by RUP: the lemmas, the reason's `root ≠ σ` for every
    non-candidate node, and `rootin<v>` under `ns[v] = 0` falsify every root
    flag, against `root1ge` (`reachable.cc:479–497`). Unit propagation cannot
    case-split over the root, which is why the lemmas are needed; the design
    note checked that the single RUP is refused with the root open.
- **Reason** — for each piece reached from a candidate without `v` (one per
  piece undirected), its border literals and `ns[m] = 1` for one selected node
  outside it; plus `root = ρ` when the root is fixed, or `root ≠ σ` for every
  non-candidate node when it is open. Not minimal, and not deduplicated
  across pieces: `border_reason` deduplicates within one border, but an edge
  fixed out between two pieces is named by both (`reachable.cc:452–472`).
  Its length is at most `|A|` border literals, since each arc leaves at most
  one piece, plus one `ns[m] = 1` per piece and at most `n − 1` root literals:
  `O(n + |E|)`, not `O(n)`.
- **Assertion** — `ns[v] = 1 ∨ ¬reason`, in both forms. Measured: root fixed to
  0 on a path `0–1–2`, `ns[2]` selected (case `cutfixed`):
  ```
  a 1 i[n1][b0] 1 ~i[n2][eq1] 1 ~i[root][eq0] >= 1::reachable:((constraint_id _1));
  ```
  root open over `0..2`, `ns[0]` and `ns[2]` selected (case `cutopen`):
  ```
  a 1 i[n1][b0] 1 ~i[n2][eq1] 1 ~i[n0][eq1] >= 1::reachable:((constraint_id _1));
  ```
  and at `Off`, the open form's two pinned lemmas and conclusion:
  ```
  rup 1 i[n1][b0] 1 ~i[root][eq0] 1 ~i[n2][eq1] 1 ~i[n0][eq1] >= 1;
  rup 1 i[n1][b0] 1 ~i[root][eq2] 1 ~i[n2][eq1] 1 ~i[n0][eq1] >= 1;
  rup 1 i[n1][b0] 1 ~i[n2][eq1] 1 ~i[n0][eq1] >= 1;
  del range -3 -1;
  ```
- **Hint** — `hints::Reachable`. The same for both forms.
- **Offline reconstructibility** — `offline`, in both forms. Root fixed, the
  clause is RUP. Root open, it often is not, but one procedure, fixed by the
  family and needing nothing chosen, always derives it from the baseline
  context: for every node `u`, derive `C ∨ ¬x[id][u][root]` by RUP, where `C` is
  the asserted clause; then derive `C` by RUP against `root1ge`. The flags and
  the row are in the `.opb`, under the constraint ID the hint carries. The
  procedure needs no knowledge of the root's domain, of the pieces, or of which
  rule fired.

  Each per-root RUP is guaranteed, from the rows and what the reason contains.
  Assume `¬C`, so the reason holds and `ns[v] = 0`. A node no longer in the
  root's domain has `root ≠ u` in the reason (`reachable.cc:488–490`), which
  falsifies `x[id][u][root]` through its reifying row. For `u = v`,
  `rootin<v>` does. For a candidate `ρ`, `root1le` falsifies every other root
  flag. The reason holds the border of the piece `ρ` reaches without `v`, and
  `ns[m] = 1` for a selected `m` outside it: the code adds both for every
  candidate's piece (`reachable.cc:452–472`). Such an `m` exists because the
  forcing fires only when no candidate's piece holds every selected node,
  which is also what makes it sound. `ns[v] = 0` falsifies every edge at `v`
  through `sgf` and `sgt`. So every arc leaving the piece is false at every
  level, and no node outside it is ever reached. `reached<m>` then conflicts.
  That per-root RUP is the solver's own pinned lemma `C ∨ root ≠ ρ`, with the
  flag in place of the value literal. Once every flag is false, `root1ge`
  conflicts, which gives the closing step.

  Checked by replay (`tmp/fd-graph/codex/reachable/replay/`). 2,300 random
  models, up to eight nodes, both spellings, holey open roots and forcing on,
  were enumerated at `Off`, up to 300 solutions each. In 635 of them the
  solver's proof holds open-root forcings: 5,856 in all, 254 of rule 7, 4,556
  of rule 8, 157 of rule 9 and 889 of rule 10, 68 of them with a single
  pinned lemma. Each was replaced by this procedure in a proof that keeps only
  the `.opb` and the proof's own literal definitions (its `red` lines), with
  each forcing's lines deleted before the next. All 635 proofs verify. As a
  control, the closing RUP alone is refused in 253 of the 635. A fact-check's
  adversarial replay (`tmp/fd-graph/codex/fc/adv/`) adds 8,000 models with
  aliased, constant and negated-view `ns` and `es`, offset and negated root
  views, self loops and parallel edges. Its 9,507 open-root forcings, in 775
  models, all verify the same way. The `n` per-root lines are sufficient, not
  minimal. The closing step needs no line for the candidates of one piece,
  because nothing outside a sealed piece is reached whichever of its nodes is
  the root. On the third forcing of the replay's fixture `t1off`, with pieces
  `{0, 1}` and `{3, 4}`, dropping the lines for nodes 0 and 3 is refused
  (`t1off.mut_block3_drop0and3.pbp`).

  The cost is `n` RUP lines of `|C| + 1` literals and a closing line of `|C|`,
  and each check propagates over up to `O(n(n + |A|))` rows. The solver's own
  derivation is `c + 1` lines. The same procedure also succeeds on rules 1 to
  6 and the fixed-root forms, because adding a hypothesis to a RUP leaves it
  RUP. A subhint saying "plain RUP" or "split" would only save lines; it adds
  no information.
- **Proof size** — root fixed, one line of `O(n + |E|)` literals. Root open,
  `c + 1` lines and a `del range`, `c` the number of candidates other than `v`,
  shrinking as search narrows the root. Every lemma repeats the whole reason,
  so a forcing writes `(c + 1)(|reason| + 2)` literal occurrences at most,
  where each lemma needs only its own piece's border (#1312). That is
  `O(c · (n + |E|))`, and so cubic in the nodes on a dense graph with `c`
  near `n`. One family shows it. Take odd `n`: a centre adjacent to every
  node, between two cliques of `(n − 1)/2`. Keep the complete graph's edge
  list, with every cross-clique edge a singleton variable fixed to 0. Select
  one node in each clique and leave the root open over every node. The root
  propagation forces the centre with `c = n − 1` lemmas, and each clique's
  border is the `((n − 1)/2)²` cross edges, named once per piece:

  | `n` | lemmas | closing clause literals (distinct) | occurrences, lemmas and closing |
  |--:|--:|--:|--:|
  | 9 | 8 | 35 (19) | 323 |
  | 17 | 16 | 131 (67) | 2,243 |
  | 33 | 32 | 515 (259) | 17,027 |

  *`86caad24`, fataepyc-10, 2026-10-09 (`tmp/fd-graph/codex/reachable/family/`;
  each proof verifies).* The occurrences grow 7.6 times per doubling at the
  top, close to cubic. On `hitori` `h5-1`, 18 forcings write 364 pinned
  lemmas, 19 to 22 apiece; on `h11-1`, 2,396 forcings write 212,458, about 89
  apiece at 152 literals each ([Proof performance](#proof-performance)).
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No lane corrupts a forcing; the `border` lane's
  corruption applies here too, but VeriPB stops at an earlier rule 6 line.

### Rule: bridge

- **Infers** — `es[e] = 1`, for an undecided edge every remaining solution must
  use (undirected).
- **Fires when** — as rule 7, from the same pass: an undecided bridge of the
  component whose removal leaves neither side holding every selected node and a
  candidate (`reachable.cc:625–633`).
- **Strength** — `partial` on `es`, alone; with rule 7 it completes the
  undirected propagator's `GAC`: `es[e] = 0` has a support exactly
  when the selected nodes lie in one component of the residual graph minus `e`
  that meets the root's domain. Checked with rule 7. Parallel edges are handled
  (the pass skips only the one copy it entered by), so a doubled edge is never a
  bridge.
- **Algorithm** — as rule 7.
- **Why it is true** — as rule 7, for an edge.
- **Proof technique** — as rule 7, both forms, with `es[e] = 0` as the
  hypothesis: it falsifies the arc flags directly. No candidate is exempted from
  the pinned lemmas, since removing an edge rules out no root.
- **Reason** — as rule 7, with at most two pieces, one per side of the
  bridge. `e` itself is never named: the arc an undecided hypothesis stops is
  left to the negated goal (`reachable.cc:324–337`).
- **Assertion** — `es[e] = 1 ∨ ¬reason`. Measured (case `cutfixed`):
  ```
  a 1 i[e1][b0] 1 ~i[n2][eq1] 1 ~i[root][eq0] >= 1::reachable:((constraint_id _1));
  ```
- **Hint** — `hints::Reachable`.
- **Offline reconstructibility** — `offline`, in both forms, by rule 7's
  procedure, checked separately for this rule. The per-root argument changes in
  two places. There is no `v`, so every node is either a candidate or a
  non-candidate. `es[e] = 0`, from `¬C`, falsifies `e`'s arc flags directly.
  A candidate's piece is its side of the bridge, sealed by its border and by
  `e`. In the replay above, all 4,556 open-root bridge forcings verify.
- **Proof size** — root fixed, one line of `O(n + |E|)` literals. Root open,
  as rule 7, with `c` counting every candidate, since none is exempted. There
  are at most two pieces, so the reason has at most `|A|` border literals, two
  `ns[m] = 1`, and `n − c` root literals. A forcing writes `O(c · (n + |E|))`
  literal occurrences.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: directed-node-forcing

- **Infers** — `ns[v] = 1`, for a node every remaining solution must use
  (directed).
- **Fires when** — `with_cut_forcing`, the directed spelling, at least one
  selected node and one candidate. For every live, unselected node `v`, the
  propagator removes `v` hypothetically and runs a forward search from each
  candidate root in turn, stopping at the first one that still reaches every
  selected node; if none does, `v` is forced (`reachable.cc:500–529`).
- **Strength** — `partial` on `ns`, alone; with rules 1 to 6 and 10 the
  directed propagator is `GAC`.
  Checked by brute force with rule 7's sweep (10,000 instances up to five nodes,
  2,000 up to seven, directed): no unsupported value. The analogue of a cut
  vertex is a dominator, but the root is existentially quantified and the
  selected node it dominates may differ from one candidate to the next, so no
  single dominator tree answers it; the design note explains why a super-root
  does not work. This asks the question directly.
- **Algorithm** — up to `|candidates|` searches per live unselected node,
  `O(n · |candidates| · (n + |A|))` per call, **whether or not anything is
  forced**; with a fixed root, `O(n · (n + |A|))`. Each forcing then builds its
  reason with one search per candidate, `O(|candidates| · (n + |A|))`. The
  design note's per-node question has a near-linear-per-candidate answer it
  does not use: a dominator tree per candidate (Lengauer and Tarjan, *A fast
  algorithm for finding dominators in a flowgraph*, TOPLAS 1(1), 1979,
  `O(|A| · α(|A|, n))`) gives, for each candidate, every node on all of its
  paths to some selected node, in one pass. Measured in [CPU
  performance](#cpu-performance).
- **Why it is true** — with `v` out, no candidate root reaches every selected
  node.
- **Proof technique** — as rule 7, both forms; the reason gets one border per
  candidate rather than per piece, since candidates inside one piece reach
  different parts of it.
- **Reason** — per candidate, the border of what it reaches without `v` and
  `ns[m] = 1` for one selected node it misses; plus the root literals as in
  rule 7. **Duplicated literals.** Each candidate's border is appended whole,
  with no sharing between candidates in the directed spelling
  (`reachable.cc:452–472`). So a literal is named once for every candidate
  whose reached set it seals, and two candidates missing the same `m` both
  push `ns[m] = 1`. Nothing deduplicates. Measured (case `dforce`, below),
  where `~i[n2][eq1]` appears twice. The checker accepts the duplicates, but
  they are what makes the reason long: at most `c(|E| + 1) + n` literals for
  `c` candidates, where its distinct literals number `O(n + |E|)`.
- **Assertion** — `ns[v] = 1 ∨ ¬reason`. Measured: arcs `0→1`, `1→2`, `3→1`,
  root over `{0, 3}`, `ns[2]` selected:
  ```
  a 1 i[n1][b0] 1 ~i[n2][eq1] 1 ~i[n2][eq1] 1 i[root][eq1] 1 i[root][eq2] >= 1::reachable:((constraint_id _2));
  ```
  (`_1` is the `In` that gives the root its holey domain.)
- **Hint** — `hints::Reachable`.
- **Offline reconstructibility** — `offline`, in both forms, by rule 7's
  procedure, checked separately for this rule. The per-root argument for a
  candidate `ρ` uses `ρ`'s own border and the `m` it misses, which the reason
  carries for every candidate. `ns[v] = 0` seals `v` as in rule 7. In the
  replay above, all 157 open-root directed node forcings verify.
- **Proof size** — root fixed, one line, with one candidate's border:
  `O(n + |E|)` literals. Root open, `c + 1` lines, each carrying the whole
  reason, so `(c + 1)(|reason| + 2)` literal occurrences, which is
  `O(c² · (|E| + 1) + c · n)`. That is quartic in the nodes on a dense digraph
  with `c` near `n`. In rule 7's family with both orientations of every edge,
  each candidate's border is the `((n − 1)/2)²` arcs into the other clique:

  | `n` | lemmas | closing clause literals (distinct) | occurrences, lemmas and closing |
  |--:|--:|--:|--:|
  | 9 | 8 | 137 (35) | 1,241 |
  | 17 | 16 | 1,041 (131) | 17,713 |
  | 33 | 32 | 8,225 (515) | 271,457 |

  *Same build and probe; each proof verifies.* The occurrences grow 15.3 times
  per doubling at the top, close to quartic. Two changes would each remove one
  factor of `c`. Deduplicating the reason makes it `O(n + |E|)`. Narrowing
  each lemma to its own candidate's border, which #1312 tracks, makes a lemma
  `O(n + |E|)` long.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: directed-edge-forcing

- **Infers** — `es[e] = 1`, for an undecided edge every remaining solution must
  use (directed).
- **Fires when** — as rule 9, for every undecided edge, with the edge removed
  hypothetically (`reachable.cc:531–533`).
- **Strength** — `partial` on `es`, alone; with rule 9 it completes the
  directed propagator's `GAC`; checked with it.
- **Algorithm** — as rule 9, `O(|E| · |candidates| · (n + |A|))` per call, and
  the same reason cost per forcing.
- **Why it is true** — as rule 9, for an edge.
- **Proof technique** — as rule 9, with `es[e] = 0` as the hypothesis.
- **Reason** — as rule 9.
- **Assertion** — `es[e] = 1 ∨ ¬reason`. Measured (case `dforce`):
  ```
  a 1 i[e1][b0] 1 ~i[n2][eq1] 1 ~i[n2][eq1] 1 i[root][eq1] 1 i[root][eq2] >= 1::reachable:((constraint_id _2));
  ```
- **Hint** — `hints::Reachable`.
- **Offline reconstructibility** — `offline`, in both forms, by rule 7's
  procedure, checked separately for this rule. As rule 9, with `es[e] = 0`
  falsifying `e`'s arc flag in place of `ns[v] = 0`. There is no `v`, so every
  node is a candidate or a non-candidate. In the replay above, all 889
  open-root directed edge forcings verify.
- **Proof size** — as rule 9, with `c` counting every candidate.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

- **`reachable_test`** (`reachable_constraint`, `gcs/CMakeLists.txt:1109`):
  twelve shapes per spelling (one node; a path; a triangle; a square; two
  pieces; a lollipop; a fixed root on a path and on a bowtie; nodes pinned in
  and out; a root over `−1..4`; edges pinned), all under
  `solve_for_tests_checking_gac`, so **GAC at every search node**, plus one
  aliased run (`dup`, two nodes sharing a variable) under plain
  `solve_for_tests`. With and without proofs; VeriPB runs when on the path. At
  most five nodes and 46 solutions. Seeded (`--seed`).
- **Mutation lanes** (`gcs/CMakeLists.txt:1130–1145`), each run against
  `reachable_test --mutate=…` on a seven-node fixture, both spellings:
  `reachable_mutation_{undirected,directed}_{border,mandatory,rootdomain}` under
  `run_test_and_expect_verify_failure.bash`, and the control
  `reachable_mutation_*_none` under `run_test_and_verify.bash`. The corruptions
  are `mutations.hh`'s: `DropBorderLiteral` (the last border literal of every
  reason), `DropMandatoryNode` (`ns[m] = 1` from rule 5's reason) and
  `DropRootDomain` (the `root ≠ w` literals from rule 6's). Run from this audit's
  scratch directory: the six corrupted proofs are refused, `border` and
  `rootdomain` at a rule 6 line and `mandatory` at a rule 5 line, and the two
  controls verify complete enumerations of 263 (undirected) and 52 (directed)
  solutions (`tmp/fd-graph/reachable/tests/`).
- **`scp_reader_test`**: `reachable` and `dreachable` enumerate correctly from
  `.scp`, and a model with both survives write, read, write unchanged.
- **MiniZinc** (`minizinc/CMakeLists.txt:186–200`): `reachabletest` (nodes
  indexed from 2), `connectedtest`, `dreachabletest`, `dconnectedtest`, each
  enumerated against the default solver with proofs, with `--fzn-pattern
  glasgow_reachable` or `glasgow_dreachable` so a lane cannot pass on the
  stdlib decomposition.
- **`examples/hitori`**: `hitori-propagator` and `hitori-propagator-no-cuts`
  solve the size-4 generated instance with proofs and verify them; the only
  lanes where the propagator meets an instance-sized graph with an open root.
- **Audit lane:** the two `NoWidePosition` rows above, which are registered as
  a test only when the guard is on, and no CI lane turns it on (#920).

**Runtime caps.** No lane sets or clears one. The default caps (300 solutions,
1,500 recursions) **do not fire**: `reachable_test --seed=1` with them set runs
all 52 cases, none truncated, the largest 46 solutions, and 26 proofs verify, in
0.45 s (`tests/capped.txt`). So the capped run checks everything the uncapped
one does.

**This audit's own checks**, beyond the suite:

- root-fixpoint GAC by brute force, both spellings, forcing on and off, and
  aliased (`strength/reachcheck.cc`; [rule 7](#rule-cut-vertex));
- 2,500 random instances solved to complete enumeration **with proofs**, both
  spellings, forcing on and off, aliased, up to six nodes: every solution count
  matches brute force and every proof verifies (`proofsweep/proofsweep.cc`,
  seeds 11 to 18);
- one fixture per rule at `Off` and `Inferences`, all verifying at `Off`
  (`rules/rules.cc`);
- views and wide roots (`views/views.cc`), and the MiniZinc differential checks
  above.

**What the tests do not cover.**

- **Graphs larger than five nodes, under the GAC check.** The suite's GAC check
  sees twelve hand-built shapes; this audit's sweeps go to seven nodes at the
  root fixpoint only, with at most seven edges at seven nodes, and 20–28% of
  their instances fail at the root and so test soundness only. The fact-check's
  denser re-runs (seven nodes with up to 14 edges, and eight nodes with up to
  13) found no unsupported value either.
- **The directed forcing at scale.** `hitori` is undirected, and no corpus
  model posts `dreachable` or `dconnected`; PR #784 said its behaviour at scale
  was "genuinely unexercised", and it still is in the suite.
- **The forcing rules' tightness.** No lane corrupts a forcing reason, and the
  `border` lane stops at a rule 6 line before reaching one. Rules 1 to 4 have
  one-literal reasons and no lane.
- **`with_cut_forcing(false)` in a unit lane.** Only `hitori-propagator-no-cuts`
  runs it.
- **Views, wide or holey roots, an empty node set, aliased edges,** in the suite.
  The audit's probes cover views and roots; the fact-check's cover aliased
  edges (see [Robustness](#robustness-and-limits)); the empty node set throws.
- **MiniZinc's int spelling and enum-typed nodes.** The four MiniZinc lanes use
  the array spelling with integer indices; this audit's differential models
  cover the rest.
- **Real instances:** none ported; `hitori` `h5-1` and `h11-1` are the design
  note's benchmarks, not tests.

### Benchmarks and examples

- **In the repository:** `examples/hitori`, whose `--connectivity` switch posts
  the same requirement four ways: `decomposition` (the stdlib's labelling, the
  default), `propagator`, `propagator-no-cuts`, and `none` (a relaxation that
  solves a different problem, kept as the proof-attribution floor).
- **Corpus:** two MiniZinc Challenge models reach the family. `hitori` 2025
  posts one `connected` over an `n × n` grid (`h5-1`, `h11-1`, `h14-1`, `h15-1`,
  `h20-2`); `surface-based-tsp` 2026 posts `tree`, so it reaches `Reachable` as
  `Tree`'s child. None posts `reachable`, `dreachable` or `dconnected`
  directly, and none is directed.
- **For CPU:** `hitori` `h11-1` (121 nodes, 220 edges), which solves in a
  quarter of a second and has enough search to separate the two forcing
  settings; `h14-1` and up for a fixed-time node rate. For the directed
  forcing, `gridprobe.cc` on a 20 × 20 grid, or `hitori` with `dconnected`
  (`hitori_d.mzn`, below).
- **For proof verification:** `hitori` `h5-1`, which verifies in 0.14 s.
  `h11-1` writes 673 MB with the forcing and verifies in 23 to 31 minutes;
  nothing larger was run with proofs in this audit, and since the encoding
  grows as `Θ(n(n + |E|))` and the lemma count with the search, larger instances
  should not be run with proofs uncapped. `--connectivity none` at `h11-1`
  writes 9.65 GB (the design note's figure; not re-run).

### CPU performance

*Release build of `86caad24` (GCC 15.2.0, `-O3 -march=native`); fataepyc-10,
one pinned core, fixed malloc thresholds; 2026-10-09. Other audits were running
on other cores throughout, so walls carry some noise; the instruction counts
(`instructions:u`) do not. Proofs off.*

**`hitori`, the one corpus model measured.** `examples/hitori --dzn`, which posts the
Challenge model's `connected` through this propagator with its forcing on
(`propagator`) or off (`propagator-no-cuts`), with the model's own branching.
Wall is the median of three for the forcing settings on `h5-1` and `h11-1`, and
one run, capped at 300 s, for the rest (`tmp/fd-graph/reachable/cpu/`).

| instance | nodes, edges | setting | recursions | propagations[0] | wall | instructions |
|---|---|---|--:|--:|--:|--:|
| `h5-1` | 25, 40 | `propagator` | 24 | 472 | 0.0014 s | 11.4 M |
| `h5-1` | | `propagator-no-cuts` | 38 | 615 | 0.0015 s | 11.9 M |
| `h5-1` | | `decomposition` | 113,671 | — | 3.24 s | 20.9 G |
| `h11-1` | 121, 220 | `propagator` | 1,932 | 44,797 | 0.257 s | 1.21 G |
| `h11-1` | | `propagator-no-cuts` | 4,920 | 94,564 | 0.371 s | 1.63 G |
| `h14-1` | 196, 364 | `propagator` | 1,674,809 | 37,764,865 | > 300 s | 1,390 G |
| `h14-1` | | `propagator-no-cuts` | 2,199,298 | 56,056,030 | > 300 s | 1,315 G |
| `h15-1` | 225, 420 | `propagator` | 197,899 | 4,956,715 | **51.4 s, optimal** | 239 G |
| `h15-1` | | `propagator-no-cuts` | 2,018,456 | 42,602,867 | > 300 s | 1,287 G |
| `h20-2` | 400, 760 | `propagator` | 594,061 | 13,937,570 | > 300 s | 1,386 G |
| `h20-2` | | `propagator-no-cuts` | 1,407,319 | 21,547,082 | > 300 s | 1,299 G |

The forcing is a straight win with proofs off: 2.5 times fewer nodes on
`h11-1` at 1.9 times the instructions per node, 0.74 times the total, and on `h15-1` the difference
between proving the optimum in 51 s and not finishing in 300. Where both time
out, nodes per second are not comparable, since the two searches differ. The
`decomposition` row is the stdlib's distance labelling in the same binary, the
design note's comparison; it is not this family. On `h11-1` a profile of the
`propagator` run puts about half the samples in the propagator's own code and
another fifth in `State::optional_single_value`, which its `fixed_to` helper
calls per node and per edge in every pass (`perf record`, one run): hotspot
context, not a saving.

**Against other solvers, on the same MiniZinc model.** Not identical trees,
and not the same strength: Chuffed binds `connected` to its own native
propagator (`chuffed_connected`) and learns clauses; Gecode runs the stdlib's
distance labelling. `fzn-glasgow` with the shipped `mznlib` reaches this
propagator.

| `hitori`, MiniZinc 2.9.7, `-a` | `h5-1` nodes | `h5-1` time | `h11-1` nodes | `h11-1` time |
|---|--:|--:|--:|--:|
| `fzn-glasgow` (this family) | 24 | 0.001 s | 1,932 | 0.30 s |
| Chuffed 0.13.2 (native `connected`, LCG) | 6 | 0.003 s | 277 | 0.020 s |
| Gecode 6.3.0 (stdlib decomposition) | 1,559,963 | 9.62 s | 5,287,841 | > 300 s |

**The directed spelling costs more per call, on the same tree.**
`hitori_d.mzn` replaces `connected` with `dconnected` over both arcs of every
adjacency, the second array defined as `hitori`'s edges are. MiniZinc merges
the two identically defined arrays, so the two arcs of each adjacency share one
edge variable (440 positions over 220 variables): an aliased `es`, under which
consistency is not claimed. The directed reachability problem is still the
undirected one. `fzn-glasgow` explores the
identical 24 and 1,932 nodes (node and failure counts equal; the trees were not
compared beyond that). On `h11-1` the directed run takes 2.30 s and 15.2 G
instructions against 0.30 s and 1.46 G, 10.4 times the instructions; on `h14-1`
in 120 s it reaches 56,751 nodes against 523,128.

Per call, alone on a grid (`gridprobe.cc`: all variables free, random order
over `ns` with seed 1, then the root, then `es`; 200 solutions; median of three;
the constraint is the model's only one, so propagations are its calls):

| grid | spelling | forcing | root | calls | µs per call | instructions per call |
|---|---|---|---|--:|--:|--:|
| 6 × 6 | undirected | on | open | 519 | 14 | 71 K |
| 6 × 6 | directed | on | open | 471 | 25 | 145 K |
| 10 × 10 | undirected | on | open | 559 | 39 | 187 K |
| 10 × 10 | directed | on | open | 616 | 145 | 1.06 M |
| 14 × 14 | undirected | on | open | 739 | 77 | 358 K |
| 14 × 14 | directed | on | open | 860 | 649 | 5.00 M |
| 20 × 20 | undirected | on | open | 1,084 | 164 | 723 K |
| 20 × 20 | undirected | off | open | 1,167 | 110 | 444 K |
| 20 × 20 | directed | on | open | 1,324 | 3,277 | 25.5 M |
| 20 × 20 | directed | on | fixed | 1,359 | 3,516 | 26.6 M |
| 20 × 20 | directed | off | open | 1,358 | 606 | 4.08 M |
| 20 × 20 | directed | off | fixed | 1,798 | 879 | 5.82 M |

The undirected spelling's cost per call roughly doubles as the node count
doubles, as one Tarjan pass and a few searches should. The directed forcing's
grows faster, 4.5 and then 5.0 times per doubling, and a fixed root does not
help: it is the search per node
and per edge of rules 9 and 10, `O((n + |A|)²)` even with one candidate. Without
the forcing the directed spelling is still super-linear, through rule 5's
backwards search per selected node. #1316 proposes one dominator
tree per candidate root.

**What these do not exercise.** `hitori` is undirected and decides the root
last, so it says nothing about the directed rules, and its forcings are nearly
all open-root ones; no corpus model reaches rules 9 and 10 at all. The grid
probe's search is an enumeration chosen to make the propagator the only cost,
not a model anyone solves.

### Proof performance

*Release build of `86caad24`, fataepyc-10, 2026-10-09; VeriPB 3.0.2 with
`--force-checked-deletion`, one pinned core. Sizes are exact. The `h5-1` and
grid check times were re-taken on a quiet machine, twice each, and agree to
0.01 s (`tmp/fd-graph/reachable/grid/quiet_times.log`; the fact-check's
independent solo runs, `tmp/fd-graph/factcheck2/reachable/gridtimes/`, are
within 2%); the first, loaded, grid figures were up to 40% higher. The `h11-1`
check times are two runs each under different and uneven loads, and differ
from each other by up to 34%; see the note under their table for which
comparisons they support.*

**`hitori` `h5-1`**, through `examples/hitori`, at `Off` (fully justified) and
`Inferences` (`GCS_ASSERTION_LEVEL=inferences`): the `.opb` is 649,792 bytes and
6,117 rows either way, of which the unfolding is most (`proof/`).

| setting | level | `.pbp` lines | `.pbp` bytes | open-root forcings | pinned lemmas | `reachable` assertions | all assertions | VeriPB |
|---|---|--:|--:|--:|--:|--:|--:|--:|
| `propagator` | `Off` | 1,679 | 234,390 | 18 | 364 | — | — | 0.14 s |
| `propagator` | `Inferences` | 283 | 35,609 | — | — | 58 | 242 | 0.01 s |
| `propagator-no-cuts` | `Off` | 1,749 | 108,001 | 0 | 0 | — | — | 0.08 s |
| `propagator-no-cuts` | `Inferences` | 576 | 73,388 | — | — | 201 | 493 | 0.01 s |

The open-root forcing's pinned lemmas are 364 of the default proof's 1,679
lines and 70% of its bytes, 22.5 literals each, which is why it is 2.2 times
the no-cuts proof's bytes on fewer lines. Narrowed to its own piece (#1312)
the proof is 177,805 bytes, still 1.65 times the no-cuts one, with the lemmas
61% of it. At `Inferences` the family's assertions
are 24% (forcing on) and 41% (off) of all assertions; the rest are the other
constraints' and backtracking. The decomposition writes 566,058,724 bytes and
9,085,583 lines on the same instance and checks in 910 s in one loaded run
(883 s in the fact-check's; the design note
measured 815 MB and 796 s at PR time; that figure is from an earlier tree and
should not be set beside this one).

**`hitori` `h11-1`, the one instance that shows the cost.** Same `.opb` for
both settings, 16,353,478 bytes and 141,505 rows.

| setting | `.pbp` lines | `.pbp` bytes | forcings | pinned lemmas (bytes) | VeriPB |
|---|--:|--:|--:|--:|--:|
| `propagator` | 289,750 | 672,571,799 | 2,396 | 212,458 (648,955,686) | 1,385 s / 1,856 s |
| `propagator-no-cuts` | 285,633 | 79,647,987 | 0 | 0 | 638 s / 621 s |
| `propagator`, narrower lemmas (experiment) | 289,750 | 514,191,979 | 2,396 | 212,458 | 1,418 s / 1,893 s |

The first figure of each pair is from runs one after another while other
audits ran on other cores. The second is from the three runs at once on
logical CPUs 100–102 of an otherwise quiet machine, which are SMT siblings
sharing L3 and memory, with the files on NFS (`tmp/fd-graph/reachable/idle/`).
The contention there was uneven: the no-cuts check had two neighbours
throughout, the other two only for its first 621 s. So the one clean
comparison in the second set is the default against the narrowed proof, which
ran side by side for the same time.

**96.5% of the default proof's bytes are pinned lemmas**, about 89 per forcing,
each carrying on average 152 literals. Of those, 32 are `root ≠ σ` literals
for non-candidates, which only the closing step needs, about 11 are other
pieces' borders, which the lemma does not need either, and the remaining ~109
are the lemma's own piece's border and its goal, which it does. So **the cost is
the number of lemmas times the size of one piece's border**. The line counts of
the two settings are within 1.5% of each other: the forcing saves 2,988 search
nodes' worth of lines and spends them on lemmas. The third row is an
experiment build (`tmp/fd-graph/reachable/src-lemma`, the diff in
`lemma-exp/narrow-lemma.diff`) in which each pinned lemma carries only its own
piece's border and the selected node that piece misses: the same search and
the same lines, 23.5% fewer bytes (24% on `h5-1`; the 1,100 random instances
of the proof sweep verify under it too), and the lemmas still 95.4% of the
bytes at 109 literals each. It verifies, and is not measurably faster to
check: 2.0% slower in the clean pair, and 2.4% in the first set, against
run-to-run differences of up to 34% between the sets, so the saving is disk and
nothing shown about time. Per line, the forcing setting's lines take longer to
check than the no-cuts setting's: 2.1 times as long on average in the first
set (2.9 in the second, where the uneven contention makes it unreliable).
Removing a quarter of the lemmas' length did not make them measurably faster,
but they are still far longer than the no-cuts proof's lines (about 2,309 bytes
against 279 on average), so length is not ruled out; why, this audit did not
establish. Filed as #1312.

**The encoding taxes every line, the family's or not.** `gridprobe.cc`
enumerating 300 solutions of `Reachable` alone on a `k × k` grid, root fixed,
so the proof is about 3,500 lines at every size and most of them are solution
and backtracking lines, not this family's (`grid/gp/`):

| grid | `.opb` rows | `Off` lines | `Off` VeriPB | `Inferences` VeriPB | `reachable` assertions |
|---|--:|--:|--:|--:|--:|
| 3 × 3 | 651 | 3,851 | 0.06 s | 0.04 s | 504 |
| 4 × 4 | 2,142 | 3,713 | 0.20 s | 0.12 s | 357 |
| 5 × 5 | 5,391 | 3,646 | 0.48 s | 0.29 s | 269 |
| 6 × 6 | 11,430 | 3,773 | 1.18 s | 0.62 s | 352 |
| 8 × 8 | 37,206 | 3,534 | 3.20 s | 2.11 s | 131 |

Check time grows with the encoding at a near-constant line count, 53 times
over a 57-fold growth in rows, and **asserting every one of this family's
inferences removes only a third of it at 8 × 8**: the solution and
backtracking lines are checked against the same rows. That is the shape the
design note measured as "DB tax" on `h11-1` (`none` against the propagator), and
it is why this family's own line count says little about its checking cost.
The directed spelling and the open root give the same picture
(the proofs are in `grid/gp/`; at 8 × 8, `Off`, quiet: 3.20 s undirected and
3.31 s directed with the root fixed, 4.55 s and 4.62 s open).

**Assertion levels.** At `Definitions` and `Links` every rule fixture
(`rules.cc`: `endpoint`, `rootreach`, `cutopen`, `dforce`, `conflict`) is
accepted under assertions. `hitori` `h5-1` is accepted at `Definitions` and
fails at `Links` on a `soli` step after an objective improvement, which is the
generic failure other families' documents report, not this family's.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified at `Off`, every assertion carries its
reason, and the propagator is the same with proofs on or off: the forcing's
switch is the caller's, not the proof logger's.

The one proof-side defect is a cost, not a gap: the open-root forcing's pinned
lemmas, a line per candidate root, each carrying the whole reason (#1312), on
a database of `Θ(n(n + |E|))` rows. It is a label-groups candidate in
[`proof-benchmarks.md`](../proof-benchmarks.md).

The SCC propagator's bare unit assertions at the assertion levels, which the
[`circuit`](circuit.md) document records as deliberately unfiled, have no
counterpart here: every `reachable` assertion carries its reason.

### Known limitations

- **Its proofs are slow to check on large graphs**, because every proof line is
  checked against an encoding of `Θ(nodes × (nodes + edges))` rows: 136,395
  rows for an 11-by-11 grid.
- **A forcing made before search has decided the root costs a proof line per
  candidate root.** `connected` leaves the root open; on `hitori` that makes the
  default proof several times the size of the no-cuts one.
- **The directed spelling's forcing gets expensive on large graphs**, even when
  it forces nothing; `with_cut_forcing(false)` turns it off at the cost of GAC.
- **A model with no nodes is an error, not unsatisfiable**, through the C++ API,
  the `.scp` reader, and MiniZinc's int spelling.
- **Repeating a variable among the nodes loses propagation**, including failure
  at the root; the solutions are still right.

### Next steps

1. **Make an empty node set unsatisfiable rather than an error.** In
   `prepare()`, or by guarding the two int overrides. Small. Buys a correct
   answer from MiniZinc's int spelling, the C++ API and the `.scp` reader, where
   today the first is `=====ERROR=====`; `Tree`'s and `Path`'s int spellings have
   the same defect (and `Path` needs its own fix, throwing before its child is
   installed). A `then false` guard in the int overrides would do for
   MiniZinc; copying `dag`'s and `subgraph`'s `then true` guard into the rooted
   `_enum` overrides would turn their accidental-but-right UNSAT into a wrong
   SAT. Filed as #1305, with `tree` and `path`.
2. **Narrow the pinned lemmas' reasons.** Each open-root lemma needs only its
   own piece's border and the selected node that piece misses; the non-candidate
   root literals and the other pieces' borders are needed by the closing step
   alone. Small, and built: the experiment cuts `h11-1`'s proof by 23.5% and
   `h5-1`'s by 24% with the same lines and search, and verifies everywhere it
   was tried. It does not change the number of lines, and the lemmas stay 95%
   of `h11-1`'s bytes, since most of each is its own piece's border. It buys
   disk; no check-time saving was measurable (2% slower in both of two pairs
   of runs, within their noise). The directed forcing has more to gain. Its
   reason repeats a border per candidate, so a forcing writes
   `O(c² · (|E| + 1) + c · n)` literal occurrences, quartic on a dense digraph
   (see [rule 9](#rule-directed-node-forcing)). Narrowing each lemma to its own
   candidate's border removes one factor of `c`. Filed as #1312, which covers
   the narrowing only. Deduplicating the reason would also shorten the
   closing line; that is not part of #1312, and is not filed (item 7).
3. **One dominator tree per candidate root for the directed forcing.** Exact,
   and near-linear per candidate: `O(|candidates| · (n + |E|))` per call (up to
   a factor `α`) instead of `O((n + |E|)² · |candidates|)`. With the root fixed
   the forcing's detection becomes `O(n + |E|)`, but the directed spelling as a
   whole still does not grow like the undirected one, since rule 5 runs a
   backwards search per selected node (879 µs a call with the forcing off and
   the root fixed at 400 nodes, against 164 µs undirected with it on); with the
   root open it is still quadratic, since the candidates can number `n`, and
   every forcing still builds its reason with a search per candidate. Moderate.
   Today the directed forcing costs 3.3 ms a call at 400 nodes with the root
   open and 3.5 ms fixed, against 0.16 ms undirected with the root open. Low priority while no corpus model
   is directed. Filed as #1316.
4. **Fix the stale text this audit found outside this document**, as small
   out-of-stack fixes; the long note stays where it is:
   - `connectivity-proofs.md`'s section "What is not one RUP" says the forcing
     is not implemented and that the propagator applies "the five rules in the
     table"; both stopped being true in 081be4c0.
   - `connectivity-proofs.md:127–130` says `reachable_test` runs every case
     through `solve_for_tests_checking_gac`; the aliased `dup` run uses plain
     `solve_for_tests`.
   - **Reported, not proposed for a fix:** the note's `hitori` propagator /
     no-cuts figures (the section at lines 256–339, including 301, 307 and
     326) and `proof-benchmarks.md`'s rows 118–119 are from an earlier tree:
     `h5-1` 246,783 and 129,545 bytes, `h11-1` 679 MB in 1,485.3 s against
     93.7 MB in 626.7 s, "7.2× the bytes for 2.4× the check". This audit
     measures 234,390 and 108,001 bytes, and 672.6 MB against 79.6 MB (8.4×
     the bytes); its check times are in [Proof performance](#proof-performance).
     `proof-benchmarks.md` is not updated for drift, by standing instruction (it
     is to be re-measured when VeriPB's label groups land); whether the design
     note gets a dated note is the maintainer's call.
   - `reachable.hh:54–55` says `with_cut_forcing` has "no effect on the
     directed spelling"; it switches rules 9 and 10 (see [Options](#options)).
   - `reachable_test.cc:180` says the mutation fixture is "six free nodes"; it
     has seven (`208–217`).
   - The comment at `reachable.cc:154–155` and `connectivity-proofs.md`'s
     statements of the size (lines 14, 234, 315, 378 and 625) give it as
     `O(nodes × edges)`, which drops the `n²` term (see [OPB
     encoding](#opb-encoding)); [`tree.md`](tree.md) lists the same lines.
5. **The audit lane's pin.** A wide root, plain or as an offset view,
   enumerates without tripping the guard (see [Interval
   efficiency](#interval-efficiency)). PR #1302 (open) re-pins this family's
   rows, with every other index-valued position's, `Clean` with
   wide-declaration rows, as the safer choice until data argue otherwise; its
   guarded run trips nothing. The lane still runs only with the guard on
   (#920).
6. **The checking cost itself** is the encoding's, `Θ(n(n + |E|))` rows taxing
   every line. VeriPB's label groups are the route `proof-benchmarks.md`
   records, and `hitori-propagator-no-cuts` is the control to measure them
   against. Nothing to do in this family until then: the alternative encodings
   are either not RUP (the stdlib's labelling) or larger (GSS's pairwise walk
   encoding).
7. **Not worth an issue now:** passing MiniZinc's root offset as a view instead
   of a shifted variable, which would save one variable and one `Equals` and
   nothing else (the `Equals` already carries holes); deduplicating the
   forcing's reason literals, which matters most for the directed spelling
   (see [rule 9](#rule-directed-node-forcing)); a mutation lane for
   the forcing rules (wanted only when their derivation next changes); a
   subhint for the open-root forcing. Reconstruction does not need the
   subhint: rules 7 to 10 are `offline` by a fixed split over the root flags
   (see [rule 7](#rule-cut-vertex)). It would only save the per-root lines
   where one RUP would do, which is a cost for the justifier to show.

## Prior art

Connectivity and reachability constraints are old in CP. CP(Graph) (Dooms,
Deville and Dupont, CP 2005) made graph variables first class; Quesada, Van
Roy, Deville and Collet (*Using dominators for solving constrained path
problems*, PADL 2006) used dominators to prune directed reachability, which is
what rules 9 and 10 compute by brute force; and forcing articulation points and
bridges of the possible graph into a connected subgraph is the standard
undirected filtering, built on Tarjan's linear-time pass. Chuffed 0.13.2 ships
native graph propagators: its `mznlib` binds `connected`, `tree`, `dtree`,
`dpath`, `bounded_dpath`, `dag` and `steiner` to its own globals (each has an
`fzn_` file), declares a `chuffed_minimal_spanning_tree` that no global uses,
and has no undirected `path`. What this family claims beyond the standard
algorithms is the GAC argument for the existentially quantified root — that
the forcing over the residual graph, against "every selected node and a
candidate root", is exactly the rest of GAC — which the design note states and
this audit checked by brute force rather than proved.

**The unfolding is not new as an encoding.** Layered reachability, over
transitions that are themselves chosen by variables, is a SAT encoding from
planning under partial observability. Chatterjee, Chmelík and Davies (*A
symbolic SAT-based algorithm for almost-sure reachability with small
strategies in POMDPs*, AAAI 2016, §3.1 of arXiv:1511.08456) define "there is a
path to the goal of length at most `j`" by an equivalence over layer `j − 1`,
with `|S|` layers enough. Their clause that a state the strategy reaches must
reach the goal plays the part of the `reached` rows here. Pandey and Rintanen
(*Planning for partial observability by SAT and graph constraints*, ICAPS
2018, p. 194, equations (8) to (10)) write the recurrence with the previous
layer as a disjunct, as `reach[v][k]` has it. They give its size as
proportional to the product of nodes and arcs (true when the arcs are at
least about as many as the nodes; their recurrence also carries every node at
every layer, see [OPB encoding](#opb-encoding)), and present it as Chatterjee
et al.'s baseline, which their linear-size encodings replace. Feyzbakhsh
Rankooh and Rintanen (*Propositional encodings of acyclicity and reachability
by using vertex elimination*, AAAI 2022, the Background section; §3 of
arXiv:2105.12908) survey a one-sided form with `|V| − 1` levels. They set it
beside reachability by acyclicity and GraphSAT's propagators, and add
encodings over vertex elimination graphs. All of these count distance to a
fixed goal or target, and hand the formula to a SAT solver. The adaptation to
this constraint is this solver's. The source is a variable root, one-hot as
`reach[v][0]` whatever the root's own encoding. Nodes and edges are picked by
the constraint's own 0/1 variables, tied together by the subgraph rows. The
undirected spelling gives each edge one arc per direction. [`tree.md`](tree.md)
and [`path.md`](path.md) inherit the unfolding through this family, and
[`dag.md`](dag.md) writes a rootless variant of it.

On the proof side, certified connectivity was first done in the Glasgow
Subgraph Solver for maximum common connected subgraph (Gocht, McBride,
McCreesh, Nordström, Prosser and Trimble, *Certifying solvers for clique and
maximum common (connected) subgraph problems*, CP 2020). Its connectivity
inference is a bare RUP against a pairwise walk encoding built by repeated
squaring, `O(n³ log n)`. Later certified reachability arguments use other
encodings. `Circuit`'s (McIlree, McCreesh and Nordström, *Proof logging for
the circuit constraint*, CPAIOR 2024) shows a reachable set too small against
its position labelling (see [`circuit.md`](circuit.md)). Feng et al. (*DRAT
proofs of unsatisfiability for SAT modulo monotonic theories*, TACAS 2024)
check graph-reachability theory lemmas in DRAT. Their reachability
definition is one-sided and `O(|E|)`, and each unreachability lemma is checked
against a bound built for that lemma from the solver's record of which
vertices it reached. The breadth-first unfolding here keeps each inference a
bare RUP against `Θ(n(n + |E|))` rows, and the open-root case split is the
standard extended-reason pinning. What is claimed is the certification, not the
encoding. Every inference is a RUP against the unfolding, the open-root
forcings after the split over candidate roots. As far as this audit knows,
neither the unfolding as a proof encoding for connectivity nor its use for an
existentially quantified root is published. The SAT papers above do not show
their encodings supporting a propagator's inferences, or a proof's solution
steps.

## Further reading

- [`connectivity-proofs.md`](../connectivity-proofs.md): the design note, shared
  with [`dag.md`](dag.md). Why the stdlib's distance labelling is not RUP (an
  induction unit propagation cannot do), the unfolding, the GAC table for the
  undirected forcing and why the directed one has no one-pass version, the
  open-root case split, the encoding-size limit, the `hitori` measurements
  against the decomposition including the DB-tax comparison with `none`, the
  tree and path family built on top, and `Dag`'s rootless variant. Its section
  "What is not one RUP" is stale: it says the forcing is not implemented, which
  081be4c0 (in PR #784) changed; the section before it is current. Its
  propagator and no-cuts `hitori` figures are from an earlier tree (see [Next
  steps](#next-steps) item 4).
- [`proof-benchmarks.md`](../proof-benchmarks.md): the `hitori` rows, including
  the propagator against no-cuts pair kept as a label-groups candidate, with the
  same earlier-tree figures.
- [`frontend-support-matrix.md`](../frontend-support-matrix.md): the
  `reachable` row and its footnote, which this document's frontend table
  supersedes.
- [`tree.md`](tree.md), [`path.md`](path.md), [`subgraph.md`](subgraph.md),
  [`dag.md`](dag.md): the families that post this one as a child, copy its
  subgraph rows, or reuse its encoding idea.
