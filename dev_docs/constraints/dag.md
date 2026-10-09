# `Dag`: the selected part of a fixed digraph has no directed cycle

> **Maturity** production ·
> **Audited** 2026-10-09 at `86caad24` ·
> **Open issues** filed by this audit: #1303 (MiniZinc's `dag` over an empty
> node set is reported unsatisfiable), #1310 (the propagator rebuilds all of
> its working state on every call), #1309 (`Propagators::install_returning_id`
> is quadratic in a propagator's trigger count, an engine issue). Already open
> and touching this family: #868 (cross-solver comparisons; this document gives
> one by hand), #1006 (MiniZinc differential tests over the shapes front ends
> get wrong), #920 (the large-domain audit binary's header; the issue also
> notes that the binary, which holds this family's row, is registered as a
> ctest only under an option no CI lane sets). See [Next steps](#next-steps). Tracked under #871.

Unless marked otherwise, every figure here was measured for this audit at
`86caad24`, in a Release build (GCC 15.2.0), on fataepyc-10, on 2026-10-09,
with VeriPB 3.0.2 run with `--force-checked-deletion`. Probe paths such as
`probes/gac.cc` are relative to `tmp/fd-graph/dag/`.

`Dag(edges, ns, es)` takes a fixed directed graph, a 0/1 variable per node and a
0/1 variable per edge. It holds when every selected edge has both endpoints
selected, and the selected edges contain no directed cycle. It is MiniZinc's
`dag`, added by #791 (PR #918). It is one propagator and five inference
rules, each a single RUP against an OPB encoding. The encoding is
`Reachable`'s level-by-level unfolding with the root taken out. The design
argument, the measurements that justified it and the comparison with the
stdlib decomposition live in
[`connectivity-proofs.md`](../connectivity-proofs.md), under "Acyclicity: the
same unfolding, without a root". This document is the per-rule record.
[`reachable.md`](reachable.md) owns the rooted unfolding and the rest of that
note.

Three things to know before touching it.

- **It is generalised arc consistent on distinct variables, and every
  inference is one RUP.** That holds over node and edge variables together.
  Acyclicity is downward closed, so leaving every undecided edge out is always
  a support. The only values that can lack support are an edge whose selection
  would close a cycle, an edge with an endpoint fixed out, and a node that a
  selected edge needs. A brute-force
  check over 10,000 random graphs with random partial domains, self loops and
  parallel edges found no unsupported value and no missed failure. Repeated
  variables lose generalised arc consistency, but no solutions: on 6,000
  aliased instances, 410 roots kept an unsupported value.
- **Its encoding costs nodes × (nodes + edges) in each strongly connected
  component of the input**: quadratic in the nodes on a sparse component,
  cubic on a dense one. A component with `V` nodes and `E` edges costs `2V² + 2E(V − 1) + E`
  OPB rows, independent of the domains, which are all 0/1. A single directed
  cycle of 400 nodes is 641,201 rows and 52 MB of OPB. An input with no cycles
  costs only the two subgraph rows per edge. The proofs are one line per
  inference, and checking the cycle rule's line takes one round of unit
  propagation per level.
- **Through MiniZinc, an empty node set is unsatisfiable.** `fzn_dag.mzn`
  takes `min(index_set(ns))`, which is undefined on an empty set. MiniZinc
  turns that into `false`, and fzn-glasgow reports `=====UNSATISFIABLE=====`
  where Gecode finds the one solution (#1303). Every non-empty shape
  agrees with brute force through every front end. Separately and
  deliberately, `Dag` is **stricter than the stdlib decomposition**. That
  decomposition lets a selected edge leave an unselected node, so on a single
  edge it has six solutions to `Dag`'s five; Chuffed's native `dag` has four.

## What it is

### Semantics

`edges[e] = (u, v)` is a directed edge from node `u` to node `v`, with nodes
numbered from zero. `ns[i]` and `es[e]` are 0/1 variables saying whether node
`i` and edge `e` are selected (`dag.hh:16–23`). The constraint holds when:

- every selected edge has both endpoints selected (MiniZinc's `subgraph`); and
- the selected edges contain no directed cycle.

An all-zero assignment is a solution. A self loop is a cycle of one, so its
edge can never be selected. Two parallel edges from `u` to `v` are not a
cycle; one in each direction is.

**The documented meaning, not the decomposition's.** MiniZinc documents `dag`
as constraining "the subgraph `ns` and `es` ... to be a DAG". The stdlib's
`fzn_dag` is a distance labelling that forces only a selected edge's *head* to
be selected. `fzn_dreachable` ends with an explicit `subgraph(...)`;
`fzn_dag` has none. So on two nodes with the one edge 0 to 1, the
decomposition admits `ns = [false, true], es = [true]`. Measured on MiniZinc
2.9.7 and 2.10.1: Gecode on the decomposition has 6 solutions, `Dag` has 5, and
Chuffed's native `dag` has 4, since it also requires weak connectivity
(`tmp/fd-graph/dag/fe/two.mzn`). `Dag` follows the documentation and the rest
of the graph family. [`minizinc.md`](../minizinc.md) ("... and the
decomposition may not match the documentation either") gives the
consequences for testing. A differential test has to post `subgraph`
alongside, as `minizinc/tests/dagtest.mzn` does.

Degenerate cases:

- **No edges:** `prepare` returns `false` (`dag.cc:184`), so the constraint
  installs nothing and writes no OPB rows. The nodes are unconstrained, which
  is the meaning. The bounds check below still runs first.
- **No nodes:** only meaningful with no edges, which is the case above, from
  C++ and from the `.scp` reader. Through MiniZinc it is unsatisfiable: see
  [Robustness and limits](#robustness-and-limits).
- **Bad arguments throw** `InvalidProblemDefinitionException` from `prepare`:
  a different number of edge variables and edges, an endpoint that is not a
  node, or a node or edge variable whose initial bounds leave `0..1`
  (`dag.cc:166–181`).
- **A repeated variable** is accepted and means what it says: two nodes
  sharing a variable are selected together (`dag.hh:45–48`). Consistency is not
  claimed then.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Dag` | ✓ `fzn_dag` → `glasgow_dag`[^mzndag] | n/a[^xdag] | n/a[^gcspy] | ✓ `dag` | no reified form anywhere; no cake counterpart |

[^mzndag]: `minizinc/mznlib/fzn_dag.mzn` overrides `fzn_dag` directly. The
    stdlib's `dag.mzn` does the `enum2int` itself and calls one `fzn_dag`, so
    there is no `_int` / `_enum` pair to override as for the rest of
    `globals.graph`. The redefinition shifts the endpoints by
    `min(index_set(ns))`, so a node index set that does not start at one is
    right. It also passes `ns` and `es` through a comprehension. fzn-glasgow
    reads the call at `fzn_glasgow.cc:969–977` through `edges_from_endpoints`,
    which every graph binding shares and which rejects a negative endpoint. The
    stdlib's `fzn_dag_reif` is an `abort`. The file's comment (line 6) says it
    shifts "as fzn_subgraph.mzn does", but there is no such file: the shift it
    means is in `fzn_subgraph_enum.mzn`. That is an out-of-stack comment fix.

[^xdag]: XCSP3 has no acyclicity constraint.

[^gcspy]: `n/a`, as the frontend support matrix records it.
    `gcspy` binds nothing in the graph families, so no CPMpy route can reach
    `Dag` today; whether CPMpy itself has a `dag` was not checked.

**What was checked, per route.** Each route was compared against brute force
on random graphs of zero to five nodes (`diff.py`'s default) or one to six
(`MINN=1 MAXN=6`), with up to seven edges, self loops, parallel edges and
some variables fixed (`tmp/fd-graph/dag/fe/diff.py`; the settings per run are
in `NOTES.txt`):

- **MiniZinc.** fzn-glasgow, and Gecode on `dag` plus `subgraph`, on node index
  sets starting at 1, 0, 3 or −2 and edge index sets starting at 1, 0 or 5.
  That is 450 instances on 2.9.7 (seed 2 with the default sizes, seed 4 with
  one to six nodes) and 450 on 2.10.1 (seeds 3 and 5 likewise). The only
  disagreements are the 81 instances with no nodes: see #1303.
  Without the `subgraph`, Gecode's solution set differs from the documented
  meaning on 288 of the 900.
- **`.scp`.** The `.scp` reader, through `glasgow_scp_solver --all`, on the
  same instances, empty ones included. No disagreement.
- **C++ API.** Covered by the strength probe under
  [Inference catalogue](#inference-catalogue): solution counts against brute
  force on every instance.

### Options

`None.` There is no consistency tag, and the only setter is
`with_proof_mutation()`, which is for the mutation lanes (see
[Tests](#tests)).

### Variable kinds and views

Plain variables, constants and views, provided every initial domain lies in
`0..1`. The propagator reads `optional_single_value()` only. The proof handles
views: every row is written over the literal `v == 1` or `v == 0` of the
variable as given, so a `1 − x` view gets its own literal. Sixty random
instances with half their positions as `1 − x` views, with proofs, all verify
(`probes/gac.cc` mode 2), and the brute-force probe found no strength loss on
views. No test in the suite posts a view.

### Reification

`None.` MiniZinc's `fzn_dag_reif` aborts, so no front end could post one. None
is wanted until a model asks.

### Relation to other families

- **Decomposes into it:** nothing in the solver. MiniZinc's `dag` reaches it
  through the override; `2016/maximum-dag`, the one corpus model with this
  problem in it, does not call `dag` and so does not.
- **Child constraints:** none.
- **Shares code:** none with another constraint class. The two subgraph rows
  per edge (`sgf<e>`, `sgt<e>`) are written identically by `Subgraph` and
  `Reachable`, and the two subgraph inferences have the same logic in all
  three. They are copies, not a shared helper. One difference: `Dag` guards
  the one-literal reasons on `want_reasons()`, while `Subgraph` and
  `Reachable` build them unconditionally (`subgraph.cc:118–131`,
  `reachable.cc:226–240`). `subgraph.md` documents the rule for `Subgraph`. Shared with every graph binding:
  fzn-glasgow's `edges_from_endpoints`, and the `.scp` reader's
  `resolve_integer_list` / `resolve_variable_list`.
- **Shares a design note:** [`connectivity-proofs.md`](../connectivity-proofs.md),
  with `Reachable` and the tree and path family. The level unfolding and the
  argument that it turns a breadth-first search into unit propagation are that
  note's, and [`reachable.md`](reachable.md) documents them for the rooted
  case. What is this family's own is the rootless form, the restriction to
  strongly connected components, and the inferences below.
- **Presolvers:** none reads it.
- **Merges:** none proposed.

## The proof model

### OPB encoding

With `C` ranging over the strongly connected components of the **input**
graph that could hold a cycle (more than one node, or one node with a self
loop), `V_C` and `E_C` its nodes and the edges with both ends in it, and
`L_C = |V_C| − 1`:

```
for every edge e = (u, v):
  es[e] = 1  ⇒  ns[u] = 1                                          sgf<e>
  es[e] = 1  ⇒  ns[v] = 1                                          sgt<e>
for every component C:
  for every v ∈ V_C:
    lev[v][0]    ⇔  ns[v] = 1                                      flag x[id][v_0][lev]
  for every k = 0 .. L_C − 1:
    for every e ∈ E_C:
      arc[e][k]    ⇔  es[e] = 1  ∧  lev[from(e)][k]                flag x[id][e_k][arc]
    for every v ∈ V_C:
      lev[v][k+1]  ⇔  ⋁_{e ∈ E_C into v} arc[e][k]                 flag x[id][v_(k+1)][lev]
  for every e ∈ E_C:
    lev[from(e)][L_C]  ⇒  es[e] = 0                                nowalk<e>
```

`lev[v][k]` means "a selected walk of exactly `k` edges inside `C` ends at
`v`", starting at a selected node. A walk of `|V_C|` edges inside `C` repeats a
node and so contains a cycle, and `nowalk` forbids exactly that walk. `L_C` is
exact, not generous: the longest simple path inside `C` has `L_C` edges, so a
DAG can reach the top level. `connectivity-proofs.md` records that one level
fewer rejects valid DAGs, checked by enumeration at four to six nodes. **Edges
between components get no level rows**, because a cycle is strongly connected
and so lies inside one component (`cyclic_parts_of`, `dag.cc:50–122`, an
iterative Tarjan). `define_proof_model` is at `dag.cc:187–256`.

**It is definitional.** Every flag is fully reified, `sgf` and `sgt` are the
subgraph half of the meaning, and `nowalk` is the acyclic half restated as "no
long walk". `lev[v][0]` is a flag equivalent to the literal `ns[v] = 1`; it
could be the literal itself, saving two rows per node.

**Size**, in rows: `2|E|` for the subgraph, plus, per component,
`2|V_C|²` (`|V_C|` levels of `|V_C|` two-row flags), `2|E_C|(|V_C| − 1)` (the
arc flags) and `|E_C|` (`nowalk`). The rows are clauses or short reified
sums, so bytes follow rows. **Independent of domain width**, which is 0/1
everywhere, and **`Θ(|V_C| · (|V_C| + |E_C|))` per component**: quadratic in
the nodes when the component is sparse, cubic when it is dense. Measured with
`probes/scale.cc`, the OPB of the constraint alone:

| input graph | nodes | edges | OPB rows | of them `Dag`'s | OPB bytes |
|---|---|---|---|---|---|
| directed path (acyclic) | 1,000 | 999 | 3,998 | 1,998 | 164,802 |
| directed cycle | 25 | 25 | 2,576 | 2,525 | 184,333 |
| directed cycle | 100 | 100 | 40,301 | 40,100 | 3,017,383 |
| directed cycle | 400 | 400 | 641,201 | 640,400 | 51,668,283 |
| complete digraph | 20 | 380 | 16,781 | 16,380 | 1,607,823 |
| complete digraph | 40 | 1,560 | 131,161 | 129,560 | 13,522,043 |
| random, out-degree 3 | 100 | 300 | 68,437 | 68,036 | 6,171,540 |

*Release build of `86caad24`, fataepyc-10, 2026-10-09.* The rest of each row
count is one bound row per variable and the `preserved` header (this
document's row counts include that header line; `reachable.md` and `tree.md`
leave it out). So even a
sparse input is quadratic in the size of its largest component: one long
cycle of 400 nodes is 52 MB. A dense component is dearer again: doubling a
complete digraph from 20 to 40 nodes multiplies `Dag`'s rows by 7.9.
`connectivity-proofs.md`'s dense table gives `Dag` 18,288 rows and 1.92 MB
for one 20-node, 380-edge component, and says nothing but the constraint was
in that model. The formula gives 16,380 `Dag` rows for any such component;
with the 400 variables' bound rows and the header that is the 16,781 measured
above, and the build at #918's merge gives the same. The fact-check found a
bare MiniZinc `dag` over the complete 20-node digraph, flattened by 2.9.7 or
2.10.1, also writes exactly 16,781 rows. The note's excess over that is
1,507 rows at 20 nodes, and by the same comparison 3,007 at 40 and 4,507 at
60: `75n + 7`, growing with the graph. It is unexplained.
`connectivity-proofs.md` measures where the encoding
overtakes the decomposition's on dense graphs, with figures from #918's
measurements, not re-taken here.

### Labels

`None` load-bearing. Every rule is a RUP that cites no row. The rows carry
labels anyway: `c[id][sgf<e>]` and `c[id][sgt<e>]`, `c[id][nowalk<e>]`, and the
flags' reification halves `x[id][v_k][lev][r]` / `[f]` and
`x[id][e_k][arc][r]` / `[f]`, with `v` a node number, `e` an edge number and
`k` the level. Those names are how an external tool finds the rows if it wants
them.

### Cake conformity

`cake_pb_cp` has no `dag`, so there is no chain case and no cake encoding to
match. The `.scp` form round-trips through the solver's own reader:
`scp_reader_test.cc`'s "dag enumerates correctly" (a triangle, 17 solutions;
a self loop, 2) and "dag survives write -> read -> write unchanged". Since the
cake chain starts at the `.scp`, the front ends are checked separately, under
[Concrete constraints and frontend coverage](#concrete-constraints-and-frontend-coverage).

### Proof-time state

- **At the root:** nothing. Every row and flag is in the OPB.
- **During search:** one RUP line per inference, at the current level, and no
  lemmas. Nothing is deleted except by the generic backtracking.
- **Naming:** as under [Labels](#labels). The flags are named by node or edge
  number and level, so a tool that knows the edge list from the `.scp` can find
  any of them.
- **Proof-only auxiliaries determined on a solution:** yes. Every flag is fully
  reified, bottom-up from `ns` and `es`, so unit propagation fixes all of them
  from a full assignment, in the one direction, which is what `solx` needs.

## The implementation

### Initialisation and global data

`prepare` (`dag.cc:164–185`) checks the argument sizes, the endpoints and the
0/1 bounds, and returns `false` on an empty edge list. There is no
initialiser and no constraint state. The strongly connected components are
computed in `define_proof_model`, so **only with proofs on**, in
`O(nodes + edges)`. But `define_proof_model` then allocates two `n`-long
vectors of vectors (`entering` and `lev`, `dag.cc:222`, `:227`) **for each
cyclic component**, so setting up the proof model costs `Θ(n × components)`
whatever the components' sizes. With `n/2` disjoint two-cycles, turning proofs
on adds about 0.5 s to the root at `n` = 10,000, 1.5 s at 20,000 and 4.5 s at
40,000, for an OPB of only 7 to 29 MB. That is wall time inside `solve_with`
to the first search node, serial, pinned, with the malloc thresholds fixed:
three runs each in the fact-check's re-check (`factcheck2/dag/pairs/`), and
one run here at 10,000 and 20,000 that agrees (`pairs/pairs.cc`). The
propagator does not use the components; see
[Mutable state and incrementality](#mutable-state-and-incrementality).

The root cost that does show is not this family's code. Installing the one
propagator, with `nodes + edges` triggers, is quadratic in that count in
`Propagators::install_returning_id` (#1309), through two loops: the linear
`contains` test that builds the propagator's scope (`propagators.cc:724–748`)
and the same test again when that scope is merged into the constraint's
(`:765–769`). Fixing the first alone leaves the install quadratic. A 100,000-node
directed path takes about 11 s inside `solve_with` to reach its first search
node (12 s for the whole process), proofs off, and about two thirds of a
30,000-node run is that function (`probes/scale.cc`, `perf record`).

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| the one propagator (`dag.cc:268–393`) | `on_change`, every node and edge variable | derived: every node and edge variable, **vacuously** | 1–5 | always, unless the edge list is empty | never claims | never |

**Idempotence.** Not claimed: it returns `PropagatorState::Enable`. The
argument that it would be safe to claim, on distinct variables: the subgraph
pass infers only `ns = 1` and `es = 0`. Neither selects an edge, so neither
changes the selected edge set the cycle pass reads. The cycle pass infers only
`es = 0`, which no rule reads back. A scratch build that claimed
`EnableButIdempotent`, run under `GCS_CHECK_IDEMPOTENT_CLAIMS=1` with the
checker confirmed on, never failed a re-run in full search over 6,000 random
instances with distinct and view positions, of which about 5,400 have edges
and so install the propagator (`tmp/fd-graph/dag/idem/`).
That is evidence for a claim, not a proof of one. Aliased positions need no
argument: the engine ignores `EnableButIdempotent` on any propagator whose
trigger positions share a variable (`positions_alias`,
`propagators.cc:120–128` and `:780`), and does not re-run it under the
checker either (`:1362`). So the 3,000 aliased instances the same run
included checked almost nothing: only the 58 whose repeats all fell on
constants, which have no underlying variable and so do not alias.

**Self-disabling.** Never. Once every edge is fixed the propagator has nothing
left to infer, and returning `DisableUntilBacktrack` there would save the
calls; small.

### Mutable state and incrementality

**None persists.** Every call rebuilds everything from the domains:

- the subgraph pass, `O(edges)`;
- `leaving`, the selected edges by tail, and `candidates`, the undecided or
  selected edges by head: two vectors of `n` vectors each, allocated afresh;
- for each head with a candidate, a depth-first search over the selected
  edges, after **clearing two `n`-long buffers** (`seen.assign`,
  `came_from.assign`, `dag.cc:353–354`).

The searches are bounded by the selected edges reachable from the head. The
clears are not: a call costs Θ(n) per head with a candidate even when every
search visits nothing. At 40,000 nodes that is about 0.2 s for one call that
infers nothing, almost all of it in the two clears; a generation stamp removes
it (`probes/scale.cc`, `ab/dag_stamp.cc`). And the propagator does not use the
input's strongly connected components, which `define_proof_model` already
computes. An edge between components can never close a cycle, and a path that
closes one never leaves its component, so both the candidates and the
searches could skip those edges. On `2016/maximum-dag` `25_04` this family is
23.9 s of a 34.9 s solve, 13.3 µs a call. Skipping the cross-component edges
cuts the run's instructions by 18.7%, and keeping the scratch buffers between
calls takes that to 29.0%, on the identical tree (#1310; see
[CPU performance](#cpu-performance)). Neither change touches an inference.

### Interior values and optional pruning

**Offers.** `None.` There is one arm, and nothing has an interior to prune:
every variable is 0/1.

**Observes.** **Nothing, in effect.** The family's whole vocabulary is
whether a 0/1 variable is fixed, which is to say its bounds. Every variable it
takes has at most two values, so none of them can have a hole, and a `Dag` is
never a reason for another constraint's interior pruning to stay on. The
triggers are `on_change`, so the derived declaration says holes affect every
variable. That over-reports, harmlessly, because the declaration only matters
for a variable that can have an interior.

### Robustness and limits

**Unbounded domains.** Not applicable: `prepare` refuses any variable whose
initial bounds leave `0..1`.

**Negative values and zero.** Node numbers are `size_t`. The `.scp` reader
and fzn-glasgow's `edges_from_endpoints` reject a negative endpoint, and `prepare` rejects one
past the last node. Through MiniZinc the shift by `min(index_set(ns))` handles
index sets that start at zero or below; the differential check above covers
starts of −2, 0, 1 and 3.

**Degenerate shapes.**

- *No edges:* nothing is installed; see [Semantics](#semantics).
- ***No nodes, through MiniZinc,* is a wrong answer.** `fzn_dag.mzn:20`
  computes `min(index_set(ns))`, which MiniZinc treats as undefined on an
  empty set. With the warning "undefined result becomes false in Boolean
  context (minimum of empty set is undefined)", the call flattens to `false`
  and fzn-glasgow reports `=====UNSATISFIABLE=====` on 2.9.7 and 2.10.1, where
  Gecode finds the one solution (`tmp/fd-graph/dag/fe/e0.mzn`). In a larger
  model, one empty `dag` makes the whole model unsatisfiable. The sibling
  redefinitions that shift by `min(index_set(...))`, such as `fzn_circuit.mzn`
  and `fzn_inverse.mzn`, guard with `if length(x) = 0 then true else ...`;
  this one does not (#1303). The four-argument
  `subgraph(from, to, ns, es)` has the same defect through
  `fzn_subgraph_enum.mzn`, also #1303, and `subgraph.md` owns it. The rooted families have
  a **different** empty-node defect with the opposite answer. There the right
  answer is unsatisfiable, since a root must be selected. Their integer
  spellings give `=====ERROR=====`, because `Reachable`, `Tree` and `Path`
  throw from `prepare`, and their `_enum` overrides give the right
  unsatisfiable answer by the same accident as here (#1305): `reachable.md`,
  `tree.md` and `path.md` own that. **The fix here must not be copied
  there:** a `then true` guard in the rooted `_enum` overrides would turn
  their accidentally right UNSAT into a wrong SAT.
- *Self loops and parallel edges:* handled, and in the strength probe.
- *Aliased variables:* sound, but not generalised arc consistent; see rule 4's
  **Strength**. The suite's one aliased run shares two nodes of a triangle.
- *Constants:* fine. A cycle of constant-1 edges fails at the root.

**Overflow.** Nothing to guard. The only arithmetic is on node, edge and level
counts, and a flag's index is a `long long` cast of a `size_t`.

**Size.** The OPB is the limit with proofs on: see [OPB encoding](#opb-encoding).
On an input with many cyclic components, setting up the proof model is a
limit before that: see
[Initialisation and global data](#initialisation-and-global-data). With proofs off, the per-call rebuild is the limit on large graphs, and
installation before it.

### Interval efficiency

**Fine at any width, trivially.** Every variable is 0/1.

1. **The propagation side.** No site walks values. The loops run over edges,
   nodes and selected edges.
2. **The reason side.** One literal per selected path edge, or one endpoint
   literal, never per value, and **every reason is guarded on
   `want_reasons()`** (`dag.cc:283`). The self loop's reason is empty and
   needs no guard.
3. **The proof side.** One RUP line per inference. Nothing is per value. The
   encoding is `Θ(|V_C| · (|V_C| + |E_C|))` per component, a graph-size cost,
   not a width cost.
4. **The audit lane.** One row, `Dag`, pinned `NoWidePosition`: a triangle
   over 0/1 variables (`large_domain_audit_test.cc:818–821`). There is no
   position a wide domain could reach, so there are no axes to vary. The
   binary is built everywhere, but its audit case is registered as a ctest
   only in a build
   configured with `-DGCS_LARGE_DOMAIN_GUARD=ON` (`gcs/CMakeLists.txt:212–213`),
   which is off by default and set by no CI lane (#920). PR #1302 (open), which
   re-pins the index-valued positions of other families `Clean`, leaves this
   row `NoWidePosition`, since every selector must be 0/1.

## Inference catalogue

Five rules: two subgraph rules, the self loop, and the cycle rule in its
removal and its conflict forms.

Four facts hold for all five.

**Each is one plain RUP, and its whole content is its reason.** The
justification is `JustifyUsingRUP` (`dag.cc:272`): the solver writes the
clause `inferred literal ∨ ¬reason` as one `rup` line, with no lemmas and no
cited rows. Rules 1 and 2 are RUP against one row, `es[e] = 1 ⇒ ns[w] = 1`,
by Theorem 2.6 of [`justification-techniques.md`](../justification-techniques.md):
the clause is that row's consequent under its condition. Rules 3 to 5 are RUP
by unit propagation up the level flags, one round per level. **No published
procedure** covers that step: the argument is the unfolding's, from
[`connectivity-proofs.md`](../connectivity-proofs.md), and each entry's
**Proof technique** gives it.

**One wire form.** `hints::Dag`, `(constraint_id <id>)`, with no subhint,
for every rule (`dag/hints.hh`).

**Every rule is `offline`.** The asserted clause is RUP against the OPB alone,
so a reconstructor can replace each `a` line with a `rup` of the same clause.
Nothing needs choosing and the hint does not need reading.

**An assertion is checked against the solutions.** At `Inferences`,
`Definitions` and `Links`, the mutation fixture's 109 `dag`-hinted assertions
are each satisfied by all 461 solutions the same proof logs
(`tmp/fd-graph/dag/assert/checka.py`), and VeriPB accepts all three proofs
under assertions.

### Rule: select-endpoints

- **Infers** — `ns[u] = 1` and `ns[v] = 1`, one inference each, for a selected
  edge `e = (u, v)`.
- **Fires when** — `es[e]` is fixed to 1 and an endpoint is not yet fixed to
  1, in the subgraph pass (`dag.cc:297–300`). If the endpoint is fixed to 0
  the inference fails, and that is how a selected edge at an unselected node is
  caught.
- **Strength** — `partial`: the node half of `GAC` on each subgraph row
  `es[e] = 1 ⇒ ns[w] = 1`. With rule 2 that row is `GAC`. `ns[i] = 0` lacks
  support on the whole constraint exactly when a selected edge touches `i`,
  so with rules 2 to 4 the constraint is `GAC`; see rule 4.
- **Algorithm** — `O(1)` per edge, inside the `O(edges)` subgraph pass.
- **Why it is true** — a selected edge has both endpoints selected.
- **Proof technique** — `RUP`: the clause `ns[u] = 1 ∨ es[e] = 0` is the row
  `sgf<e>` (or `sgt<e>`) itself.
- **Reason** — `es[e] = 1`. Minimal. Guarded on `want_reasons()`.
- **Assertion** — `ns[u] = 1 ∨ es[e] = 0`, the same line whether it succeeds
  or fails. Measured at `Inferences`, edge 0 to 1 with the edge branched first
  (`probes/assert.cc fwd`):
  ```
  a 1 i[n0][b0] 1 ~i[e0][b0] >= 1::dag:((constraint_id _1));
  ```
- **Hint** — `hints::Dag`: `originator`, the `ConstraintID`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line of two literals.
- **Gaps** — `None.`
- **Tightness** — **shown by a probe, not a lane.** `dag_mutation_endpoint`
  drops the endpoint literal from both subgraph rules, but its fixture
  branches nodes before edges, so the line VeriPB refuses is rule 2's (see
  there). With the same mutation and edges branched first
  (`tmp/fd-graph/dag/mut/fwdmut.cc`), VeriPB refuses line 2,
  `rup 1 i[n0][b0] >= 1`, which is this rule's; the unmutated proof verifies.

### Rule: drop-edge-at-unselected-node

- **Infers** — `es[e] = 0`.
- **Fires when** — `es[e]` is undecided and one of its endpoints is fixed to 0,
  in the subgraph pass (`dag.cc:302–308`). One inference per edge, from the
  first endpoint found.
- **Strength** — `partial`: the edge half of `GAC` on each subgraph row.
  `es[e] = 1` needs both endpoints selectable.
- **Algorithm** — `O(1)` per edge.
- **Why it is true** — a selected edge would select its endpoint.
- **Proof technique** — `RUP`, against the same row as rule 1. The clause is
  the same clause.
- **Reason** — `ns[w] = 0` for the endpoint `w`. Minimal. Guarded.
- **Assertion** — `es[e] = 0 ∨ ns[w] = 1`: the same clause as rule 1's, so an
  external tool cannot tell the two apart and does not need to. Measured at
  `Inferences` (`probes/assert.cc bwd`):
  ```
  a 1 ~i[e0][b0] 1 i[n0][b0] >= 1::dag:((constraint_id _1));
  ```
- **Hint** — `hints::Dag`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line of two literals.
- **Gaps** — `None.`
- **Tightness** — `dag_mutation_endpoint`: with the endpoint literal dropped,
  VeriPB refuses the fixture's line 2, `rup 1 ~i[e0][b0] >= 1`, which is this
  rule's (re-run at `86caad24`). The fixture is two triangles sharing a node
  plus a spur, and `dag_mutation_none` verifies the same fixture unmutated
  (461 solutions).

### Rule: self-loop

- **Infers** — `es[e] = 0` for an edge from a node to itself.
- **Fires when** — every call, for every self-loop edge not yet fixed to 0, in
  the cycle pass (`dag.cc:339–340`). At the root that removes it for good.
- **Strength** — `partial`: `GAC`'s removals on self-loop edge variables,
  whose 1 never has support.
- **Algorithm** — `O(1)`.
- **Why it is true** — a self loop is a cycle.
- **Proof technique** — `RUP` with an empty reason: `es[e] = 1` selects `v`
  through `sgf<e>`, so `lev[v][0]`, and walking the loop sets `lev[v][k]` for
  every `k` up to `L_C`. Then `nowalk<e>` says `es[e] = 0`. When `v` is a
  component of its own, `L_C = 0`, and `sgf<e>`, the level-0 flag and
  `nowalk<e>` conflict at once.
- **Reason** — empty, which is right: the unit holds in every solution.
- **Assertion** — the unit clause `es[e] = 0`. Measured at `Inferences`
  (`probes/assert.cc loop`):
  ```
  a 1 ~i[e0][b0] >= 1::dag:((constraint_id _1));
  ```
  This is a bare unit with no reason, but unlike `SmartTable`'s and
  `Circuit`'s SCC propagator's (see [`smart_table.md`](smart_table.md)) it is
  a consequence of the model alone, so it is a correct assertion. Applied to
  a self-loop edge that is already selected, the inference fails and the line
  is the same.
- **Hint** — `hints::Dag`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line, one literal. Checking it takes up to `L_C + 1`
  rounds of unit propagation.
- **Gaps** — `None.`
- **Tightness** — `Not shown`, and there is no part of an empty reason to
  drop.

### Rule: close-cycle

- **Infers** — `es[e] = 0`, for `e = (u, v)`, when the selected edges already
  run from `v` back to `u`.
- **Fires when** — in the cycle pass, after the subgraph pass, for each
  undecided edge whose head has a selected path to its tail
  (`dag.cc:345–389`). The candidates are grouped by head, and one search from
  each head answers for every candidate into it.
- **Strength** — `partial` alone: `GAC`'s removals of cycle-closing edges.
  With rules 1 to 3 the constraint is `GAC`, over node and edge variables
  together, on distinct variables. The argument: acyclicity is downward closed,
  so with every undecided edge left out, what remains is the selected edges,
  which are acyclic or the search would already have failed. So `es[e] = 0` and
  `ns[i] = 1` are always supported. `es[e] = 1` is supported unless it closes
  a cycle (this rule) or meets an unselected node (rule 2), and `ns[i] = 0`
  unless a selected edge touches it (rule 1). Checked by brute force at the
  root, against the projection of the solution set, on random graphs of one to
  six nodes and up to ten edges, with self loops and parallel edges, and each
  position free, fixed by its domain or a constant (`probes/gac.cc`): 10,000
  instances at seeds 1 and 2, 3,000 more at seed 3 with at most four nodes, and
  6,000 with half the positions `1 − x` views. There were no unsupported
  values, no missed failures, and every solution count matched. About a third
  of those roots fail outright, and the probe checks that those have no
  solution. `dag_test` checks GAC at every search node on its eleven shapes.
  **Aliasing loses it:** with every position drawn from a pool of about
  two-thirds as many variables (node and node, edge and edge, node and edge),
  208 of 3,000 roots at seed 1 and 202 at seed 2 keep an unsupported value,
  94 of each involving a node variable. No solution is lost, and every count
  matches. The simplest shape is a two-cycle whose edges share one variable
  `x`: `x = 1` closes the cycle, but neither edge is selected until `x` is
  fixed, so nothing is removed at the root.
- **Algorithm** — one depth-first search over the selected edges per head that
  has a candidate: at most one per node, `O(nodes + selected edges)` each, so
  `O(nodes × (nodes + edges))` per call at worst. Plus the per-call rebuild and
  the per-head buffer clears under
  [Mutable state and incrementality](#mutable-state-and-incrementality). The
  reason path is the search tree's path from `v` to `u`, walked back through
  `came_from`.
- **Why it is true** — a selected path from `v` to `u` plus the edge from `u`
  to `v` is a directed cycle.
- **Proof technique** — `RUP`. Under `es[e] = 1` and the reason, `sgt<e>`
  selects `v`, so `lev[v][0]`. Each `arc` and `lev` row then carries the walk
  one edge further round the cycle per level, and at level `L_C` the walk
  sits at some node whose next cycle edge is selected, which that edge's
  `nowalk` row forbids. Every node and edge on the cycle lies in one component,
  so the levels are there. That is `L_C` rounds of unit propagation, not a
  search. `connectivity-proofs.md` recounts checking this as a single RUP
  against hand-written encodings before it was implemented.
- **Reason** — `es[f] = 1` for each edge `f` of the path from `v` to `u`. A
  simple path, so subset-minimal: dropping any edge leaves no cycle. It is not
  necessarily the shortest such path, since the search is depth-first. One literal per
  path edge, never per value. Guarded on `want_reasons()`.
- **Assertion** — `es[e] = 0 ∨ ⋁_{f on the path} es[f] = 0`. Measured at
  `Inferences`, a triangle with `e0` and `e1` branched to 1
  (`probes/assert.cc cycle`):
  ```
  a 1 ~i[e2][b0] 1 ~i[e1][b0] 1 ~i[e0][b0] >= 1::dag:((constraint_id _1));
  ```
- **Hint** — `hints::Dag`.
- **Offline reconstructibility** — `offline`. The clause is RUP against the
  OPB, and the path is readable off the clause.
- **Proof size** — one line of `path length + 1 ≤ |V_C|` literals. **Checking
  it** takes `L_C` rounds of unit propagation over a database of
  `Θ(|V_C| · (|V_C| + |E_C|))` rows. A path of `n − 1` selected edges closed on a directed `n`-cycle
  (`probes/scale.cc cycle n closing`; the path edges are selected by their
  initial domains, so they are unit rows in the OPB rather than search
  decisions) verifies in 0.02, 0.05, 0.21 and 0.91 s
  at `n` = 50, 100, 200 and 400, against 0.01, 0.03, 0.13 and 0.54 s for an
  empty proof over the same OPB. The OPB dominates. (Single runs on a loaded
  machine; VeriPB 3.0.2, `--force-checked-deletion`.)
- **Gaps** — `None.`
- **Tightness** — `dag_mutation_path`: with the last path edge dropped,
  VeriPB refuses the fixture's line 347, a removal whose reason is left as one
  edge of a two-edge path (re-run at `86caad24`). `dag_mutation_none` is the
  control. The fixture's cycles are triangles, so a dropped edge leaves a path
  rather than a shorter cycle, as its comment requires.

### Rule: selected-cycle

- **Infers** — a contradiction, through rule 4's own inference: the edge it
  would remove is already selected.
- **Fires when** — the selected edges already contain a cycle when the
  propagator runs. That happens when more than one edge of a cycle is fixed
  between two calls: the objective's linear row fixing the remaining edges
  together, for instance, or a model whose edges are coupled by other
  constraints. Search fixing one edge at a time never reaches it, because rule
  4 removes the closing edge first. On `2016/maximum-dag` `25_04`, where
  every node is fixed in and there are no self loops, so no other rule can
  fail, 569,244 of the propagator's 1,789,933 calls end in a contradiction
  (`GCS_PROPAGATOR_STATS=time`).
- **Strength** — `partial`: it fails any partial or full assignment whose
  selected edges already hold a cycle, so it is at least a `checker`.
- **Algorithm** — as rule 4. The candidate is the selected edge itself.
- **Why it is true** — as rule 4.
- **Proof technique** — `RUP`, as rule 4. The line is the same.
- **Reason** — as rule 4.
- **Assertion** — `es[e] = 0 ∨ ¬reason`, the attempted literal (false) with
  the negated reason: an ordinary failed inference, not a `contradiction()`.
  Measured at `Inferences`, a triangle whose three edges three one-way rows
  `x ≤ es[e]` fix together when `x = 1` is branched on
  (`tmp/fd-graph/dag/mut/selmut.cc`):
  ```
  a 1 ~i[e2][b0] 1 ~i[e1][b0] 1 ~i[e0][b0] >= 1::dag:((constraint_id _1));
  ```
  With the edges' domains `{1}` from the start, the line for the same
  triangle reads `a 1 i[e2][eq0] 1 ~i[e1][eq1] 1 ~i[e0][eq1] >= 1`
  (`probes/assert.cc selcycle3`).
- **Hint** — `hints::Dag`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — as rule 4.
- **Gaps** — `None.`
- **Tightness** — **shown by a probe, not a lane.** The mutation lanes'
  fixture branches one variable at a time, so this form never fires there. On
  `selmut.cc`, `DropPathEdge` makes VeriPB refuse line 30, this rule's line,
  and the unmutated proof verifies (17 solutions). Two easier fixtures do not
  work, and are worth knowing about. With the edges' domains `{1}`, the OPB
  already knows every edge is selected. With one equality row
  `e0 + e1 + e2 = 3x`, unit propagation recovers the dropped edge through the
  row. Both verify under the mutation.

## Evidence

### Tests

- **`dag_test`** (`dag_constraint`): eleven shapes, each enumerated against a
  brute-force checker under `solve_for_tests_checking_gac`, so GAC at every
  search node. The shapes are an empty edge list, a directed path, a triangle, a
  diamond whose cycle needs three edges, two triangles sharing a node, two
  two-cycles joined by an edge no cycle uses, a two-cycle, and a self loop with
  two parallel edges. Three more have pinned positions: two edges of a
  triangle constant 1, one node of the bowtie constant 0, and every node
  constant 1. Plus one aliased run, two nodes of a triangle sharing a variable,
  under plain `solve_for_tests`. Each runs without and with proofs, and VeriPB
  checks the proofs when it is on the path. Seeded: `--seed=1`, 2, 3 and 42
  all pass, with 12 proofs verified each.
- **Mutation lanes** (`gcs/CMakeLists.txt:1111–1125`): `dag_mutation_path`
  and `dag_mutation_endpoint` under `run_test_and_expect_verify_failure.bash`,
  and the control `dag_mutation_none` under `run_test_and_verify.bash`, on one
  fixture. All three behave as expected at `86caad24`. Which line each lane
  breaks is in rules 2 and 4.
- **`minizinc-dag`**: `dagtest.mzn`, two triangles sharing a node plus a spur,
  nodes indexed from 2, with `subgraph` posted alongside. It is differentially
  enumerated against MiniZinc's default solver, with `--fzn-pattern
  glasgow_dag` insisting the builtin ran. The proof verifies (461 solutions)
  on 2.9.7 and 2.10.1.
- **`.scp`**: the two `scp_reader_test` cases above.
- **Audit lane**: the one row above, registered only under
  `GCS_LARGE_DOMAIN_GUARD=ON`, which no CI lane sets (#920).

**Runtime caps.** No lane sets or clears one, and the default caps do not
fire: with `GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500`,
`dag_test --seed=1` reports no truncated run (the largest shape has 169
solutions), and its output matches the uncapped run's. So the capped run
checks everything the uncapped one does. Invocation:
`GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500 dag_test --seed=1`, at
`86caad24`, VeriPB 3.0.2 on the path.

**Tightness.** Two lanes and a control, on one fixture: some named
corruptions are refused on that fixture. The forward subgraph rule and the
conflict form of the cycle rule are shown only by the probes in their
entries.

**What the tests do not cover.**

- **Edge-edge and node-edge aliasing.** The one aliased run shares two nodes.
  The brute-force probe covers the other shapes; none loses a solution.
- **Views.** Nothing in the suite posts one. The probe's 6,000 instances and
  60 verified proofs do.
- **The cycle rule's conflict form.** No test fixes two edges of a cycle
  between calls. The corpus benchmark does it half a million times.
- **Components of more than five nodes.** Nothing in the suite has a component
  bigger than five nodes, so nothing tests the encoding's size. The probes go
  to 400 nodes in one component.
- **An empty node set through MiniZinc**, which is wrong (#1303).
- **Real instances:** none ported. `2016/maximum-dag` needs a model
  change to reach `Dag` at all.

### Benchmarks and examples

- **In the repository:** no example posts `Dag`.
- **Corpus:** no MiniZinc Challenge model calls `dag`. `2016/maximum-dag` (five
  instances, 25 to 31 nodes, 76 to 95 edges) is the problem written out by
  hand, with the stdlib's own `dist[n] = max(...)` labelling. It reaches `Dag`
  with the labelling replaced by
  `dag(tails, heads, [true | n in nodes], chosen)`, which is how it is run
  below (`tmp/fd-graph/dag/cpu/maxdag_dag.mzn`). The original exempts node 1
  from the labelling, which is correct only because no instance has an edge
  into node 1. That holds for all five, checked again here.
- **For CPU:** `maximum-dag` `25_04`, which proves its optimum in about half a
  minute, with `Dag` most of the time.
- **For proof verification:** maximum acyclic subgraph on small random
  digraphs (`probes/scale.cc random3 n mas`), and the closing-cycle probe of
  rule 4 for the encoding's cost. The corpus instances are out of reach with
  proofs: their searches are millions of nodes.

### CPU performance

*Release build of `86caad24` (GCC 15.2.0, `-O3 -march=native`); MiniZinc
2.9.7 flattening once per instance, then `fzn-glasgow -s` and Gecode 6.3.0's
`fzn-gecode` run directly; fataepyc-10, pinned to core 61, malloc thresholds
fixed, serial, 300 s cap; 2026-10-09. Core 61's SMT sibling was running other
jobs, so wall times are inflated by an unknown factor and only the
instruction counts and node counts are firm.*

Maximum acyclic subgraph on the five `2016/maximum-dag` instances, every
node fixed in, `bool_search(chosen, input_order, indomain_max)`. Three
runs per instance: `Dag`; the same `fzn-glasgow` on the stdlib
decomposition, flattened against a copy of `mznlib/` with `fzn_dag.mzn`
removed; and Gecode on the decomposition. A **bold** best value is proved
optimal; the others are the best found when the 300 s cap fired.

| instance (nodes, edges) | run | nodes | best | solve time | `instructions:u` |
|---|---|---|---|---|---|
| `25_01` (25, 78) | `Dag` | 4,877,311 | **71** | 143.8 s | 666.0·10⁹ |
| | decomposition, GCS | 1,191,710 | 71 | > 300 s | 1,644.1·10⁹ |
| | decomposition, Gecode | 21,207,201 | **71** | 246.6 s | 1,194.9·10⁹ |
| `25_04` (25, 76) | `Dag` | 1,138,559 | **70** | 32.7 s | 152.4·10⁹ |
| | decomposition, GCS | 1,246,285 | 70 | > 300 s | 1,695.1·10⁹ |
| | decomposition, Gecode | 7,461,969 | **70** | 77.5 s | 399.8·10⁹ |
| `31_02` (31, 95) | `Dag` | 1,412,837 | **89** | 49.7 s | 231.0·10⁹ |
| | decomposition, GCS | 947,831 | 85 | > 300 s | 1,707.0·10⁹ |
| | decomposition, Gecode | 10,466,009 | **89** | 140.4 s | 693.6·10⁹ |
| `25_03` (25, 87) | `Dag` | 8,879,393 | 77 | > 300 s | 1,373.3·10⁹ |
| | decomposition, GCS | 1,838,019 | 77 | > 300 s | 1,655.5·10⁹ |
| | decomposition, Gecode | 33,835,841 | 77 | > 300 s | 1,541.0·10⁹ |
| `25_06` (25, 88) | `Dag` | 8,943,737 | 80 | > 300 s | 1,382.5·10⁹ |
| | decomposition, GCS | 1,219,413 | 76 | > 300 s | 1,609.9·10⁹ |
| | decomposition, Gecode | 30,377,622 | 76 | > 300 s | 1,443.7·10⁹ |

`Dag` proves the three optima that anything proves, in 1.8 to 3.0 times
fewer instructions than Gecode needs, and with 4.3 to 7.4 times fewer nodes.
On `25_06` it also finds the best value of the three runs. GCS on the decomposition proves
nothing in 300 s. Its node rate is a fifth to a ninth of `Dag`'s, because the
decomposition brings its per-edge products and per-node maxima with it.

**There is no identical-tree comparison with Gecode.** Gecode has no `dag`, and
its run is the stdlib decomposition, which propagates less, so its tree is
different and its node rate is not comparable.

**Where the time goes.** On `25_04`, `GCS_PROPAGATOR_STATS=time` puts 23.9 s
of a 34.9 s solve in `Dag` (1,789,933 calls, 13.3 µs each), 3.8 s in the 76
`Equals` that channel `chosen` and 3.4 s in the objective's linear row. That
is hotspot context, not a saving. The saving was measured as an A/B: a scratch
`fzn-glasgow` relinked with a modified `dag.cc`, one run each on core 62
(`tmp/fd-graph/dag/ab/`):

| `25_04`, proofs off | nodes | objective | `instructions:u` | solve time |
|---|---|---|---|---|
| shipped `fzn-glasgow` | 1,138,559 | 70 | 152.43·10⁹ | 32.83 s |
| control: the same `dag.cc`, rebuilt | 1,138,559 | 70 | 152.38·10⁹ | 32.89 s |
| skip edges between input components | 1,138,559 | 70 | 123.90·10⁹ | 27.98 s |
| that, plus scratch buffers kept between calls | 1,138,559 | 70 | 108.23·10⁹ | 25.72 s |

The tree is the same by construction, since no inference changes, and the
node counts and optimum agree. The control matches the shipped binary, so
there is no layout penalty in the comparison. That is 29.0% of the
instructions (#1310).

**Measured elsewhere.** `connectivity-proofs.md` gives `Dag` 46.35 s and
4,877,311 nodes on `25_01`, and 15.84 s and 1,412,837 nodes on `31_02`,
measured for #918. Those figures come from a different measurement and are
not to be mixed with the table above. The node counts reproduce exactly here.
The times are about three times longer here. A build of #918's merge
commit spends 3.9% more instructions than main on `25_04` (158.4·10⁹ against
152.4·10⁹, same 1,138,559 nodes), so main has not regressed since then. The difference was not chased further.

**What the benchmark does not exercise.** Free nodes, since every node is
fixed in, so rules 1 and 2 never fire. Self loops. And any graph whose
components are larger than 25 nodes.

### Proof performance

*Same build and machine, core 62, single runs; VeriPB 3.0.2 with
`--force-checked-deletion`.*

**Maximum acyclic subgraph** on random digraphs of out-degree 3, every node
selected, branching on the edges in order, largest value first
(`probes/scale.cc random3 n mas`):

| nodes | edges | recursions | `.opb` | `.pbp`, `Off` | VeriPB, `Off` | `.pbp`, `Inferences` | `dag` assertions | their bytes |
|---|---|---|---|---|---|---|---|---|
| 8 | 24 | 395 | 43,041 B | 631,981 B | 0.11 s | — | — | — |
| 10 | 30 | 1,295 | 54,854 B | 2,540,994 B | 0.47 s | 1,900,561 B | 1,190 | 92,320 B (4.9%) |
| 12 | 36 | 3,675 | 82,179 B | 9,895,038 B | 2.17 s | 7,337,726 B | 2,768 | 266,949 B (3.6%) |

All three verify. At `Inferences` the rest is the objective's
`linear_equality` assertions (9,483 and 40,735, 83% and 86% of the bytes) and
backtracking. So on an optimisation model this family's proof is a small
share, and the objective dominates. **Own against shared**, for the encoding,
is the OPB table above: on a single component nearly every row is `Dag`'s, and
its count is `2V² + 2E(V − 1) + E`. On the proof side, each inference is one
line whose length is the reason. What grows with the component is the cost of
checking a line, not its size: the closing-cycle measurement under rule 4.

**Assertion levels.** On the mutation fixture the proof verifies at `Off`
(461 solutions) and is accepted under assertions at `Definitions`, `Links`
and `Inferences`, with 109 `dag`-hinted assertions, each consistent with
every logged solution.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is a checked RUP at `Off`, and the propagator is the
same with proofs on or off. The deliberately unfiled bare-unit defect of
`SmartTable` and `Circuit`'s SCC propagator does not occur here. Their bare
units drop a reason the clause needs; `Dag`'s one bare unit, the self loop,
holds in every solution.

### Known limitations

- **Through MiniZinc, `dag` over an empty node set makes the model
  unsatisfiable** (#1303).
- **It disagrees with MiniZinc's default decomposition on solution counts,
  deliberately**: a selected edge may not leave an unselected node here. Post
  `subgraph` alongside to make the two agree.
- **Its proofs get expensive on graphs with large strongly connected
  components**, sparse ones included: the OPB costs nodes × (nodes + edges)
  per component, 52 MB for one 400-node cycle. With many small cyclic
  components, it is the proof model's setup that grows instead.
- **It repeats work on every call**, including on edges that cannot close a
  cycle. On large graphs one call costs time proportional to nodes times heads,
  and installing it costs time quadratic in nodes plus edges.
- **Repeated variables weaken it**, without losing solutions.

### Next steps

1. **Guard the empty node set in `fzn_dag.mzn`.** One line,
   `if length(ns) = 0 then true else ... endif`, as the sibling files do, and a
   `minizinc/tests/` case. Trivial; it fixes a wrong answer. #1303, which
   also covers the four-argument `subgraph`. The same guard must not go into
   the rooted families' `_enum` overrides, whose empty case is genuinely
   unsatisfiable; see [Robustness and limits](#robustness-and-limits).
2. **Stop the per-call rebuild doing useless work.** Skip edges between input
   components in the candidates and the searches, keep the scratch buffers
   between calls, and replace the per-head clears with a generation stamp. Small.
   The first two are measured: 29.0% of the instructions on `25_04`, same tree.
   The third removes the Θ(n)-per-head cost on large graphs. #1310. The
   reason paths cannot change: a node outside the head's component can never
   lead back into it, so the depth-first search finds the in-component nodes in
   the same order with the same `came_from`. The fact-check found the first
   two changes' proofs byte-identical to the shipped ones on three
   maximum-acyclic-subgraph runs. Also size `define_proof_model`'s
   per-component vectors by the component, or index them by position in it,
   rather than by the whole graph's node count.
3. **Make `install_returning_id`'s scope linear.** An engine change, not this
   family's, and it affects every large-scope propagator. Both `contains`
   loops have to go, the scope's and the constraint scope's. #1309.
4. **Claim idempotence, and disable once every edge is fixed.** Both look safe
   on distinct variables, and the claim checker found no counterexample. The
   engine already drops the claim when positions alias. Small,
   and worth measuring before doing.
5. **Port a `maximum-dag` instance into a test, and add a test with views and
   one with the cycle rule's conflict form.** The two probes in rules 1 and 5
   could become mutation lanes, since their fixtures took work to build. Small.
6. **A `--variant`-style switch to the decomposition**, as `hitori` has for
   connectivity, would make the propagator-against-decomposition comparison
   one binary rather than two `mznlib` directories. Small.

## Prior art

Acyclicity as a constraint has a long history outside proof logging. Dooms,
Deville and Dupont's CP(Graph) (CP 2005) gives graph variables with
constraints over them. Gebser, Janhunen and Rintanen (*SAT Modulo Graphs:
Acyclicity*, JELIA 2014) build acyclicity into a SAT solver and compare that
with encoding it. Chuffed ships a native `dag`, which
also requires weak connectivity, as measured above. The propagation here is
the textbook one: an edge goes when the selected edges already reach its tail
from its head. Generalised arc consistency follows from downward closure,
which this audit argues and checks by brute force rather than citing.

As far as this audit knows, no published work certifies acyclicity in a
pseudo-Boolean proof system. The encoding is this solver's (#791): it spreads
the walk length over a flag per level, as `Reachable`'s unfolding spreads a
distance, so that every inference is one RUP. Restricting it to the input's
strongly connected components is also this solver's. The nearest published
relative is the transitive-closure-by-squaring encoding that the Glasgow
Subgraph Solver uses to certify connected maximum common subgraph (Gocht,
McBride, McCreesh, Nordström, Prosser and Trimble, CP 2020), which
`connectivity-proofs.md` discusses.

## Further reading

- [`connectivity-proofs.md`](../connectivity-proofs.md), "Acyclicity: the same
  unfolding, without a root": why the stdlib's distance labelling cannot be
  RUP, the encoding, the restriction to components, the pre-implementation
  checks against hand-written encodings, and #918's comparison against the
  decomposition (8 and 12 nodes with proofs, the corpus without). Its figures
  are #918's, not re-taken here, except the one under
  [CPU performance](#cpu-performance). Three details do not match this
  audit. It says the `dag_mutation_*` lanes keep "the first two" of its four
  unsound variants honest, which would be a missing path edge and a flipped
  conclusion; the lanes are a missing path edge and a missing subgraph
  endpoint. Its `maximum-dag` times do not reproduce, though its node counts
  do. And its dense table's 18,288 rows for a 20-node, 380-edge component are
  more than the constraint alone writes (16,781): see
  [OPB encoding](#opb-encoding).
- [`reachable.md`](reachable.md): the rooted unfolding this is built from.
- [`minizinc.md`](../minizinc.md): the divergence from the decomposition and
  what it means for testing.
- [`justification-techniques.md`](../justification-techniques.md):
  Theorem 2.6, the reified-row step behind rules 1 and 2.
