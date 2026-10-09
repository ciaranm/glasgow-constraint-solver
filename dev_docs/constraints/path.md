# `Path`: the selected subgraph is a simple path from `start` to `end`

> **Maturity** production ·
> **Audited** 2026-10-09 at `86caad24` ·
> **Open issues** none was open against this family before the audit. Filed
> by this audit: #1313 (the missing degree lower bound, which is worth 33 times
> fewer search nodes on a grid enumeration) and #1305 (an empty node set gives
> `=====ERROR=====` from MiniZinc's `int` spelling where every reference solver
> says unsatisfiable; the same issue covers `reachable` and `tree`). #1303 is a
> different defect with the opposite answer: a satisfiable empty `dag` or
> four-argument `subgraph` that the overrides flatten to a wrong
> `UNSATISFIABLE`. Also touching this family: #1309 (the engine's quadratic
> install) and #1316 (the directed forcing `DPath` inherits). The rest of what
> it would change is
> small and is under [Next steps](#next-steps). Already open and
> touching this family: #868 (cross-solver comparisons; this document gives one,
> by hand). Tracked under #871.

`Path(edges, start, end, ns, es)` and `DPath(...)` are MiniZinc's `path` and
`dpath`. Over a fixed graph with a 0/1 variable per node (`ns`) and per edge
(`es`), they say that the selected nodes and edges form one simple path from
`start` to `end`. `Path` may follow an edge either way, and `DPath` only from
`edges[e].first` to `edges[e].second`. Both are a **decomposition with rows of
their own**. `prepare()` installs a [`Reachable`](reachable.md) child (or
`DReachable`, for `DPath`) rooted at `start`, a [`LinearEquality`](linear.md)
child for `Σ es = Σ ns − 1`, and a handful of counting rows: degree bounds, the
two endpoint conditions, and "the end is selected". It enforces those rows with
one propagator of its own, written in `gcs/constraints/innards/graph_rules.hh`,
which it shares with `Tree` and `DTree`. Everything to do with connectivity
(the breadth-first unfolding, cut-vertex and bridge forcing, the largest share
of the proof and of the checking time) belongs to the reachability child and is
documented in [`reachable.md`](reachable.md). This document covers the counting
rows, their propagator, and how the three parts fit together.

Three things to know before touching it.

- **It is sound, verifies, and is far from GAC.** There were no unsound
  prunings and no wrong solution counts in 28,000 random root checks with full
  enumerations at seed 1, nor in all seven modes again at seed 2 in an
  independent re-run, and all 1,200 random proofs verify. The one wrong answer is an
  empty node set, which errors instead of being unsatisfiable (#1305). But no variable kind is
  GAC. The largest gap is the **degree lower bound**: nothing says that a
  selected node which is not an end needs two selected edges (one in and one
  out, directed). Adding that bound as redundant linear rows cuts the
  enumeration of the 8,512 corner-to-corner paths on a 5 × 5 grid from 887,711
  search nodes to 26,481, and 31.0 s to 1.27 s. Finding a first directed path
  across a 6 × 6 grid drops from 29.7 s to 0.56 s. This is #1313.
- **Its OPB is the reachability unfolding, and its own rows are noise beside
  it.** The rows this class writes number at most `5n`, against
  `2(n + (n − 1)(A + n))` flag-definition rows for the unfolding, where `A` is
  the number of arcs. On a 10 × 10 grid that is 500 rows (38 KB) against 91,280
  rows (9.36 MB). In the proof, its assertions are 26 to 38% of the count and
  14 to 16% of the bytes. They cost 2 to 3% of VeriPB's checking time on the
  4 × 4 grids (about 8% for `DPath` in an independent re-run, by mean), against
  51 to 59% for the reachability child's.
- **The cardinality row is implied, so the OPB is not strictly definitional.**
  Reachability from `start`, the degree bounds and "the end is selected"
  already pin the solutions down, for both spellings: brute force over
  2,754,728 assignments finds no difference with or without the row. It stays
  in the model, rarely prunes (0.2% of its calls are effectful on the grid
  benchmark), and is exactly the lemma a degree-lower-bound derivation would
  need.

Probe paths in this document are relative to `tmp/fd-graph/path/` unless they
begin with `tmp/`. Those under `tmp/fd-graph/factcheck/path/` and
`tmp/fd-graph/factcheck2/path/` are from two independent re-checks of this
audit, and each figure cited from them was reproduced.

## What it is

### Semantics

`Path(edges, start, end, ns, es)`: nodes are numbered `0 .. n − 1` with
`n = |ns|`, and `edges[e] = (u, v)`, with `es[e]` its selector. The constraint
holds exactly when:

- `ns[start] = ns[end] = 1`;
- every selected edge has both endpoints selected;
- walking from `start` along selected edges (either way for `Path`, forwards
  for `DPath`) never branches and never revisits a node, ends at `end`, and on
  the way visits every selected node and uses every selected edge.

That is `path_test.cc`'s own oracle, written as a walk so that it is
independent of the degree counting that is posted. `start = end` means the path
is that one node and no edges.

- **Empty `ns`**: `InvalidProblemDefinitionException` ("Path needs at least one
  node"). MiniZinc's reading is that the model is unsatisfiable, so the `int`
  spelling `path(0, 0, …)` prints `=====ERROR=====` where Gecode prints
  `=====UNSATISFIABLE=====`, on both MiniZinc versions. So do `dpath(0, 0, …)`,
  `bounded_path(0, 0, …)` and `bounded_dpath(0, 0, …)`
  (`mzn/tests/{p,d,bp,bdp}_empty_int.mzn`). This is #1305. The `enum` spelling reaches `UNSATISFIABLE` only because its
  override's `min(index_set(ns))` is undefined and becomes `false`. The message
  says `Path` for `DPath` too, since both throw from `PathBase::prepare`. The same goes for an edge count unequal to `|es|`, an
  edge endpoint `≥ n`, and a node or edge variable whose bounds are not inside
  `0..1` (`path.cc:37–51`).
- **Endpoints outside the numbering** are not an error. `prepare()` defines
  `end`'s bounds to be `0 .. n − 1` (`path.cc:58–59`), and the reachability
  child does the same for `start`. An endpoint with no node value in its domain
  makes the problem unsatisfiable at the root, and the proof says so
  (`degen.cc`: `start ∈ 5..6` and `end ∈ −3..−1`, both `s VERIFIED
  UNSATISFIABLE`). MiniZinc's reading is the same, since `ns[s]` with `s`
  outside the index set is false.
- **Self loops and parallel edges** are accepted. A path can never use a self
  loop, and it can use at most one of a set of parallel edges. Undirected, a
  self loop counts twice towards its node's degree (`path.cc:114–120`).
- **Start and end** may be the same variable, constants, or views; see
  [Variable kinds and views](#variable-kinds-and-views).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Path` | ✓ `fzn_path` (`_int` and `_enum`) → `glasgow_path`[^mznshift] | n/a | n/a[^gcspy] | ✓ `path` | also reached by `bounded_path`[^bounded] |
| `DPath` | ✓ `fzn_dpath` (`_int` and `_enum`) → `glasgow_dpath`[^mznshift] | n/a | n/a[^gcspy] | ✓ `dpath` | also reached by `bounded_dpath`[^bounded] |

[^mznshift]: `minizinc/mznlib/fzn_{d,}path_{int,enum}.mzn` make the numbering
    zero-based. They subtract `1` (the `int` spelling) or `min(index_set(ns))`
    (the `enum` spelling) from `from` and `to`, which are parameters, and from
    `s` and `t`, which are **variables**. So the closing remark of #803, that
    the graph family "shifts parameters, which costs nothing", is not quite
    right for the endpoints (nor for `reachable`'s and `tree`'s root). `s − 1`
    flattens to a two-term `int_lin_eq` defining a fresh variable, and
    `fzn_glasgow.cc`'s two-variable recovery posts it as `Equals` with a view,
    which is domain consistent. Holes therefore cross in both directions and
    nothing is lost beyond one variable and one `Equals` per endpoint.
    MiniZinc's `fzn_path_reif` and `fzn_dpath_reif` `abort`.

[^gcspy]: As `frontend-support-matrix.md` has it. `gcspy` binds nothing in this
    family.

[^bounded]: The stdlib defines `bounded_path` and `bounded_dpath` as the path
    plus a weighted sum, in both spellings, on 2.9.7 and 2.10.1, so they reach
    `glasgow_path` and `glasgow_dpath`. This was checked by the builtin
    appearing in the flattened model (`mzn/tests/bp_*.mzn`, `bdp_*.mzn`).

**Differential check, every route.** The audit ran 16 MiniZinc models, each on
both MiniZinc 2.9.7 and 2.10.1, through `fzn-glasgow`, Gecode 6.3.0/6.4.0 with
its own globals, and Gecode with `-G std`. Two checks per run. First, the
solution sets, projected to `s`, `t`, `ns`, `es` (`tmp/fd-graph/path/mzn/diff.sh`).
Second, each output's status marker: `==========` (search complete),
`=====UNSATISFIABLE=====` or `=====ERROR=====`. `diff.sh` itself compares only
solutions and the `UNSATISFIABLE` line, so a run that errored or was cut off
after printing every solution would have passed it. The marker check was run
on the audit's own outputs, and again independently over all 20 models plus
the repository's `boundeddpathtest.mzn` on both versions
(`tmp/fd-graph/factcheck/path/mzn/`, `tmp/fd-graph/factcheck2/path/mzn/`). `boundeddpathtest.mzn` optimises, so it
is not counted below. The models were:

- the `int` spelling, with a self loop and a parallel edge;
- the `enum` spelling with nodes `3..7` **and** edges `0..6`;
- a real `enum` node type;
- endpoints declared wider than `1..N` (`var −1..6`);
- `start` and `end` the same variable;
- `bounded_path` and `bounded_dpath` in both spellings;
- the repository's own `pathtest.mzn` and `dpathtest.mzn`;

each for `path` and `dpath` where it applies. On every one of these 16, all
three solvers' runs are complete and their solution sets agree, on both
versions, from 4 to 109 solutions. The one disagreement the
audit found is the empty node set: `path` and `dpath` in each spelling with no
nodes, and `bounded_path` and `bounded_dpath`. The `int` spelling gives `=====ERROR=====` against
both Gecodes' `UNSATISFIABLE` (#1305), and the `enum` spelling is
`UNSATISFIABLE` everywhere. Proofs from three of the 16 verify through
`fzn-glasgow --prove`. The `.scp` check below compares solution sets only, not
completeness. For the `.scp` route, six `.scp` files written by hand to mirror the
`int`-spelling models (no views) give the same solution sets under
`glasgow_scp_solver --all` (`tmp/fd-graph/path/scproute/mk.py`). There is no
XCSP3 graph-path constraint, and `gcspy` has no binding.

### Options

`None.` There is no consistency tag. There is also no way to pass `Reachable`'s
`with_cut_forcing()` through, so the child always forces cut vertices and
bridges. For `DPath` that means the directed forcing, which is
[`reachable.md`](reachable.md)'s dearest rule (one search per candidate root
per node and per edge, on every call; #1316). The audit's A/B, made by linking a modified `path.cc`
ahead of the library, says the forcing is load-bearing here: see [CPU
performance](#cpu-performance).

### Variable kinds and views

`ns` and `es` take any variable kind whose bounds lie in `0..1` when the
problem is prepared, including constants. `start` and `end` take plain
variables, constants and views of either sign, at any width the solver accepts.

The proof handles all of these. The counting rows read `start` and `end` only
through equality literals `start = v`, which exist for views. All eight shapes
of `views.cc` verify, with `Path` and `DPath`: offset and negated views, the
same view for both ends, and a constant against a view. Endpoints declared over
`±(2⁶⁰ − 1)` give the same 26 and 12 solutions, the same search nodes, and
verifying proofs as endpoints declared over `−3..3`, in about 7 ms (`wide.cc`).

**Aliasing** is handled rather than rejected. It covers repeated node or edge
variables, and a node sharing its variable with an edge. 3,000 random
instances per spelling, with `k` underlying Booleans shared at random among
the `n + m` positions, give no wrong solution count, and 300 of their proofs
verify (`alias/aliascheck.cc`). `start` and `end` being one variable is also
correct, and propagates exactly as two variables constrained equal do; see
[Robustness and limits](#robustness-and-limits).

### Reification

`None.` MiniZinc's `_reif` forms `abort`, and no model in the corpus would want
one.

### Relation to other families

- **Decomposes into it:** MiniZinc's `bounded_path` and `bounded_dpath`, via
  the stdlib. Nothing inside the solver.
- **Child constraints:** a `Reachable` (`Path`) or `DReachable` (`DPath`) from
  `start` (`path.cc:64–73`), and a `LinearEquality` `Σ es − Σ ns = −1`
  (`path.cc:75–82`). Both carry this constraint's ID (see #449 for why they
  must), so their rows, flags and assertions are named after the `Path`. They
  can share the ID because their roles never collide. Reachability uses `sgf`,
  `sgt`, `rootin`, `root1le`, `root1ge` and `reached`; the linear equality uses
  `le` and `ge`; this class uses the role names under [Labels](#labels). A
  second linear child would collide with the first, which is why the counting
  rules are rows of this class's own and not more children (`constraints.md`,
  "a ceiling on how many children one constraint can install").
- **Shares code:** `gcs/constraints/innards/graph_rules.{hh,cc}`, with
  [`tree.md`](tree.md)'s `DTree`, and with nothing else (its only callers are
  `path.cc` and `tree.cc`). `Path` is the caller that exercises all of it: both
  rule kinds, conditional rows, two-condition rows and rows with limit 0.
  `DTree` uses only the unconditional `AtMost` (`indeg`). So the rules are
  catalogued here, and `tree.md` owns `DTree`'s use of them. A change to
  `graph_rules::propagate` is a change to both.
- **Circuit:** no shared code and no shared encoding. `Circuit` and `SubCircuit`
  ([`circuit.md`](circuit.md)) work over successor variables with
  `AllDifferent` and their own prevent and SCC propagators. `Path` works over
  node and edge selectors with a reachability unfolding. A Hamiltonian path and
  a circuit are close in meaning, but neither family posts the other, and no
  helper crosses between them.
- **Presolvers:** none reads it.
- **Reachable only from a frontend?** No. The C++ API and the `.scp` reader post
  it directly.
- **Merge question:** none is open in the family list. Settled as separate
  documents for `path`, `tree` and `reachable`, each owning its own posted
  classes, with `graph_rules` catalogued here.

## The proof model

### OPB encoding

Three blocks, all under this constraint's ID `id`.

```
-- from the Reachable / DReachable child (reachable.md; arcs: 2 per edge for Path, 1 for DPath)
es[e] → ns[from(e)],  es[e] → ns[to(e)]                      sgf<e>, sgt<e>
root[v] ⇔ start = v;  Σ_v root[v] = 1;  root[v] → ns[v]      x[id][v][root], root1le / root1ge, rootin<v>
arc[a][k] ⇔ es[edge(a)] ∧ reach[from(a)][k−1]                x[id][a_k][arc],  k = 1 .. n−1
reach[v][k] ⇔ reach[v][k−1] ∨ ⋁_{a into v} arc[a][k]         x[id][v_k][reach]
ns[v] → reach[v][n−1]                                         reached<v>

-- from the LinearEquality child
Σ_e es[e] − Σ_v ns[v] = −1                                     le, ge

-- this class's own rows (graph_rules::define), per node v
end = v → ns[v]                                                endin<v>          (every v)
Path, for v with an incident edge (inc(v) lists a self loop twice):
    Σ inc(v) ≤ 2                                               deg<v>
    start = v → Σ inc(v) ≤ 1                                   startdeg<v>
    end = v   → Σ inc(v) ≤ 1                                   enddeg<v>
    start = v ∧ end = v → Σ inc(v) ≤ 0                         loop<v>
DPath, for v with an entering edge:                  for v with a leaving edge:
    Σ in(v) ≤ 1               indeg<v>                   Σ out(v) ≤ 1             outdeg<v>
    start = v → Σ in(v) ≤ 0   startin<v>                 end = v → Σ out(v) ≤ 0   endout<v>

-- define_bound, only when end is declared wider than the numbering (unlabelled)
end ≥ 0,  end ≤ n − 1
```

A half-reified row takes the usual big-M form. Over three nodes,
`loop1` is `−es0 − es1 + 2·[start ≠ 1] + 2·[end ≠ 1] ≥ 0`
(`assert/u_loop_backward_off.opb`).

**Is it definitional?** Every row this class writes is part of the meaning.
`endin` is what puts the end on the path, and the degree rows are what make
the reached subgraph a path rather than a tree. The **cardinality row is not**.
It is implied by the rest, for both spellings. Undirected, a connected
subgraph with every degree at most two and a node of degree at most one (the
start) is a path. Directed, in-degree at most one with nothing entering the
start and everything reached from it makes each selected node other than the
start have exactly one incoming edge, which is the count already. Checked by
brute force: on 300 random multigraphs with up to five nodes and six edges
(loops and parallel edges included), over every `start`, `end`, `ns` and `es`,
the rows without the count accept exactly the walk oracle's solutions, and so
do the rows with it: 2,754,728 assignments, no mismatch
(`tmp/fd-graph/path/redundancy/red.py`, seed 1). The class documentation's
argument, "a connected subgraph with one fewer edge than nodes is a tree", is
correct but does not need the count. It is a consequence row in the model. It
is benign, and it is the lemma a degree-lower-bound proof would use (see
[Next steps](#next-steps)).

Some rows are also **tautologies**. `deg<v>` is written for every node with an
incident edge, including those with at most two edge slots, and `startdeg`,
`enddeg`, `indeg` and `outdeg` likewise at their limits. An example is
`deg0 −es0 ≥ −2` at a node with one edge. They cost a row and a per-call scan
each, and nothing else.

**Size.** This class writes `n` `endin` rows, plus four rows per node with an
incident edge (undirected) or two per node with an entering edge and two per
node with a leaving edge (directed). That is at most `5n` rows and `Θ(n + m)`
terms, independent of every domain width. The reachability child writes
`2(n + (n − 1)(A + n))` flag-definition rows, with `A = 2m` arcs for `Path`
and `A = m` for `DPath`: `Θ(n(n + m))`. That term is what makes the family
expensive at scale. Measured on `k × k` grids with `start` the corner `0` and
`end` the opposite corner, first solution only (`sizes/sizes.cc`,
`opbsplit.sh`; `86caad24`, 2026-10-09):

| grid | `Path` own rows | own bytes | unfolding flag rows | flag bytes | reachability rows | linear | whole `.opb` |
|---|--:|--:|--:|--:|--:|--:|--:|
| 3 × 3 | 45 | 2,685 | 546 | 49,447 | 44 | 2 rows | 56,189 B |
| 4 × 4 | 80 | 5,235 | 1,952 | 185,462 | 82 | 2 | 198,452 B |
| 5 × 5 | 125 | 8,599 | 5,090 | 495,547 | 132 | 2 | 516,769 B |
| 6 × 6 | 180 | 12,771 | 10,992 | 1,088,162 | 194 | 2 | 1,119,584 B |
| 8 × 8 | 320 | 23,635 | 36,416 | 3,687,034 | 354 | 2 | 3,744,954 B |
| 10 × 10 | 500 | 38,179 | 91,280 | 9,357,476 | 562 | 2 | 9,450,661 B |

`DPath` on the bidirected grid (both arcs of every grid edge, so the same `A`)
gives the same own-row counts (45, 80, 125, 180) and the same flag counts. Its
reachability rows grow by the doubled `sgf` / `sgt` pairs (68 against 44 at
3 × 3).

### Labels

The own rows are labelled `c[id][role]`, with `role` one of `endin<v>`,
`deg<v>`, `startdeg<v>`, `enddeg<v>`, `loop<v>`, `indeg<v>`, `startin<v>`,
`outdeg<v>` and `endout<v>`. **No justification cites a label.** Every
inference is a plain RUP with no antecedent list: `graph_rules::propagate`
justifies with `JustifyUsingRUP{hint}` (`graph_rules.hh:88`), and nothing
passes it a line. The row has to be in the OPB, since the RUP depends on it,
but no proof line names its label. That holds for `DTree`'s `indeg<v>` rows
too, which go through the same call. What the labels do is keep
three role namespaces apart under one ID: `ProofModel::claim_labels` throws on
a repeated label, and the parent shares its ID with both children. The
`define_bound` rows are unlabelled.

### Cake conformity

There is no counterpart. `cake_pb_cp` reports `unsupported constraint: path`,
and there is no `dpath` either. No chain case exists, and the family is
cake-blocked rather than unconformed. The `.scp` term,
`(id path (from…) (to…) start end (ns…) (es…))` and the same with `dpath`, is
the solver's own. It round-trips through `read_scp` (`scp_reader_test.cc`: a
`path` and a `dpath` enumeration of two solutions each, and a write → read →
write identity over all five graph classes), and the six hand-written `.scp`
files above agree with Gecode.

**A `.scp` from a MiniZinc path model cannot be read back at all** whenever
the endpoints are variables. The endpoint shift of the MiniZinc overrides arrives as
`(_2 equals t (X_INTRODUCED_35_ + 3))`, and neither `read_scp` nor cake parses
a view term ("expected an atom, found a list"). This is the known exclusion
#432 records ("views are excluded throughout"). It is generic, not this
family's, and it would stop a chain before cake even if cake had a `path`
keyword.

### Proof-time state

- **At the root:** nothing from this class's propagator. When `end` is declared
  wider than the numbering, the two `define_bound` initialisers assert its
  bounds, as `a 1 i[t][ge0] >= 1::initial_bound:;` with no constraint ID
  (`wide/wideinf.cc`). The reachability child's root work is its own.
- **During search:** one line per inference of this class: a RUP at `Off`, an
  `a` line at the assertion levels. There are no lemmas, nothing at
  `ProofLevel::Temporary`, and nothing deleted.
- **Naming, the load-bearing part.** One `Path` produces assertions under
  **three** hint names, all carrying its own `constraint_id`:
  `::path:((constraint_id _N))` for the counting rules (both spellings share
  `hints::Path`), `::reachable:((constraint_id _N))` for the child's rules
  (both spellings share `hints::Reachable`), and
  `::linear_equality:((constraint_id _N))` for the count. The `.scp` says only
  `(_N path …)`. An external justifier that meets a `reachable` hint on a
  `path` constraint has to know that `path` and `dpath` post a reachability
  child under their own ID, rooted at `start`, together with its rows
  (`sgf`, `rootin`, `reached`, …) and flags (`x[_N][…][root|arc|reach]`). This
  document and [`reachable.md`](reachable.md) are where that is written down.
- **Auxiliaries:** none of this class's own. The reachability flags are
  extension variables written into the OPB (`create_proof_flag_fully_reifying`),
  fully reified, so unit propagation determines them on a solution.
- **Proof-only vectors:** none.

## The implementation

### Initialisation and global data

`prepare()` does everything once (`path.cc:35–141`):

1. validates the arguments;
2. defines `end`'s bounds;
3. installs the reachability child (whose own `prepare()` defines `start`'s
   bounds, and whose `define_proof_model` writes the unfolding);
4. installs the linear child;
5. builds the rule vector, in `O(n + m)`.

It returns `true` (there is always at least the `endin` rows), so
`define_proof_model` writes the rows and `install_propagators` installs one
propagator. There is no initialiser of this class's own beyond `define_bound`.
The root cost that dominates with proofs on is the child's `Θ(n(n + m))`
unfolding. With proofs off, the root cost is quadratic in the trigger count.
`Propagators::install_returning_id` deduplicates each propagator's scope with a
linear `contains` per trigger (`propagators.cc:724–748`), and then unions it
into the constraint's scope with another linear `contains` per scope variable
(`:765–769`). Fixing the first loop alone leaves the install quadratic. This
class's propagator has about eight trigger entries per edge
([below](#propagator-inventory)), so its install is
`Θ(|triggers| · |scope|)`. This engine defect is #1309.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| `graph_rules` propagator (stats type `path` / `dpath`) | `on_change` on every variable a rule reads: the `ns` and `es` named by rules, `start`, `end`, each once per rule occurrence | derived: every `ns` and `es` (vacuously, being `{0, 1}`) and `start`, `end`. **Over-reported** on the endpoints: truthfully nothing, since the rules read them only through `= v` literals | 2–7 | always | never claims | never |
| `define_bound` initialisers, `end ≥ 0` and `end ≤ n − 1` | once, at the root | n/a | 1 | `end` declared outside `0 .. n − 1` | n/a | n/a |
| `Reachable` / `DReachable` child | `on_change`: `ns`, `es`, `start` | derived: every `ns` and `es` (vacuously) and `start`; truthful for `start`, whose values it walks | [`reachable.md`](reachable.md) | always, cut forcing on | never claims | never |
| `LinearEquality` child (BC arm) | `on_bounds`: `ns`, `es` | derived: nothing | [`linear.md`](linear.md) | always | as there | as there |

**Why `Holes affect` over-reports on the endpoints.** A rule condition is a
literal `start = v` or `end = v`. `conditions()` treats a definitely false
condition as "this rule cannot fire" and skips the rule
(`graph_rules.hh:93–102`). Every inference needs its conditions definitely true
(forwards), or all but one definitely true and that one undecided (backwards).
Removing a value strictly inside a variable's bounds can make `x = v` false. It
can never make it true, because that needs `x` fixed, and an interior removal
leaves both bounds in place. So a hole only ever switches rules off, and never
gives this propagator an inference it could not already make. `end` is read by
nothing else after the root, so a `Path` over-reports `end` as hole-sensitive.
That direction costs only efficiency: another constraint's optional interior
pruning on `end` stays on when it need not. `start` is genuinely hole-sensitive
through the reachability child, which reads every remaining candidate root.

**Duplicates in the trigger list.** `graph_rules::variables_of()` returns one
entry per rule occurrence, and `install()` does not deduplicate wake entries
(its wake loop, `propagators.cc:785–786`, calls `trigger_on_change` once per
entry, `1479–1493`). So undirected, each edge selector sits in the
wake list eight times (four rules at each endpoint), `end` about `3n` times and
`start` about `2n`. Each event walks those entries. The same repetition makes
`positions_alias()` true, so any `Path` whose trigger list repeats a
non-constant variable adds one to the solve's `idempotence downgrades`
statistic, although the propagator never claims idempotence. Constants are
skipped, so a single edge with a constant selector and constant ends adds
none, while a variable selector or a variable start adds one
(`tmp/fd-graph/factcheck2/path/examples/idem.cc`).

**Self-disabling.** It never disables itself; it returns `Enable` from every
call.

**Idempotence.** Not claimed, and one pass is not a fixpoint. The rules run in
order: all `endin` first, then the degree rows node by node. A backward
inference late in the list can fix `end` (for example, `enddeg<v>` removing the
last value but one), and `endin` for the surviving value then waits for the
next call. Returning `Enable` makes the framework requeue it, so the fixpoint
is reached across calls.

### Mutable state and incrementality

`None`, in this class. The rules are copied into the propagator's closure, and
each call **rescans every rule**. Undirected that is at most `8m` edge-selector
reads, `n` node-selector reads and `5n` condition tests. A rule whose condition
is definitely false is skipped before its variables are read
(`graph_rules.hh:108–109`, `147–148`), so with both ends constants, as in the
benchmarks below, a call reads `2m + deg(start) + deg(end)` selectors (84 on
the 5 × 5 grid), one node selector and about `4n` conditions. It does that
whatever changed, so a call costs `Θ(n + m)`, through the unconditional degree
rows, even when one edge moved. Measured: 6.1 µs a call on the 5 × 5 grid and 9.2 µs
on the bidirected 6 × 6 grid. That is 31% and 18% of propagation time in the
two benchmarks below. Indexing the rules by variable, and visiting only the
rules a changed variable occurs in, would make a call proportional to what
changed. The children's state is theirs.

### Interior values and optional pruning

**Offers.** `None.`

**Observes.** From this class: **nothing**, truthfully, though the triggers
declare `start` and `end` (see the [inventory](#propagator-inventory)). The
node and edge variables are `{0, 1}`, so they have no interior. From the
children: holes in `start`, because the reachability child walks the candidate
roots. So a `Path` is a genuine reason to keep another constraint's interior
pruning on `start`, and an overstated one for `end`.

### Robustness and limits

**Unbounded domains.** Fine. The endpoints are trimmed to `0 .. n − 1` at the
root by `define_bound` rows, and nothing else in the family has a width. The
probe at `±(2⁶⁰ − 1)` is under [Variable kinds and
views](#variable-kinds-and-views).

**Negative values and zero.** Node `0` is a node. A negative endpoint value is
outside the numbering and is removed at the root. `path_test`'s
`path3_wide_ends` declares `start ∈ −1..3`.

**Degenerate shapes.**

- *One node, no edges:* one solution (`path_test`'s `single`).
- *Empty `ns`, a short `es`, a bad endpoint, a node variable over `0..2`:*
  `InvalidProblemDefinitionException`, as under [Semantics](#semantics). Only
  the first is a well-formed model, unsatisfiable rather than malformed
  (#1305).
- *Only a self loop:* one solution, the node alone, with the loop unselected.
- *`start` and `end` the same variable:* correct (`p_same.mzn` and
  `d_same.mzn` agree with Gecode; `pathcheck` `alias` mode finds no count
  mismatch in 2,000 trials per spelling), and **no weaker than two variables
  constrained equal**. An `aliaseq` mode posts the same instances with two
  endpoint variables over the same domain plus `Equals{s, t}`, and every
  counter matches the one-variable run at both seeds: 162 and 148 of 825 and
  829 unsatisfiable undirected roots missed, 472 and 471 non-GAC instances, and
  6 and 5 missed directed (`tmp/fd-graph/factcheck/path/strength/pathcheck2.cc`).
  Root domains, solutions and search trees are identical instance by instance
  (`tmp/fd-graph/factcheck2/path/alias/aliascmp.cc`). What both lose is the
  `loop<v>` rule backwards. With both ends open it has two undecided
  conditions, whether they are one literal twice or two literals, and needs
  exactly one (`graph_rules.hh:137`). For example, a single edge `(0, 4)` fixed
  in, with `start = end` over `{0, 4}`, is unsatisfiable, and the root does not
  refute it with one variable or two
  (`tmp/fd-graph/factcheck2/path/examples/ex2.cc`, `same_single_edge_es1`). The weakness belongs to
  instances where the ends may coincide, not to aliasing. With one variable,
  the duplicated literal appears twice in the assertion,
  `a 1 ~i[start][eq2] 1 ~i[start][eq2] 1 ~i[es1][b0] >= 1`, which VeriPB
  accepts. Deduplicating a row's open conditions would let one variable do
  better than two (next step 6).
- *`start` passed as a node variable:* accepted and correct (`degen.cc`:
  four and three solutions, proofs verify).
- *Two `Path`s over the same selectors:* fine. Each has its own ID and labels
  (`degen.cc`, `two_paths_same_vars`).

**Overflow.** Nothing to guard. The only arithmetic is node numbers converted
to `Integer` and rule counts compared with limits of 0 to 2.

**Size.** With proofs on, the reachability child's unfolding,
`Θ(n(n + m))` OPB rows, is what limits the graph size. At `n = 1000` and
`m = 4000` (undirected) it is about 18 million rows. With proofs off there is
no such limit.

### Interval efficiency

**Fine at any width.** The only variables that can be wide are `start` and
`end`, and they are cut to `n` values at the root.

1. **The propagation side.** `graph_rules::propagate` reaches for no per-value
   iterator. It calls `test_literal` on equality literals and
   `optional_single_value` on `{0, 1}` variables, bounded by the rules, which
   is `Θ(n + m)`. The reachability child does walk the root's values
   (`for_each_value_immutable`), but over a domain already cut to
   `0 .. n − 1`; see [`reachable.md`](reachable.md).
2. **The reason side.** A reason is the true conditions plus the selected edges
   of one rule: at most `limit + 1 + |conds| ≤ 5` literals, except for
   degree-overflow (rule 6), whose reason lists every selected term of the row.
   Never per value.
   Assembling it is **not** guarded on `want_reasons()`. The `ones` list is
   built for every `AtMost` rule whose conditions are not false, on every call, and the reason vectors for
   every firing, with proofs off too. The cost is bounded by the rule size and
   independent of width, and it is part of the per-call cost above.
3. **The proof side.** One line per inference, of at most five literals plus
   the inferred one (rule 6: every selected term of the row). No line is per value, and there is no width gate because none
   is needed.
4. **The audit lane.** Two rows in `gcs/large_domain_audit_test.cc`, `Path` and
   `DPath`, both pinned `NoWidePosition`. Each declares `r, t ∈ 0..2` on a
   three-node path. `start` and `end` **can** be declared wide, and are trimmed
   at the root. The rows vary
   none of a wide endpoint, a holey one, a view, or one variable for both
   ends. The lane is registered as a ctest only under
   `-DGCS_LARGE_DOMAIN_GUARD=ON`, which no CI lane sets (#920). **The fact:**
   in a guarded build (`gcs-fd-small-am1-patch-wt/build-guard`, `c9ceea25`,
   whose `path/`, `graph_rules` and `reachable/` sources are identical to
   `86caad24`'s), endpoints declared over `0..10⁹`, over `±(2⁶⁰ − 1)` and over a
   holey set with those extremes enumerate without tripping the guard: 12 runs,
   `Path` and `DPath`, with and without proofs, all proofs verifying. A control
   `AllDifferent` over four `0..10⁹` variables does trip it (`guard/g.cc`).
   At `86caad24` the rows are pinned `NoWidePosition`. PR #1302 (open) pins
   them `Clean`, with rows that declare the endpoints wide, as the safer
   choice for every index-valued position, and its guarded run trips
   nothing.

## Inference catalogue

Seven rules belong to this class: the `end` bound initialiser and the six
inferences of the `graph_rules` propagator. Every other inference a `Path`
makes belongs to a child: [`reachable.md`](reachable.md)'s rules (root
filtering, unreachable nodes, cut vertices and bridges, subgraph) under the
`reachable` hint, and [`linear.md`](linear.md)'s bounds rules under
`linear_equality`.

Four facts hold for rules 2 to 7.

**Each is one plain RUP against the row its rule wrote** (`JustifyUsingRUP`),
and the content is the reason. The row is a half-reified cardinality bound; the
reason makes its conditions true and names the selected terms, so the
negated conclusion falsifies the row by unit propagation. The licence is the
reified-row consequent of
[`justification-techniques.md`](../justification-techniques.md) (Theorem 2.6),
over a row whose terms are 0/1 literals. The procedure is not published as a
graph rule, but it is the generic one: the rule's row is the whole argument.

**No justification reads `state`.** The reason is built from the state; the
proof line is built from the reason.

**One wire form:** `hints::Path`, `::path:((constraint_id <id>))`, with
`originator` its only field and no subhint, for both spellings. The `.scp`
says which spelling it is, and the role names say which row.

**Assertion shapes were checked against real `a` lines** at
`AssertionLevel::Inferences` on targeted instances (`assert/shapes.cc`), and the
`Off` proofs of the same instances all verify. In the examples, `i[es0][eq1]`
is an edge selector declared over `{1}`; a selector fixed by search appears as
`i[es0][b0]`.

### Rule: end-in-range

- **Infers** — `end ≥ 0` and `end ≤ n − 1`.
- **Fires when** — once, at the root, from the initialisers `define_bound`
  installs when `end` is declared outside the numbering (`path.cc:58–59`).
  `start`'s twin is the reachability child's.
- **Strength** — `bounds(Z)` on `end` for this row: it is exactly the row.
- **Algorithm** — `O(1)`.
- **Why it is true** — the end is a node, and nodes are `0 .. n − 1`.
- **Proof technique** — `RUP`, against the unlabelled row `define_bound` adds
  to the OPB: the row is the conclusion. The row is part of the definition,
  since without it the OPB would accept an `end` that indexes nothing.
- **Reason** — none (`NoReason`).
- **Assertion** — the bound literal alone. Measured, `end` over `−5..9` on three
  nodes: `a 1 i[t][ge0] >= 1::initial_bound:;` and
  `a 1 ~i[t][ge3] >= 1::initial_bound:;`.
- **Hint** — `hints::InitialBound`, the framework's, with **no** constraint ID.
- **Offline reconstructibility** — `offline`: the conclusion is an OPB row.
- **Proof size** — one line per bound, at most two.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: end-selected

- **Infers** — `ns[v] = 1`.
- **Fires when** — `end` is fixed to `v` (`Selected` forwards,
  `graph_rules.hh:150–154`), on any call.
- **Strength** — `partial`: GAC on its own row, `end = v → ns[v]`.
- **Algorithm** — a test of the condition and of `ns[v]`, `O(1)` per row. All
  `n` rows are scanned every call.
- **Why it is true** — the path ends at a selected node.
- **Proof technique** — `RUP` against `endin<v>`.
- **Reason** — `end = v`. Minimal.
- **Assertion** — `ns[v] = 1 ∨ end ≠ v`. Measured: `a 1 i[ns2][b0] 1 ~i[end][eq2]
  >= 1::path:((constraint_id _8));`. If `ns[v]` is already 0, the same line is
  asserted and the backtrack closes the conflict.
- **Hint** — `hints::Path`: `originator`.
- **Offline reconstructibility** — `offline`: the clause names `end = v`, which
  names the row.
- **Proof size** — one line, two literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` There is no mutation lane for this family.

### Rule: unselected-not-end

- **Infers** — `end ≠ v`.
- **Fires when** — `ns[v]` is fixed to 0 and `end = v` is undecided (`Selected`
  backwards, `graph_rules.hh:155–159`).
- **Strength** — `partial`: GAC on its own row, with rule 2.
- **Algorithm** — `O(1)` per row.
- **Why it is true** — an unselected node cannot be the end.
- **Proof technique** — `RUP` against `endin<v>`.
- **Reason** — `ns[v] = 0`. Minimal.
- **Assertion** — `end ≠ v ∨ ns[v] ≠ 0`. Measured (`ns2` declared over `{0}`):
  `a 1 ~i[end][eq2] 1 ~i[ns2][eq0] >= 1::path:((constraint_id _8));`.
- **Hint** — `hints::Path`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line, two literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: degree-full

- **Infers** — every undecided edge selector of the row is 0.
- **Fires when** — an **unconditional** degree row is full: `deg<v>` with two
  incident selections fixed to 1, or `indeg<v>` / `outdeg<v>` with one
  (`graph_rules.hh:133–136`, `open` empty).
- **Strength** — `partial`: GAC on its own row when the row has no repeated
  term.
  **Not GAC** on a row with one: an undirected self loop appears twice in
  `inc(v)`, and aliased selectors repeat too. Every occurrence is collected
  (`graph_rules.hh:116–121`), but the firing test compares only the
  selections already fixed with the limit (`graph_rules.hh:124`), and never
  weighs an undecided term's multiplicity. So a term whose own weight would
  overflow the row stays. With `(0, 1)` fixed in and a self loop at node 1,
  the loop keeps its 1 although selecting it gives `deg1 = 3 > 2`
  (`tmp/fd-graph/factcheck/path/examples/loop.cc`, `deg_full_selfloop`). The
  same holds for an aliased selector (`tmp/fd-graph/factcheck2/path/examples/ex2.cc`,
  `deg_full_aliased`). A `DPath` self loop is listed once in `in(v)` and once
  in `out(v)`, so it is not a repeated term, and is removed at the root
  (`dpath_selfloop`).
- **Algorithm** — one scan of the row's variables, `O(deg(v))`. Every row is
  scanned on every call.
- **Why it is true** — a path node has at most two path edges (undirected), or
  at most one in and one out (directed).
- **Proof technique** — `RUP` against `deg<v>`, `indeg<v>` or `outdeg<v>`.
- **Reason** — the selected selectors, `limit` of them. A self loop fixed to 1
  appears twice. Minimal.
- **Assertion** — `es[e] = 0 ∨ ¬reason`, per pushed edge. Measured, undirected:
  `a 1 ~i[es2][b0] 1 ~i[es0][eq1] 1 ~i[es1][eq1] >= 1::path:((constraint_id _10));`.
  Directed `outdeg`: `a 1 ~i[es1][b0] 1 ~i[es0][eq1] >= 1::path:((constraint_id _9));`.
- **Hint** — `hints::Path`.
- **Offline reconstructibility** — `offline`: the node is the common endpoint of
  the reason's edges, and the limit gives the row.
- **Proof size** — one line per pushed edge, `limit + 1` literals.
- **Gaps** — none in the logging. The strength gap above explains why an
  undirected self loop survives where selecting it would overflow its row. A
  lone self loop at a node that is not an end satisfies `deg<v>` (`2 ≤ 2`), so
  even a GAC degree row would keep it; see [Strength of the
  whole](#strength-of-the-whole).
- **Tightness** — `Not shown.`

### Rule: end-degree-full

- **Infers** — every undecided edge selector of the row is 0.
- **Fires when** — a **conditional** row has all its conditions true and is
  full: `startdeg<v>` / `enddeg<v>` (`start` or `end` fixed to `v`, one incident
  edge selected); `loop<v>` (both fixed to `v`); `startin<v>` / `endout<v>`
  (`start` or `end` fixed to `v`). The last three have limit 0, so they fire
  with nothing selected: fixing `start` to `v` empties `v`'s incoming edges
  for `DPath`, and fixing both ends to `v` empties every incident edge for
  `Path`.
- **Strength** — `partial`: GAC on its own row, given distinct condition
  variables. On a
  row with limit 1 and a repeated term (`startdeg`, `enddeg`) it is not, as
  rule 4. With `start = 0` and edges `(0, 0)`, `(0, 2)`, `(0, 3)`, the self loop
  keeps its 1 although selecting it gives `startdeg0 = 2 > 1`
  (`tmp/fd-graph/factcheck/path/examples/loop.cc`, `startdeg_selfloop`), and an
  aliased selector does the same (`ex2.cc`, `enddeg_aliased`). The limit-0
  rows (`loop`, `startin`, `endout`) stay GAC with repeats, since they fire
  with nothing selected and push every undecided occurrence.
- **Algorithm** — as rule 4.
- **Why it is true** — a path's ends have one path edge each, nothing enters the
  start or leaves the end of a directed path, and a path from a node to itself
  has no edges.
- **Proof technique** — `RUP` against the conditional row; its conditions are in
  the reason, which switches the half-reification on.
- **Reason** — the true conditions, plus the selected selectors. Minimal.
- **Assertion** — `es[e] = 0 ∨ ¬reason`. Measured: `startdeg`,
  `a 1 ~i[es1][b0] 1 ~i[start][eq0] 1 ~i[es0][eq1] >= 1::path:((constraint_id _10));`;
  `startin` (limit 0), `a 1 ~i[es0][b0] 1 ~i[start][eq0] >= 1::path:((constraint_id _10));`;
  `loop`, `a 1 ~i[es0][b0] 1 ~i[start][eq1] 1 ~i[end][eq1] >= 1::path:((constraint_id _8));`.
- **Hint** — `hints::Path`.
- **Offline reconstructibility** — `offline`: the condition literals name the
  node and which end, and the selected edges' count gives the limit.
- **Proof size** — one line per pushed edge, at most three literals.
- **Gaps** — none in the logging; the repeated-term strength gap is rule 4's.
- **Tightness** — `Not shown.`

### Rule: degree-overflow

- **Infers** — a contradiction.
- **Fires when** — any degree row, conditional or not, has all its conditions
  true and more selections fixed to 1 than its limit
  (`graph_rules.hh:131–132`). Search fixes one selector at a time and rule 4
  would have stopped it, so this needs either several selectors fixed between
  two calls of this propagator, for example by the reachability child's cut
  forcing, or a condition becoming true over a row that is already over its
  limit. The second happens when the ends may coincide: `loop<v>` waits with
  two open conditions, and fixing the end makes both true with an edge at `v`
  already selected. With one edge fixed in and the ends one variable (or two
  plus `Equals`), branching on the end alone gives two such contradictions with
  no selector fixed by search (`tmp/fd-graph/factcheck2/path/examples/r6.cc`).
  On the undirected benchmark this is **not** a corner case but the main
  failure route. On the 5 × 5 enumeration, where both ends are constants, this
  propagator ends in a contradiction on 247,393 of its 1,529,855 calls, 57% of
  the 435,344 contradicting propagations. With constant ends, rules 2, 3 and 7
  have nothing to fail on, and an ordinary inference of rules 4 and 5 only
  pushes undecided selectors, so these are rule 6. On the `DPath` 6 × 6 search
  it is 21,011 of 148,103 (14%), and the reachability child has the other 86%
  (`GCS_PROPAGATOR_STATS=time`, `lb/lb.cc`).
- **Strength** — `partial`: with rules 4 and 5, GAC on its own row.
- **Algorithm** — as rule 4.
- **Why it is true** — as rules 4 and 5.
- **Proof technique** — `RUP` against the row.
- **Reason** — the conditions and every selected selector of the row. **Not**
  minimal when the count exceeds the limit by more than one, since any
  `limit + 1` of them would do.
- **Assertion** — `¬reason`, from `contradiction()`. Measured (`start` fixed to
  0, both its edges selected): `a 1 ~i[start][eq0] 1 ~i[es0][eq1] 1 ~i[es1][eq1]
  >= 1::path:((constraint_id _8));`. This is the same clause rule 7 asserts
  when `start = 0` is still open, because there the attempted literal is the
  negation of the missing condition, and `attempted ∨ ¬reason` and `¬(cond ∧
  reason)` are one clause.
- **Hint** — `hints::Path`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line, at most `limit + 1 + |conds|` literals, plus any
  surplus selectors.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: end-excluded-by-degree

- **Infers** — the one undecided condition is false: `start ≠ v` (from
  `startdeg`, `startin`, or `loop` with `end = v` fixed) or `end ≠ v` (from
  `enddeg`, `endout`, or `loop` with `start = v` fixed).
- **Fires when** — a conditional row is over its limit with exactly one
  condition undecided and any others true (`graph_rules.hh:138–141`). For
  example: two edges at `v` selected, so `v` is neither end; an edge into `v`
  selected, so `v` is not `DPath`'s start; an edge at `v` selected with `start
  = v`, so `end ≠ v`. **Not fired** for `loop<v>` while both ends are open,
  since the row then has two open conditions. That holds whether the ends are
  one variable or two; see [Robustness](#robustness-and-limits).
- **Strength** — `partial`: GAC on its own row over distinct condition
  variables. This is the
  only rule that prunes an endpoint's domain from inside this class, one value
  at a time.
- **Algorithm** — as rule 4.
- **Why it is true** — the rows of rule 5 read backwards: a node with too many
  path edges cannot be the end the row is about.
- **Proof technique** — `RUP` against the row; under the negated conclusion
  every condition is true, and the reason's selections overflow it.
- **Reason** — the true conditions and the selected selectors. Minimal when the
  count is exactly `limit + 1`.
- **Assertion** — `cond ≠ ∨ ¬reason`. Measured: `startdeg`,
  `a 1 ~i[start][eq0] 1 ~i[es0][eq1] 1 ~i[es1][eq1] >= 1::path:((constraint_id _10));`;
  `loop` with `start = 0` fixed,
  `a 1 ~i[end][eq0] 1 ~i[start][eq0] 1 ~i[es0][eq1] >= 1::path:((constraint_id _8));`;
  `endout`, `a 1 ~i[end][eq1] 1 ~i[es1][eq1] >= 1::path:((constraint_id _8));`.
- **Hint** — `hints::Path`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line, at most three literals.
- **Gaps** — `None.` A repeated term does no harm here: selections fixed to 1
  are counted with multiplicity.
- **Tightness** — `Not shown.`

### Strength of the whole

Each rule is `partial`, GAC on its own row over distinct condition variables, except
that rules 4 and 5 are not on a row with limit at least 1 and a repeated term:
`deg`, `startdeg` and `enddeg` with an undirected self loop or an aliased
selector, and `indeg` or `outdeg` with an aliased selector. Each
child is `GAC` on its own: [`reachable.md`](reachable.md) claims it for
`Reachable` with cut forcing on, and the count is a unit-coefficient
equality over 0/1 variables. Their conjunction is **`decomposition`**, and the
audit measured how far that is from GAC. It compared the root fixpoint with the
projection of the brute-forced solution set, on random multigraphs with
`n ≤ 5` and `m ≤ 7` (or `n ∈ 4..6`, `m ∈ 3..9`), random fixed selectors, and
random holey endpoint domains over `−1 .. n`. That is 2,000 instances per mode
and spelling at seed 1 (`strength/pathcheck.cc`, 86caad24), and the same seven
modes again at seed 2 in an independent re-run
(`tmp/fd-graph/factcheck/path/strength/out_*_s2.txt`). The ranges below span
both seeds; 939 is that re-run's `DPath` `bigger` count at seed 2:

- **No unsound pruning and no wrong count**, in any mode.
- **Not GAC on any variable kind.** On simple graphs (no loops, no parallel
  edges) with every selector free, seed 1: `Path` leaves unsupported values on
  162 of the 1,779 satisfiable instances, in `ns` on 162, `start` on 101 and
  `es` on 61. `DPath` does so on 280 of 1,745: `ns` 252, `es` 186, `start` 183.
  With fixed selectors and multigraphs the counts rise; for example, `Path`
  `plain` leaves values in `es` on 413 of 1,232.
- **Unsatisfiable roots missed:** 3 to 5 of 768 to 905 in `plain`, 10 to 21 of
  410 to 939 on the larger graphs, none with every selector free, and 148 to 162
  of about 825 with one variable for both ends (undirected; 5 to 6 directed),
  exactly as many as with two endpoint variables plus `Equals`.

The shapes behind the gaps, from the probe's examples:

1. **No degree lower bound.** A selected node that is not an end needs two
   selected edges (in = out = 1 directed), and nothing says so. On the path
   `2 – 1 – 0` (edges `(2, 1)` and `(0, 1)`) with `start = 2` and
   `end ∈ {1, 2}`, node 0 and edge `(0, 1)` keep their 1, though selecting them
   would make 0 an end. This is
   #1313, and the one that costs search; see [CPU
   performance](#cpu-performance).
2. **No coupling of the two ends.** `start = v` needs some candidate end
   reachable from `v`, and nothing checks it. With no edges, `start ∈ {0, 1, 2}`
   and `end ∈ {0, 1}`, `start = 2` stays. The reachability child filters roots
   only against nodes already *fixed* selected, and `end`'s node is not fixed
   until `end` is.
3. **Undirected self loops are never removed for being loops.** A self loop can never be
   on a path, and no row says so on its own. It is removed when its node's
   degree row fills, or when the node is ruled out (`tmp/fd-graph/factcheck/path/examples/ex.cc`,
   `selfloop_start` and `selfloop_mid`), but rules 4 and 5 do not remove a
   repeated term whose own weight would overflow the row (see rule 4).
4. **Ends that may coincide.** While both ends are open, the `loop` rule never
   fires backwards (rule 7), with one endpoint variable or two.

## Evidence

### Tests

- **`path_test`** (`path_constraint`, registered through `run_test_only.bash`;
  the harness verifies its own proofs when `veripb` is on the path). It runs 15
  shapes for each spelling, with proofs and without: one node; a three-node
  path; a triangle; a square; two disjoint edges; a lollipop; an antiparallel
  pair; a self loop with parallel edges; `start = end` fixed (two shapes); both
  ends fixed; one end fixed; edges pinned in and out; a node pinned out; and
  `start` declared over `−1..3` (with `end` over `0..3`). Solutions are compared with the walk oracle
  under plain **`solve_for_tests`, not the GAC check**, deliberately, as the
  test says ("Not the GAC check; see Tree"). Seeded (`--seed=N`).
- **`scp_reader_test`**: a `path` and a `dpath` enumeration, and the five-class
  graph round trip.
- **MiniZinc** (`minizinc/CMakeLists.txt:219–228`): `minizinc-path` and
  `minizinc-dpath` (the `enum` spelling over nodes `2..5`, all solutions,
  proofs on, with a `--fzn-pattern` guard that the builtin was reached), and
  `minizinc-bounded-dpath` (the `int` spelling, optimisation).
- **Audit lane:** the two `NoWidePosition` rows above, registered as a ctest
  only under `-DGCS_LARGE_DOMAIN_GUARD=ON`, which no CI lane sets (#920).
- **Mutation lanes:** none for this family. `reachable_mutation_{undirected,
  directed}_{border,mandatory,rootdomain}` and their `_none` controls corrupt
  the reachability child's reasons, but through `Reachable` posted directly,
  not through a `Path`.

**Runtime caps.** No lane sets or clears one, and the defaults **do not fire**.
`GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500 path_test --seed=1`
runs all 60 cases (30 without proofs, 30 with), the largest having 28
solutions, and prints no `[truncated run]` line. So the capped run is the full
check. It takes 0.56 s including VeriPB (86caad24, fataepyc-10, one core).

**Tightness:** no lane. No rule's derivation has been shown to be refused when
corrupted.

**What the tests do not cover.**

- **Strength, at all.** No test asserts any pruning, and none could catch a
  propagator that did nothing until every variable was fixed. The root probe
  above is the only record.
- **Views, aliasing, and one variable for both ends.** The `same_ends` cases
  pass the constant twice. The audit's probes cover these; the suite does not.
- **Holey endpoint domains**, and endpoints wider than `−1..3`.
- **The `int` spelling of `path` / `dpath` with enumeration, and `bounded_path`
  undirected**, in the MiniZinc lanes; the audit's differential covers both.
- **Graphs of more than four nodes.** The suite never reaches a size where the
  degree lower bound or the cut forcing visibly matters.
- **An empty node set**, through any route, which is how #1305 went
  unnoticed.
- **Real instances:** none ported; none exists in the corpus (below).

### Benchmarks and examples

- **In the repository:** no example posts `Path` or `DPath`.
- **Corpus:** no MiniZinc Challenge model posts `path`, `dpath`,
  `bounded_path` or `bounded_dpath` (grep of `mzn-challenge-a8448864`, every
  year). `orthorio` 2026 has a `path` array and function, but routes agents with
  `subcircuit`.
- **For CPU:** enumerating every simple path between opposite corners of a
  `k × k` grid (`tmp/fd-graph/path/bench/gridpaths.mzn`; `lb/lb.cc` in C++).
  The work is fixed (184 paths at `k = 4`, 8,512 at `k = 5`) and the node count
  measures strength. For `DPath`, the first solution from corner to corner on
  the bidirected grid, which is search-order sensitive and shows weak failure
  detection plainly.
- **For proof verification:** the same enumeration at `k = 3, 4`. `k = 5` is
  887,711 nodes and was not run with proofs.

### CPU performance

*Release build of `86caad24` (GCC, `-O3 -march=native`), fataepyc-10, one
pinned core, fixed malloc thresholds, proofs off, 2026-10-09. Search:
`in_order(es)`, `largest_in`, edges listed node by node (each node's right edge, then its
down edge, each followed by its reverse arc for `DPath`).*

**The degree lower bound, measured by posting it.** The "+ bound" columns add,
as redundant `LinearGreaterThanEqual` rows, `Σ inc(v) − 2·ns[v] ≥ 0` for every
node other than the two ends (undirected), or `Σ out(v) − ns[v] ≥ 0` for every
node other than `end` (directed). These are consequences of the constraint, so
the solution counts are unchanged. They are a model-level stand-in for a rule,
used to say what the rule would buy (`lb/lb.cc`):

| shape | solutions | nodes | failures | time | `instructions:u` | nodes, + bound | time, + bound | `instructions:u`, + bound |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| `Path` 4 × 4, all | 184 | 5,337 | 4,691 | 0.138 s | 0.665 × 10⁹ | 523 | 0.019 s | 0.086 × 10⁹ |
| `Path` 5 × 5, all | 8,512 | 887,711 | 856,677 | 31.0 s | 153.0 × 10⁹ | 26,481 | 1.27 s | 5.91 × 10⁹ |
| `DPath` 4 × 4, all | 184 | 1,245 | 658 | 0.052 s | — | 589 | 0.028 s | — |
| `DPath` 5 × 5, first | 1 | 1,507 | 1,490 | 0.102 s | 0.576 × 10⁹ | 56 | 0.008 s | 0.053 × 10⁹ |
| `DPath` 6 × 6, first | 1 | 296,234 | 296,204 | 29.7 s | 168.0 × 10⁹ | 3,294 | 0.56 s | 3.36 × 10⁹ |

That is 33.5 times fewer nodes and 26 times fewer instructions on the 5 × 5
enumeration, and 90 times fewer nodes on the directed 6 × 6 search. Without
the bound, 96.5% of the 5 × 5 enumeration's nodes are failures.

**Where the time goes**, on the same runs (`GCS_PROPAGATOR_STATS=time`):

| shape | reachability child | `graph_rules` | linear child |
|---|---|---|---|
| `Path` 5 × 5, all (31.2 s) | 1,717,806 calls, 19.7 s, 11.5 µs a call | 1,529,855 calls, 9.35 s, 6.1 µs | 1,126,740 calls, 0.93 s, 2,508 effectful |
| `DPath` 6 × 6, first (29.6 s) | 677,302 calls, 23.1 s, 34.2 µs | 550,517 calls, 5.09 s, 9.2 µs | 459,974 calls, 0.75 s, 3,664 effectful |

The linear child is effectful on 0.2% and 0.8% of its calls. This is hotspot
context, not a saving.

**The child's cut forcing is load-bearing here.** With a modified `path.cc`
linked ahead of the library, turning `with_cut_forcing(false)` on the child
(`nocut/path_mod.cc`, an experiment; nothing committed) changes the results as
follows:

| shape | nodes, forcing on | time | nodes, forcing off | time |
|---|--:|--:|--:|--:|
| `Path` 5 × 5, all | 887,711 | 31.1 s | 4,139,447 | 73.6 s |
| `DPath` 6 × 6, first | 296,234 | 29.4 s | 5,686,456 | 218.2 s |
| `Path` 5 × 5, all, + bound | 26,481 | 1.27 s | 26,483 | 1.04 s |
| `DPath` 6 × 6, first, + bound | 3,294 | 0.56 s | 34,202 | 2.02 s |

Without the degree bound, cut forcing is a large part of what strength the
family has. With it, the undirected forcing saves two search nodes in 26,483
and adds about 21% to the time. The directed forcing still cuts nodes
ten-fold. So whether `Path` wants the child's forcing depends on whether #1313
lands.

**Against the stdlib decomposition, and Gecode.** Gecode has no native path
propagator, so there is no identical-tree comparison. With `gridpaths.mzn`
through MiniZinc 2.9.7 (`bool_search(es, input_order, indomain_max)`; the edge
order differs from `lb.cc`'s, so the node counts are not comparable with the
table above):

| `k = 4`, all 184 paths | nodes | failures | solve |
|---|--:|--:|--:|
| GCS, `Path` | 1,761 | 1,100 | 0.064 s |
| GCS, stdlib decomposition (`-G std`) | 124,573 | 123,457 | 6.38 s |
| Gecode 6.3.0, stdlib decomposition | 65,605 | 22,147 | 11.97 s |

The strengths differ (the stdlib's two spanning trees with distance labels,
against one unfolding and counting rows), so this compares models, not
propagators. GCS with `Path` at `k = 5`: 289,305 nodes, 12.2 s. The
decompositions were not run at `k = 5`.

**What the benchmarks do not exercise.** Open endpoints (both are constants
here, so rules 3 and 7 and the reachability child's root filtering hardly fire),
multigraphs, and graphs past 36 nodes.

### Proof performance

*Same build and machine; VeriPB 3.0.2 with `--force-checked-deletion`; one
pinned core; the grid enumeration with `start` and `end` the two corners
(`sizes/sizes.cc`); 2026-10-09.*

| shape | nodes | `.opb` | `.pbp` at `Off` | lines | VeriPB at `Off` | `.pbp` at `Inferences` | VeriPB at `Inferences` |
|---|--:|--:|--:|--:|--:|--:|--:|
| `Path` 3 × 3 | 87 | 56,189 B | 38,874 B | 793 | 0.025 s | 48,398 B | — |
| `Path` 4 × 4 | 5,337 | 198,452 B | 3,153,400 B | 41,273 | 1.84 s | 3,830,505 B | 0.18 s |
| `DPath` 3 × 3 | 49 | 58,503 B | 40,779 B | 739 | 0.022 s | 48,760 B | — |
| `DPath` 4 × 4 | 1,245 | 203,032 B | 1,510,891 B | 17,046 | 0.61 s | 1,877,797 B | 0.12 s |

Every `Off` proof is `s VERIFIED COMPLETE ENUMERATION OF 12` or `184
SOLUTIONS`; the `Inferences` ones are `UNDER ASSERTIONS`. The 4 × 4 times are
three runs each, 1.83 to 1.85 s and 0.611 to 0.616 s. The `Inferences` proof is
larger in bytes than the `Off` one, because an `a` line carries its hint and an
`Off` RUP does not.

**Assertions by hint at `Inferences`,** which is what an external justifier
consumes:

| shape | `path` | `reachable` | `linear_equality` | `backtrack` | `solx_block` | all `a` |
|---|---|---|---|---|---|---|
| `Path` 4 × 4 | 6,266 (25.8%), 526 KB, 2.9 literals | 12,444, 1.74 MB, 6.4 literals | 94, 33 KB | 5,337, 1.07 MB | 184 | 24,325 |
| `DPath` 4 × 4 | 4,282 (37.9%), 295 KB, 2.0 literals | 5,177, 692 KB, 5.9 literals | 402, 197 KB | 1,245, 278 KB | 184 | 11,290 |

**Own against shared, in checking time.** In the `Off` proof, the audit turned
every RUP whose clause is one of a given hint's `a` lines into an `a` line
(`proofperf/assertpath.py`, no clause collisions between hints). It then timed
VeriPB again, over three runs each:

| shape | as written | `path` RUPs asserted | `reachable` RUPs asserted |
|---|--:|--:|--:|
| `Path` 4 × 4 | 1.84 s | 1.81 s (6,266 lines) | 0.76 s (12,444 lines) |
| `DPath` 4 × 4 | 0.61 s | 0.59 s (4,282 lines) | 0.30 s (5,177 lines) |

So this class's 6,266 RUPs cost VeriPB about 0.03 s on `Path`, about 2%, and
its 4,282 about 0.02 s on `DPath`, about 3%. An independent re-run gives 0.04 s
on `Path`, and about 8% on `DPath` by mean (0.62 s against 0.57 s). The reachability child's cost
1.09 s (59%) and 0.31 s (51%). Each counting-rule RUP propagates a
short clause against one cardinality row, while each reachability RUP replays
a breadth-first search through the unfolding. Hinting this class's RUPs with
their row would save almost nothing.

**Against the OPB:** at 4 × 4, this class's own rows are 2.6% of the `.opb`
bytes and the unfolding's flags 93%; see the [OPB
encoding](#opb-encoding) table for how that scales.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference of this class is a RUP at `Off`, and every probe proof
verifies: 900 random (`proofsweep`, seed 7, plain, aliased endpoints and larger
graphs, 536 enumerations and 364 refutations), 300 with aliased selectors, 8
with views, 6 wide-endpoint, the targeted shapes, the test suite's 30, and
three through MiniZinc. The propagator does the same with proofs on and off.
The children's gaps are theirs: see [`reachable.md`](reachable.md) and
[`linear.md`](linear.md).

### Known limitations

- **A path over no nodes is reported as an error, not as unsatisfiable**, from
  MiniZinc's `path(0, 0, …)` and `dpath(0, 0, …)` (#1305).
- **Search on a path model is much larger than it needs to be.** The
  constraint never forces an edge in from a node's degree, so a partial path
  that has run into a dead end is not noticed until the count or connectivity
  runs out of room. On a 5 × 5 grid, 96.5% of the nodes in enumerating all
  corner-to-corner paths are failures (#1313).
- **A start that cannot reach any possible end is not ruled out** until the end
  is fixed.
- **When the two ends may coincide**, a node with an edge selected is not ruled
  out as the shared end until one end is fixed. This happens with one
  endpoint variable or two.
- **With proofs, the graph size is limited by the reachability unfolding**,
  `Θ(n(n + m))` OPB rows.
- **A `.scp` written from a MiniZinc model cannot be re-solved or chained**:
  the endpoint shift becomes a view, which the `.scp` reader does not parse,
  and cake has no `path` anyway.

### Next steps

1. **Add the degree lower bound.** Undirected: a selected node that is neither
   end has degree at least two, and an end other than a single-node path has
   degree at least one. Directed: a selected node other than `end` has an
   outgoing selected edge. Propagation is the `AtMost` machinery read the other
   way, `O(deg)` per row. The proof is the work. The rows are consequences, not
   definitions, so they should not go into the OPB. One derivation is a `pol`
   that sums the count row with every node's degree row (`Σ_v deg(v) = 2Σ es =
   2Σ ns − 2`, with each `deg(u) ≤ 2·ns[u]` and each end `≤ 1`), either once per
   node at the root as a lemma or per inference, at `O(n + m)` terms.
   `deg(u) ≤ 2·ns[u]` is not an OPB row, since `deg<u>` is unconditional, and
   how it is derived depends on the number `k` of incident slots at `u`. For
   `k ≤ 2` it is the sum of `u`'s subgraph rows `es ≤ ns[u]`. For `k = 3`,
   `deg<u>` plus twice those rows gives `3·Σ es − 6·ns[u] ≤ 2`, and one
   division by 3 gives the target. From `k = 4` no single rounding step
   suffices, so it needs a case split on `ns[u]` or a longer derivation. With
   variable endpoints the end terms need the one-hot `root` flags, and something
   like them for `end`. That technique is not yet in `dev_docs/`, so it wants
   the Fable consult `CLAUDE.md` asks for before coding. What it would buy is
   the table in [CPU performance](#cpu-performance): 33.5 times fewer nodes and
   26 times fewer instructions on the 5 × 5 enumeration. #1313.
2. **Then re-measure the child's cut forcing.** With the bound in place, the
   undirected forcing prunes almost nothing on the grid (two nodes in
   26,483) and adds about 21% to the time. A `Path`
   option, or an internal choice, could pass `with_cut_forcing(false)` to an
   undirected child. Measure on more than one graph shape first. Small, after
   item 1.
3. **Couple the ends.** Rule out `start = v` when no candidate end is reachable
   from `v`, and the mirror for `end`. This is one search per candidate over
   the remaining graph, and its reason is the reachability child's border
   reason. Moderate. Not filed: models usually fix the ends.
4. **Make `graph_rules` incremental.** Index rules by variable and rescan only
   the rules a changed variable occurs in, instead of all `Θ(n + m)` each call.
   That is 18 to 31% of propagation time on the benchmarks here. Moderate.
   It is a change to the shared helper, so it touches `DTree` too, whose share
   is small: [`tree.md`](tree.md) measures 1.9% of self time in
   `graph_rules::propagate` on `dsteiner` 5 × 5 and does not recommend it for
   that family. So the case for it rests on `Path` and `DPath`.
5. **Trigger the endpoints on bounds, not on change.** Holes in `start` and
   `end` never enable a counting-rule inference, so `on_bounds` loses nothing
   for this propagator. It stops its own endpoint holes from re-waking it, and
   stops it over-reporting `end` to `consistency::Auto`. Deduplicating the
   trigger list removes the spurious idempotence-downgrade count too. Small.
6. **Treat a repeated condition as one.** Deduplicate a `graph_rules` row's open
   conditions, so that `loop<v>` with one variable for both ends fires
   backwards. With the change patched in
   (`tmp/fd-graph/factcheck/path/strength/dedup/`), the one-variable runs miss
   31 and 30 unsatisfiable roots instead of 162 and 148, with no count
   mismatch, while two variables plus `Equals` stay at 162 and 148. So one
   variable would become the stronger spelling. Small. Item 3's coupling would
   not help two variables: in the single-edge example above, `start = 0` can
   reach the candidate end 4 and is a candidate end itself. Ruling out
   `start = end = v` needs `Path` to know that the two ends are equal.
7. **Drop tautological rows.** Skip a degree row whose variable count does not
   exceed its limit, in `graph_rules::define` and the propagator, which covers
   `DTree`'s single-arc `indeg<v>` rows too (the same change [`tree.md`](tree.md)
   lists). Small; it saves rows and scan, not search.
8. **Widen the tests.** (The audit lane's pin is PR #1302's; see
   [Interval efficiency](#interval-efficiency).) In `path_test`, add a
   view-position pass, one variable for both ends, holey endpoints, and graphs
   of six to ten nodes. Add an `int`-spelling MiniZinc enumeration lane and a
   `bounded_path` lane. Small.
9. **Report an empty node set as unsatisfiable.** Post a contradiction in
   `prepare` instead of throwing, or guard the `_int` overrides with
   `if N = 0 then false`. `Reachable` and `Tree` need the same fix, but
   `PathBase::prepare` throws before its child is installed, so `Path` needs its
   own. Small. #1305. **Caution:** `dag` and the four-argument
   `subgraph` have the opposite defect (#1303), a satisfiable empty model flattened to
   a wrong `UNSATISFIABLE`, whose fix is an override guard returning `true`.
   Copying that `then true` guard into the rooted `_enum` overrides (`path`,
   `reachable`, `tree`) would turn their accidental-but-right `UNSATISFIABLE`
   into a wrong `SAT`.
10. **Cosmetic.** `DPath`'s errors say "Path".

Not a next step: the cardinality row is implied, but it is item 1's lemma and
occasionally prunes, so it stays.

**Out-of-stack documentation fixes this audit found.**
`connectivity-proofs.md`'s family table gives `DPath` "the end is selected" but
not `Path`, which has the same `endin<v>` rows (`path.cc:86–87`). Its "These
are not GAC" paragraph names cycle closure as the concrete gap; for `Path` and
`DPath` the larger one is the missing degree lower bound.

## Prior art

Path constraints over a graph variable go back to CP(Graph) (Dooms, Deville and
Dupont, CP 2005). Quesada, Van Roy, Deville and Collet (*Using Dominators for
Solving Constrained Path Problems*, PADL 2006) propagate simple paths with
dominators, which is the directed analogue of the cut forcing the reachability
child does. The `tree` constraint line (Beldiceanu, Flener and Lorca, CPAIOR
2005; Fages and Lorca, CP 2011) is the nearest relative of the decomposition
here, which is a tree plus degree bounds. MiniZinc's `globals.graph`
decomposition, the one this class replaces, builds `dpath` as two `dtree`s and
`path` as a `dpath` over doubled edges. As far as this audit knows, no path
constraint has been certified before in any proof system. What is new here is
on the proof side: one breadth-first unfolding, `Reachable`'s adaptation of a
published layered SAT reachability encoding (see
[`reachable.md`](reachable.md#prior-art)), serves the whole family
([`connectivity-proofs.md`](../connectivity-proofs.md)), and every counting
rule is a single RUP against a row the constraint writes itself. The
propagation rules are the straightforward ones, and the class documentation
says so.

## Further reading

- [`connectivity-proofs.md`](../connectivity-proofs.md): the design note for the
  reachability encoding and the tree and path family built on it. It covers why
  the breadth-first unfolding makes reachability RUP where the stdlib's
  distance labelling does not, why the counting rules are this class's own rows
  rather than children, the `start = end` corner, and the `steiner` measurements
  for `Tree`.
- [`reachable.md`](reachable.md): the child's rules, cut forcing, encoding and
  costs.
- [`tree.md`](tree.md): `Tree` and `DTree`, the other callers of
  `graph_rules`.
- [`constraints.md`](../constraints.md), "a ceiling on how many children one
  constraint can install": why `graph_rules` exists.
