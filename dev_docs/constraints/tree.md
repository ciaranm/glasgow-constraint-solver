# `Tree`, `DTree`: the selected subgraph is a tree, or an arborescence, rooted at `root`

> **Maturity** production ·
> **Audited** 2026-10-09 at `86caad24` ·
> **Open issues** filed by this audit: #1314 (`DTree` has no rule that nothing
> enters the root), #1315 (neither spelling notices a selected cycle until the
> count runs out), #1305 (a zero-node `tree`, `dtree`, `dsteiner` or
> `d_weighted_spanning_tree` is a solver error through MiniZinc, where the
> standard library says unsatisfiable; shared with `reachable` and `path`); see
> [Next steps](#next-steps). Already open and
> touching this family: #1210 (`AssertionLevel::Links` rejects the first
> solution line), #868 (no identical-search-tree comparison against another
> solver). Tracked under #871.

`Tree` and `DTree` are MiniZinc's `tree` and `dtree`: over a fixed graph, a 0/1
variable per node and per edge picks a subgraph, and the subgraph has to be a
tree containing the root (`Tree`, edges followed either way) or an arborescence
out of it (`DTree`, edges followed from `first` to `second`). They are also what
`steiner`, `dsteiner` and both `weighted_spanning_tree` spellings reach, through
the standard library's own wrappers. The family is a **delegating** one:
`prepare()` posts a [`Reachable`](reachable.md) (or `DReachable`) child and a
[`LinearEquality`](linear.md) child for `Σ es = Σ ns − 1`, both under its own
constraint ID, and only `DTree` adds anything of its own: one at-most-one row per
node over the arcs entering it, propagated by the shared
`innards/graph_rules.{hh,cc}`. Everything about connectivity, its encoding, its
proofs and its cost is the reachability child's and is documented in
[`reachable.md`](reachable.md); this document covers what is posted, the count,
`DTree`'s in-degree rows, and what the conjunction does and does not achieve.

What to know before touching it:

- **It is a decomposition, and not GAC.** The reachability child is GAC and the
  count is GAC, but their conjunction is not. A brute-force sweep at `86caad24`
  over 3,000 random instances of up to four nodes found the root fixpoint
  missing a removal on 26 for `Tree` and 201 for `DTree`. Undirected, every
  missing removal is an edge that would close a cycle; on the same sample,
  adding one `Σ_{e ∈ C} es[e] ≤ |C| − 1` row per cycle `C` made `Tree` GAC at
  every search node, up to six nodes. Directed, most of the rest is that
  **nothing may enter the root**, for which `DTree` has no rule, though `DPath`'s
  `startin` rows say exactly that about the start of a path. Neither
  strengthening is a RUP against the current encoding in general.
- **A root fixpoint can survive with no solution.** A cycle among edges already
  selected is invisible until the count has no slack left: one five-node
  instance with a fixed triangle in it leaves the root with three candidates and
  two undecided nodes, and has no solution. Search still finds that out, since
  every full assignment is checked exactly.
- **Its cost is the reachability child's.** The OPB is `Θ(nodes × arcs)` rows,
  and on an 8 × 8 grid `Tree` contributes 2 of its 37,208 rows (`DTree`, with
  its in-degree rows, 66 of 37,608). On the directed Steiner benchmarks below
  the in-degree rule makes 41–45% of the assertions carrying this constraint's
  ID (about a tenth of all `a` lines), and the count almost none.
- **The frontends agree.** 1,930 random instances through MiniZinc 2.9.7 and
  2.10.1 (both index conventions, index sets not starting at 1), the `.scp`
  reader and Gecode's standard-library decomposition gave the same 10,405
  solutions; 200 `steiner`, `dsteiner` and spanning-tree optimisations agreed on
  every optimum. The one disagreement is the empty graph (#1305), where
  `tree`, `dtree`, `dsteiner` and `d_weighted_spanning_tree` are a solver error.

## What it is

### Semantics

`Tree(edges, root, ns, es)`, with nodes numbered `0 .. n − 1`, `edges[e]` the
pair `(u, v)` of edge `e`'s endpoints and `ns`, `es` 0/1 variables, holds exactly
when

- `root` is a node and is selected: `0 ≤ root ≤ n − 1` and `ns[root] = 1`;
- every selected edge has both endpoints selected;
- every selected node is reachable from `root` along selected edges, each
  followed in either direction; and
- `Σ es = Σ ns − 1`.

The last two together say "a tree": a connected graph with one fewer edge than
nodes is a tree, and a tree is such a graph.

`DTree` reads `edges[e]` as an arc from `first` to `second`, follows arcs only
that way, and adds that **at most one selected arc enters each node**. Those say
"arborescence rooted at `root`": every selected non-root node has an arc in (it
is reached), so exactly one, and the count then leaves none for the root.

MiniZinc's reading is the same (`fzn_tree` doubles every edge and calls
`fzn_dtree`, which is a parent-and-distance labelling plus the same count), and
the differential tests in [Tests](#tests) found no instance where they differ
except the empty graph. Degenerate shapes:

- **No nodes:** `InvalidProblemDefinitionException` ("Tree needs at least one
  node"). The constraint is false there (the root has to be a selected node),
  and the standard library says so: `tree(0, 0, …)`, `dtree(0, 0, …)`,
  `dsteiner(0, 0, …)` and `d_weighted_spanning_tree(0, 0, …)` are unsatisfiable
  through Gecode and an `=====ERROR=====` through Glasgow, on both MiniZinc
  versions (#1305). The directed wrappers take the root as an argument, so
  nothing empties a root domain before the class is posted; `steiner(0, 0, …)`
  and `weighted_spanning_tree(0, 0, …)` are unsatisfiable through Glasgow too,
  because their own `var 1..N` root is empty. The five-argument
  `tree([], [], r, [], [])` comes out unsatisfiable through Glasgow too, but
  only because `min(index_set(ns))` is undefined in the override.
- **A root value that is not a node:** simply false. The reachability child
  clamps the root to `0 .. n − 1` with `define_bound`, so a constant root of 5
  on three nodes is a verified UNSAT at the root.
- **One node, no edges:** the root is 0 and the node is selected.
- **A self loop** can never be selected: a selected subgraph of `k` nodes and
  `k − 1` edges, one of them a loop, has `k − 2` other edges and cannot be
  connected. Under `DTree` a loop at `v` also counts towards `v`'s in-degree
  row.
- **Parallel edges** (and antiparallel arcs): at most one of a pair, since both
  would close a cycle.
- **The same variable at two positions** (two nodes, two edges, or a node and an
  edge) is accepted and means they are selected together; the count's
  `tidy_up_linear` merges the repeated terms. Consistency is not claimed for it,
  as for `Reachable`.
- **Argument errors** throw `InvalidProblemDefinitionException` from
  `prepare()` (`tree.cc:40–53`): one edge variable per edge, endpoints below
  `n`, and every `ns` and `es` with initial bounds inside `0..1`. The messages
  name `Tree` for both spellings.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Tree` | `fzn_tree` ✓[^mznover] | n/a[^xcsp] | n/a[^cpmpy] | ✓ `tree` | also reached by `steiner` and `weighted_spanning_tree`[^wrappers] |
| `DTree` | `fzn_dtree` ✓[^mznover] | n/a[^xcsp] | n/a[^cpmpy] | ✓ `dtree` | also reached by `dsteiner` and `d_weighted_spanning_tree`[^wrappers] |
| reified | `unsupported`: the standard library's `fzn_tree_reif` and `fzn_dtree_reif` are `abort`s in 2.9.7 and 2.10.1 | n/a | n/a | — | |

[^mznover]: Four overrides in `minizinc/mznlib/`, `fzn_tree_{int,enum}.mzn` and
    `fzn_dtree_{int,enum}.mzn`, which shift the nodes and the root to start at
    zero (by 1 for the `_int` spelling, by `min(index_set(ns))` for `_enum`) and
    call `glasgow_tree` / `glasgow_dtree`; `fzn_glasgow.cc:985` posts the class.
    The undirected one goes straight to `glasgow_tree` rather than doubling the
    edges into a `dtree` as the standard library does. That does **not** halve
    the reachability encoding, whatever `fzn_tree_enum.mzn`'s comment says:
    undirected `Reachable` already makes two arcs per edge (`reachable.cc:50–60`),
    so a `dtree` over the doubled edge list has the same `2E` arcs. In the size
    table under [OPB encoding](#opb-encoding) the reachability rows of the two
    are identical at every size, and the whole OPBs differ by 7% at 3 × 3 down
    to 1.1% at 8 × 8. What doubling would add is the standard library's `2E`
    fresh arc variables, each edge channelled to its two, `E` more terms in the
    count, `2E` more subgraph rows, the in-degree rows, and the directed
    forcing's search per candidate root, which is the dearer one (unmeasured
    here).
    `minizinc/tests/treetest.mzn` and `dtreetest.mzn` (nodes indexed `2..5`) and
    `steinertest.mzn` each carry a `--fzn-pattern` guard that the builtin was
    reached.

[^xcsp]: XCSP3-core has no tree constraint.

[^cpmpy]: `n/a`, as the frontend support matrix records it for the tree and
    path family. `gcspy`, CPMpy's route into this solver, binds nothing in this
    family; CPMpy itself was not examined.

[^wrappers]: The standard library's `fzn_steiner` is `let { var 1..N: r } in
    tree(…) ∧ weight = Σ es·w`, `fzn_dsteiner` is `dtree(…)` with the given
    root, and `fzn_wst` / `fzn_dwst` are the same over an all-true `ns`. None is
    overridden; they reach `glasgow_tree` / `glasgow_dtree` through `tree` and
    `dtree`, which this audit checked in the flattened model of every instance it
    ran.

### Options

`None.` Neither class has a `with_consistency()` or any other option. In
particular the reachability child's `with_cut_forcing()` is not passed through:
a tree always forces cut vertices and bridges, and a `DTree` always runs the
directed forcing searches, which [`reachable.md`](reachable.md) says are the
expensive half. The count child is posted at `LinearEquality`'s default,
`consistency::BC`. With every coefficient `±1` over 0/1 variables that is GAC on
the count alone.

### Variable kinds and views

`ns` and `es` take any `IntegerVariableID` whose initial bounds lie inside
`0..1`: plain variables, constants, and views such as `−y` over `y ∈ −1..0` or
`y + 3` over `y ∈ −3..−2`. `root` takes any `IntegerVariableID`, constants and
views included; values outside `0 .. n − 1` are clamped away.

The proof handles all of these: probes at `86caad24` with a view node
(`−y` and `y + 3`), a negated and an offset root view (`−x`, and
`x + 2⁶⁰ − 6` over `x ∈ −(2⁶⁰ − 1) .. 2`), a constant root inside and outside
the node range, and a node variable aliased with an edge variable each enumerate
completely with a VeriPB-verified proof, both spellings
(`tmp/fd-graph/tree/robust/robust.cc`). The reachability child names every
literal through the variable's own encoding; see [`reachable.md`](reachable.md).

### Reification

`None.` MiniZinc's reified forms are `abort`s in the standard library, so
`b <-> tree(…)` does not flatten for any solver. A reified form would need a
reified reachability encoding, which `Reachable` does not have either.

### Relation to other families

- **Decomposes into:** a `Reachable` (`Tree`) or `DReachable` (`DTree`) child
  over the same edges, root and node and edge variables (`tree.cc:65–74`); a
  `LinearEquality` child, `Σ es − Σ ns = −1` (`tree.cc:78–85`); and, for
  `DTree` only, one `graph_rules::AtMost` row per node with at least one
  entering arc, `Σ_{a into v} es[a] ≤ 1`, labelled `indeg<v>`, with one
  propagator of its own. Both children carry this constraint's ID, the pattern
  `SeqPrecedeChain` and `Circuit` use (#449): they can share it because their
  labels differ (`Reachable`'s are per node and per edge, the equality's are
  `le` and `ge`), and a third linear child could not, which is why the in-degree
  rows are this constraint's own rather than more children (see
  [`constraints.md`](../constraints.md), the ceiling on children).
- **Child constraints:** those two.
- **Shares code:** `gcs/constraints/innards/graph_rules.{hh,cc}`, with `Path` and
  `DPath` and nobody else (callers: `tree.cc`, `path.cc`). This family uses only
  `AtMost` with no conditions and a limit of 1, so `graph_rules`' backward
  branch (a rule that cannot hold rules out its one open condition) and its
  `Selected` rule never run here; [`path.md`](path.md) uses and documents
  both. A change to `graph_rules::propagate` or `define` is a change to both
  families. `hints::Tree` is this family's own.
- **The boundary with `reachable/`, `dag/` and `circuit/`.** With `reachable/`,
  the coupling is total and one-way: this family posts a whole `Reachable`, so
  its connectivity rules, the breadth-first unfolding, the `root`/`arc`/`reach`
  flags, their labels and the open-root case split are documented once, in
  [`reachable.md`](reachable.md), and only counted here. With `dag/` and
  `circuit/` there is **no shared code**. `Dag`'s two subgraph rows per edge
  (`sgf<e>`, `sgt<e>`) are identical copies of the reachability child's, as
  `Subgraph`'s are ([`subgraph.md`](subgraph.md)), but its rootless level
  unfolding, restricted to strongly connected components, is its own (`dag.cc`
  includes nothing from `reachable/`). `Circuit` works on successor variables
  and shares nothing.
- **Presolvers:** none reads it (nothing under `gcs/presolvers/` names `Tree`,
  `Reachable` or `graph_rules`).
- **Reachable directly:** yes, from C++, from `.scp` and from MiniZinc; it is not
  only a decomposition target.

**Not merged with `reachable` or `path`.** Settled: `Tree` posts a `Reachable`
but has its own `.scp` term, its own count and (directed) its own rows and hint,
and it shares with `Path` only the `graph_rules` helper, whose other half only
`Path` uses.

## The proof model

### OPB encoding

Three parts, under this constraint's ID; `n` nodes, `E` edges, `A` arcs (`2E`
for `Tree`, `E` for `DTree`), `levels = n − 1`.

1. **The reachability child's encoding,** in full: see
   [`reachable.md`](reachable.md) and
   [`connectivity-proofs.md`](../connectivity-proofs.md). In outline,

   ```
   es[e] = 1  ⇒  ns[from(e)] = 1,  es[e] = 1  ⇒  ns[to(e)] = 1     c[id][sgf<e>], c[id][sgt<e>]
   x[id][v][root]  ⇔  root = v                                      flags, 2 rows each
   x[id][v][root]  ⇒  ns[v] = 1                                     c[id][rootin<v>]
   Σ_v x[id][v][root] = 1                                           c[id][root1le], c[id][root1ge]
   x[id][a_k][arc]  ⇔  es[edge(a)] = 1 ∧ reach[from(a)][k − 1]      flags, k = 1..levels
   x[id][v_k][reach] ⇔ reach[v][k − 1] ∨ ⋁_{a into v} arc[a][k]     flags, k = 1..levels
   ns[v] = 1  ⇒  reach[v][levels]                                   c[id][reached<v>]
   0 ≤ root ≤ n − 1                                                 unlabelled, only if declared wider
   ```

2. **The count**, from the `LinearEquality` child:

   ```
   Σ_e es[e] − Σ_v ns[v] = −1                                       c[id][le], c[id][ge]
   ```

3. **`DTree` only**, one row per node `v` with at least one entering arc:

   ```
   Σ_{a : to(a) = v} es[a] ≤ 1                                      c[id][indeg<v>]
   ```

**It is definitional**: every row is the constraint's meaning or the definition
of an auxiliary flag, and the count and in-degree rows are the meaning. A node
with exactly one entering arc gets a row `−es[a] ≥ −1`, which is always true and
can never propagate: two of the four in-degree rows of the four-node example
under [Tightness](#rule-indegree-full) are of that kind, and none on a grid
with both arcs per edge. Harmless, and cheap to skip.

**Size, measured** (`tmp/fd-graph/tree/size/size.cc` at `86caad24`: a `k × k`
grid, the root over `0 .. n − 1`, the OPB written and the search stopped at the
first node; `DTree` with both arcs of every grid edge; rows are constraint rows,
so the `preserved:` header line is not counted, as in `reachable.md`):

| grid | n | E (Tree) | rows, `Tree` | of which this family's own | rows, `DTree` | of which own (count + `indeg`) | bytes, `Tree` |
|---|---|---|---|---|---|---|---|
| 3 × 3 | 9 | 12 | 653 | 2 | 698 | 2 + 9 | 56 KB |
| 4 × 4 | 16 | 24 | 2,144 | 2 | 2,232 | 2 + 16 | 197 KB |
| 6 × 6 | 36 | 60 | 11,432 | 2 | 11,648 | 2 + 36 | 1.1 MB |
| 8 × 8 | 64 | 112 | 37,208 | 2 | 37,608 | 2 + 64 | 3.7 MB |

The reachability child's rows are `2E` subgraph rows (`2A` for `DTree`), `3n + 2`
for the root, `2·A·levels` for the arc flags, `2·n·levels` for the reach flags and
`n` `reached` rows: at 8 × 8, 28,224 rows of arc flags alone. This family's own
rows are 2 (with `2(n + E)` terms) plus, for `DTree`, at most `n` (with `E` terms
in all). The remainder is the variables' literal layer. **Independent of domain
width** apart from the root's bit-sum encoding: a root declared over
`±(2⁶⁰ − 1)` takes a three-node `Tree`'s OPB from 5.6 KB to 22 KB, and the clamp
adds two rows.

### Labels

| Label | Rows | Used by |
|---|---|---|
| `c[id][indeg<v>]` | `DTree`'s in-degree row for node `v` | [indegree-full](#rule-indegree-full) and [indegree-overfull](#rule-indegree-overfull) need the row: each is a plain RUP (`JustifyUsingRUP`, no antecedent list) that unit propagation finds against it, and deleting the row from the OPB makes VeriPB refuse the first such step ([Tightness](#rule-indegree-full)). **No proof line names the label**, as `path.md` says of the same `graph_rules` rows |
| `c[id][le]`, `c[id][ge]` | the count | the count child's rules; see [`linear.md`](linear.md) |
| `c[id][sgf<e>]`, `sgt<e>`, `rootin<v>`, `root1le`, `root1ge`, `reached<v>` | the reachability child's | its rules; see [`reachable.md`](reachable.md) |

Labels are written here as `c[id][role]`; the OPB spells them `@c[id][role]`.
A role names everything that varies, as `ProofModel` requires: `indeg<v>` names
the node, and nothing else in the family or its children uses `indeg`. A
`DTree` root in-degree row (#1314) could not be labelled `rootin<v>`, which the
reachability child already uses for "the root is selected".

### Cake conformity

**Not covered.** `cake_pb_cp` has no `tree` or `dtree` (nor `reachable`): the
only graph constraint its binary names is `circuit`. So there is no
`scp_chain_*` case, and the encoding above has never been compared with a
verified one. What is checked instead is the `.scp` term itself:
`(label tree (from…) (to…) root (ns…) (es…))`, written by `base_s_expr`
(identical to `Reachable`'s apart from the name), survives write → read → write
unchanged (`scp_reader_test`, "the tree family survives write -> read -> write
unchanged"), enumerates correctly through the reader (a triangle: 6 trees and
5 arborescences), and agreed with a brute-force oracle on 1,930 random instances
in this audit ([Tests](#tests)). The `.scp` says nothing about the two children:
a checker reading `tree` has to know that its encoding is the reachability
encoding, the count and (directed) the in-degree rows, all under one ID.

### Proof-time state

- **At the root:** nothing proof-only. Every flag the family uses (the
  reachability child's `root`, `arc` and `reach` flags) is defined in the OPB
  with `create_proof_flag_fully_reifying`, so each is an OPB extension variable
  and, being fully reified over the model's own literals, is fixed by unit
  propagation on a solution. The clamp rows are in the OPB too, and the clamp
  initialiser's inference carries the shared `initial_bound` hint.
- **Lazily:** this family's own rules emit one RUP line each and nothing else.
  The reachability child's forcing with the root still open emits one
  `ProofLevel::Temporary` line per candidate root before its conclusion; see
  [`reachable.md`](reachable.md). The count child's lines are `linear.md`'s.
- **Deleted:** only those temporary lines. Nothing a later reconstruction needs
  is deleted.
- **Naming, for an external tool.** All three parts live under this constraint's
  ID: rows `c[<id>][<role>]` with the roles in [Labels](#labels), flags
  `x[<id>][<v>][root]`, `x[<id>][<a>_<k>][arc]` and `x[<id>][<v>_<k>][reach]`.
  Assertions carry **three hint names** for one `.scp` term: `tree` (this
  family's own rule, `DTree` only), `reachable` and `linear_equality`, each with
  `constraint_id` set to this constraint. So a reconstructor that dispatches on
  the hint name and then looks the ID up in the `.scp` will find `tree` or
  `dtree` where it expected `reachable` or `linear_equality`, and has to know
  the composition above. The count child names a 0/1 variable through its `ge1`
  order atom, which the proof defines with two `red` lines on first use at `Off`
  and `Definitions` and leaves undefined at `Links` and `Inferences`, while the
  reachability child and the in-degree rule name the bit `b0` directly. They are
  the same literal, and a reconstructor has to know it.
- **No proof-only vector** is indexed by anything that dangles with proofs off.

## The implementation

### Initialisation and global data

`prepare()` validates the arguments, installs the two children (whose own
`prepare()` and installs run there and then), and for `DTree` builds the
entering-arc lists and one `AtMost` rule per node that has any. It returns
whether there are rules, so `Tree` installs no propagator and writes no rows of
its own, and `DTree` installs one propagator. The reachability child's
`prepare()` adds the root clamp (two `define_bound` calls, each writing a row and
installing an initialiser only where the declared bound is outside
`0 .. n − 1`). Root cost: `O(n + E)` for this family's own work, but installing
each propagator is quadratic in its trigger count, because
`Propagators::install_returning_id` deduplicates the scope with a linear search
per trigger (`propagators.cc:724–748`), and then unions it into the
constraint's scope with another (`:765–769`), so fixing the first alone leaves
the install quadratic (#1309). That union is per constraint ID, and this
family's three propagators share one. Every propagator here has at least `E`
triggers (the reachability child `n + E + 1`, `DTree`'s in-degree propagator
`E`), so with proofs off the root is quadratic in the graph. Not measured for
this family; `dag.md` measures about 11 s at the root of a 100,000-node path.
With proofs on, the reachability child's `define_proof_model` adds its
`Θ(n · A)` rows.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| root clamp, two initialisers (the reachability child's) | — (once, at the root) | n/a | clamp, in [the inherited table](#inherited-inferences) | the root's declared bounds outside `0 .. n − 1` | n/a | n/a |
| the reachability child's propagator | `on_change`: every `ns`, every `es`, `root` | derived: every `ns` and `es` (vacuously, being `0..1`) and the root | see [`reachable.md`](reachable.md) | always | never claims | never |
| the count child's propagator (`propagate_linear_incremental` once there are at least 8 terms, else `propagate_linear`) | `on_bounds`: every `ns`, every `es` | derived: none | see [`linear.md`](linear.md) | always | as [`linear.md`](linear.md) | as [`linear.md`](linear.md) |
| `DTree`'s in-degree propagator (`graph_rules::propagate`) | `on_change`: every arc that enters a node, which is every `es` | derived: every `es`, vacuously (0/1 variables have no interior) | [indegree-full](#rule-indegree-full), [indegree-overfull](#rule-indegree-overfull) | `DTree` with at least one edge | never claims | never |

The in-degree propagator always returns `PropagatorState::Enable`: it does not
claim idempotence, and it is not self-disabling, even when every arc into every
node is decided. Running it twice in a row infers nothing the second time
(each rule's only effect is to fix every undecided arc into a full node), so a
claim would be true; it is simply not made.

### Mutable state and incrementality

`None` of its own. `graph_rules::propagate` rescans every rule on every call,
so a `DTree` call costs `Σ_v indeg(v) = E` reads whichever arc woke it. A
watch-per-node version would cost the touched node's in-degree instead. As
hotspot context, not a saving: a `perf` profile of the `dsteiner` 5 × 5
benchmark below (proofs off, `86caad24`) puts 1.9% of self time in
`graph_rules::propagate` and about half in the reachability child's propagator
lambdas. `path.md` (next step 4) proposes making `graph_rules` incremental,
where it is 18–31% of propagation on its grid benchmarks; the change is to the
shared helper and would reach `DTree` too, where its share is this small. The
count child
keeps `LinearEquality`'s incremental fold state when it has at least 8 terms
after `tidy_up_linear`, which folds constants out and merges repeated variables:
`n + E` terms for plain variables, only `E` for both spanning-tree wrappers,
whose `ns` is an all-true constant array, and fewer than `n + E` wherever nodes
are fixed, as `steiner`'s and `dsteiner`'s terminals are. The reachability
child is stateless and recomputes per call.

### Interior values and optional pruning

**Offers.** `None.` Nothing here installs a pair, and neither child does.

**Observes.** Holes in the **root**, truthfully, through the reachability child:
a candidate root removed from the middle of the root's domain changes which
regions are reached and which candidates the forcing has to case-split over.
Every other variable this family reads is 0/1 and has no interior, so for them
the question does not arise: their whole vocabulary is the two values, which are
the bounds. Nothing declares `Triggers::holes_affect_propagation`; every entry in
the inventory is `derived`.

### Robustness and limits

**Unbounded domains.** `ns` and `es` must start inside `0..1`. The root may be
anything: `±(2⁶⁰ − 1)`, with and without holes (`{−(2⁶⁰ − 1), −1, 0, 2, 7,
2⁶⁰ − 1}`), enumerates completely with a verified proof in 0.01–0.03 s, both
spellings; the clamp narrows it to node numbers before any propagator runs. An
unbounded MiniZinc `var int: r` gives the same 18 solutions as Gecode on both
versions.

**Negative values and zero.** A negative or out-of-range root value is removed
by the clamp, at the root, with a verified proof.

**Degenerate shapes.** See [Semantics](#semantics): the empty node array is a
throw (and a MiniZinc `=====ERROR=====`, #1305); one node, self loops, parallel
and antiparallel edges, a constant root, constant nodes and edges and a node
variable aliased with an edge variable all enumerate and verify. The strength
sweep's aliasing runs (self loops, parallel edges, one aliased node pair and
one aliased edge pair per instance, 3,000 instances per spelling and seed, two
seeds) found no wrong solution set and no unsound removal.

**Overflow.** The count is a sum of at most `n + E` unit terms. The clamp's bounds
are `0` and `n − 1`. A view offset on the root goes into the clamp and the root
flags' literals, and an offset outside `±(2⁶⁰ − 1)` is refused at construction
since #1214; `x + (2⁶⁰ − 6)` over `x ∈ −(2⁶⁰ − 1) .. 2` verifies. Nothing here
was found to overflow.

### Interval efficiency

**Fine at any width,** because the only variable that can be wide is the root and
the clamp narrows it to at most `n` values before anything walks it.

1. **The propagation side.** This family's own propagator walks rules and arcs,
   never values. The reachability child walks the root's values in four places
   (`reachable.cc:247, 361, 376, 429`) and the node numbers `0 .. n − 1` in one
   (`:488`); every one of them is bounded by `n` once the clamp has run, and the
   clamp is an initialiser, which runs before any propagator. The count child
   reads bounds.
2. **The reason side.** This family's reasons are the arcs fixed to 1 at one
   node: at most its in-degree, one literal per arc, built unconditionally
   (not guarded on `want_reasons()`) and never proportional to width. The
   reachability child's reasons name `root ≠ u` per node `u` of a region and one
   literal per border arc or node, so they are bounded by the graph, never the
   root's declared width.
3. **The proof side.** One line per inference here. The reachability child's
   root flags are one per node, `x[id][v][root] ⇔ root = v`, so the proof names
   the root's equality literals for node numbers only; the root's own bit-sum
   encoding is logarithmic in its declared width (60 bits and a sign at
   `±(2⁶⁰ − 1)`).
4. **The audit lane.** Two rows, `Tree` and `DTree` in
   `gcs/large_domain_audit_test.cc`, pinned `NoWidePosition`, over a three-node
   path with `r ∈ 0..2`. The root is a position a model can make wide (an
   unbounded MiniZinc `var int` is one), and the clamp narrows it before any
   propagator runs. A wide root does not trip the guard: the fact-check ran a
   standalone probe (the lane's rows themselves unchanged) against a build with
   `GCS_LARGE_DOMAIN_GUARD=ON` (`gcs-fd-small-am1-patch-wt/build-guard`, at
   `c9ceea25`, where `tree/`, `reachable/` and `graph_rules` are identical to
   `86caad24`): `Tree` and `DTree` on a three-node path with the root over
   `0..10⁹`, over `±(2⁶⁰ − 1)` and over the holey wide set, full enumeration,
   proofs off and on, 12 runs, no trip, while an `AllDifferent` control over
   four `0..10⁹` variables trips (`tmp/fd-graph/factcheck/tree/guard/`; re-run
   by this audit, same result). At `86caad24` the rows are pinned
   `NoWidePosition`. PR #1302 (open) pins them `Clean`, with a wide-declared
   root, as the safer choice (Ciaran, 2026-10-09: "whichever is safer until we
   have data that argues otherwise"), together with every other index-valued
   position (`Circuit`, `SubCircuit`, `Inverse`, `Reachable`, `Path` and the
   rest), and its guarded run trips nothing. The rows vary nothing else: no holes, no views, no
   constant root. This audit's probes cover those; see
   [Robustness](#robustness-and-limits). `Reachable`, `DReachable`, `Path` and
   `DPath` have the same rows with the same label. The lane is registered as a
   ctest only under `-DGCS_LARGE_DOMAIN_GUARD=ON`, which no CI lane sets
   (#920).

## Inference catalogue

`Tree` makes **no inference of its own**: everything it infers is one of its
children's, under this constraint's ID. `DTree` adds two rules, both from its
in-degree rows through `graph_rules::propagate`. Facts that hold for both of
them:

- **Hint:** `hints::Tree`, `tree` on the wire, one field, `originator`
  (`ConstraintID`): this constraint. No subhint and no payload; the `.scp` says
  whether it is a `tree` or a `dtree`. (The struct's comment says both spellings
  use it. Only `DTree` emits it, since `Tree` has no rule of its own.)
- **No justification reads `state`**: each is a `JustifyUsingRUP` over an
  `ExplicitReason` assembled by the propagator.
- **The rows have no conditions**, so `graph_rules`' backward rule (rule out the
  one open condition of a rule that cannot hold) never fires here.

**The family as a whole achieves `decomposition`**, and which variables that
leaves short differs between the spellings (the sweep under [Tests](#tests)).
For `Tree`, every value of `ns`, of `root` and every `es = 0` kept its support
at the root on the samples of up to four nodes, and only `es = 1` values went
unsupported; from five nodes on, the zero-solution fixpoints lack support on
every variable at once. For `DTree`, values of all five kinds (`es = 1`,
`root = v`, `es = 0`, `ns = 0`, `ns = 1`) go unsupported, in that order of
frequency.

### Inherited inferences

Each of these is documented, with every field, in the family that owns it; the
table says what it means in a tree and what it carries.

| Inference | From | Hint on the `a` line | Documented in |
|---|---|---|---|
| clamp the root to `0 .. n − 1` | the reachability child's `define_bound` initialisers | `initial_bound` (no constraint ID) | [`reachable.md`](reachable.md) |
| a selected edge's endpoints are selected; an edge at an unselected node is not | reachability child | `reachable` | [`reachable.md`](reachable.md) |
| the root is not an unselected node; a fixed root is selected | reachability child | `reachable` | [`reachable.md`](reachable.md) |
| the root is not a node that cannot reach some selected node | reachability child | `reachable` | [`reachable.md`](reachable.md) |
| a node that no candidate root can reach is not selected | reachability child | `reachable` | [`reachable.md`](reachable.md) |
| a cut vertex or bridge of what is left is selected (`Tree`); a node or arc every candidate root needs is selected (`DTree`) | reachability child, cut forcing (always on here) | `reachable` | [`reachable.md`](reachable.md) |
| bounds of `Σ es − Σ ns = −1`: with the node count settled the edges follow, and the other way about, and a count that cannot balance fails | count child | `linear_equality` | [`linear.md`](linear.md) |

On the benchmarks below, the count child almost never fires (0 and 3 of the two
undirected Steiner proofs' assertions; 19 and 14 of the directed ones), because
the reachability child's forcing reaches most of what it would.

### Rule: indegree-full

- **Infers** — `es[b] = 0`, for every undecided arc `b` entering node `v`, once
  an arc `a` entering `v` is selected. `DTree` only.
- **Fires when** — `DTree`'s in-degree propagator runs (any change to an arc
  variable) and the rule `indeg<v>` has exactly one entering arc fixed to 1 and
  some undecided. Rows exist for nodes with a single entering arc too, and can
  never fire.
- **Strength** — `partial`: GAC on its own row only (the at-most-one over the
  arcs entering `v`, on those `es`), together with
  [indegree-overfull](#rule-indegree-overfull).
- **Algorithm** — per call, every rule: count the entering arcs fixed to 1 and
  collect the undecided ones; at the limit, fix the undecided ones to 0.
  `O(E)` per call in arcs, whichever arc changed, since every rule is rescanned.
  Plain at-most-one propagation; no literature needed.
- **Why it is true** — in an arborescence every node has at most one selected
  arc entering it (the root none, every other node exactly one: its parent), so
  with `a` selected no other arc into `v` can be.
- **Proof technique** — `RUP`, against the `indeg<v>` row alone: with the
  negated conclusion `es[b] = 1` and the reason's `es[a] = 1`, the row
  `Σ_{into v} es ≤ 1` is violated. Licensed by **Theorem 2.6** of
  [`justification-techniques.md`](../justification-techniques.md) (the
  inference is stated under its reason), over a row whose terms are 0/1
  literals, as `path.md` cites for the same `graph_rules` rows. No published
  procedure is specific to it; the row is the whole argument. Precondition: the
  row is in the OPB, which it is whenever `v` has an entering arc.
- **Reason** — `es[a] = 1` for the arc fixed to 1. Minimal. One literal, never
  per value; not guarded on `want_reasons()`, and cheap either way.
- **Assertion** — `es[b] = 0 ∨ es[a] = 0`, i.e. `~es[b] + ~es[a] ≥ 1`. Measured at
  `Inferences` on a four-node `DTree` where edges 3 and 4 both enter node 3:
  ```
  a 1 ~i[e4][b0] 1 ~i[e3][b0] >= 1::tree:((constraint_id _1));
  ```
  If `es[b]` is already 0 nothing is inferred; it is never already 1 here,
  because that is [indegree-overfull](#rule-indegree-overfull)'s case.
- **Hint** — `hints::Tree`, as in the preamble.
- **Offline reconstructibility** — `offline`: the clause is two arcs into one
  node, the `.scp` gives the edge list, and the clause is RUP against that
  node's row (or simply against the whole OPB).
- **Proof size** — one `rup` line of two literals per removed arc, so
  `O(indeg(v))` lines per firing, in arcs; independent of everything else.
- **Gaps** — `None.`
- **Tightness** — no lane. A one-off at `86caad24`
  (`tmp/fd-graph/tree/assert/mut/`), on a four-node `DTree` with 27 solutions
  whose uncorrupted proof verifies: dropping the reason literal from the first
  such step (`rup 1 ~i[e4][b0] >= 1` for `rup 1 ~i[e4][b0] 1 ~i[e3][b0] >= 1`)
  is refused there as not RUP, and so is the uncorrupted proof against an OPB
  with the `indeg3` row deleted. Neither is a ctest lane.

### Rule: indegree-overfull

- **Infers** — a contradiction: two or more arcs entering `v` are selected.
  `DTree` only.
- **Fires when** — the in-degree propagator finds more than one arc into `v`
  fixed to 1. Search alone never gets there, because
  [indegree-full](#rule-indegree-full) removes the second arc as soon as the
  first is decided; it takes another propagator fixing two at once, or initial
  domains. Reached by a five-node probe (arcs `0→2` and `1→2` fixed to 1, root
  0, slack elsewhere so neither child fails first); not reached by
  `tree_test`, whose only shape with a node of in-degree two is `triangle`.
- **Strength** — as [indegree-full](#rule-indegree-full).
- **Algorithm** — the same scan.
- **Why it is true** — as [indegree-full](#rule-indegree-full).
- **Proof technique** — `RUP` against `indeg<v>`: the reason alone violates the
  row. Theorem 2.6 over 0/1 literals, as above.
- **Reason** — every arc into `v` fixed to 1. **Not minimal** when there are
  three or more: any two suffice.
- **Assertion** — `contradiction()`, so `¬reason`, with no attempted literal.
  Measured at `Inferences`:
  ```
  a 1 ~i[e0][eq1] 1 ~i[e1][eq1] >= 1::tree:((constraint_id _1));
  ```
  (the two arcs were created fixed, hence `eq1` atoms). With a limit of 1 and
  two arcs this clause has the same shape as an indegree-full assertion
  (`¬es[b] ∨ ¬es[a]`), so the two rules cannot be told apart by shape on the
  wire. indegree-full itself never makes a failed inference: it only infers on
  undecided arcs.
- **Hint** — `hints::Tree`.
- **Offline reconstructibility** — `offline`, as indegree-full.
- **Proof size** — one line per firing, its length the number of selected
  entering arcs.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

- **`tree_test`** (ctest `tree_constraint`, through `run_test_only.bash`):
  eleven fixed shapes (`single`, `path3`, `triangle`, `square`, `two_pieces`,
  `lollipop`, `antiparallel`, `lollipop_root0`, `lollipop_pinned`,
  `square_edges`, `path3_wide_root` with the root over `−1..4`), each for both
  spellings, with and without proofs: 44 runs, 22 of them verified by VeriPB
  when it is on the `PATH`. Plain `solve_for_tests` against an oracle that
  checks "connected and acyclic" directly rather than the decomposition:
  enumeration and the proof, **no consistency check**, deliberately (the class
  comment says why). Seeded through `establish_and_announce_seed`, which fixes
  the random brancher; the shapes are fixed, so the seed changes only the
  branching. The idempotence-claim checker is on, and this family never claims.
- **MiniZinc lanes:** `minizinc-tree` and `minizinc-dtree` enumerate a
  triangle-with-a-tail indexed from 2 against MiniZinc's default solver, with
  proofs, behind a `--fzn-pattern glasgow_tree` / `glasgow_dtree` guard;
  `minizinc-steiner` compares the optimum, with a proof, also guarded.
- **`scp_reader_test`:** the tree family's enumerations through the reader, and
  the write → read → write round trip.
- **Audit lane:** the `Tree` and `DTree` rows, `NoWidePosition`; registered as
  a ctest only under `-DGCS_LARGE_DOMAIN_GUARD=ON`, which no CI lane sets
  (#920).

**Runtime caps.** `tree_constraint` neither sets nor clears a cap, so it runs
under the suite defaults; they never fire. With
`GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500 tree_test --seed=1` at
`86caad24` all 44 runs complete (the largest has 40 solutions), no
`[truncated run` line appears, and all 22 proofs verify, in 0.42 s.

**Mutation lanes:** none for this family. `Reachable`'s
`reachable_mutation_*` lanes corrupt `Reachable`'s reasons, through an option
`Tree` does not expose, so no lane reaches a `Tree`. The one-off above is the
only tightness evidence for the in-degree rule.

**This audit's own checks**, all at `86caad24`, with their harnesses under
`tmp/fd-graph/tree/`:

- **Strength and soundness** (`strength/strength.cc`): random graphs of up to
  four or six nodes and seven edges, each node and edge variable free (70%) or
  fixed to 0 or 1 (15% each), the root over a random subset of `−1 .. n`; every
  solution by brute force; at every search node, which values left have no
  support; at the root, whether any removed value had one; and the solution set.

  | sample (3,000 instances each) | root not GAC | any node not GAC | missing kinds at the root |
  |---|---|---|---|
  | `Tree`, ≤ 4 nodes, seeds 1 / 2 / 3 | 26 / 22 / 26 | 78 / 72 / 77 | `es = 1` only |
  | `Tree`, ≤ 5 nodes, seed 21 | 35 | 128 | `es = 1`, plus one zero-solution instance |
  | `Tree`, ≤ 6 nodes, seed 1 / seed 21 | 24 / 46 | 108 / 106 | `es = 1`, plus one zero-solution instance at each seed |
  | `DTree`, ≤ 4 nodes, seeds 1 / 2 / 3 | 201 / 203 / 223 | 289 / 296 / 311 | `es = 1` most, then `root = v` (about half as many), then `es = 0`, `ns = 0`, `ns = 1` |
  | `DTree`, ≤ 6 nodes, seed 1 / seed 21 | 202 / 198 | 257 / 270 | as above |
  | either spelling, ≤ 4 nodes, self loops, parallel edges and aliasing, seeds 11 and 12 | 318–347 | 328–359 | all kinds (consistency is not claimed under aliasing) |

  **No run produced a wrong solution set or an unsound root removal.**
  Smallest witnesses: `DTree` on arcs `1→0`, `0→1` with the root fixed to 1
  keeps `0→1`, an arc into the root; on the cycle `2→0`, `1→2`, `0→1` with
  `1→2` selected it keeps `root = 2`, the head of a selected arc. `Tree` on
  edges `1–0`, `2–1`, `2–0`, `3–1` with `2–1` and `2–0` selected and node 0
  selected keeps `1–0`, which closes the triangle. That needs a fourth node:
  on a bare triangle the count has no slack, and removes the third edge.
- **What the two missing inferences would buy**, by posting them alongside as
  ordinary constraints (`NotEqualsIf(root, head(a), es[a] = 1)` per arc for
  "nothing enters the root", one `LinearLessThanEqual` per cycle of the
  underlying undirected multigraph for "no selected cycle"), seed 1, 3,000
  instances:

  | | ≤ 4 nodes: root / any node not GAC | ≤ 6 nodes |
  |---|---|---|
  | `Tree` as shipped | 26 / 78 | 24 / 108 |
  | `Tree` + cycle rows | **0 / 0** | **0 / 0** |
  | `DTree` as shipped | 201 / 289 | 202 / 257 |
  | `DTree` + nothing into the root | 73 / 126 | 62 / 91 |
  | `DTree` + cycle rows | — | 126 / 167 |
  | `DTree` + both | 29 / 57 | 23 / 34 (all `es = 1`) |

  The `DTree` remainder is measured: with both additions, 29 / 57 at up to
  four nodes and 23 / 34 at up to six, every missing value an `es = 1`. That
  these need a case split over the root (an arc whose only supports would
  enter whichever node the root turns out to be) is a reading of the
  witnesses, not a measurement.
- **Frontends** (`frontends/diff.py`): 1,930 random instances (up to five nodes
  and seven edges, random fixings, the root over a range that may leave
  `0 .. n − 1`) through the seven-argument `_int` spelling and the
  five-argument `_enum` spelling with node index sets starting at 0, 3 and −2
  and edge index sets at 0, 5 and −4, each of `tree` and `dtree` 212 to 275
  times: Glasgow and Gecode on MiniZinc 2.9.7 and 2.10.1, and
  `glasgow_scp_solver --all` on the same instance as `.scp`, all equal to a
  Python oracle, 10,405 solutions in all. `frontends/diff_opt.py`: 200 random
  `steiner`, `dsteiner`, `weighted_spanning_tree` and
  `d_weighted_spanning_tree` optimisations (69 of them infeasible), the same
  optimum from Glasgow, Gecode and brute force on both versions, and
  `glasgow_tree` or `glasgow_dtree` in every flattened model. **A weakness in
  these two harnesses:** they read a Glasgow or `.scp` `=====ERROR=====` as "no
  solutions", so an error on an instance whose answer is unsatisfiable (363 of
  the 1,930, and the 69 infeasible optimisations) would have passed, and neither
  checked that an optimisation run reported `==========`. The fact-check re-ran
  both with error and completeness detection (`tmp/fd-graph/factcheck/tree/
  frontends/diff_fc.py`, `opt_fc.py`): 360 fresh instances at seed 9101, 120
  optimisations at seed 9202, and this audit's 200 optimisations at seed 1, all
  with 0 mismatches. So the conclusion stands on those runs, not on the
  original harnesses alone.
- **Assertions against solutions** (`checka/checka.py`): every `reachable`,
  `linear_equality` and `tree` assertion at `Inferences`, in four enumeration
  proofs (four and five nodes, both spellings, 27 to 444 solutions, 804 family
  assertions), checked against every solution the same proof logs. None is
  falsified.

**What the tests do not cover.**

- **Strength**, deliberately; this audit's sweep is the only measurement.
- **The in-degree rule, nearly.** In `tree_test` only `triangle` has a node
  with two entering arcs; on every other shape each node has at most one, so
  `DTree`'s own propagator has nothing to do. indegree-overfull is reached by
  no test.
- **Views, constants and aliasing** in `tree_test` (constant nodes and edges
  appear only through `lollipop_pinned`, `square_edges` and the fixed root).
  The probes above cover them; nothing in the suite does.
- **A wide or holey root** beyond `path3_wide_root`'s `−1..4`.
- **`dsteiner`, `weighted_spanning_tree`, `d_weighted_spanning_tree`** and the
  seven-argument `dtree` have no MiniZinc lane; only `steiner` and the
  five-argument `tree` and `dtree` do. Nor does the empty graph (#1305).
- **Real instances.** None exists to port; see the next section.

### Benchmarks and examples

- **In the repository:** none in `examples/` or `benchmarks/`; the MiniZinc
  lanes' three small models.
- **Corpus:** no MiniZinc Challenge instance in the 285-instance flattened
  corpus at `tmp/fd-table/corpus/fzn/` reaches `glasgow_tree` or
  `glasgow_dtree`; a source grep of `mzn-challenge-a8448864` agrees.
  `2018/steiner-tree` defines its own `my_fzn_tree` decomposition, so it never
  reaches the class, and
  `2026/surface-based-tsp` posts `tree(T, E, …)` but has no data files in the
  checkout (`mzn-challenge-a8448864`).
- **For CPU:** `steiner` and `dsteiner` on a `k × k` grid, weights 1–5 drawn with
  a fixed seed, the four corners and the centre as terminals, `dsteiner` with
  both arcs per grid edge and its root at a corner
  (`tmp/fd-graph/tree/bench/gen.py k 1 steiner|dsteiner`). `k = 4` is too small
  to time well (0.05 s); `k = 5` takes 5.8 s and 11.1 s.
- **For proofs:** the same at `k = 4`, whose `Off` proof is 14 MB and checks in
  9 s. **Do not run `k = 5` with proofs uncapped:** it searches 158,000 nodes
  against `k = 4`'s 1,472, so expect a proof two orders of magnitude larger.

These benchmarks are dominated by the **reachability child**, not by this
family: `steiner` runs no rule of `Tree`'s own (there are none) and the count
fires 0 to 3 times per proof; in `dsteiner` the in-degree rule is about a tenth
of all `a` lines and 41–45% of those carrying this constraint's ID. A
per-inference cost read off them is the reachability child's.

### CPU performance

*Release build of `86caad24`; Gecode 6.3.0 (`fzn-gecode` from the MiniZinc
2.9.7 bundle); fataepyc-10, `taskset -c 112`, serial,
`GLIBC_TUNABLES=glibc.malloc.mmap_threshold=33554432:glibc.malloc.trim_threshold=4294967295`;
wall time of the whole `fzn-*` run under `perf stat`, flattening excluded,
median of five (one at `k = 5`); proofs off; 2026-10-09. "Glasgow, decomposed"
is the same binary with the four `fzn_tree`/`fzn_dtree` overrides removed from
its `mznlib`, so it runs the standard library's parent-and-distance labelling,
except that the labelling's own `subgraph(…)` call still reaches Glasgow's
`Subgraph` propagator (one `glasgow_subgraph` in each decomposed flattening).
Gecode runs the labelling with `subgraph` decomposed too.*

| instance | optimum | Glasgow, `Tree` / `DTree` | recursions | `instructions:u` | Glasgow, decomposed | recursions | Gecode | nodes |
|---|---|---|---|---|---|---|---|---|
| `steiner`, 3 × 3 | 14 | 0.008 s | 170 | 1.6·10⁷ | 0.190 s | 4,989 | 1.82 s | 182,717 |
| `dsteiner`, 3 × 3 | 12 | 0.009 s | 73 | 1.6·10⁷ | 0.020 s | 503 | 0.138 s | 12,243 |
| `steiner`, 4 × 4 | 16 | 0.048 s | 1,472 | 2.1·10⁸ | 266 s | 4,478,535 | not optimal at 900 s | 54,099,359 |
| `dsteiner`, 4 × 4 | 18 | 0.061 s | 1,023 | 3.2·10⁸ | 7.61 s | 241,969 | 106 s | 6,280,976 |
| `steiner`, 5 × 5 | 28 | 5.83 s | 157,922 | 3.0·10¹⁰ | no solution at 600 s | 7,477,135 | no solution at 600 s | 27,071,862 |
| `dsteiner`, 5 × 5 | 32 | 11.1 s | 107,991 | 7.6·10¹⁰ | no solution at 600 s | 7,407,340 | no solution at 600 s | 23,949,253 |

The Glasgow 3 × 3 times are under the 10 ms where a wall time means much; read their
recursion and instruction counts. A timed-out run reports the cap, not the
search (`bench/bench_small2.txt`, `bench_k5_2.txt`; `bench/runbench.py`). An
earlier run of the two 5 × 5 instances, without the fixed malloc thresholds
and not under `perf stat`, took 16 s and 33 s for the same recursion counts;
the cause was not chased, and those figures are not used.

The three columns do not search the same tree, and the strengths differ by
construction: Glasgow's `Tree` is the reachability propagator plus a count,
while Gecode and "Glasgow, decomposed" propagate the labelling's element and
reified constraints (plus Glasgow's `Subgraph` in the latter). So this is a
comparison of **models**, not of propagators (#868). It does show the scale of
what the overrides buy, and that the recursion counts, not the per-node cost,
carry it: on `steiner` 4 × 4 Glasgow's `Tree` spends about 144,000 instructions
per recursion, the decomposition 317,000 and Gecode 88,000.

### Proof performance

*Same build and machine, `taskset -c 113`; VeriPB 3.0.2 with
`--force-checked-deletion`; the `fzn-glasgow --prove` route on the same flattened
models, to optimality; 2026-10-09.* Assertion levels through
`GCS_ASSERTION_LEVEL`.

| instance | nodes | OPB rows (`Off`) | `Off`: lines | bytes | VeriPB | `Definitions`: lines, VeriPB | `Links` | `Inferences`: lines, VeriPB |
|---|---|---|---|---|---|---|---|---|
| `steiner`, 3 × 3 | 170 | 734 | 4,502 | 454 KB | 0.16 s | 2,416, 0.02 s | fails[^links] | 1,823, 0.01 s |
| `dsteiner`, 3 × 3 | 73 | 731 | 2,126 | 140 KB | 0.02 s | 1,535, 0.01 s | fails[^links] | 996, 0.01 s |
| `steiner`, 4 × 4 | 1,472 | 2,289 | 77,252 | 14.4 MB | 8.93 s | 27,915, 0.28 s | fails[^links] | 26,539, 0.11 s |
| `dsteiner`, 4 × 4 | 1,023 | 2,309 | 34,605 | 3.0 MB | 0.85 s | 20,168, 0.21 s | fails[^links] | 18,885, 0.07 s |

[^links]: At the first `soli` line, "the propagated assignment does not satisfy
    the constraint", on all four: #1210, the generic `Links` failure whenever a
    variable is wider than `{0,1}` (the objective, and for `steiner` the root;
    `dsteiner`'s root is the constant 1). Not this family's.

The `steiner` OPBs are smaller at `Inferences` (696 and 2,223 rows), which
leaves out only the equality and order atom definitions of a proof-only view of
the root (`@po[0][eq…]`, `@po[0][ge…]`); `dsteiner`'s root is a constant, and
its OPB is the same at every level. `Off` verifies (`s VERIFIED BOUNDS`) on all
four; `Definitions` and `Inferences` are accepted `UNDER ASSERTIONS`. The solve
with proofs takes 0.02 to 0.15 s, so checking the undirected `4 × 4` proof costs
about 60 times the solve, and the directed one about 8 times.

**Where the assertions come from**, at `Inferences` (`proof/split.py`), as a
share of all `a` lines:

| instance | `a` lines | `reachable` (this ID) | `tree` (in-degree) | `linear_equality` (the count) | other constraints | search |
|---|---|---|---|---|---|---|
| `steiner`, 3 × 3 | 1,356 | 523 (38.6%) | — | 0 | 658 (48.5%) | 175 (12.9%) |
| `steiner`, 4 × 4 | 22,270 | 9,712 (43.6%) | — | 3 (0.0%) | 11,074 (49.7%) | 1,481 (6.7%) |
| `dsteiner`, 3 × 3 | 756 | 103 (13.6%) | 85 (11.2%) | 19 (2.5%) | 471 (62.3%) | 78 (10.3%) |
| `dsteiner`, 4 × 4 | 15,809 | 2,026 (12.8%) | 1,688 (10.7%) | 14 (0.1%) | 11,051 (69.9%) | 1,030 (6.5%) |

"Other constraints" are the objective's linear equality and the
Boolean-to-integer channelling MiniZinc adds for `es[e] * w[e]`; "search" is
backtracking and the objective's improvement lines.

**The undirected proof's size is the open root.** The `steiner` wrapper makes
the root an existential `var 1..N`, so every cut-vertex and bridge forcing the
reachability child makes before search fixes the root is in its open-root
regime, one temporary line per candidate root ([`reachable.md`](reachable.md);
each of those lines carries the whole forcing reason, #1312).
The same `4 × 4` model written as `tree(…)` plus the weighted sum, once with a
free root and once with the root fixed to a terminal corner (which every
solution contains, so the optimum is the same 16), gives 77,252 lines, 14.3 MB
and 8.78 s to check against 34,847 lines, 3.2 MB and 0.75 s (1,472 and 1,369
search nodes, so the search differs too; `proof/treefree_k4.mzn`,
`treefixed_k4.mzn`). `dsteiner` fixes its root and pays none of this.

**Own against shared**, in the OPB: see the size table under [OPB
encoding](#opb-encoding). This family's own rows are 2 for `Tree` and `2 +
(nodes with an entering arc)` for `DTree`, against the reachability child's
`Θ(n · A)`: 0.005% and 0.18% of an 8 × 8 grid's OPB.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference this family makes is a RUP against its own row, and the
children's are justified as their documents say. Proofs do not change what is
propagated: nothing in `tree.cc` or `graph_rules` depends on whether a logger is
present, and the reachability child's forcing is on with and without proofs.

The defect `SmartTable` and `Circuit`'s SCC propagator share since `4a433958`, an
inference asserted as a bare unit clause with no reason (for the SCC propagator
an assignment, `succ[v] = u`, for *fix required*, `circuit_scc.cc:1029`, and
removals for the two *prune skip* rules, `:979`) at `Definitions`, `Links`
and `Inferences`, is **deliberately unfiled** (Matthew will meet it when the
justifier is ready to deal with it; see [`circuit.md`](circuit.md) and
[`smart_table.md`](smart_table.md)). It does not occur in this family: the
assertion check above found none of 804 family assertions falsified by a logged
solution, and every one carries its reason.

### Known limitations

- **Not GAC, in two ways.** Neither spelling removes an edge that would close a
  cycle with edges already selected until the count runs out of room, and a
  cycle among selected edges can leave the root fixpoint standing with no
  solution (#1315). `DTree` does not remove an arc into the root, or a root
  candidate that a selected arc enters (#1314). The class comment names the
  first and not the second.
- **The proof is as large as the reachability child makes it**: `Θ(nodes ×
  arcs)` rows before search, and, with the root existential (every `steiner`),
  a line per candidate root for every forcing made while the root is open. See
  [`reachable.md`](reachable.md) and
  [`connectivity-proofs.md`](../connectivity-proofs.md).
- **`DTree`'s forcing costs a search per candidate root per node and arc** on
  every call, and there is no switch to turn it off from a tree (#1316).
- **An empty graph is an error through MiniZinc** (`tree(0, 0, …)`,
  `dtree(0, 0, …)`, `dsteiner(0, 0, …)`, `d_weighted_spanning_tree(0, 0, …)`),
  where the standard library reports unsatisfiable (#1305).
- **No `cake_pb_cp` coverage**: the encoding is checked only against itself.

### Next steps

1. **`DTree`: nothing enters the root** (#1314). One conditional row
   per node, `root = v ⇒ Σ_{into v} es ≤ 0`, exactly `DPath`'s `startin<v>`;
   `graph_rules` already propagates it both ways (forwards it removes every arc
   into a fixed root, backwards it removes `root = v` once an arc into `v` is
   selected). On the sample it cuts `DTree`'s non-GAC root fixpoints from 201 to
   73 at four nodes and from 202 to 62 at six. **The catch is the proof**: the
   clause `root ≠ v ∨ es[a] = 0` is not a RUP against the current encoding
   (checked on a four-node `DTree`), so it is either a non-definitional OPB row,
   which the template's standard rules out, or a derivation: from the
   unfolding, every selected non-root node has a selected arc in; summed against
   the count, that leaves the root none. That is a counting argument and wants
   the second opinion `CLAUDE.md` asks for before it is written. The label
   cannot be `rootin<v>`, which the reachability child uses.
2. **No selected cycle** (#1315). A union-find over the selected
   edges, removing any undecided edge whose endpoints are already joined, is the
   strengthening the class comment names; posting one `Σ_{e∈C} es ≤ |C| − 1` per
   cycle `C` made `Tree` GAC at every search node of both 3,000-instance
   samples, up to four and up to six nodes. The
   propagation is near-linear; the proof is the work. The cycle clause is RUP
   only when the count has no slack (it is on a four-node graph whose other
   edges are forced, and is not on a triangle with a two-edge tail), so in
   general it needs the same counting argument as item 1: a connected selection
   of `k` nodes containing a cycle has at least `k` edges. Worth doing for
   `Tree`, where it is the whole of the gap; for `DTree` it is the smaller half.
3. **The empty graph through MiniZinc** (#1305). Post a false
   constraint from `prepare()` instead of throwing, or have the int overrides
   say `false` for an empty node set, so that `tree(0, 0, …)` is unsatisfiable
   as it is everywhere else. Trivial. `reachable` and `dreachable` error the
   same way; `path` and `dpath` too, but `PathBase::prepare` throws before its
   child is installed, so `Path` needs its own fix; the directed `dsteiner` and
   `d_weighted_spanning_tree` wrappers reach it through `dtree`. **Not** the
   same defect as `dag` and the four-argument `subgraph` over an empty node set
   (#1303), which are satisfiable and flattened to a wrong
   UNSAT, and whose fix is an mznlib guard returning `true`. Copying that
   `then true` guard into this family's rooted `_enum` overrides would turn
   their accidental but right UNSAT into a wrong SAT.
4. **Correct three passages outside this document** (trivial, comment and
   design-note text only). `minizinc/mznlib/fzn_tree_enum.mzn:8–12` and
   `connectivity-proofs.md:376–380` ("One reachability encoding, not two") both
   say doubling the edges would double the `O(nodes × edges)` encoding; it would
   not (see the footnote under [Concrete
   constraints](#concrete-constraints-and-frontend-coverage)); only a second
   spanning tree would. `connectivity-proofs.md:402–412` ("These are not GAC")
   and `tree.hh:91` name cycle closure as the gap, and leave out `DTree`'s
   larger one, nothing entering the root (#1314).
5. **Land PR #1302** (open), which re-pins the `Tree` and `DTree` audit-lane
   rows `Clean` with a wide-declared root, the safer choice Ciaran picked; see
   [Interval efficiency](#interval-efficiency), item 4.
6. **Tests.** A `DTree` shape with several nodes of in-degree two or more, so
   that indegree-full fires on more than one node, and one that reaches
   indegree-overfull; views and aliasing in `tree_test`; `dsteiner` and the
   spanning-tree wrappers as MiniZinc lanes. Small.
7. **Tidying.** Skip in-degree rows for nodes with a single entering arc, which
   can never fire; that is `path.md`'s next step 7 (skip any `graph_rules` row
   whose variable count does not exceed its limit), one change in the shared
   helper or its callers. Fix `hints.hh`'s "both spellings use it". Trivial.

## Prior art

The propagation here is a decomposition and claims no algorithm of its own;
connectivity is `Reachable`'s, whose encoding is ours
([`connectivity-proofs.md`](../connectivity-proofs.md)). The tree constraints in
the literature are a different shape. Beldiceanu, Flener and Lorca's `tree`
(CPAIOR 2005), revisited by Fages and Lorca (CP 2011), partitions a whole
digraph given by successor variables into a bounded number of
anti-arborescences, with filtering through dominators and strongly connected
components; Dooms and Katriel's minimum spanning tree constraint (CP 2006) is the
weighted spanning-tree relative. MiniZinc's `tree` and `dtree` are subgraph
selections over a fixed graph with a single root, and the standard library
decomposes them into a parent-and-distance labelling. We know of no earlier
certified propagation of either: what is new here is the reachability unfolding
that makes connectivity a plain RUP, which this family inherits, with the
count and the in-degree rows on top of it.

## Further reading

- [`connectivity-proofs.md`](../connectivity-proofs.md): the reachability
  encoding and every proof idea this family uses. Its section "The tree and path
  family, on top of this" explains why one reachability encoding serves `Tree`,
  `DTree`, `Path` and `DPath`, why the counting rows are the constraint's own
  rather than more children, and why they are not GAC (though its "One
  reachability encoding, not two" overstates what doubling costs, and its
  "These are not GAC" omits `DTree`'s root in-degree gap; see next step 4);
  "Measured, on a grid
  Steiner tree" is the original decomposition-against-propagator comparison, on
  a different instance from the one above.
- [`reachable.md`](reachable.md): the child that does almost all the work.
- [`path.md`](path.md): the other user of `graph_rules`, which documents its
  backward rule and its `Selected` rows.
- [`linear.md`](linear.md): the count child.
- [`constraints.md`](../constraints.md), on the ceiling of one child per label
  namespace, which is what put the in-degree rows here.
