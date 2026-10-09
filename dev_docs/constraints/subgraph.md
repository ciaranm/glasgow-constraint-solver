# `Subgraph`: every selected edge has both its endpoints selected

> **Maturity** production ·
> **Audited** 2026-10-09 at `86caad24` ·
> **Open issues** filed by this audit: #1303 (the four-argument MiniZinc
> spelling over an empty node set is reported unsatisfiable; one issue with the
> same line in `fzn_dag.mzn`), #1311 (every call rescans every edge, so the
> class is slower than the two clauses per edge it replaces). Also touching
> this family: #1309 (the engine's propagator install is quadratic in the
> trigger count). Already open and touching this family: #868 (cross-solver
> comparisons; this document gives one, by hand). Tracked under #871.

`Subgraph(edges, ns, es)` is MiniZinc's `subgraph`: over a fixed edge list, 0/1
node and edge variables, and the single condition that a selected edge has both
endpoints selected. It is two binary clauses per edge, encoded as exactly those
two rows, and one propagator runs both directions of each clause, with every
inference a one-line RUP against the row for that edge and endpoint. The header
says what it is for: the constraint "exists for the sake of the C++ and `.scp`
interfaces rather than because it infers anything a decomposition would not".

Three things to know before touching it.

- **It is generalised arc consistent on the node and edge variables, as long as
  no variable appears in two positions with opposite signs.** Checked by brute
  force on 24,000 random instances with distinct variables, constants, positive
  sharing, and offset or negated views at distinct positions: no failure. A position that is the view `1 − x` of a
  variable used positively elsewhere loses it (in 33–36% of the small random
  instances that share a variable with opposite signs, fewer on larger graphs), which only the C++ API can build: MiniZinc's `not x` arrives as a second
  variable, and the `.scp` reader takes no views at all.
- **It costs more than the decomposition it stands in for.** Each call walks
  every edge, whatever woke it, where the clauses wake only on their own two
  variables. On a 5×5 grid model through MiniZinc the override takes 11.0 s
  against the stdlib decomposition's 6.9 s, on the same 1,461,275 nodes; on a
  path of 10,000 edges with 12 of them undecided it is 9.4 times slower. A
  candidate with one propagator per edge, which disables itself once its edge is
  decided or entailed, is as fast as the decomposition or slightly faster, with
  fewer calls (#1311).
- **Its rows and its propagation loop are copied, not shared.** `Reachable`
  (and so `Tree`, `DTree`, `Path` and `DPath`) and `Dag` each write the same
  `sgf`/`sgt` rows under their own constraint ID and run the same two rules in
  their own propagators, under their own hints. Nothing calls this class. A fix
  here does not reach them, and theirs does not reach it.

## What it is

### Semantics

`Subgraph(edges, ns, es)`: nodes are numbered from zero; `edges[e]` is the pair
of endpoints of edge `e`; `ns[i]` and `es[e]` are 0/1 variables saying whether
node `i` and edge `e` are selected. It holds when, for every `e = (u, w)`,
`es[e] = 1` implies `ns[u] = 1` and `ns[w] = 1`. Edges are undirected for this
purpose (the stdlib's "directed graph" changes nothing, since both endpoints are
treated alike), and nothing requires a selected node to be on a selected edge,
so all-zero is always a solution.

- **No edges:** the constraint says nothing. `prepare` still checks the arrays
  (below) and then returns `false`, so no rows and no propagator are installed
  (`subgraph.cc:81`).
- **No nodes:** only with no edges, since an edge must name two nodes.
- **Self loops and parallel edges** are ordinary edges. A loop's two rows are
  the same row, written twice.
- **Constants** are accepted in either array.
- **A shared variable** is accepted anywhere, including as both a node and an
  edge.

`prepare` throws `InvalidProblemDefinitionException` when `es` and `edges` differ
in length, when an endpoint is not less than `ns.size()`, or when any variable's
initial bounds leave `0..1` (`subgraph.cc:61–81`). The last check uses the
initial state at prepare time, so a variable declared over `0..5` is refused
even if another constraint would cut it to `0..1`.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Subgraph` | ✓ `fzn_subgraph` (both spellings)[^mznsub] | n/a[^xsub] | n/a[^cpsub] | ✓ `subgraph` | the reified form decomposes[^reif] |

[^mznsub]: `minizinc/mznlib/fzn_subgraph_int.mzn` takes the six-argument
    `subgraph(N, E, from, to, ns, es)`, whose nodes are `1..N`, and subtracts one
    from each endpoint. `fzn_subgraph_enum.mzn` takes the four-argument
    `subgraph(from, to, ns, es)`, whatever its index sets, and subtracts
    `min(index_set(ns))`. Both call `glasgow_subgraph`, which
    `fzn_glasgow.cc:978–984` posts after `edges_from_endpoints` (shared with the
    other graph families) has refused a negative endpoint. Over an empty node
    array the four-argument override gives the wrong answer: see [Robustness and
    limits](#robustness-and-limits) and #1303.

[^xsub]: XCSP3-core has no subgraph constraint.

[^cpsub]: `n/a`, as the frontend support matrix records it. `gcspy` binds
    nothing in this family; whether CPMpy has a `subgraph` global was not
    checked.

[^reif]: There is no override for `fzn_subgraph_reif`, so
    `b <-> subgraph(...)` gets the stdlib's decomposition and never reaches this
    class. Its solutions agree with Gecode's (`mzn/m7_reif.mzn`, 64 solutions).

**The MiniZinc routes were diffed against Gecode**, with every solution
compared, on MiniZinc 2.9.7
and 2.10.1 (`tmp/fd-graph/subgraph/mzn/run.sh`, at `86caad24`). Gecode's own
mznlib has no override for any graph constraint, so Gecode reads the stdlib
decomposition here, and the extra run with `-G std` is the same reference again,
not a second one. They agree on
both versions for: the six-argument form; the four-argument form with node index
sets starting at 0, 2, 3 and −2 and edge index sets starting at 0 and 5; a real
`enum`; self loops with parallel edges; constant entries; `not x` entries; nodes
with no edges in either spelling; `N = 0` in the six-argument form; and the
reified form. They disagree in three shapes, none of them reached by a corpus
model:

| Shape | Glasgow | Gecode (the stdlib decomposition) |
|---|---|---|
| four-argument form, no nodes (`m10`, `m17`) | `=====UNSATISFIABLE=====`, from MiniZinc itself | 2 solutions |
| six-argument form, an endpoint of 0 (`m11`) | `=====ERROR=====`: "subgraph has a negative edge endpoint" | 5 solutions |
| six-argument form, an endpoint of `N + 1` (`m16`) | `=====ERROR=====`: "Subgraph has an edge endpoint that is not a node" | 5 solutions |

The first is a wrong answer (#1303). In the other two the stdlib reads the
out-of-range `ns` entry as undefined, which MiniZinc's relational semantics turns into `false`,
so the edge is forced out; its documentation asks for endpoints in `1..N`, but
only the four-argument spelling asserts it. Through Glasgow they are errors,
not wrong answers. The six-argument form with a non-1-based `from` is a stdlib
assertion failure for every solver alike (`m14`).

`minizinc/tests/subgraphtest.mzn` (four nodes indexed from 2) is the registered
lane, with `--fzn-pattern glasgow_subgraph`, so it cannot pass against the
decomposition. Run by hand at `86caad24`, it passes on both MiniZinc versions and
its proof verifies (49 solutions).

**The `.scp` route** was checked on 900 random instances (distinct variables,
constants, positive sharing; seed 11), each written by the solver and read back
by `glasgow_scp_solver --all`: every solution count matches brute force
(`proofs/scpsweep.sh`). With views in the arrays, 277 of 300 files are refused
on reading with `S-expression error: expected an atom, found a list`: the writer
spells a view as a list, `(-_4 + 1)`, and `resolve_variable`
(`scp_reader.cc:141`) takes atoms only. That is the reader's limitation, as
[`in.md`](in.md) and [`all_equal.md`](all_equal.md) record, not this family's.
The 23 files without a view agree.

### Options

`None.` There is no consistency tag.

### Variable kinds and views

Plain variables, constants and views of either sign, provided every one has
initial bounds inside `0..1`. The propagator reads only
`optional_single_value`. **The proof handles views.** Each row is written over
the position's own literal, so a view is spelled through the view layer's
proof variable (`p[0_view_of_y_plus_-3][eq1]`; see
[`view-proof-logging.md`](../view-proof-logging.md)), and an offset of `2⁴⁰`
works as well as one of 3. 300 random instances with offset and negated views at
distinct positions, and 300 with them shared, each enumerated to the end with
proofs on, all verify, with brute-force solution counts (`proofs/sweep.sh`,
modes `viewdistinct` and `viewalias`, seed 7).

### Reification

`None` in the class. MiniZinc's reified `subgraph` reaches the stdlib's
decomposition, which is fine: the constraint is a conjunction of clauses, and a
reified conjunction of clauses decomposes without loss. No reified class is
wanted.

### Relation to other families

- **Decomposes into it:** MiniZinc's `subgraph`, only when posted directly. The
  stdlib's `fzn_dreachable` and `fzn_dtree` call `subgraph` themselves, and
  `fzn_dpath` does too, its int spelling through `fzn_dtree` and its enum
  spelling directly (`fzn_dpath_int.mzn:13`, `fzn_dpath_enum.mzn:40`). Glasgow
  overrides all three, so those calls never happen.
- **Child constraints:** none.
- **Shares code:** none. **It shares an encoding, by copy.**
  `ReachableBase::define_proof_model` (`reachable.cc:137–145`) and
  `Dag::define_proof_model` (`dag.cc:189–197`) write the same two rows per edge,
  with the same labels `sgf<e>` and `sgt<e>`, under their own constraint IDs, and
  both propagators run the same two rules with the same one-literal reasons,
  under `hints::Reachable` and `hints::Dag` (`reachable.cc:224–240`,
  `dag.cc:285–309`). `Tree`, `DTree`, `Path` and `DPath` get them through their
  `Reachable` child. `Dag`'s copy guards its reasons on `want_reasons()` and has
  a mutation lane on them; this class's does neither. Those copies are
  documented in their own families' documents; this one covers the
  `Subgraph` class only. The front end's `edges_from_endpoints`
  (`fzn_glasgow.cc:183`) is shared with all of them.
- **Presolvers:** none reads it.
- **Reachable only through a decomposition?** No: the C++ API, the `.scp` reader
  and MiniZinc all post it directly. No corpus model does (see
  [Benchmarks and examples](#benchmarks-and-examples)).
- **The merge question.** The family list gives `subgraph` its own row. It
  stays separate: a merge into `reachable` would document one class inside
  another that does not call it. The candidate fix in #1311 makes the
  question sharper, since `Reachable` and `Dag` could post a `Subgraph` child
  instead of carrying copies, but that is a design change for those families,
  not a documentation one.

## The proof model

### OPB encoding

Per edge `e = (u, w)`:

```
sgf<e>:  es[e] = 1  ⇒  ns[u] = 1        written as  [ns[u] = 1] + ¬[es[e] = 1] ≥ 1
sgt<e>:  es[e] = 1  ⇒  ns[w] = 1        written as  [ns[w] = 1] + ¬[es[e] = 1] ≥ 1
```

`add_labelled_constraint` with `HalfReifyOnConjunctionOf{{es[e] == 1}}`
(`subgraph.cc:89–94`). Over a plain 0/1 variable each literal is its bit,
`i[x][b0]`, so a row is a two-literal clause. A constant condition folds: a
constant-1 edge gives the unit rows `[ns[u] = 1] ≥ 1`, and a constant-0 edge
gives two rows that are trivially satisfied (`≥ −1`), kept. A view position is
written over the view's own literal, whose definition the view layer adds to the
OPB.

**It is definitional**: the rows are `fzn_subgraph`'s two implications and
nothing more. **Size:** `2E` rows of two literals, independent of domains, which
are 0/1 by contract.

### Labels

`c[<id>][sgf<e>]` and `c[<id>][sgt<e>]`. **Nothing cites them**: every rule is a
plain RUP with no antecedent list. They exist because a labelled row's role
must name everything that varies. An external tool locating a row by label
needs the constraint ID as well: `Reachable` and `Dag` use the same two names
under theirs, and a model that posts `Subgraph` alongside one of them has each
row twice.

### Cake conformity

`cake_pb_cp` has no `subgraph` encoder: given the solver's `.scp` it prints
`unsupported constraint: subgraph` (and exits 0). There is no chain case, so
workflow 2 cannot cover this family. If cake gains one, `fzn_subgraph`'s two
implications are the obvious encoding and match these rows.

### Proof-time state

- **At the root:** nothing beyond the OPB rows.
- **During search:** nothing but the inference's own RUP line. Nothing is
  deleted.
- **Naming:** the labels above; no flags.
- **Proof-only auxiliaries:** none.

## The implementation

### Initialisation and global data

`prepare` does the three checks above, `O(n + E)`, and returns `false` with no
edges. There is no initialiser and no constraint state. Installing the one
propagator is not linear, though: `Propagators::install` deduplicates the scope
with a linear `contains` per trigger (`propagators.cc:724–748`), and then
builds the constraint's scope union the same way (`:765–769`), so with `n + E`
triggers it is quadratic in `n + E`, with proofs off as well, and fixing the
first loop alone leaves it quadratic (#1309). That engine cost was measured on
`Dag`; it was not measured here.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| the subgraph propagator | `on_change`, every `ns` and `es` | derived: every `ns` and `es`, **vacuously** | 1, 2 | at least one edge | never claims | never |

**Holes affect.** The declaration is the derived one, and it is exact in the
only sense available: every variable here has bounds inside `0..1`, so it has no
interior, and no other family's interior pruning can be kept alive by it. The
family's whole vocabulary is whether a 0/1 variable is fixed, and to what.

**Idempotence.** Not claimed (`PropagatorState::Enable` on every return,
`subgraph.cc:134`). On distinct variables a call is idempotent in effect: rule 1
sets a node to 1 and rule 2 sets an edge to 0, and neither can enable another
inference. Under sharing it is not: an edge set to 0 that is also some node
variable can enable rule 2 at an edge the loop has already passed, which the
next call picks up.

**Self-disabling.** Never, even when every edge is decided.

### Mutable state and incrementality

None. Every call walks the whole edge list from the start, reading two or three
fixed values per edge, `subgraph.cc:118–133`: `Θ(E)` per call, whatever changed.
That is the cost in [CPU performance](#cpu-performance). A backtrackable list
of open edges would cut a call to the open edges. One propagator per edge, woken
by its own three variables and disabled once its edge is decided, comes within
about 10% of the decomposition's time but makes 12 times as many calls on the
paths and 96 times on the grid, because it stays awake on an edge that is
already entailed; disabling it there too makes it as fast as the
decomposition or slightly faster, with fewer calls (#1311).

### Interior values and optional pruning

**Offers.** `None.` There is one arm, and there are no interiors.

**Observes.** **Nothing that matters.** Every variable is 0/1 by contract, so
the derived `on_change` declaration cannot keep another constraint's interior
pruning alive.

### Robustness and limits

**Unbounded domains.** Refused: any variable whose initial bounds leave `0..1`
is an `InvalidProblemDefinitionException` at prepare.

**Negative values and zero.** Zero is the "not selected" value. Negative values
are refused, and a negative endpoint is refused by the `.scp` reader and by
`edges_from_endpoints` before it can become a `size_t`.

**Degenerate shapes.**

- *No edges:* nothing installed; tested (`empty`).
- *No nodes:* in C++ and `.scp`, fine with no edges. Through MiniZinc's
  four-argument spelling, **wrong**: `fzn_subgraph_enum.mzn:10` computes
  `min(index_set(ns))`, undefined on an empty set, MiniZinc turns that into
  `false`, and the model flattens to `bool_eq(false, true)`: `UNSATISFIABLE`
  where the answer has solutions, on both MiniZinc versions. No proof is
  written, since the solver never sees the constraint. The six-argument spelling
  has no `min` and is right. `fzn_dag.mzn` has the same line and the same wrong
  answer, and the two are one defect, fixed by a guard in each file. The
  shifting overrides of other families (`fzn_circuit.mzn`, `fzn_inverse.mzn`
  and others) guard it with `if length(x) = 0 then true else …`. Filed as
  #1303. The rooted graph families have a **different** defect with the
  opposite answer: an empty `reachable`, `tree` or `path` is unsatisfiable,
  because the root must be a selected node. Their int spellings give
  `=====ERROR=====` from a C++ `prepare()` throw, where the answer is
  `UNSATISFIABLE`; their `_enum` overrides carry the same unguarded `min`,
  which happens to give the right `UNSATISFIABLE`. That is the `reachable`,
  `tree` and `path` audits' finding (#1305), not this one.
- *Self loops and parallel edges:* tested (`loop_and_parallel`). A selected loop
  makes one inference, not two (`proofs/asrt`, case `loop`).
- *Constants:* tested (`path3_edge_in`, `path3_node_out`), and swept (mode
  `const`).
- *Shared variables:* positive sharing keeps generalised arc consistency and
  loses no solutions; sharing with opposite signs, through a view, loses
  generalised arc consistency and no solutions. See rule 1's **Strength**.
- *An out-of-range endpoint* in MiniZinc's six-argument spelling is an error
  through Glasgow and a forced-out edge through the stdlib; see the table under
  [frontend coverage](#concrete-constraints-and-frontend-coverage).

**Overflow.** Nothing to overflow: the propagator compares fixed values to 0 and
1, and the endpoint arithmetic is on `size_t` indices that `prepare` bounds by
`ns.size()`. An endpoint too large for the node array is refused, however
large. View offsets are bounded by the range policy upstream; a view at an
offset of `±2⁴⁰` verifies (`proofs/constopb/big.cc`).

### Interval efficiency

**Fine at any width**, since the width is two.

1. **The propagation side.** One loop over the edges, `O(E)` per call, reading
   `optional_single_value`. It reaches for `State`'s per-value iterators nowhere.
   The cost that matters is the per-call edge count, not a width.
2. **The reason side.** One literal per inference, never per value. Built
   unconditionally, not guarded on `want_reasons()`, but per inference rather
   than per call: 753 inferences over 44,044 calls on the 3×3 grid enumeration.
3. **The proof side.** One RUP line of two literals per inference. No width
   gate is needed.
4. **The audit lane.** One row, `Subgraph`, pinned `NoWidePosition`: a path of
   three nodes over plain `0..1` variables (`large_domain_audit_test.cc:794`).
   There is no axis to vary: every position is 0/1 by contract, and the only
   wide thing a position can be is a view of a two-valued variable with a large
   offset, which is a value range, not a width. PR #1302 (open), which re-pins
   index-valued positions in other families `Clean`, leaves this row
   `NoWidePosition`, since a selector must be `0..1`. The lane is registered as a
   ctest only under `-DGCS_LARGE_DOMAIN_GUARD=ON`, which no CI lane sets (#920),
   so in CI it is built and never run.

## Inference catalogue

Two rules, run by the one propagator in one loop over the edges. For each edge
`e = (u, w)`: if `es[e]` is fixed 1, rule 1 for each endpoint not already fixed
1; otherwise, if `es[e]` is not fixed 0, rule 2 at the first endpoint fixed 0.

Four facts hold for both.

**Each is one `RUP` against one row, and the procedure is ours only in name.**
The asserted clause is the row for that edge and endpoint, `sgf<e>` or
`sgt<e>`, read as a clause. The licence is **Theorem 2.6** over a row whose
terms are 0/1 literals: with the reason stated, the half-reified row reduces to
its consequent, one literal, which unit propagation sets. (Over a view or a
fixed-valued variable the row's literal is the view's or the equality literal,
and the encoding's own definitions carry it to the bits, Theorem 3.3.) The
thesis gives no procedure for `subgraph`; nothing here is more than one step of
unit propagation over a clause.

**The reason is one literal**, the one that triggers the rule: `es[e] = 1` for
rule 1, `ns[u] = 0` for rule 2. It is minimal.

**One wire form.** `hints::Subgraph`, `subgraph:((constraint_id <id>))`:
`originator`, a `ConstraintID`, and no subhint (`hints.hh`).

**No `state` is read by a justification.** `JustifyUsingRUP` writes the
assertion clause and nothing else.

### Rule: edge-selects-endpoint

- **Infers** — `ns[u] = 1` for an endpoint `u` of an edge `e` whose `es[e]` is
  fixed 1; for both endpoints, one at a time.
- **Fires when** — any node or edge variable changes, and the loop reaches an
  edge fixed in with an endpoint not fixed in. If the endpoint is fixed 0, the
  inference fails, and this is how the constraint's only conflicts arise.
- **Strength** — `GAC` on the node and edge variables, with rule 2, when no
  variable appears in two positions with opposite signs. Checked by brute force
  at the root (`probes/sgcheck.cc`): graphs of 1 to 4 nodes and 0 to 5 edges,
  self loops and parallel edges allowed, each variable two-valued or fixed,
  3,000 instances at each of seeds 1 and 2 in each of four modes:
  distinct variables, constants, positive sharing (positions drawn from a
  smaller pool), offset and negated views at distinct positions, and none
  failed. The argument: every clause is `¬es ∨ ns`, so at the fixpoint every
  value extends to a solution, by putting every undecided node in and every
  undecided edge out, or, for a value 0, by also putting out everything that
  implies it; positive sharing keeps the implication graph positive, and the
  argument goes through. **Opposite signs break it**: with `1 − x` at one
  position and `x` at another, the clauses can say `x ⇒ ¬x`, which unit
  propagation over separate clauses does not see. 733 and 734 of 3,000
  instances lose generalised arc consistency (mode `negview`, seeds 1 and 2;
  762 and 779 in `viewalias`), and none loses a solution. Counted against the
  instances that actually share a variable with opposite signs (2,210 and
  2,130; 2,191 and 2,185), that is 33–36%; every failure is one of them. That
  rate belongs to `sgcheck`'s small graphs (1 to 4 nodes, 0 to 5 edges): it falls
  as the graphs grow. The fact-check's own checker gives 35% with up to 2 nodes
  and 2 edges, 27.5% with up to 3 and 3, 23.5% with up to 4 and 5, and 17.7% to
  19.7% with up to 5 and 6. One of them:
  edge `(2, 0)`, `ns = [1 − x, x, x]`, `es = [x]`, where `x = 1` would select
  the edge and so need `1 − x = 1`; `x` keeps both values. Only the C++ API can
  build it.
- **Algorithm** — the loop above, `O(E)` per call, `O(1)` per edge.
- **Why it is true** — a selected edge has both endpoints selected.
- **Proof technique** — `RUP` against `sgf<e>` or `sgt<e>`; see the preamble.
- **Reason** — `{es[e] = 1}`. Not guarded on `want_reasons()`.
- **Assertion** — `ns[u] = 1 ∨ ¬(es[e] = 1)`, for a success and for a conflict
  alike: the conflict is an ordinary inference whose literal is already false,
  so it asserts the attempted literal, and the backtrack closes it. Measured at
  `Inferences` (`proofs/asrt`, a path `0–1–2` with `es[0]` over `{1}`, and for
  the conflict `ns[0]` over `{0}` too):
  ```
  a 1 i[_1][b0] 1 ~i[_4][eq1] >= 1::subgraph:((constraint_id _1));
  a 1 i[_1][eq1] 1 ~i[_3][eq1] >= 1::subgraph:((constraint_id _1));
  ```
  (`eq1` because those variables have a single value; over `0..1` it is `b0`.)
- **Hint** — `hints::Subgraph`: `originator`, the `ConstraintID`.
- **Offline reconstructibility** — `offline`: an unhinted RUP of the assertion
  succeeds.
- **Proof size** — one line of two literals per inference, at `Off`:
  `rup 1 i[_1][b0] 1 ~i[_4][eq1] >= 1;`.
- **Gaps** — `None.`
- **Tightness** — no registered lane. Shown by hand on a probe-local copy of
  `subgraph.cc` whose only change empties this rule's reason
  (`proofs/mut/mut_subgraph.cc`): a triangle with a pendant edge, enumerated
  with edges branched first, largest value first, so this rule fires. VeriPB
  rejects line 2 as not RUP, and the uncorrupted copy verifies on the same
  fixture (49 solutions). `Dag`'s registered `dag_mutation_endpoint` lane
  empties the reasons of both of `Dag`'s copies, but on its fixture VeriPB
  rejects rule 2's line (`rup 1 ~i[e0][b0] >= 1;`), so it is no evidence for
  rule 1 in either class.

### Rule: endpoint-out-deselects-edge

- **Infers** — `es[e] = 0` for an edge `e` not yet decided, one of whose
  endpoints is fixed 0.
- **Fires when** — as rule 1, at an edge whose `es[e]` is undecided; the loop
  stops at the first endpoint fixed 0. It never conflicts, since `es[e]` is not
  fixed when it runs.
- **Strength** — `GAC`, with rule 1; see rule 1.
- **Algorithm** — as rule 1.
- **Why it is true** — a selected edge would need the unselected endpoint
  selected.
- **Proof technique** — `RUP` against `sgf<e>` or `sgt<e>`.
- **Reason** — `{ns[u] = 0}`, the first endpoint found fixed 0. Minimal. Not
  guarded on `want_reasons()`.
- **Assertion** — `es[e] = 0 ∨ ¬(ns[u] = 0)`. Measured at `Inferences`, the same
  path with `ns[1]` over `{0}`:
  ```
  a 1 ~i[_4][b0] 1 ~i[_2][eq0] >= 1::subgraph:((constraint_id _1));
  ```
- **Hint** — `hints::Subgraph`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line of two literals per inference.
- **Gaps** — `None.`
- **Tightness** — as rule 1, by hand: emptying this rule's reason in the
  probe-local copy, with nodes branched first, smallest value first, so this
  rule fires, makes VeriPB reject line 2; the control verifies.

## Evidence

### Tests

- **`subgraph_test`** (`subgraph_constraint`): six shapes, `empty`, `path3`,
  `triangle`, `loop_and_parallel`, `path3_edge_in` and `path3_node_out`, the
  last two with constants, under `solve_for_tests_checking_gac`, so GAC is
  checked at every node; and one duplicate-variable run (`path3` with node 0 and
  node 2 the same variable) under plain `solve_for_tests`. Each with and without
  proofs; without VeriPB on the path the proof lane is skipped entirely
  (`subgraph_test.cc:130`), leaving 7 runs. With it, every proof verifies.
  Seeded.
- **`scp_reader_test`**: enumerates `(_1 subgraph (0) (1) (N0 N1) (E0))` to its
  five solutions, and round-trips a `Subgraph` posted with the tree family
  through write, read and write.
- **MiniZinc:** `minizinc-subgraph`, differential against MiniZinc's default
  solver, with `--fzn-pattern glasgow_subgraph` and a proof.
- **Audit lane:** the one row above, registered as a ctest only under
  `-DGCS_LARGE_DOMAIN_GUARD=ON`, which no CI lane sets (#920).

**Runtime caps.** No lane sets or clears one, and the default caps (300
solutions, 1,500 recursions) cannot fire: the 14 runs, seven shapes in each
lane, have at most 18 solutions. The configuration the results came from:
`subgraph_test --seed=1` of the audit build, VeriPB 3.0.2 on the path, 0.13 s
for the lot (the fact-check measured 0.10 s).

**Tightness:** no registered mutation lane. The two hand-made lanes above, on a
probe-local copy with a control, are the only evidence, and they show one
corruption per rule rejected on one fixture each.

**What the tests do not cover.**

- **Sharing with opposite signs**, the one shape that is not GAC, and so the
  known loss of strength; the duplicate run shares positively and checks no
  consistency.
- **Views** in any test. The audit's sweeps cover them (above).
- **An empty node array through MiniZinc's four-argument spelling**, which is
  the shape that gives the wrong answer. `subgraphtest.mzn` has four nodes.
- **Large graphs.** The biggest tested graph has three edges, so nothing in the
  suite would notice the per-call cost.
- **Real instances:** none ported; there is none to port.

### Benchmarks and examples

- **In the repository:** no example or benchmark posts it. `examples/hitori`
  mentions the `subgraph` half of the stdlib's `fzn_dreachable`, and leaves it
  out of its decomposition on purpose, as vacuous for that model
  (`hitori.cc:114–116`).
- **Corpus:** **no model posts it.** Of the 285 flattened MiniZinc Challenge
  models (`tmp/fd-table/corpus/fzn`, flattened 2026-09-04, after #787 added the
  override), none contains `glasgow_subgraph`; the only graph builtin in it is
  `hitori`'s `glasgow_reachable`. `steiner-tree` 2018 writes its own
  `my_fzn_subgraph` decomposition, and the 2026 `surface-based-tsp` posts `tree`,
  which reaches `Tree`.
- **For CPU:** synthetic. The path with a 12-edge undecided window
  (`bench/shapes.hh`, `window L 12`) for the per-call scan, a 3×4 grid with
  everything free for the case with no fixed part, and `bench/mznab/densest.mzn`
  for the MiniZinc route.
- **For proof verification:** the 3×3 grid enumeration below: 17 MB, 0.68 s.
  The window shape writes a `solx` line per solution over every variable, so at
  `L = 1000` with a 10-edge window (`window 1000 10`) its proof is 486 MB for
  17,711 solutions; do not use it for proofs
  past `L = 100`.

### CPU performance

*Release build of `86caad24` (GCC 15.2.0, `-O3 -march=native`); Gecode 6.3.0,
static, built locally; fataepyc-10, boost off, `taskset -c 135`, malloc
thresholds fixed (`GLIBC_TUNABLES=glibc.malloc.mmap_threshold=33554432:glibc.malloc.trim_threshold=4294967295`);
2026-10-09. Median of five runs; `instructions:u` from `perf stat`.*

**Against the decomposition and Gecode.** Every solution,
branching on the free nodes and then the free edges in input order, smallest
value first; `dec` posts two `LessThanEqual(es[e], ns[endpoint])` per edge;
Gecode posts `rel(es[e], BOT_IMP, ns[endpoint], 1)` and branches
`BOOL_VAR_NONE`, `BOOL_VAL_MIN` (`bench/bench_gcs.cc`, `bench_gecode.cc`,
`runbench.sh`, `bench_86caad24.txt`). All three propagate the two
implications to their fixpoint at every node, so they should search the same
tree. What was compared is counts: in every row the three solution counts agree
and GCS's recursions equal Gecode's nodes.

| Shape | Solutions | Nodes | `Subgraph` | decomposition | Gecode |
|---|---|---|---|---|---|
| 3×4 grid, all free (17 edges) | 984,547 | 1,969,093 | 2.885 s, 15.27·10⁹ | 1.505 s, 11.52·10⁹ | 0.391 s, 2.99·10⁹ |
| path of 10 edges, all free | 28,657 | 57,313 | 0.063 s, 0.36·10⁹ | 0.041 s, 0.30·10⁹ | 0.012 s, 0.08·10⁹ |
| path of 100, 12 free | 121,393 | 242,785 | 1.574 s, 6.22·10⁹ | 0.323 s, 2.92·10⁹ | 0.095 s, 0.85·10⁹ |
| path of 1,000, 12 free | 121,393 | 242,785 | 14.59 s, 52.8·10⁹ | 1.757 s, 19.1·10⁹ | 0.521 s, 5.80·10⁹ |
| path of 10,000, 12 free | 121,393 | 242,785 | 145.9 s, 520·10⁹ | 15.52 s, 181·10⁹ | 4.711 s, 54.8·10⁹ |

`Subgraph` against the decomposition: 1.9, 1.5, 4.9, 8.3 and 9.4 times the
wall time, and 1.3, 1.2, 2.1, 2.8 and 2.9 times the instructions. `Subgraph`'s
excess is about 52 ns per edge per call at both 1,000 and 10,000 edges. The two
ratios part because the decomposition runs at a much higher rate than the scan
does, and the scan does not miss beyond L2. The fact-check's counters at
`L = 1000` (`tmp/fd-graph/factcheck/subgraph/bench/perf_sub.txt`,
`perf_dec.txt`) give `Subgraph` 33.0·10⁹ cycles for 52.8·10⁹ instructions (1.6
per cycle) and the decomposition 3.9·10⁹ for 19.1·10⁹ (4.9 per cycle). Per edge
per call the excess is about 118 cycles and 137 instructions, with 3.1 L1 data
misses and 0.12 L2 misses (the L2 event, `l2_cache_req_stat.ic_dc_miss_in_l2`,
counts instruction-cache misses too). At `L = 10,000` the second fact-check
measured 120.5 cycles, 137.4 instructions, 3.17 L1 data misses and 0.08 L2 misses
(`tmp/fd-graph/factcheck2/subgraph/perf_{sub,dec}_10000.txt`), so the cost per
edge does not change with the graph's size. The excess runs at about 1.2
instructions per cycle with its L1 misses served from L2, so L2 latency may be
part of it; what the counters rule out is L3 and memory. The decomposition and
Gecode grow with the path too (0.32, 1.76 and 15.5 s; 0.095, 0.52 and 4.7 s);
why was not measured. `Subgraph` adds a scan of every edge to whatever that
is. `Subgraph`'s propagation count is the call
count, about one per node (246,881 calls for 242,785 nodes); the decomposition's is the clause wakes
(20,500).

**Through MiniZinc.** `densest.mzn` on a 5×5 grid with `K = 9`: `subgraph`, `sum(ns) ≤ 9`,
maximise `sum(es)`, branching on the edges largest value first, then the nodes.
Flattened by MiniZinc 2.9.7 with `<build>/glasgow.msc`, and with a copy of the
mznlib without the two `fzn_subgraph` files, which leaves the stdlib's 80
`bool_clause`s; `fzn-glasgow -s` on each, five runs:

| Route | Nodes | `solveTime` | `instructions:u` |
|---|---|---|---|
| override, `glasgow_subgraph` | 1,461,275 | 11.01 s | 50.28·10⁹ |
| stdlib decomposition | 1,461,275 | 6.95 s | 40.59·10⁹ |

The two print identical solutions. The override costs a MiniZinc user 1.58
times the time on this model.

**A candidate, one propagator per edge.** A probe-local copy of `subgraph.cc`
whose only change is `install_propagators`: one propagator per edge, triggered
on its three variables, `DisableUntilBacktrack` once its edge is decided or it
has made its inference, the reason guarded on `want_reasons()`, the same rules, reasons and hint
(`bench/peredge/edge_subgraph.cc`, linked against the shipped library, with the
shipped class and the decomposition in the same binary; three runs):

| Shape | `Subgraph` | per edge | decomposition |
|---|---|---|---|
| 3×4 grid | 2.932 s, 15.27·10⁹ | 1.643 s, 11.94·10⁹ | 1.536 s, 11.52·10⁹ |
| path of 100, 12 free | 1.576 s, 6.22·10⁹ | 0.337 s, 2.96·10⁹ | 0.322 s, 2.92·10⁹ |
| path of 1,000, 12 free | 14.54 s, 52.84·10⁹ | 1.753 s, 19.15·10⁹ | 1.732 s, 19.09·10⁹ |

The node counts are identical, and the candidate's proof of the 2×3 grid
enumeration verifies. It is close to the decomposition, not equal to it: 1–5%
slower on the paths and 7% on the grid in these runs (3.6% in instructions); across
the two fact-checks' runs it was 7–14% on the grid (the second's median of five,
10.4%). And it makes many more calls: 247,879 against 20,500 on the path of 1,000
(12 times) and 1,973,153 against 20,551 on the grid (96 times). The cause is
that it returns `Enable` while its edge is undecided and both endpoints are
fixed 1, so it stays awake on an edge that is already entailed, where each of
the decomposition's comparisons disables itself once entailed
(`comparison.cc:230`).

**The same candidate with an entailment disable**, measured by the second
fact-check (`tmp/fd-graph/factcheck2/subgraph/pe/edge_subgraph_ent.cc`: one
added line, `DisableUntilBacktrack` when both endpoints are fixed 1; the same
build, machine and commit, core 136, five runs each, medians; kept apart from
the table above, which is this audit's run):

| Shape | candidate | candidate, entailment disable | decomposition |
|---|---|---|---|
| 3×4 grid | 1.697 s, 11.94·10⁹, 1,973,153 calls | 1.464 s, 11.48·10⁹, 12,251 calls | 1.537 s, 11.52·10⁹, 20,551 calls |
| path of 100, 12 free | 0.344 s, 2.96·10⁹, 246,979 | 0.319 s, 2.91·10⁹, 12,385 | 0.331 s, 2.92·10⁹, 20,500 |
| path of 1,000, 12 free | 1.779 s, 19.15·10⁹, 247,879 | 1.751 s, 19.09·10⁹, 13,285 | 1.770 s, 19.09·10⁹, 20,500 |

With the disable it makes fewer calls than the decomposition and is as fast or
slightly faster: 11.48·10⁹ instructions against 11.52·10⁹ on the grid, and on
the paths the time gaps are within noise. Its install is still quadratic in the
number of edges today, through the engine's constraint-scope union (#1309),
since it installs one propagator per edge under one constraint. Its proofs of the 2×3 and 3×3 grid enumerations verify (491 and 21,799
solutions). Three runs of my own on the grid agree (median 1.458 s against
1.537 s, core 135). #1311 proposes this version.

**What the benchmarks do not exercise.** Conflicts: an enumeration of a
constraint alone never fails, so rule 1's failing form appears only on the
MiniZinc model. And any real model, since none in the corpus posts this.

### Proof performance

*Same build and machine; VeriPB 3.0.2 with `--force-checked-deletion`; one run
each, serial.*

**The 3×3 grid, all 21,799 solutions** (`bench_gcs`, 43,597 nodes), branched
two ways: nodes first, smallest value first, so that rule 2 fires; and edges
first, largest value first (`bench_gcs_ord`, `BENCH_ORDER=edges_max`), so that
rule 1 does:

| Branching | Class | Lines, `Off` | Bytes, `Off` | VeriPB, `Off` | This family's assertions at `Inferences` | VeriPB, `Inferences` |
|---|---|---|---|---|---|---|
| nodes first | `Subgraph` | 240,968 | 17.06 MB | 0.68 s | 753 | 11.29 s |
| nodes first | decomposition | 241,056 | 17.06 MB | 0.77 s | 753 (`comparison`) | 11.29 s |
| edges first | `Subgraph` | 246,182 | 16.28 MB | 0.68 s | 3,741 | 9.02 s |
| edges first | decomposition | 246,267 | 16.29 MB | 0.77 s | 3,741 (`comparison`) | 9.06 s |

**Own against shared.** The family's whole contribution is one RUP line per
inference: nodes first, the proof's 44,351 `rup` lines are its 43,597
backtracks, its 753 inferences and the conclusion; edges first, 47,339, with
3,741 inferences. Everything else is the shared layers': a `solx` line per
solution and its bookkeeping, and nothing at all for the literals, since a 0/1
variable's literal is its bit. So here the family is 0.3% and 1.5% of the
proof's lines. The OPB is the variables plus `2E` two-literal rows: 1,755 bytes
for 9 nodes and 12 edges. The decomposition writes the same number of
inferences under `comparison`, a proof within 0.04% of the lines, and within
0.03% of the bytes branching nodes first, 0.063% branching edges first.

**Through MiniZinc**, `densest.mzn` on a 4×4 grid with `K = 6` (6,441 nodes),
with `--prove`: 194,869 lines and 17.9 MB, `VERIFIED BOUNDS −7 ≤ obj ≤ −7` in
0.92 s; the decomposition's proof has the same line count, 17.97 MB, 0.91 s. At
`Inferences` (`GCS_ASSERTION_LEVEL=inferences`) the proof has 99,040
assertions, of which 21,228 (21.4%) are `subgraph`; the rest are 46,296
`equals`, 8,363 `linear_equality`, 6,441 `backtrack`, 2 `soli_improve`, and
16,710 with no hint at all. Every one of those is over the 16 integer copies
of the node variables that MiniZinc's `bool2int` introduces, the terms of the
flattened `int_lin_le(…, 6)`, and 15,157 of them are seven of those copies'
negated `≥ 1` literals: the `sum(ns) ≤ 6` row's clauses. The
decomposition has 21,228 `or` assertions in place of the `subgraph` ones and the
same 16,710 unhinted.

**Assertion levels.** At `Off` every proof here verifies. At `Inferences` each
is accepted under assertions. On these enumerations the asserted proof is the
larger (23.2 MB against 17.1 MB) and slower to check (11.29 s against 0.68 s),
with the decomposition exactly the same, so that is the asserted backtrack and
`solx_block` lines', not this family's.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is one justified RUP at `Off`, nothing is asserted, and
the propagator infers the same with proofs on and off.

### Known limitations

- **A MiniZinc `subgraph(from, to, ns, es)` with no nodes is reported
  unsatisfiable** (#1303). The six-argument spelling, the `.scp`
  reader and the C++ API are right.
- **It is slower than posting the two implications per edge**, by 1.6 times on a
  MiniZinc model and by a factor that grows with the graph when most of it is
  decided (#1311).
- **A variable in two positions with opposite signs**, through a view, loses
  generalised arc consistency, though not solutions. Only the C++ API can post
  it.
- **An edge endpoint outside `1..N`** in MiniZinc's six-argument spelling is an
  error, where the stdlib forces that edge out.
- **No `cake_pb_cp` chain**: cake has no encoder.
- **No views from `.scp`**, which is the reader's limitation.

### Next steps

1. **Guard the empty node array in `fzn_subgraph_enum.mzn`**, as the other
   shifting overrides do: `if length(ns) = 0 then true else … endif`, and add a
   `minizinc/tests/` case with no nodes. One line; fixes a wrong answer. The same
   line in `fzn_dag.mzn` is part of the same issue, #1303. **Do not copy the guard into the
   rooted `_enum` overrides** (`fzn_reachable_enum.mzn`, `fzn_tree_enum.mzn`,
   `fzn_path_enum.mzn` and their directed forms): there `then true` would turn
   an accidentally right `UNSATISFIABLE` into a wrong satisfiable answer. Their
   empty case wants `then false`, or a fix in `prepare()`, which is #1305.
2. **One propagator per edge**, disabled until backtrack once its edge is
   decided or entailed (both endpoints fixed 1), as the candidate with the
   entailment disable above: as fast as the decomposition or slightly faster,
   with fewer calls, and the same rules, rows and hint. Small; its install
   stays quadratic until #1309 is fixed. Guard the reason on `want_reasons()`
   while there. #1311. The same structure
   would let `Reachable` and `Dag` post a `Subgraph` child in place of their
   copies. Whether their copies of the scan cost them anything was not
   measured, and that is their documents' call.
3. **A test for opposite-sign sharing**, recording the loss of strength rather
   than fixing it; and views in `subgraph_test`. Small. Making the shape GAC
   needs 2-SAT reasoning over the implication graph, which nobody has asked for.
   Unfiled.
4. **Out-of-range endpoints in the six-argument spelling.** Either assert, as the
   four-argument spelling does, or drop the offending edges' clauses and fix them
   out as the stdlib's semantics do. Not worth an issue on its own.

## Prior art

There is no propagation algorithm to cite: the constraint is two binary clauses
per edge, which unit propagation decides, and Gecode has no global
for it; MiniZinc's decomposition is the definition. Certifying it is equally
unremarkable: each inference is one RUP against one clause, which VeriPB's unit
propagation handles natively. Its interest is as the shared base of the
`globals.graph` ladder (`reachable`, `tree`, `path`, `dag`), where the same two
rows carry every walk through an unselected node; see
[`connectivity-proofs.md`](../connectivity-proofs.md).

## Further reading

- [`connectivity-proofs.md`](../connectivity-proofs.md): the design note for
  `Reachable`, the tree and path family and `Dag`, all of which carry this
  family's two rows, and why "a selected edge selects its endpoints" is what
  stops a walk through an unselected node. It mentions `Subgraph` as built on
  the same encoding; it is the first two rows of it.
- [`minizinc.md`](../minizinc.md): the `mznlib/` overrides, and the divergence
  between what `dag` is documented to mean and what `fzn_dag` enforces, which is
  exactly this constraint on an edge's tail.
