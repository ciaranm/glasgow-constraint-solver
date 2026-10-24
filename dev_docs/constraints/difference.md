# `DifferenceConstraints`: a system of `x − y ≤ d`, propagated as one graph

> **Maturity** production (the C++ API and `.scp`; reached from MiniZinc and
> XCSP3 only through the opt-in `difference_logic` presolver) ·
> **Audited** 2026-10-19 at `86caad24` ·
> **Closed by decision** since this audit: #1371, the
> shortest-path arithmetic of the incremental route and of root
> simplification (potentials, reduced weights and costs, keys, distances)
> is plain `Integer`, so in-range systems throw `IntegerOverflow`, also
> through `--difference-logic` in its default configuration and from
> MiniZinc; #1372, `difference_graph.cc`'s Bellman-Ford bounds
> and cycle sums (the from-scratch reference route's, and root
> simplification's witness check) are plain `Integer` too. Both still
> throw, and now say so; see [Known limitations](#known-limitations).
> Already open and touching
> this family: #1072 (a push cites a predecessor bound the proof already has),
> #594 (zero-weight-cycle unification, the deferred fourth sub-step of root
> simplification), #582 (no propagator priorities), #1225 (a range-literal
> condition throws with proofs on; #310 is the encoding fix), #1210 (the
> generic `Links`-level solution-line rejection for range-declared variables,
> which this family's proofs meet too), #598 and #983 (the presolver's reach;
> #983 is the parity system's issue, and its general half is about presolver
> reach; recorded in [`difference_logic.md`](../presolvers/difference_logic.md)),
> #868 (cross-solver comparison), #1309 (installing is quadratic in the
> trigger count, from either entry point), #816 (initialisers, root
> simplification's included, do not observe `--timeout`), and the sibling
> #1298 (reified linear
> inequalities, the same class of overflow). Filed since: #1378, reaching in
> from a presolver (an `AutoTable`'s throwaway root search makes the
> incremental route's first call below a guess, so the default incremental
> mode throws `UnexpectedException`); and, from the review of this document,
> #1384 (a negative cycle's or a root witness's reason deduplicates its
> conditions by linear search, `k(k−1)/2` comparisons for `k` distinct
> conditions, proofs on or off) and #1385 (root simplification counts
> isolated nodes as removed, but the propagator still seeds, scans and wakes
> on them). Tracked under #871.

One posted class, `DifferenceConstraints`, holds a list of edges
`x − y ≤ d`, each optionally half-reified as `cond → x − y ≤ d`, and
propagates the whole system with one propagator over its constraint graph. The
same machinery — `install_difference_propagator`, its root initialiser, its
incremental Dijkstra and its proofs — is what the `difference_logic` presolver
installs over two-term linear and comparison donors it finds in a model. This
document owns that machinery whoever installs it;
[`difference_logic.md`](../presolvers/difference_logic.md) owns the detection
and the rewrite.

Two things to know before touching it. **Every certificate is a sum of the
model's own rows**: a pushed bound is one edge row plus one literal definition,
a negative cycle is its edge rows added up so that every bit telescopes away,
and no flag, auxiliary or lemma outlives the inference that made it. And **the
hard part is not on the proof side at all.** Nearly every way the incremental
machinery can go wrong loses an inference, and a lost inference is invisible to
VeriPB. That is why the from-scratch Bellman-Ford route is kept compiled and
selectable, why every data-driven fixture in `difference_constraints_test.cc`
(and the restart stress) runs both routes and demands equal recursion counts,
and why this audit's two new defects (#1371 and #1372) are overflows in the
propagator's arithmetic — in the incremental machinery and root
simplification (#1371), and in `difference_graph.cc`'s Bellman-Ford
bounds and cycle sums (#1372) — rather than proofs that fail.

## What it is

### Semantics

`DifferenceConstraints(vector<DifferenceEdge> edges)`, with
`DifferenceEdge{x, y, d, cond}`, enforces, for every edge,

```
x − y ≤ d                  when cond is absent
cond → x − y ≤ d           when cond is an IntegerVariableCondition
```

`x` and `y` are `IntegerVariableID`s: a variable, a constant, or a
`+X + c` view. `cond` is any `IntegerVariableCondition` (`=`, `≠`, `≥`, `<`,
`in_range`, `not_in_range`) over any variable, including one of the system's
own nodes. An edge whose condition is false constrains nothing. Nothing is ever
inferred about a condition from the graph except at the root (rules 6 and 8):
neither the paper's §5.4 bounds check nor its `IncImp` runs during search
([`difference-logic.md`](../difference-logic.md), "Half-reified edges").

Degenerate cases, each checked:

- **An empty edge list** installs nothing (`prepare()` returns `false`,
  `difference_constraints.cc:113`). A `.scp` `(_1 difference ())` over one
  variable enumerates all three values and its proof verifies.
- **One operand a constant** is a *static bound* on the other operand: `x − c ≤ d`
  is `x ≤ d + c`, and `c − y ≤ d` is `y ≥ c − d`. It is not a graph edge.
- **Both operands the same variable**, directly or through offset views
  (`x − (x + 1) ≤ 3`), or **both constants**, say `0 ≤ d'` after folding.
  Vacuous when `d' ≥ 0`; when `d' < 0`, a root contradiction unconditionally
  (rule 7) and `¬cond` under a condition (rule 6).
- **A negated view** (`−X + c`) as an operand is refused at construction with
  `InvalidProblemDefinitionException`: `−X − W ≤ d − c` is not a difference
  constraint, and treating it as one would be unsound. A condition *over* a
  negated view is fine, since a condition is a literal, not an operand.
- **The same condition on several edges**, and both polarities of one Boolean
  (`b → i before j`, `¬b → j before i`), are accepted and are the normal shape
  of a disjunctive encoding; they are where the strength claims below stop.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `DifferenceConstraints` | `n/a`[^mzn] | `n/a`[^mzn] | `n/a`[^cpmpy] | ✓ `difference` | half-reified edges carry a fourth element, `(var op value)`[^scp] |

[^mzn]: Neither modelling language has a "system of difference constraints"
    global, and neither front end gained a Glasgow-only predicate for one. Both
    reach this machinery only through the `difference_logic` presolver behind
    `--difference-logic`, over the two-term rows they already emit
    (MiniZinc's two-term `int_lin_le` recovered by `fzn-glasgow` as a
    `LessThanEqual`, `fzn_glasgow.cc:729`; XCSP3's as two-term linears); the
    entry points and what they detect are
    [`difference_logic.md`](../presolvers/difference_logic.md)'s. Neither
    produces a half-reified donor, because `minizinc/mznlib/` declares no
    `*_imp` predicate ([`comparison.md`](comparison.md)'s [^imp]) and XCSP3's
    binding turns a top-level `imp` into an unreified `Or` over a fully
    reified comparison (`xcsp_glasgow_constraint_solver.cc:1841-1849`; the
    `*If` row of `comparison.md`'s frontend table).
[^cpmpy]: CPMpy has no such global, and `gcspy` binds no
    `DifferenceConstraints` (no hit for `difference` anywhere under `python/`).
[^scp]: `(id difference ((x y d) (x y d (b = 1)) ...))`. Constants appear as
    integers in either operand position. A view operand is *written* as a list,
    `((x + 2) (y + -1) -3)`, which the reader refuses ("expected an atom, found
    a list"); that is the general reader limitation `scp_reader.hh` records
    for every view operand, not this family's. `cake_pb_cp` has no `difference`
    keyword (see [Cake conformity](#cake-conformity)).

`examples/difference_chain` (`--variant=global`) and `examples/rcpsp`
(`--variant=global`, and `--machine=difference` for conditional edges) post
the class directly.

### Options

Four builder methods and one environment variable. **None of them changes the
OPB model**: the `.opb` of `rcpsp --size 12 --seed 2 --machine-fraction 0.8
--machine difference --variant global` has the same MD5 under all four
combinations of `--simplify` and `--incremental` (measured at `86caad24`).

- **`simplifying_at_root(bool = true)`**, on. Runs the root simplification
  stage (Johnson's all-pairs pass, `difference_simplify.cc`) from the root
  initialiser: drops edges a shorter path implies, fixes conditions whose edge
  would close a negative cycle (rule 8), drops edges whose condition is
  already false, and lowers the from-scratch passes' round bound to the
  number of nodes that still have an edge. It reports the other nodes as
  `isolated_nodes_removed`, but they stay in the propagator: it still seeds
  them (on the incremental route's first call, and on every call from
  scratch), scans them on every wake and is woken by their bounds (#1385).
  On by default because the paper
  calls it "an important part of the practical success of difference logic"
  (by its Tables 1–3, in MiniZinc-challenge points against Huub without
  difference logic, simplification is 73% of the gain on the MiniZinc set and
  66% on ProdCons, but 43% on RCPSP/max), and it is what refutes this tree's own
  RCPSP/max fixtures at the root; it is a large loss on dense unconditional
  systems ([CPU performance](#cpu-performance)). Only rule 8 changes what is
  inferred. The two edge removals change what is propagated *over*, and the
  lower round bound only how soon a from-scratch pass still relaxing
  declares a cycle (it stays above any simple path among the nodes left);
  neither changes the fixpoint (in this audit's fact-check, of 2,700
  random instances solved with
  simplification on and off, every one where no condition was fixed gave
  identical recursions and solution sequences; the ones with a root fix
  differed, as they should).
- **`reporting_simplification_to(shared_ptr<DifferenceSimplificationStats>)`**.
  Shares a stats block the stage fills in; it reaches `--stats` and
  `%%%mzn-stat` as the component `difference_logic_simplify`. The counters are
  what tests assert on, because a stage that did nothing would pass every
  other check.
- **`incrementally(bool = true)`**, on. Selects the incremental route (a
  maintained potential function, `IncSat` on arc activation, and one Dijkstra
  per direction over the bounds that moved) or the from-scratch route (two
  Bellman-Ford passes from the current bounds, every wake). The two reach the
  same per-call fixpoint, so recursions and the solution sequence must match;
  `propagations` and proof bytes may differ (28,625 against 29,106
  propagations at 9,572 recursions on `rcpsp --size 22 --seed 4
  --max-lag-density 0.25`).
- **`auditing_incremental_propagation(bool = true)`**, off. After every
  incremental call, re-runs the from-scratch pass on the same bounds and edge
  set and throws if the two fixpoints differ or the incremental pass missed a
  negative cycle. `GCS_DIFFERENCE_AUDIT=1` (anything but empty or `0`) turns it
  on for every difference propagator in the process, presolver-installed ones
  included.

No `with_consistency()`. There is one level to have: the propagator reads and
writes bounds only, and there is no cheaper arm worth selecting and no
interior-value arm (see [Interior values and optional
pruning](#interior-values-and-optional-pruning)).

### Variable kinds and views

Operands: plain variables, constants and offset views, all accepted at no cost.
Every operand is reduced to a bare `SimpleIntegerVariableID` plus an offset,
the offsets fold into the weight (`(X + c1) − (Y + c2) ≤ d` is
`X − Y ≤ d − c1 + c2`), and the graph has one node per bare variable, so `x`
and `x + 3` in two edges meet at one node. Negated views are refused, as
above.

**The proof handles views by construction**, and this is the load-bearing
design decision: `define_proof_model` writes each edge's row over the
*deviewed* operands, so two edges meeting at a node through two different
views still cancel exactly in a telescoping `pol`
([`view-proof-logging.md`](../view-proof-logging.md), invariant 1). Every `pol`
also cites rows through a `PolBuilder` in deview mode, which is a no-op for
this class's own rows and is what makes a presolver-built graph's donor rows
(written in the user's views' bits) telescope too. Covered: the `views` test
mode, the view-wrap sweep under `GCS_ENABLE_VIEW_WRAP_SWEEP=ON` (nine of the
nineteen wraps negate, `view_neg` and the eight `view_neg_offset`s, and the
sweep checks that every one is refused), and
this audit's strength sweep, which used offset views on a third of its
operands.

Conditions may be over a view, a constant or a node: `(−b + 1) = 1` (22
solutions, proof verifies), `1 = 1` and `0 = 1` on a constant (6 and 16
solutions, both verify), all measured at `86caad24`.

### Reification

Half-reification only, per edge, through `DifferenceEdge::cond`; there is no
full reification and no reified form of the whole system. An edge's row is
emitted under `HalfReifyOnConjunctionOf{cond}`, so it carries a big-M term on
`¬cond` that never telescopes and survives every sum as the residual a learned
clause needs. A half-reified edge takes part in the graph exactly while
`cond` is entailed (`literal_is_entailed`), snapshotted once per call. A
condition is never inferred during search, so nothing here is a reified
dispatcher in [`reification.md`](../reification.md)'s sense.

A **range-literal condition** (`in_range`, `not_in_range`) gives the right
answers with proofs off (50 and 60 solutions for `cond → x − y ≤ −1` on
`x, y ∈ 0..3`, `z ∈ 0..4`, with `cond` `z ∈ 1..3` and `z ∉ 1..3`, checked
against a hand count) and throws `range literals during model writing are not
yet supported` with proofs on, from `NamesAndIDsTracker::need_invar`. That is
#1225, whose fix is #310; `comparison` has the same throw. No front end can
post one.

Full reification would add nothing the posted rows cannot say and is not
wanted. Inferring `¬cond` during search is the missing direction, in both of
the paper's forms: its §5.4 bounds check (an implied edge that the bounds
falsify propagates `b ↦ ⊥`) and its `IncImp` (Algorithm 2, the graph-path
check); [Next steps](#next-steps) says what is known about each.

### Relation to other families

- **Decomposes into this family.** Nothing: no constraint posts a
  `DifferenceConstraints` as a decomposition. The class is posted by the C++
  API, the `.scp` reader (`scp_reader.cc:878`) and the two examples.
- **Posts as children.** Nothing.
- **Shares code.** `install_difference_propagator`
  (`difference_graph.cc:1149`) is called from exactly two places:
  `DifferenceConstraints::install_propagators` and
  `DifferenceLogic::run` (`difference_logic.cc:339`). `deview_difference_operand`
  likewise. Everything in `difference_incremental.cc`, and the algorithm in
  `difference_simplify.cc`, is used only by that one installer;
  `difference_simplify.cc` also defines `DifferenceSimplificationStats`'s
  public methods, which the front ends, the examples and the presolver
  (`difference_logic.cc:79`) report through. So a change to the
  propagator, the initialiser or a proof shape is a change to the presolver's
  installed machinery, and it is documented here for both.
- **Presolvers.** `difference_logic` *rewrites into* this machinery: it
  builds a `DifferenceGraph` from donors, installs it under
  `CurrentlyUnnamedConstraint`, and can disable the unconditional donors'
  propagators. From that route the graph has only proper edges (the presolver
  skips constant and aliased donors and installs nothing below two edges,
  `difference_logic.cc:198` and `:336`), so rules 4 to 7 below never fire
  there, while 1, 2, 3 and 8 do. Its root initialiser is this family's
  initialiser, and runs root simplification over the lifted graph; that is how
  `DifferenceLogic` changes what `CumulativeStrengthening`,
  `InferredCumulative` and `InferredDisjunctive` later read, as their
  documents record (rule 8 can fix a condition that is a bound literal on a
  start or a capacity). Nothing rewrites a `DifferenceConstraints`.
- **Reached only through a decomposition?** No. MiniZinc and XCSP3 reach the
  propagator only through the presolver; the `.scp` reader posts the class
  directly.
- **Not merged with `comparison` or `linear`**, whose rows are exactly
  difference rows: they are the per-edge spellings, this is the global one,
  and they share no code — only the row shape, which is what lets the
  presolver cite their rows. `increasing`'s chain rows are difference rows
  too, and are invisible to the presolver ([`increasing.md`](increasing.md)).

## The proof model

### OPB encoding

One labelled row per **posted** edge, in posted order, over the deviewed bare
variables, with offsets folded into the right-hand side:

```
e<i>:   BinEnc(X) − BinEnc(Y) ≤ d − c1 + c2                 unconditional
e<i>:   cond → BinEnc(X) − BinEnc(Y) ≤ d − c1 + c2          half-reified
```

A constant operand drops its term; an aliased edge keeps both copies of the
variable's bits with opposite coefficients, so the row is identically
`0 ≤ d'` but is not written as an empty sum; two constants give an empty left
side. Measured, `x, y ∈ 0..10`, `n ∈ −10..10`, `b ∈ 0..1`:

```
x − y ≤ −1                @c[_1][e0] -1 i[x][b0] .. -8 i[x][b3] 1 i[y][b0] .. 8 i[y][b3] >= 1;
b → x − y ≤ −1            @c[_1][e0] -1 i[x][b0] .. 8 i[y][b3] 16 ~i[b][b0] >= 1;
n − y ≤ −1                @c[_1][e0] 16 i[n][sign] -1 i[n][b0] .. 8 i[y][b3] >= 1;
x − 2 ≤ 3                 @c[_1][e0] -1 i[x][b0] -2 i[x][b1] -4 i[x][b2] -8 i[x][b3] >= -5;
x − (x + 1) ≤ 3           @c[_1][e0] -1 i[x][b0] .. -8 i[x][b3] 1 i[x][b0] .. 8 i[x][b3] >= -4;
4 − 1 ≤ 3                 @c[_1][e0] >= 0;
(n ≥ 3) → x − y ≤ −1      @c[_1][e0] -1 i[x][b0] .. 8 i[y][b3] 16 ~i[n][ge3] >= 1;
```

The encoding is **definitional** — each row states its posted edge and nothing
else — and **logarithmic in the domains' magnitudes**, not their widths. Size,
from the emission code (`difference_constraints.cc:173-226`) and measured on
`0..W` and `−W..W` at `W` = 10, 1,000 and 10⁹:

- **rows:** exactly one per posted edge, `|edges|`, including static-bound,
  aliased and constant edges; no flags, no auxiliaries;
- **terms per row:** `bits(X) + bits(Y)` for a graph edge, `bits(X)` for a
  static bound, `2·bits(X)` for an aliased edge, `0` for two constants, plus
  one for a half-reified edge's `¬cond`. `bits(v)`, from
  `get_bits_encoding_coeffs` (`bits_encoding.cc:35-38`), is
  `bit_width(h)` magnitude bits with `h = ub(v)` when `lb(v) ≥ 0` and
  `h = max(|lb(v)| − 1, ub(v))` otherwise, plus one sign bit when
  `lb(v) < 0`; so at most `⌈log₂(max(|lb|, |ub|) + 1)⌉`, plus the sign bit
  (one fewer at `lb = −2^k` with `ub < 2^k`: `−16..0` has 4 magnitude
  bits).
  It depends on magnitude, not width: `1000..1010` (width 10) takes 10 bits,
  `5..6` takes 3, and `−10..10` takes 4 plus the sign. Measured: 8, 20 and 60
  terms for two variables over `0..W` at the three values of `W`, 9, 21 and 61
  with one over `−W..W`;
- **weights and the big-M coefficient** grow with the declared bounds, not the
  row count (16 above, the worst-case violation the reification layer
  computes).

A condition that is not a Boolean's own bit (`n ≥ 3` above) needs its literal
defined in the OPB too — two rows from the shared literal layer, not this
family's. The bit encodings themselves are the shared layer's.

### Labels

| Label | Row | Used by |
|---|---|---|
| `@c[id][e<i>]` | posted edge `i`'s row, `i` its index in the posted list | every `pol` in rules 1, 2, 3 and 8, through `DifferenceGraph::edge_lines` |

Rules 4 to 7 are plain RUPs and cite no label. Under the presolver the cited
rows are the donors' own (`@c[<donor id>]`, named through
`ConstraintProofModelData::primary_row_role`), and no `e<i>` row exists; that
naming contract is [`difference_logic.md`](../presolvers/difference_logic.md)'s.
The `e<i>` roles are this family's own invention: no `cake_pb_cp` keyword
re-derives them.

### Cake conformity

**Not conformant, and not reachable.** `cake_pb_cp` has no `difference`
keyword: on every `.scp` this audit tried it prints `unsupported constraint:
difference` and **exits 0** with an empty output, so a harness that only checks
the exit status would pass. There is no `scp_chain_*` case for the family, and
none could pass today. The rows themselves are ordinary two-term linear rows,
so a cake keyword would be small, but it is cake's to add (upstream).

The presolver route is the opposite case: the rows it cites are the donors',
which cake does re-derive, so a presolved model's `.opb` is whatever the donor
families' conformity is ([`comparison.md`](comparison.md),
[`linear.md`](linear.md)).

### Proof-time state

**Nothing at the root, nothing flagged, nothing left behind.**

- **At the root:** nothing is emitted beyond the OPB rows. Rules 4, 6, 7 and 8
  fire at the root and write ordinary inference lines.
- **Lazily:** each inference writes, at most, one `pol` at
  `ProofLevel::Temporary`, its closing `rup`, and a `del id -2` deleting the
  `pol` at once. The order literals a reason or conclusion names are defined
  by the shared literal layer on first use (`red` pairs, at `Top`).
- **Deleted:** only the `pol` lemmas, immediately. Nothing a later inference
  cites is deleted, and nothing here cites an earlier inference's line: every
  derivation starts from OPB rows and literal definitions, so deletion never
  blocks a reconstruction.
- **Naming:** an external tool finds the rows by `@c[<id>][e<i>]` (or the
  donors' labels). It does **not** find the family from an assertion: there is
  no hint on any of them (see the [Inference catalogue](#inference-catalogue)
  preamble), so at `AssertionLevel::Inferences` this family's lines are bare
  `a <clause> >= 1;`, indistinguishable by annotation from a linear
  inequality's equally unhinted pushes.
- **OPB versus proof:** no auxiliary anywhere, in either. Nothing to determine
  on `solx`.
- **Proof-only vectors:** `DifferenceGraph::edge_lines` is indexed by
  `posted_index` and is **empty when proofs are off**. Every read of it is
  inside a `JustifyExplicitly` callback, which runs only when a logger exists,
  so nothing dangles; but a future caller indexing it unconditionally would.

## The implementation

### Initialisation and global data

Four costs, kept apart.

1. **`prepare()`** canonicalises the edges into a `DifferenceGraph` (nodes,
   edges, static bounds, disallowed conditions): `O(|edges| log n)`, through a
   `std::map` node index. `define_proof_model` writes the rows.
2. **`install_difference_propagator`** repacks the edges into an arc array
   of at most 32 bytes an arc (a `static_assert` caps the size,
   `difference_incremental.hh:38`, because the relaxation loop scans it once
   per round) and a parallel condition array that stays *empty* when
   nothing is conditional, and registers one trailed `size_t`. Installing is
   quadratic in the trigger count, from either entry point:
   `Propagators::install_returning_id` deduplicates each trigger with a
   linear `contains` (#1309), and the condition-variable list is built with a
   linear `find` per conditional edge, conditional static bound and
   disallowed condition (`difference_graph.cc:1189-1197`), so
   `O(conditions × distinct condition variables)`.
   [`difference_logic.md`](../presolvers/difference_logic.md) measures the
   first at about 3.0 s of a 3.1 s presolver pass at 100,000 nodes.
3. **The root initialiser** (`InitialiserPriority::Expensive`,
   `difference_graph.cc:1261-1283`) infers each disallowed condition
   (rule 6), applies every static bound whose condition is absent or already
   entailed at the root (rule 4, and rule 5 for an entailed one), and runs
   root simplification. **That stage dominates the root on dense systems.**
   Each round is Bellman-Ford from an imaginary zero source, `O(n·m)`, then one
   Dijkstra on reduced costs from each node that is the tail of an edge or the
   head of a candidate. The Dijkstra is a `std::priority_queue` with lazy
   deletion (`difference_simplify.cc:201`, `:237-255`): every relaxation that
   improves a distance pushes an entry and stale ones stay, so the queue can
   hold one entry per arc scanned and each Dijkstra is
   `O((n + m) log(n + m))`. A round runs at most `n` Dijkstras, each
   reaching only what the arcs reach, so it is `O(n·m log(n + m))` in the
   worst case, plus Tarjan
   over the zero-reduced-cost subgraph; a per-source threshold prunes paths
   that cannot matter. `log(n + m)` is `O(log n)` whenever `m` is polynomial
   in `n`, as it is without parallel edges (`m < n²`), but nothing bounds the
   parallel edges: `prepare()` and the presolver keep one arc per posted edge
   or donor, MiniZinc (2.9.7 and 2.10.1) flattens 200 constraints
   `x − y ≤ k` over one pair into 200 `int_lin_le`, all lifted by
   `--difference-logic`, and this pass drops the redundant ones only after
   its own Dijkstras have scanned them. With two nodes and `m` parallel edges
   posted in descending weight, the source's queue held `m` entries (an
   instrumented copy, `m = 1,000`), and the extra `instructions:u` over the
   ascending order grew from 545 to 678 to 810 per edge at
   `m = 10⁴, 10⁵, 10⁶`, the `m log m` shape (`86caad24`, fataepyc-08,
   2026-10-21). It iterates while a
   round fixes a condition, so at most one round more than the conditions it
   fixes. On `difference_chain --mode fixpoint -n 640` (1,282 nodes, 206,400
   edges, unconditional) it takes **0.762 s of a 0.930 s solve** and drops 639
   edges, 0.3%; on the RCPSP/max fixture of [CPU
   performance](#cpu-performance) it is the whole refutation, in 0.2 ms. It
   has no budget, and like every initialiser it does not observe `--timeout`
   (#816).
4. **The incremental route's first call** builds the two adjacency arrays,
   `O(n + m)`, and the potential function, one more `O(n·m)` Bellman-Ford over
   the active arcs (`difference_graph.cc:903-933`). It throws
   `UnexpectedException` if it ever finds itself below a decision on that
   call. Search never puts it there, since it propagates the root before any
   guess, but an `AutoTable` presolver's throwaway root search does: it
   guesses `TrueLiteral` before its first `propagate()`. So a posted
   `DifferenceConstraints`, or a `DifferenceLogic` added before the
   `AutoTable` that installs a propagator (two edges or more), throws in its
   default incremental mode (#1378). The from-scratch route builds neither.

All four are paid with proofs off too.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| root contradiction (`install_initial_contradiction`) | — (once, at the root) | n/a | 7 | `DifferenceConstraints` only, an unconditional degenerate edge with `d' < 0`; installs nothing else | n/a | n/a — the model is refuted |
| root initialiser | — (once, at the root) | n/a | 4, 5 (a condition already entailed), 6, 8 | always; `InitialiserPriority::Expensive` | n/a | n/a — one shot |
| difference propagator, incremental | `on_bounds` on every node; `on_change` on each distinct condition variable | derived: **the condition variables only**, including a node that is also some edge's condition variable; nodes that are only nodes, no | 1, 2, 3, 5 | `incrementally(true)`, the default | never claims | never |
| difference propagator, from scratch | as above | as above | 1, 2, 3, 5 | `incrementally(false)` | never claims | never |

**Idempotence: not claimed, and correctly so.** One pass reaches the fixpoint
of the bounds abstraction, but an inferred bound can snap past a hole and seed
the next call higher, so a second call can infer more. The *hole-snapping
second call* test (`run_hole_snap_test`, commit `16b3b690`, in the `basic` and
`incremental` modes, both routes) is exactly that: `y` with the hole
`{3, 4, 5}` between `x − y ≤ −3` and `y − z ≤ −2`; the first call computes
`lb(y) = 3`, which snaps to 6, and pushes `z` only to 5; the second, seeded
from 6, reaches `z ≥ 8`. An idempotence claim leaves `z` at 5, which the
recorded mutation confirms. The incremental route has a second reason to rely
on that self-wake: it records in `Do` the bound it propagated *from*, not the
snapped one, precisely so that the re-wake finds the node in `Vl`.

**Self-disabling: never.** Nothing in the propagator returns
`DisableUntilBacktrack`, not even when every active edge is entailed by the
bounds; in a conditional system that would also be wrong, since a condition
can still become true and add an arc, and an unconditional one simply keeps
being woken.

**Holes affect.** Derived from the triggers, and the triggers tell the truth
about the nodes: every read of a node is `state.bounds()` or a lower or upper
bound, so no interior removal in a node gives an inference that could not
already be made. A bound that snaps over a hole is not hole sensitivity, for
the reason [`comparison.md`](comparison.md) gives: what is inferred depends on
bounds only, and the hole changes only the domain the inference lands on.
**The condition variables over-report.** `on_change` is registered for every
condition whatever its operator (`difference_graph.cc:1186-1202`). Holes in a
condition variable decide entailment only for `≠` and `not_in_range`, and
disentailment, which can be decided by a hole, is irrelevant here because a
false condition only removes an arc; an `=`
is entailed only once the domain is a singleton, which an interior removal
cannot cause, and `≥`, `<` and `in_range` are bounds questions. So for those
conditions the declaration is conservative — it keeps another family's
optional interior pruning on, and wakes this propagator on interior changes it
cannot use. For the usual Boolean `b = 1` there is no interior and it costs
nothing. Over-reporting is the safe direction; see [Next steps](#next-steps).

### Mutable state and incrementality

Everything lives in the propagator's lambda (`DifferencePropagatorMemory`,
`mutable`) and a shared `DifferenceRootGraph`, and **one number is trailed**.

- **The root graph** (arc array, condition array, round bound) is rewritten
  once by the initialiser and read-only afterwards. Not trailed, because
  everything simplification concludes is a fact about the graph at the root.
- **The potential function** `π` (and its negation, for the upper-bound pass)
  is valid for every arc in `arc_was_active`, **never trailed and never
  reset**: backtracking only removes arcs, which keeps it valid. It only ever
  decreases, and nothing bounds how far; with weights near the range's edge
  that is an overflow (#1371).
- **`Do`** (`do_lb`, `do_ub_neg`) and **`arc_was_active`** must be restored
  *exactly* on backtracking (a lazy clamp silently loses propagation;
  `run_stale_do_test` runs the scenario). They are restored by an undo trail in
  untrailed memory whose length belongs to a trailed constraint-state slot, so
  entering an epoch is `O(1)` and the next call pops the trail down to the
  restored mark. The mark is published at the end of a call, so a
  contradiction part-way leaves its entries to be undone.
- **Recomputed every call**: the active-arc snapshot, `O(m)`, for a system
  with any condition (none for an unconditional one, which iterates the arcs
  straight through); the `Vl` scan, `O(n)`; every static bound, `O(s)`
  (unconditional ones are already in the state and are skipped); and the
  trail pop after a backtrack. The per-wake cost of the incremental route is
  then `O(n + s + [m])`, plus one `IncSat` repair for each newly active arc
  and the two `IncLB`/`IncUB` Dijkstras over what they reach, each
  `O(n + (|Vl| + R) log(n + R))` for `R` arcs reached, against
  `O(rounds·m)` from scratch. Every seed in `Vl` and every improving
  relaxation goes on the binary heap and deletion is lazy, so the heap holds
  up to `|Vl| + R` entries, not one per node. With parallel arcs that is
  real: two nodes and 1,000 parallel unconditional arcs in descending weight,
  simplification off, put 1,001 entries on the first call's lower-bound heap,
  and 1,000 parallel arcs on one undecided condition, which simplification
  keeps, put 1,000 on each pass's heap when the condition became true
  (instrumented copy, `86caad24`, fataepyc-08). Without parallel arcs
  `log(n + R)` is `O(log n)`.
- **What could be maintained instead**: the `O(n)` `Vl` scan and the `O(m)`
  snapshot. [`difference-logic.md`](../difference-logic.md) explains, under
  "What this does not fix", why the refined-watch inbox cannot replace the
  scan, and measures the snapshot, under the preceding "Measurements", at 19%
  of the profile of both routes on the pairwise disjunctive RCPSP models.

### Interior values and optional pruning

**Offers.** `None.` No rule removes an interior value, so there is no pruning
to make optional and no pair to install.

**Observes.** Bounds only, on every node: **a family whose whole vocabulary on
its integer variables is bounds**, like [`comparison`](comparison.md) and the
linear inequalities. A `DifferenceConstraints`, or the presolver's propagator,
is never a reason for another family's interior pruning to stay on because of
a node that is only a node. Its condition variables are the exception, as
[Propagator inventory](#propagator-inventory) says: declared hole-sensitive
whatever the operator, which is true for `≠` and `not_in_range` and
over-reported for the rest. A node that is also some edge's condition variable
is declared hole-sensitive too, since the two trigger lists are deliberately
not deduplicated (`difference_graph.cc:1183-1202`). Because
`gcs::solve_with()` makes the `consistency::Auto` choice after the last
presolver, a presolver-installed propagator's condition variables count too.

### Robustness and limits

- **Unbounded domains.** None exist: every domain lies in the bounded range of
  `dev_docs/integer-ranges.md` (on main), and the constructor checks every
  weight and every condition value with `require_bounded`.
- **Negative values and zero.** Covered: the test modes use domains from −4
  upwards, negative and zero weights, and zero-weight cycles; this audit's
  sweep drew lower bounds from −3 to 3 and weights from −4 to 4.
- **Degenerate shapes.** All handled, as [Semantics](#semantics) lists, and
  all checked: the empty system, constant operands on either side, aliasing
  directly and through views, two constants, a condition over a node, a
  constant or a view, shared conditions and both polarities. The root
  contradiction's message says "an expression is strictly less than itself"
  for two constants too (`4 − 1 ≤ 2`), which is inaccurate wording, not a
  defect.
- **Overflow.** Held in `WideSum` (exact to 128 bits): the from-scratch
  Bellman-Ford's candidate bounds and its two early-exit limits (the limits
  are never narrowed), the initial potential's floor and candidates
  (`difference_incremental.cc:63-79`), and simplification's Bellman-Ford and
  Dijkstra candidates and its per-source threshold
  (`difference_simplify.cc:124-139`, `:227-247`). A value that has to come
  back to `Integer` goes
  through `narrow_or_throw`; everything else is checked `Integer` arithmetic,
  which throws `IntegerOverflow` and never wraps. `integer-ranges.md` (on main)
  accepts a throw for a path sum the answer genuinely needs, and cites a chain
  of nine edges of weight `−max_bounded_value()` as one (it names no domain;
  `run_overflow_test`'s, the whole range, is the one meant, and that test
  requires the throw).
  **That answer does not need it**: the from-scratch route without
  simplification proves the nine-edge chain unsatisfiable in one recursion,
  and the other three routes throw from a potential function. The throws on
  values nothing needs fall into two issues, split by file. **Both lists are
  what the audit found, and neither is exhaustive**: each round of checking
    found more sites, so each issue asked for an audit of its files rather than
  a patch of the lines it names. Both were closed instead by keeping the
  throws, with a message (see [Known limitations](#known-limitations)).
  - **#1371: the shortest-path arithmetic** of `difference_incremental.cc`
    and `difference_simplify.cc` — the potentials (incremental `π`,
    simplification's `h`), the reduced weights and costs, keys and distances
    formed from them, all in plain `Integer`. Sites found so far, with `M`
    for `max_bounded_value()`:
    - `:226`, IncLB's key `bound[v] + potential[v]`: a chain of *eight* edges
      `x[i] − x[i+1] ≤ −M` over the whole range, which from scratch proves
      unsatisfiable;
    - `:79`, the initial potential, and `difference_simplify.cc:139`,
      simplification's: a chain of nine;
    - `difference_simplify.cc:162`, simplification's reduced weight: that
      eight-edge chain plus one redundant edge `x[0] − x[8] ≤ 8`, over `0..1`
      or the whole range;
    - `difference_simplify.cc:297`, the candidate's cycle test: the eight-edge
      chain plus an undecided `b → x[8] − x[0] ≤ −M`;
    - `:239` and `:281`, IncLB's seed key and reduced cost, with
      simplification off;
    - `:120`, `IncSat`: two conditional arcs re-activated alternately drift
      the untrailed potential past the end of `Integer` in nine alternations
      with weights near `2^60`, whether simplification is on or off.
  - **#1372: `difference_graph.cc`'s Bellman-Ford bounds and cycle sums**,
    the from-scratch reference route's and root simplification's witness
    check:
    - `:798` (mirror `:837`): the from-scratch Bellman-Ford narrows a
      candidate bound before comparing it with the node's own domain. So the
      nine-edge chain over `0..1`, refuted by its first edge, throws at `:798`
      on the reference route, and at #1371's sites on the others; a plain
      chain of ten such edges over the whole range throws at `:798` on the
      reference route too.
    - `:564`: `contradict_on_cycle` re-checks a cycle by summing its weight in
      a plain `Integer`.
    - `:301`: root simplification's witness check sums the same way; it runs
      on every route with simplification on, and is reached once #1371's
      `:297` no longer throws first.

  **A heavy negative cycle** — `k` edges `x[i] − x[i+1] ≤ −M` closed by
  `x[k] − x[0] ≤ −M` — throws on every route once its total weight passes
  `Integer` (nine edges; eight are refuted in one recursion everywhere). On
  the reference route it throws at `:564` over the whole range at nine edges,
  and at `:798` over `0..1` or from ten edges; on the others it throws at
  #1371's `:79` or `:139`. Nothing but the self-check needs its weight:
  the refutation is one `pol` over the cycle's rows, and no proof line writes
  the weight out; the same rows as `LinearLessThanEqual`s are refuted in one
  recursion. So the early-exit limits that `difference-logic.md` ("Extreme
  weights") records as fixing a heavy cycle fix one whose weight fits
  (`run_heavy_edge_test`'s two edges of weight `min_bounded_value()`), not one whose weight
  does not. This shape, the chain of nine over `0..1`, and shape B (the
  undecided closing edge, which after #1371's fix lands at `:301`) need
  **both** issues' fixes.

  None is reachable with ordinary weights (the drift needs about 10¹⁶
  alternations at weight 1,000). With such weights every shape but the drift,
  written as a `.scp` `difference` term, throws under `glasgow_scp_solver`
  today. That solver and the term take no route options, so they run the
  default route (incremental, simplification on). Checked for every shape:
  the eight-edge chain over the whole range at `difference_incremental.cc:226`; the nine-edge chain and
  the nine-edge cycle at `difference_simplify.cc:139`; the chain with the
  redundant edge, and shape Z, at `difference_simplify.cc:162`; and the chain
  with the undecided closing edge at `difference_simplify.cc:297` (over the
  whole range, `Integer overflow: -1152921504606846975 + -9223372036854775800`). The drift needs
  a search order the solver cannot set: its default order gives 217
  solutions and no throw with `g` in `0..30`.

  **The presolver route reaches #1371's
  sites** (both audits, at `86caad24`), including in the shipped default,
  where simplification runs in an initialiser before the donors propagate:
  - a chain of nine heavy two-term donors, which the donors alone refute at
    the root, throws at `difference_simplify.cc:139` whenever simplification
    is on, with or without the donors retired, and at `:79` with the donors
    retired and simplification off;
  - the eight-edge chain with a redundant donor throws at
    `difference_simplify.cc:162` in the default configuration, and with an
    undecided `LinearLessThanEqualIf` closing donor at `:297`;
  - a chain of eight throws at `:226` with the donors retired, and the long
    negative cycle in the default configuration and with the donors retired;
  - the drift, posted as `LinearLessThanEqualIf` donors, throws at `:120` in
    the hybrid and with the donors retired (72 solutions without the
    presolver).

  The hybrid with simplification off protects every shape the donors refute
  at the root (all of these but the drift), and the default also protects the
  plain eight-edge chain (UNSAT in one recursion), whose potential and reduced
  weights still fit. From MiniZinc, both a nine-edge chain and the
  eight-edge chain with a redundant constraint give `=====ERROR=====` with
  `--difference-logic` on 2.9.7 and 2.10.1, against `=====UNSATISFIABLE=====`
  without it. #1372's sites are reachable through the presolver only with
  the donors retired, the from-scratch route and simplification off, which no
  front end can select.

### Interval efficiency

**Fine at any width on the propagation, reason and proof sides, with one
exception that is not this family's: the bounds crawl through holes.**

1. **The propagation side.** No per-value loop anywhere in
   `gcs/constraints/difference/`: no `each_value`, no `for_each_value`, no
   `IntervalSet` walk, no loop over a range. Every loop is per node, per arc,
   per static bound, per relaxation round (at most the number of live nodes
   plus one with simplification on, the full node count plus one with it
   off), per Dijkstra settle, or, in simplification only, per source node
   (Johnson's, so `O(n·m log(n + m))` per round with a lazy binary heap;
   `O(n·m log n)` without parallel edges). Large weights
   are arithmetic, not iteration. **The exception is a property of bounds
   reasoning on holey domains**: `y = x + 1` as two edges over the even
   numbers `0..2W` has no solution, and bounds reasoning finds that only by
   snapping a hole at a time. Measured at `86caad24` on fataepyc-09, serial,
   `taskset -c 52`, load average under 3, 2026-10-20: at `W = 10³, 10⁴, 10⁵`
   this family's propagator runs 1,001, 10,001 and 100,001 times in either
   route (`W + 1`), and the two `In` propagators that a value-list
   declaration posts run 2,000, 20,000 and 200,000 times; the same two edges
   as `LinearLessThanEqual` run 1,001, 10,001 and 100,001 times between them,
   beside 1,999, 19,999 and 199,999 `In` calls. Wall time at `W = 10³` is
   about 0.011 s on all three (median of three, re-taken by the fact-check),
   and at `W = 10⁴, 10⁵` 0.98 s and 96.9 s for the incremental route, 0.98 and
   96.8 s from scratch, and 0.99 and 96.5 s for the linears; `instructions:u`
   at `W = 10³, 10⁴` is 0.114 G and 10.71 G for both routes and 0.113 G and
   10.70 G for the linears. The calls are linear in `W` and match the
   decomposition's; the quadratic time is the domain layer's (at
   `W = 20,000`, `IntervalSet::each_interval_minus`, called from `In`'s
   propagator, takes 45% of samples, `State::change_state_for_not_in_range`
   19%, `State::in_domain` 15%; none of it is this family's code).
   Zero-weight-cycle unification (#594) would not remove it either, since
   unified nodes keep their own domains.
2. **The reason side.** A push's reason is the predecessor's bound literal
   and the edge's condition: one or two literals. A cycle's reason is the
   cycle's distinct conditions, at most its length; rule 8's is the witness
   path's conditions. Nothing names a run or a value, and **the work of
   finding a reason** is the predecessor walk (per node) or, for a cycle, the
   extraction and the deduplication. The extraction is `O(n)`, not
   `O(cycle)`: it allocates an `n`-entry `seen` vector, and its walk can pass
   every node before it closes the cycle (a two-edge cycle with a chain of
   `L` negative edges hanging off it walks all `L + 2` nodes, `L` up to
   10,000, both routes). The deduplication, for a cycle and for rule 8's
   witness path alike, is a linear `find` per conditional edge
   (`difference_graph.cc:572`, `:313`): `O(k·c)` comparisons for `k`
   conditional edges and `c` distinct conditions, exactly `k(k−1)/2` when
   each has its own (#1384). In a ring of `k` such edges closed by a
   `−1`, proofs off, that block took 0.030 s at `k = 8,000` and 0.136 s at
   `16,000` (an instrumented copy, median of three); the whole solves take
   0.24 s and 0.73 s, and at `16,000` installation is the larger share (54%
   of samples, #1309 and the condition-variable `find`, against 19% for the
   deduplication). With one shared condition it is `k − 1` comparisons and
   0.14 ms at `k = 16,000`. Measured at `86caad24` on fataepyc-08,
   2026-10-21. Both are paid
   with proofs off. Reasons are built unguarded: the
   `ExplicitReason` of every push is assembled whether or not
   `want_reasons()` is true. It is one or two literals and built only when a
   bound actually moves, so it is not width-proportional; whether it costs
   anything measurable with proofs off was not measured (it was 43% of
   `comparison`'s cycles, #907, where the reason was built on every call).
3. **The proof side.** One `pol` per inference over two rows (a push), or over
   a cycle's rows, or over a candidate and its witness path; never a per-value
   line and no width-gated second form. Each `pol` line cites two rows (or a
   cycle's), so the line is `O(1)` (or `O(k)`) references; the rows it adds
   have `O(log M)` terms for `M` the largest magnitude in the domains.
4. **The audit lane.** One row, `DifferenceConstraints` in
   `gcs/large_domain_audit_test.cc:834`, pinned `Clean`: three `0..probe_width`
   variables and two unconditional edges, `v0 − v1 ≤ 0` and `v1 − v2 ≤ 1`,
   propagated once at the root. No row in the `"Large domain proof sizes"`
   case. **What the row does not vary is most of the family.** Its edges infer
   nothing at all at the root over equal wide domains, so the row runs the
   setup, the initialiser and one call that pushes nothing; it has no holes
   (which is where the crawl lives), no condition, no view, no constant
   operand, and runs only the default route with simplification on. The
   absence of any per-value site is a property of the source, so a sharper row
   could not trip on this family's own code, but it would show the crawl.

## Inference catalogue

Eight rules. 1 and 2 are the bound pushes, 3 the negative-cycle refutation, 4
and 5 the static bounds, 6 the disallowed condition, 7 the degenerate
contradiction, and 8 root simplification's one inference. A bound push that
empties a domain is not a separate rule: it is rule 1 or 2 asserting a
literal that is already false.

Facts that hold for all eight:

**No hint, anywhere.** The family passes no hint type, so every assertion uses
the default `NoHint` and is a bare `a <clause> >= 1;` with no annotation:
verified on every rule's fixture at `AssertionLevel::Inferences`
(`rules.cc`, `86caad24`). An external justifier can tell nothing about the
origin of such a line from its annotation, and this family's pushes have the
same clause shape as a linear inequality's, which are also unhinted
([`linear.md`](linear.md)). A presolver-installed propagator is the same: no
`constraint_id unnamed` hint, because there is no hint at all.

**What licenses them.** Rules 1 and 2 are **JP 3.15 (linear inequality
propagation)** on a two-term row, with this solver's usual departures: the
`pol` adds only the predecessor's bound definition, the closing step is a
reason-wrapped RUP rather than a syntactic implication, and the conclusion's
own literal definition is left to the RUP. Theorem 2.9 would license a bare
RUP only for a row degree in `{0, 1}`, and a difference row's degree is
arbitrary ([`justification-techniques.md`](../justification-techniques.md),
"Where the third one stops"), which is why the `pol` is there; that unit
propagation alone cannot add the edge row to the definition is
[`difference-logic.md`](../difference-logic.md)'s "Proof shape 2". Rules 3
and 8 follow **no published procedure**: they are a Farkas certificate for a
totally unimodular system — sum the cycle's rows with unit multipliers — which
McIlree's thesis proposes in general as future work (§8.2.2, "Further General
Justification Procedures", under its run-in heading "Justifications via Linear
Programming": for any constraint with a totally unimodular linearisation,
with `GlobalCardinality` as its example and network-flow constraints more
broadly), but states no procedure for; argued in their entries. Rules 4 to 7
are bare RUPs by Theorem 2.7 or by normalisation alone, with conditions by
Theorem 2.6.

**No justification reads `state`.** Every `JustifyExplicitly` callback reads
the arc, the snapshotted bound it was handed and the edge rows; the reason
literals are built from the same values.

**Every `pol` goes through deview mode** and is written at
`ProofLevel::Temporary` and deleted (`del id -2`) on the line after its
closing RUP.

**Tightness, family-wide.** There is no mutation lane for this family. The
code comments record development-time mutation results — a cycle condition
dropped from the reason is rejected by VeriPB on the reified fixtures; the
cycle's and rule 8's `saturate` are *not* load-bearing; rule 8's path
conditions are not needed in the reason at the root — and so does
[`difference-logic.md`](../difference-logic.md) for the incremental gates.
None of them is a standing lane; each entry below says `Not shown.` on that
basis.

### Rule: lower-bound-push

(Rule 1.)

- **Infers** — `y ≥ L − d` across an active arc `x --d--> y` (the edge
  `x − y ≤ d`), where `L` is the bound the pass holds for `x`: its current
  lower bound, or a bound inferred earlier in the same call.
- **Fires when** — a node's lower bound or a condition changes; in the
  incremental route, for every node Dijkstra settles with a bound above its
  current one, in settle order (`difference_graph.cc:1032-1036`); from
  scratch, for every node with a predecessor after Bellman-Ford, in
  predecessor-forest order (`infer_along_forest`, `:633`). Both call
  `infer_lower_bound` (`:682`), which re-checks the arithmetic and returns
  early if the state already has the bound.
- **Strength** — with rule 2, the propagator's fixpoint is `partial`:
  **`bounds(D)` and range consistency on the node variables with respect to
  the sub-system of edges whose conditions currently hold**, and nothing on
  the condition variables. On the whole constraint, and still on the node
  variables only, that is `bounds(D)` (and `bounds(Z)`, and range) whenever
  every undecided condition can be made false at once without touching a
  node: separate condition variables, each used in one polarity, none of them
  a node. That is sufficient, not necessary: the fact-check's sweep found the
  claim holding at 8,777 of the 16,270 traced nodes per route where the
  condition fails. It is not `GAC`: with holes, `x =
  y` as two edges over `D(x) = {0, 1, 2}`, `D(y) = {0, 2}` leaves `1` in
  `x`. The argument: at the fixpoint every active arc has
  `lb(y) ≥ lb(x) − d` and `ub(x) ≤ ub(y) + d`, so "every node at its lower
  bound" and "every node at its upper bound" are both solutions of the
  active sub-system, and both use values in the domains. Range consistency
  follows from total unimodularity: fixing one variable to a value between its
  bounds leaves a non-empty polytope with integer vertices. **Checked by brute
  force** (`strength.cc`, `86caad24`): seeds 11–16, 600 random instances in
  each of seven families (unconditional; unconditional with holey initial
  domains; extreme weights; `b = 1` conditions on separate Booleans, shared
  across edges; both polarities of one Boolean; conditions on node variables;
  any operator on any variable, holes included), offset views and constants on
  a third of the operands, solved to completion with a random variable order
  and `random_out` values (so holes appear during search), checking every
  search node: 1,074,971 nodes in each of the four routes (incremental and from
  scratch, simplification on and off). Against the active sub-system, **zero**
  `bounds(D)` and zero range violations in every family and route, and 31
  `GAC` violations (holes). Against the whole constraint, zero `bounds(D)`
  violations in the four families the claim covers, and 7,051 to 12,653 per
  route in the three it does not. Zero solution mismatches, and identical
  counts between the incremental and from-scratch routes. An independent sweep
  by this audit's fact-check (seeds 101–116, 9,600 systems, about 462,000
  nodes per route; all six condition operators, over Booleans, wider
  variables, nodes, offset and negated views and constants; range- and
  list-declared variables) found the same: zero active-sub-system `bounds(D)`
  or range violations, 60 `GAC` ones, and zero whole-constraint violations
  where the condition holds; it also met #1371's drift once. Rule 1 alone
  gives the lower-bound half.
- **Algorithm** — incremental: `IncLB` (the paper's Algorithm 3, transcribed
  from its Example 7, since lines 15–16 of its pseudocode are wrong), one
  Dijkstra on reduced costs seeded from `Vl` (nodes whose bound beat `Do`,
  plus the tails of newly active arcs), expanding only nodes that beat `Do`:
  `O(n + (|Vl| + R) log(n + R))` for `R` the arcs it reaches, since every
  seed and every improving relaxation goes on the binary heap, with lazy
  deletion ([Mutable state and incrementality](#mutable-state-and-incrementality)).
  From scratch: Bellman-Ford over the active arcs from the current
  lower bounds, `O(n·m)`, with at most one round per live node plus one when
  simplification has run (per node plus one when it is off), stopping early
  when a round changes nothing.
  In nodes and arcs, never values. Kletzander, Dekker, Schutt and Stuckey
  (arXiv:2607.20022), from Feydy, Schutt and Stuckey (PPDP 2008).
- **Why it is true** — `x − y ≤ d` and `x ≥ L` give `y ≥ x − d ≥ L − d`; under
  a condition, only while it holds. A chain of pushes along a path is a chain
  of such single-edge steps, each citing the bound the one before it set.
- **Proof technique** — `pol` then `RUP`: `pol <edge row> <Def of x ≥ L> +`,
  which cancels `BinEnc(x)` and leaves `BinEnc(y) + M·¬[x ≥ L] (+ M'·¬cond) ≥
  L − d`; then the reason-wrapped RUP derives the push. JP 3.15 on a two-term
  row, departures as in the preamble. Precondition: the row's two variables
  are in the same representation as the definition's — guaranteed for this
  class's own rows by canonicalisation and for donor rows by deview mode.
- **Reason** — `{x ≥ L}` plus the edge's condition if it has one. Minimal for
  the single-edge step: `x ≥ L` is the weakest antecedent for `y ≥ L − d`, so
  this is the paper's per-edge bound explanation (its eq. (1), §4.3.1). **Not
  minimal against the proof**: when `L` is `x`'s declared lower bound and its
  boundary pin is already a unit, the literal is true at the top and could be
  dropped, which #1072 measures as rare: in the unhinted bucket (all unhinted
  literals, this family's among them), 8.2% at a declared bound on
  `2019_accap`, 22 literals on `2011_cyclic-rcpsp`, and 0 on four other
  models. One or two literals, never per value. Not guarded on
  `want_reasons()`.
- **Assertion** — `y ≥ L − d ∨ ¬(x ≥ L) [∨ ¬cond]`. Measured:
  ```
  a 1 i[y][ge3] 1 ~i[x][ge0] >= 1;                       x − y ≤ −3, x at its declared 0
  a 1 i[y][ge8] 1 ~i[x][ge5] 1 ~i[b][eq1] >= 1;          b → x − y ≤ −3
  ```
  When the push empties `y`'s domain, the same line is written with an
  already-false conclusion and the conflict is closed by the backtrack; there
  is no separate contradiction line. For `x ∈ 5..10`, `y ∈ 0..6` and
  `x − y ≤ −3`: `a 1 i[y][ge8] 1 ~i[x][ge5] >= 1;`, then the backtrack.
- **Hint** — none (`NoHint`); see the preamble. A work item: [Next
  steps](#next-steps).
- **Offline reconstructibility** — `search`. The clause names `x`, `y` and the
  condition, but not the row. A sufficient derivation is JP 3.15 against any
  model row stating `x − y ≤ d'` with `d' ≤ d` (under that condition, if any);
  the reconstructor finds one by trying the two-term rows over `x`'s and `y`'s
  bits (or a view's, through its link), and any that licenses the clause will
  do. A constraint-id hint would make it `hinted`; it would supply nothing
  missing.
- **Proof size** — three lines per push (`pol`, `rup`, `del`); the `pol` line
  cites two lines, and the derived constraint has `O(log M)` terms before
  cancellation, for `M` the largest magnitude in the two domains. Constant in
  `n` and `m`. The literal layer adds definitions for any literal not yet
  introduced: on `difference_chain --mode fixpoint -n 40`, 81 pushes give 243
  of the 1,398 lines (17%).
- **Gaps** — `None.`
- **Tightness** — `Not shown.` The corruption to try first is the `pol`
  without the definition row: the RUP should then fail, since unit
  propagation cannot add the two rows (`view-proof-logging.md`, invariant 3).

### Rule: upper-bound-push

(Rule 2.)

- **Infers** — `x ≤ U + d` across an active arc `x --d--> y`, where `U` is
  the bound the pass holds for `y`.
- **Fires when** — as rule 1, in the upper-bound pass: `IncUB` is `IncLB` on
  the reverse graph with the potential, the bounds and the gate negated
  (`difference_graph.cc:1077-1084`), or `relax_upper_bounds` from scratch.
  Both call `infer_upper_bound` (`:705`).
- **Strength** — with rule 1, as rule 1 says; alone, the upper-bound half.
- **Algorithm** — as rule 1, mirrored. One implementation serves both
  directions in the incremental route.
- **Why it is true** — `x ≤ y + d ≤ U + d`.
- **Proof technique** — `pol` then `RUP`, with the definition of `y < U + 1`;
  as rule 1.
- **Reason** — `{y < U + 1}` plus the edge's condition. As rule 1, including
  #1072's case at a declared upper bound.
- **Assertion** — `x < U + d + 1 ∨ ¬(y < U + 1) [∨ ¬cond]`, for example
  `a 1 ~i[y][ge7] 1 i[z][ge11] >= 1;` (`y − z ≤ −4`, `z ≤ 10`).
- **Hint** — none.
- **Offline reconstructibility** — `search`, as rule 1.
- **Proof size** — as rule 1.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: negative-cycle

(Rule 3.)

- **Infers** — a contradiction: the active arcs contain a cycle of negative
  total weight.
- **Fires when** — from scratch: a Bellman-Ford pass still relaxes in its last
  round, or a candidate bound passes the limit (best seed plus the sum of the
  negative weights) that no simple path can exceed; the walk back along the
  predecessors then always reaches a cycle, and every predecessor cycle is
  negative ([`difference-logic.md`](../difference-logic.md), "Rounds, and why
  the extraction is total"). Incremental: `IncSat` fails to repair the
  potential when an arc becomes active, or the first call's potential
  computation fails, and the route hands over to the from-scratch pass to find
  and refute the cycle (`refute_negative_cycle`, `:861`). An unconditional
  cycle is found on the first call; a conditional one when its last condition
  becomes true. The extracted cycle is checked arithmetically before anything
  is written.
- **Strength** — n/a; this is a refutation. It is complete for the active
  arcs: a negative cycle among them is always found on the call where it
  appears. From scratch (and in the initial potential), Bellman-Ford's
  last-round and limit tests detect one whenever it exists. Incrementally,
  the potential stays valid for the arcs already active, so a new cycle must
  contain a newly active arc, and `IncSat` detects it when its repair reaches
  that arc's tail (`difference_incremental.cc:131`, `:167`); the cycle is
  then extracted by `refute_negative_cycle`'s Bellman-Ford. By the paper's
  Theorem 1 (a system is satisfiable iff its graph has no negative cycle) that
  is every graph-only infeasibility.
- **Algorithm** — the pass that finds it (`O(n·m)` from scratch; `IncSat`, a
  Dijkstra over the violated region with a binary heap and lazy deletion,
  `O((n + m) log(n + m))` per repair, incremental, then one `O(n·m)` pass once
  per refuted branch), then the cycle extraction, `O(n)`, and the reason's
  deduplication, `O(k·c)` comparisons for `k` conditional edges and `c`
  distinct conditions (#1384; [Interval efficiency](#interval-efficiency)
  measures both). Cotton and Maler
  (SAT 2006) for `IncSat`, which the paper notes is the algorithm of
  Ramalingam, Song, Joskowicz and Miller (*Algorithmica* 23, 1999).
- **Why it is true** — summing `x_i − x_{i+1} ≤ d_i` around a cycle cancels
  every variable and leaves `0 ≤ Σ d_i < 0`. With conditions, the sum holds
  only when all of them do, so the conclusion is that not all of them do.
- **Proof technique** — `pol` then `RUP`: the cycle's rows added with unit
  multipliers, every bit telescoping, which leaves `Σ Mᵢ·¬condᵢ ≥ −W`, a
  condition on several edges taking the sum of their `Mᵢ`; then, if any edge
  is conditional, one `saturate`, which caps every coefficient at the degree
  `−W`; then the RUP of `¬reason`. The saturated line is the clause
  `¬cond₁ ∨ … ∨ ¬cond_k` scaled by `−W` exactly when every coefficient
  reaches `−W`: equivalent to the clause, and the clause itself only when
  `−W = 1`. Otherwise it is a PB constraint strictly stronger than the
  clause: saturation lowers a coefficient but cannot raise one, and `Mᵢ`,
  the row's big-M, is `max(maxposᵢ − dᵢ, 1)`, for `maxposᵢ` the largest
  value of `xᵢ − yᵢ` over the bits the row is written in and `dᵢ` the
  deviewed weight (`names_and_ids_tracker.cc:3034`; a presolver donor row
  over a registered view uses the view's own bits), which can fall short of
  `−W`. For
  `x, y ∈ 0..1`, `b → x − y ≤ −2` and `c → y − x ≤ −2`, conditions forced
  true, the rows are `-1 x 1 y 3 ~b >= 2` and `-1 y 1 x 3 ~c >= 2` (writing
  each variable's one bit as its name), and the line is `3 ~b 3 ~c >= 4`,
  which says both conditions are false. Either way the reason's literals
  falsify it, so the closing RUP derives the clause, whatever the saturated
  line's shape. Of the fixtures run, only `x, y ∈ 0..10` with
  `b → x − y ≤ −1` and `c → y − x ≤ 0` (`−W = 1`) gives literally
  `1 ~b 1 ~c >= 1`. VeriPB 3.0.2, with
  `--force-checked-deletion`, verifies that proof and the three-variable one
  under *Reason* (`86caad24`, fataepyc-08, 2026-10-21). **No published
  procedure**: this is a Farkas certificate, and the
  node-arc incidence matrix being totally unimodular is why unit multipliers
  always suffice; argued under *Why it is true*. Precondition: consecutive rows
  share a representation for the shared node (canonicalisation, or deview mode
  for donor rows).
- **Reason** — the distinct conditions on the cycle; empty for an
  unconditional cycle. **Sufficient, not minimal.** It is irredundant for the
  cycle as a graph: without the domains, the cycle less the edges of any one
  condition is acyclic, so it has a solution. But the rows also carry the
  variables' encoding ranges, and against those fewer conditions can
  already be contradictory:
  - in the example under *Proof technique*, each row alone entails its own
    condition false (a one-row OPB verifies `rup ~b`);
  - with `x ∈ 0..10`, `y ∈ 0..1`, `z ∈ −10..10` and `b₁ → x − y ≤ −5`,
    `b₂ → y − z ≤ 0`, `b₃ → z − x ≤ 0`, the saturated line is
    `5 ~b₁ 5 ~b₂ 5 ~b₃ >= 5`, the clause over all three scaled by 5, yet the
    `b₁` row alone entails `¬b₁`.

  A saturated coefficient below the degree always marks such a condition,
  but a clause-shaped line does not rule one out. The code comment's mutation
  result (a condition dropped from the reason fails VeriPB) is about the
  reified fixtures. Nor is it minimal over cycles: another negative cycle
  might need fewer conditions, and the first one found is the one cited.
  Deduplicated, so a Boolean on several edges appears once, at the cost in
  *Algorithm*.
- **Assertion** — an explicit `contradiction()`, so `¬reason` with no
  attempted literal: `a >= 1;` for an unconditional cycle, and
  `a 1 ~i[b][b0] 1 ~i[c][b0] >= 1;`-shaped for a conditional one. Measured at
  `AssertionLevel::Inferences`; the fully justified form is
  ```
  pol @c[_1][e2] @c[_1][e1] + @c[_1][e0] + ;
  rup >= 1;
  del id -2;
  ```
- **Hint** — none.
- **Offline reconstructibility** — `search`. The clause says which conditions
  to assume (none, for an empty clause), and the rows are in the model; a
  reconstructor finds a negative cycle among the two-term `±1` rows active
  under those assumptions (the unconditional ones and the half-reified ones
  whose big-M literal is one of the clause's negated conditions) by one
  Bellman-Ford over them, `O(n·m)`, and sums it. Any negative cycle will do. A
  hint listing the cycle's rows would make it `hinted`.
- **Proof size** — three lines; the `pol` line cites one row per cycle edge,
  `O(k)` references for a cycle of `k` edges (the derived constraint has
  `O(k log M)` terms before it telescopes). Independent of the domains:
  `difference_chain --mode refute` is a whole proof of 12 lines at `n = 40`
  and `n = 160`, and byte-identical at domain multipliers 2 and 8 (796 bytes
  at `n = 40`; 2,639 at `n = 160`, where the cycle is four times longer),
  because the line cites labels only; against 68,430 lines for the decomposed
  model at `n = 40`.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` (The development-time mutation in the
  preamble: a condition dropped from the reason is rejected; the `saturate`
  removed is accepted.)

### Rule: static-bound

(Rule 4.)

- **Infers** — `x ≤ d + c` for an unconditional edge `x − c ≤ d`, or
  `y ≥ c − d` for `c − y ≤ d`.
- **Fires when** — once, in the root initialiser
  (`apply_difference_static_bounds`, `difference_graph.cc:430`, which applies
  every static bound whose condition is absent or already entailed, so it
  fires rule 5 too at the root); the propagator re-runs the same pass every
  call, and the unconditional bounds are then already in the state. Never from
  the presolver, which skips constant donors.
- **Strength** — `GAC` on that edge: a unary bound.
- **Algorithm** — one bound comparison per static bound. `O(1)`.
- **Why it is true** — the edge is the bound.
- **Proof technique** — `RUP`, by **Theorem 2.7**: the negated conclusion
  bounds `BinEnc(x)` from one side and the row from the other.
- **Reason** — none.
- **Assertion** — the bound literal alone, for example `a 1 ~i[x][ge6] >= 1;`
  for `x − 2 ≤ 3`. Fully justified, `rup 1 ~i[x][ge6] >= 1;` with no `pol`.
- **Hint** — none.
- **Offline reconstructibility** — `offline`: the clause is RUP against the
  database as it stands.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: conditional-static-bound

(Rule 5.)

- **Infers** — the static bound of a half-reified constant-operand edge, once
  its condition is entailed.
- **Fires when** — every propagator call re-tests every conditional static
  bound. `run_conditional_static_bound_test` checks that one applied in a
  failing branch leaves nothing behind.
- **Strength** — `GAC` on the operand while the condition holds; nothing on
  the condition.
- **Algorithm** — `O(1)` per conditional static bound per call.
- **Why it is true** — as rule 4, under the condition.
- **Proof technique** — `RUP`, Theorem 2.7 with the condition carried by
  **Theorem 2.6**.
- **Reason** — `{cond}`. Minimal.
- **Assertion** — `bound ∨ ¬cond`, for example `a 1 ~i[x][ge4] 1 ~i[b][b0] >=
  1;` for `b → x − 0 ≤ 3`.
- **Hint** — none.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: disallowed-condition

(Rule 6.)

- **Infers** — `¬cond` for a half-reified edge that canonicalises to
  `cond → 0 ≤ d'` with `d' < 0` (an aliased edge, or two constants).
- **Fires when** — once, in the root initialiser, unless `cond` is already
  false. A soundness obligation, not a nicety: dropping the edge would let
  `cond` hold with the edge violated. Never from the presolver, which leaves
  degenerate donors to their own propagators.
- **Strength** — `GAC` on the condition.
- **Algorithm** — `O(1)`.
- **Why it is true** — `0 ≤ d' < 0` is false, so its condition cannot hold.
- **Proof technique** — `RUP`. The row's integer terms cancel (or are absent),
  so it normalises to `M·¬cond ≥ −d'` with `−d' ≥ 1`, which propagates `¬cond`
  directly; Theorem 2.6.
- **Reason** — none.
- **Assertion** — `¬cond`, for `b → x − (x + 1) ≤ −2` the unit
  `1 ~i[b][b0] >= 1`. Fully justified, `rup 1 ~i[b][b0] >= 1;`.
- **Hint** — none.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`; there is nothing to corrupt but the
  conclusion.

### Rule: degenerate-edge-contradiction

(Rule 7.)

- **Infers** — a contradiction, from an unconditional edge that canonicalises
  to `0 ≤ d'` with `d' < 0`: `x − x ≤ −1`, `x − (x + 3) ≤ −5`, or two
  constants such as `4 − 1 ≤ 2`.
- **Fires when** — at install, through `install_initial_contradiction`
  (`difference_constraints.cc:247`); the first offending edge is named in the
  message, and nothing else of the constraint is installed. `DifferenceConstraints`
  only. Refuted in 0 recursions.
- **Strength** — n/a.
- **Algorithm** — `O(1)`, the check made during `prepare()`.
- **Why it is true** — the edge's statement is false.
- **Proof technique** — `RUP`: the row normalises to `0 ≥ −d' ≥ 1`.
- **Reason** — none.
- **Assertion** — the empty clause, `a >= 1;`.
- **Hint** — none.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: root-condition-fixing

(Rule 8.)

- **Infers** — `¬cand` for a conditional edge `u --d--(cand)--> v` whose
  condition is undecided at the root, when the root base graph (unconditional
  edges, and conditional ones whose condition is already true) has a path
  `v ⇝ u` with `d + w(v ⇝ u) < 0`.
- **Fires when** — once, in the root initialiser, when
  `simplifying_at_root` is on (the default), from either entry point;
  iterated to a fixpoint, since fixing one polarity of a Boolean makes the
  other's edge part of the base graph (`difference_graph.cc:226-380`). When
  both polarities are fixable in one round, the second inference contradicts
  the first and the model is refuted at the root, in 0 recursions. The
  algorithm is the "fixing Boolean variables to ⊥" sub-step of the paper's
  Algorithm 4; the inference is the one the paper's `IncImp` (its Algorithm 2)
  makes during search, here made only at the root.
- **Strength** — `partial`, on the condition variables only: at the root, every
  undecided condition whose edge would close a negative cycle with the base
  graph is fixed false; during search, nothing.
- **Algorithm** — Johnson's all-pairs pass per round, as in [Initialisation and
  global data](#initialisation-and-global-data); the witness is the
  shortest-path tree's path from `v` to `u`, re-checked arithmetically before
  anything is written. The paper's Algorithm 4 (its section 5.2), iterated as
  its section 5.3 says.
- **Why it is true** — `cand` together with the path's edges, all of which
  hold whenever their conditions do, sum to `0 ≤ d + w < 0`; so `cand` cannot
  hold together with the path's conditions.
- **Proof technique** — `pol` then `RUP`: the candidate's row plus the path's
  rows, one `saturate`, then the RUP. The same Farkas sum as rule 3, with the
  candidate's big-M residual as the surviving literal; as there, the
  saturated line is the clause scaled by the degree exactly when every
  coefficient reaches the degree, and the RUP derives the clause either way.
  No published procedure.
- **Reason** — the path's distinct conditions, all true at the root,
  deduplicated by the same linear search as rule 3's, `p(p−1)/2` comparisons
  for a path of `p` distinct conditions (#1384). **Not
  load-bearing in the proof** (they are root facts, so unit propagation
  recovers them), and kept because the reason is also what the state and the
  nogood machinery see.
- **Assertion** — `¬cand ∨ ¬(path conditions)`; with an unconditional path,
  the unit `a 1 ~i[bf][b0] >= 1;`. On `rcpsp --size 9 --machine-fraction 0.9
  --max-lag-density 0.4 --max-lag-slack 0 --machine difference --seed 6
  --variant global` the whole proof is six such units, the last
  contradicting an earlier one, and the empty clause: 24 lines fully
  justified.
- **Hint** — none.
- **Offline reconstructibility** — `search`, as rule 3: assume `cand` and the
  clause's other negated conditions and look for a negative cycle.
- **Proof size** — three lines; the `pol` has `1 + |path|` addends.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

One test binary, `difference_test` (`difference_constraints_test.cc`), run as
nine ctest lanes (`difference_constraint_{basic, cycles, views, alias,
reified, simplify, incremental, random, random_reified}`), plus seven view-sweep
registrations under `add_view_tests` (`gcs/CMakeLists.txt:985-991`). Elsewhere:
`scp_reader_test` (two cases: enumeration, and write→read→write with
`=` and `≥` conditions), `integer_ranges_test` (a weight out of range is
refused), `solve_test` (`x − x ≤ −1` reports its message), the large-domain
row, and the example lanes (`difference_chain-global-*`,
`rcpsp_machine_difference_global` and `rcpsp_machine_difference_nosimplify`,
among others), which run with `run_test_and_verify.bash`.

- **The data-driven modes** (`run_test`) solve each fixture three ways — as
  `DifferenceConstraints` with the differential audit on, as
  `DifferenceConstraints` from scratch, and as one `LinearLessThanEqual` (or
  `…If`) per edge — and require all three solution sets to equal a brute-force
  oracle *and* the two routes' recursion counts to be equal. That last check
  is the sharpest test of the incremental machinery there is.
- **Not `solve_for_tests_checking_gac`**, correctly, since the family is not
  `GAC`. Nothing in the suite asserts a `bounds(D)` claim; this audit's sweep
  ([Inference catalogue](#rule-lower-bound-push), rule 1) is the evidence.
- **Hand-built tests.** In every mode and every view lane: the negated-view
  refusal and the extreme-weight test (`run_overflow_test`, chains of two,
    three and nine edges over the whole range, default route only; it requires
  the nine-edge chain to *throw* `IntegerOverflow`, saying it came from
  difference logic). `basic` adds `run_near_edge_shapes_test`: the shapes of
  #1371 and #1372 (chains of eight to ten edges, cycles of nine and ten, the
  redundant edge, the undecided closing edge and shape Z, over the whole range
  and `0..1`) on all four routes, each of which must either give the answer
  the same rows give as linear inequalities or throw that message. It also adds
  the transitive push, the hole snap (both routes) and the heavy-edge test
  (`run_heavy_edge_test`, weights `±(2^60 − 1)` in three configurations:
  default, simplification off, and from scratch with simplification on);
  `reified` the
  push across conditional edges with a false-condition negative control and
  the degenerate conditional edge; `simplify` thirteen fixtures pinning each
  sub-step's counter, plus the root refutation in 0 recursions; `incremental`
  the stale-`Do`, activation-seed, re-activation, conditional-static-bound and
  hole-snap scenarios with a per-node invariant, and twenty random systems
  under Luby restarts on both routes.
- **VeriPB runs**, in every mode that writes a proof (`incremental` writes
  none). At `--seed=1`: 86 proving runs across the eight modes, all verifying.
- **Runtime caps: the defaults do not fire.** No lane sets or clears a cap.
  Run directly with the ctest defaults (300 solutions, 1,500 nodes) and
  without them at `--seed=1`, all nine lanes pass in 0.02–0.48 s each and no
  run reports a truncation; the hand-built tests, `run_simplify_test` among
  them, call `solve_with` directly and bypass the cap wrapper altogether. So
  the capped and uncapped lanes checked the same thing at that
  seed. The `random` modes draw from the announced seed, so another seed can
  differ.
- **Seeded**: the random modes and the restart stress take `--seed=N`.
- **Real instances**: none ported. The RCPSP/max shapes the design was built
  for live in `examples/rcpsp` and in the `simplify` mode's miniatures.
- **No mutation lane, and no control lane.** The recorded mutation results are
  in the code comments and in `difference-logic.md`'s incremental table; they
  are not re-run by anything.

What the tests do **not** cover:

- **Condition operators other than `=`.** `run_test` and the random modes
  condition on `vars[i] == value` only; `≠`, `≥`, `<`, conditions on a node,
  on a view or on a constant appear nowhere but a `≥` in one `.scp`
  round-trip. This audit's sweep and `.scp` differential cover them, with no
  defect found.
- **Strength.** Solution equality cannot see an over-weak propagator; the
  `bounds(D)` and range claims rest on this audit's brute force only.
- **The overflow shapes of #1371 and #1372**: the eight-edge chain, alone, with
  the redundant edge `x[0] − x[8] ≤ 8`, or with an undecided closing edge; the
  eight-edge chain over `0..1` with `z = M` and `z − x[8] ≤ M` (shape Z); the
  nine-edge chain over `0..1`; the ten-edge chain; the heavy negative cycle;
  and the potential drift. `run_overflow_test` runs on the default route
  only; `run_heavy_edge_test` runs three configurations but never from scratch
  with simplification off, the reference route.
- **Holey wide domains**, and so the crawl. The only wide domains in
  `difference_constraints_test.cc` are `run_overflow_test`'s whole-range
  chains; the large-domain audit row is wide but has no holes.
- **`cake_pb_cp`**: no chain case can exist (no keyword).
- **Proofs above `AssertionLevel::Off`**: none in the suite. This audit ran
  each rule's fixture at `Inferences` (all `UNDER ASSERTIONS` with the right
  conclusion) and the benchmarks at `Links` and `Inferences`; its fact-check
  ran every rule's fixture, declared both as ranges and as value lists, and 720
  random systems at all five levels. `Off` verifies; `Definitions`,
  `Inferences` and `Backtracking` are accepted everywhere. `Links` rejects
  proofs at a solution line only when a variable wider than `{0, 1}` is
  declared as a range (146 of the range-declared random systems, each at a
  solution line; not every such run, since 8 of 68 satisfiable `.scp` runs
  passed), on
  the decomposed model too (#1210), and accepts every model declared with
  value lists (359, 137 of them satisfiable).
- **The `.scp` route with views**: unreadable by design (above).

This audit's own checks, all at `86caad24` on fataepyc-09:

- **`.scp` differential** (`scpdiff.py`, seed 1 with 60 instances and seeds
  2–11 with 300 each): 3,060 random `.scp` systems through
  `glasgow_scp_solver --all` with `GCS_DIFFERENCE_AUDIT=1` — up to four nodes
  and up to two further condition variables, constants, aliasing, all four
  `.scp` condition operators over Booleans, wider condition variables and
  nodes, weights of `±(2^60 − 1)`, empty edge lists — against brute force: all
  agree, and none errored (a non-zero exit counts as a failure, not as
  agreement); every third or fourth, 770 in all, also with `--prove`, all
  `VERIFIED` with the expected enumeration count or `UNSATISFIABLE`. The
  fact-check's independent harness added 2,100 more (seeds 21–23): all agree
  with brute force, and its proofs, at rotating assertion levels, behave as
  the assertion-level bullet above says.
- **Strength sweep**, as in rule 1.
- **Proofs on and off search identically**: `rcpsp --size 12 --seed 2
  --machine-fraction 0.8 --machine difference --variant global` takes 1,667
  recursions and 3,216 propagations either way, and `difference_chain
  --mode fixpoint -n 160 --variant global` 323 and 327.

### Benchmarks and examples

- **`examples/difference_chain`**, the paper's Example 8: `--variant=global`
  posts the system as one `DifferenceConstraints`, `decomposed` as one
  linear (or `--donor=comparison`) per edge, `presolved` through the
  presolver. `--mode=fixpoint` exercises rule 1 only (81 lower-bound pushes at
  `n = 40`): the lower-bound bump that starts the chase is a
  `LinearGreaterThanEqual` posted in every variant (`difference_chain.cc:432`),
  and there is no constant-operand edge. `--mode=refute` exercises rule 3
  only.
- **`examples/rcpsp`**: `--variant=global` posts the temporal network
  (precedences, maximum lags, makespan bounds) as one `DifferenceConstraints`;
  `--machine=difference` adds the machine as conditional edges, the only
  source among the examples of conditional edges, conditional cycles and
  rule 8 (the test suite's `reified` and `simplify` modes are the others in the
  tree).
  `--file` reads ProGen/max `.sch` instances.
- **For CPU benchmarking: `difference_chain --mode fixpoint -n 640
  --variant global --simplify off`** for the propagator (dense, `|E| ≫ n`,
  propagation-bound, 1,283 recursions); the same with simplification on to
  measure the stage. For the conditional machinery, `rcpsp --size 12 --seed 2
  --machine-fraction 0.8 --machine difference --variant global`.
- **For proof benchmarking: `difference_chain --mode fixpoint -n 160
  --variant global`** (5,478 lines, 0.43 s to verify) for pushes, and the
  `rcpsp --machine difference` instance above for conditional cycles (30,683
  lines, 1.04 s). `rcpsp --size 22 --seed 4 --max-lag-density 0.25` is 38.6 MB
  and 77 s to verify, almost all of it the resources'.
- **Never run uncapped**: `difference_chain --variant decomposed` at large `n`
  in `refute` mode with `--prove` (its proof grows with `n²k`), and the crawl
  shape above at large width.

### CPU performance

*Measured 2026-10-19 at `86caad24`, Release, fataepyc-09 (AMD EPYC, 192 cores,
otherwise idle for this core), `taskset -c 50`, serial,
`GLIBC_TUNABLES=glibc.malloc.mmap_threshold=33554432:glibc.malloc.trim_threshold=4294967295`,
median of three; `instructions:u` from `perf stat`. `difference_chain` at
`k = 2`, `--order unlucky`.*

| Benchmark | Variant | Recursions | Propagations | Time (s) | Instructions:u |
|---|---|---:|---:|---:|---:|
| chain fixpoint `n = 160` | decomposed | 163 | 2,126,002 | 0.1623 | 1.256 G |
| | global | 323 | 327 | 0.0241 | 0.192 G |
| | global, simplify off | 323 | 327 | **0.0097** | 0.060 G |
| | global, from scratch, simplify off | 323 | 327 | 0.0458 | 0.417 G |
| chain fixpoint `n = 640` | decomposed | 643 | 132,305,602 | 9.619 | 69.29 G |
| | global | 1,283 | 1,287 | 0.930 | 8.384 G |
| | global, simplify off | 1,283 | 1,287 | **0.166** | 0.741 G |
| | global, from scratch, simplify off | 1,283 | 1,287 | 2.208 | 22.80 G |
| | global, from scratch | 1,283 | 1,287 | 2.965 | 30.36 G |
| chain refute `n = 160` | decomposed | 1 | 4,139,782 | 0.3029 | 2.328 G |
| | global | 1 | 1 | 0.0195 | 0.196 G |
| | global, simplify off | 1 | 1 | **0.0138** | 0.140 G |
| chain refute `n = 640` | global | 1 | 1 | 1.044 | 10.82 G |
| | global, simplify off | 1 | 1 | **0.691** | 7.367 G |
| `rcpsp --size 22 --seed 4 --max-lag-density 0.25` | decomposed | 9,572 | 96,670 | 0.1259 | 0.926 G |
| | global | 9,572 | 28,625 | **0.0972** | 0.713 G |
| | global, simplify off | 9,572 | 28,625 | 0.0976 | 0.716 G |
| | global, from scratch | 9,572 | 29,106 | 0.1172 | 0.807 G |
| `rcpsp --size 12 --seed 2 --machine-fraction 0.8 --machine difference` | decomposed | **277** | 13,638 | **0.0060** | 0.044 G |
| | global | 1,667 | 3,216 | 0.0134 | 0.095 G |
| | global, simplify off | 2,091 | 3,640 | 0.0174 | 0.123 G |
| | global, from scratch | 1,667 | 3,216 | 0.0143 | 0.098 G |
| `rcpsp --size 9 --machine-fraction 0.9 --max-lag-density 0.4 --max-lag-slack 0 --machine difference --seed 6` | decomposed | 1,525 | 78,399 | 0.0274 | 0.189 G |
| | global | **0** | 0 | **0.0002** | 0.006 G |
| | global, simplify off | 4,149 | 6,048 | 0.0317 | 0.229 G |

What to read out of it:

- **The propagator is a large win where the paper says it is.** On Example 8
  at `n = 640` the incremental route without simplification is 58× the
  decomposition's wall time and 93× fewer instructions, at a different search
  shape: `recursions` is not comparable across the global and decomposed chain
  rows, plausibly because the default `dom_then_deg` sees different variable
  degrees (one global propagator against one per edge; not tested). The
  rcpsp rows use a static order; the size-22 rows agree on recursions, and the
  machine rows differ because the propagation does. Incremental against from
  scratch, both with simplification off, at equal recursions and
  propagations: 13× at `n = 640`.
- **Root simplification is most of the cost on a dense unconditional system**
  and buys nothing there: 0.762 s of the 0.930 s at `n = 640` (82%), dropping
  0.3% of the edges, and 34% of the refutation's time. On the tight RCPSP/max
  instance it is the whole answer, a root refutation in 0.2 ms against 1,525
  and 4,149 nodes without it.
- **Without a condition inference during search, conditional edges cost
  search.** On the pairwise disjunctive machine the global model takes 6× the
  decomposition's nodes (1,667 against 277). The decomposition posts each
  conditional edge as a `LinearGreaterThanEqualIf` (`rcpsp.cc:889`); one whose
  edge the bounds falsify fixes its own Boolean, and this propagator never
  does. That is the bounds-side check of the paper's §5.4 (an implied edge
  that the bounds falsify propagates `b ↦ ⊥`), which the paper's final
  configuration keeps; `IncImp`, the graph-path implication, is a separate and
  costlier check that it leaves off. Simplification recovers a fifth of the
  gap. Propagations are the wrong metric there. The from-scratch route costs
  4% more instructions than the incremental one with simplification on (98.4 M
  against 94.6 M) and 3% more with it off (127.3 M against 123.4 M, re-taken
  2026-10-20, median of three). `difference-logic.md` measured it 5–8% faster
  with simplification off, at an older commit, on three instances; on this
  one, the only one re-taken, the ordering has reversed.
- **Not exercised by these benchmarks**: rules 4 to 7 (the static and
  degenerate shapes), holey domains, views.

Figures **measured elsewhere** — `dev_docs/difference-logic.md`'s tables, on
a different machine and older commits — are not repeated here and must not be
put beside these. Its `n = 640` incremental figure is 0.057 s against 0.166 s
here. The decomposed-to-incremental ratio roughly agrees (64× there, 58×
here); the from-scratch-to-incremental ratio does not (5.7× there, 13.3×
here).

**Cross-solver comparison: `Not measured.`** (#868.) Example 8 is easy to give
any solver as a MiniZinc model, but the natural comparison is with the
decomposition, which the table has; a Gecode or Choco row would compare their
per-constraint propagation, which is the decomposed row's job.

### Proof performance

*Same build and machine, `taskset -c 51`, VeriPB 3.0.2 with
`--force-checked-deletion`; `GCS_ASSERTION_LEVEL` for the levels. "Ours" counts
this family's `pol`, `rup` and `del` lines. VeriPB times are single runs.*

| Instance | Variant | Level | `.pbp` lines | bytes | ours | VeriPB (s) | Verdict |
|---|---|---|---:|---:|---:|---:|---|
| chain refute `n = 40` | global | `Off` | 12 | 796 | 3 | 0.022 | `VERIFIED UNSATISFIABLE` |
| | | `Inferences` | 10 | 183 | — | 0.018 | `UNDER ASSERTIONS UNSATISFIABLE` |
| | decomposed | `Off` | 68,430 | 2,852,628 | 0 | 2.29 | `VERIFIED UNSATISFIABLE` |
| chain refute `n = 160` | global | `Off` | 12 | 2,639 | 3 | 0.051 | `VERIFIED UNSATISFIABLE` |
| chain fixpoint `n = 40` | global | `Off` | 1,398 | 82,962 | 243 | 0.033 | `VERIFIED SATISFIABLE` |
| | | `Inferences` | 89 | 12,752 | — | 0.018 | `UNDER ASSERTIONS SATISFIABLE` |
| | decomposed | `Off` | 22,929 | 1,163,965 | 0 | 0.69 | `VERIFIED SATISFIABLE` |
| chain fixpoint `n = 160` | global | `Off` | 5,478 | 389,247 | 963 | 0.43 | `VERIFIED SATISFIABLE` |
| | | `Inferences` | 329 | 61,656 | — | 0.047 | `UNDER ASSERTIONS SATISFIABLE` |
| rcpsp `--machine difference`, size 12 seed 2 | global | `Off` | 30,683 | 2,369,646 | 9,612 | 1.04 | `VERIFIED BOUNDS 21 <= obj <= 21` |
| | | `Inferences` | 9,579 | 978,865 | — | 0.041 | `UNDER ASSERTIONS BOUNDS 21 <= obj <= 21` |
| | decomposed | `Off` | 25,283 | 1,690,434 | 0 | 0.71 | `VERIFIED BOUNDS 21 <= obj <= 21` |
| rcpsp tight, seed 6 | global | `Off` | 24 | 676 | 18 | 0.018 | `VERIFIED BOUNDS INF <= obj <= INF` |
| | global, simplify off | `Off` | 39,932 | 3,268,650 | 19,596 | 0.51 | `VERIFIED BOUNDS INF <= obj <= INF` |
| rcpsp size 22 seed 4 | global | `Off` | 256,873 | 38,636,429 | 43,413 | 77.3 | `VERIFIED BOUNDS 32 <= obj <= 32` |
| | | `Inferences` | 63,461 | 8,195,936 | — | 0.23 | `UNDER ASSERTIONS BOUNDS 32 <= obj <= 32` |

- **Own against shared, measured.** This family writes exactly three lines
  per inference; everything else is the literal layer, the search and the
  other constraints. On Example 8's fixpoint, `n` from 40 to 160, the family
  is `3·(2n + 1)` lines (243, then 963) in a whole proof of about 17 lines per
  push (1,398, then 5,478): the rest writes about 4.7 lines for every line of
  ours (1,155 against 243, 4,515 against 963). At `n = 40` the largest part is
  the solution block (the `solx` line and the literal definitions and `pol`
  lines it needs, 825 lines, 59% of the proof), and the pushed literals'
  definitions are 328 lines; at `n = 160` the solution block is 3,225 of
  5,478. On the refutation the family's three lines are the proof.
- **Verification time is not mostly this family's**: 0.43 s against a
  0.087 s solve with proof logging on the chain (5×; 0.024 s without proofs),
  but 77 s against 0.44 s with proof logging on the size-22 RCPSP/max (175×;
  0.097 s without), where 17% of the lines are ours. The rest was not
  attributed by constraint: 62,081 of its 80,047 `pol` lines cite no label,
  and 32.6 of the 38.6 MB is `rup` lines.
- **Assertions carrying this family's hint: none**, because there is no hint.
  At `Inferences` the family's assertions are the unannotated ones (on these
  generated single-mode instances the `global` variants post no linear
  inequality, the other unhinted family — `rcpsp.cc:920-926` posts one only for
  variable durations or a `.sch` source — and every unannotated line has one of
  this family's shapes): 81 of the 83 assertions on the chain fixpoint at
  `n = 40` are this family's pushes (of the other two, one is the unhinted
  `LinearGreaterThanEqual` bump, `a 1 i[y[0]][ge40] >= 1;`, and one the
  solution block); 3,204 of 5,030 on the conditional RCPSP, by shape 1,182
  unconditional pushes, 1,589 conditional ones, 425 conditional cycles of two
  to five conditions, and 8 root fixes; 14,471 of 36,428 on the size-22
  instance, all unconditional pushes.
- **`Links` is rejected** at the solution line on the satisfiable rows, whose
  variables are declared as ranges wider than `{0, 1}`, on the decomposed model
  too: #1210, which value-list declarations avoid. `Off` and `Inferences` were
  checked on every row.

## Status, gaps, and next steps

### Proof-logging gaps

**None in the proof direction.** Every inference is justified at `Off`, there
is no `a` oracle and no `AssertRatherThanJustifying`, and the propagator's
strength does not change with proofs on (no budget, no proof-only decline;
search shapes checked equal above). The OPB says what the model says and no
more.

Two things that are gaps for the external justifier rather than for VeriPB:
**no assertion carries a hint**, so rules 1, 2, 3 and 8 are `search`; and a
range-literal condition cannot be written into the model at all with proofs
on (#1225, with #310 as the encoding fix), which is a model-writing gap shared
with `comparison`.

### Known limitations

- **A condition is never inferred during search.** A model whose conditional
  edges are infeasible together is explored until a branch closes the cycle,
  and on a pairwise disjunctive machine that costs 6× the decomposition's
  nodes. Branch on the condition variables, and leave root simplification on;
  `examples/rcpsp` puts them first, and an unbranched condition can leave a
  "solution" that violates a resource.
- **Bounds only, on integer variables.** Interior values are never removed,
  and a holey domain is crawled one hole per call.
- **Neither MiniZinc nor XCSP3 posts this class** (only the C++ API and the
  `.scp` reader do), and neither can produce a half-reified edge, even
  through the presolver.
- **Weights near the edge of the range** throw `IntegerOverflow` on values the
  answer does not need, in the incremental route and root simplification
  (#1371) and in `difference_graph.cc`'s Bellman-Ford bounds and cycle sums
  (#1372). A chain of
  nine edges of weight `−max_bounded_value()` throws on every route except
  from scratch without simplification over the whole range, and on every
  route over `0..1`; a chain of eight with the redundant edge
  `x[0] − x[8] ≤ d`, `d ≥ 8`, throws whenever simplification is on; a negative cycle of nine such edges throws on every
    route. Through `--difference-logic` such models are `=====ERROR=====` where
  the model alone is `=====UNSATISFIABLE=====`. The shapes known are listed in
  the two issues, which do not claim to be complete. **This is deliberate**
  since #1371 and #1372 were closed: the initialiser and the propagator
  rethrow any `IntegerOverflow` saying it came from difference logic and why
  (`explaining_overflow` in `difference_graph.cc`), and
  `run_near_edge_shapes_test` checks that no route answers those shapes
  wrongly. Carrying every potential, distance and bound wide through the
  heaps and the simplification stage was judged not worth it for weights
  this close to `2^60`.
- **The `.scp` writer writes view operands the reader cannot read back**, and
  `cake_pb_cp` cannot check this family at all.
- **Root simplification can dominate a dense unconditional model**, at 82% of
  the solve on Example 8; `simplifying_at_root(false)` (or `--simplify off`)
  is the switch.

### Next steps

Ranked by value for cost.

1. (Declined: auditing `difference_incremental.cc`, `difference_simplify.cc`
   and `difference_graph.cc` to hold every potential, distance, reduced
   weight and Bellman-Ford bound in `WideSum`, which #1371 and #1372 asked
   for. They were closed with a clear `IntegerOverflow` instead, under the
   rule that a clean error is acceptable where wide arithmetic is not
   straightforward; see [Known limitations](#known-limitations). The issues
   keep the list of sites and shapes, should an application need it.)
2. **Give the assertions a hint.** A `hints::Difference` carrying the
   constraint id (and, for rules 3 and 8, the posted indices of the rows
   summed) would turn four `search` verdicts into `hinted`, and would let a
   justifier tell this family's pushes from a linear inequality's. Small in
   the code; it is the information Matthew's tool would otherwise search for.
   Not filed: hint sufficiency is settled against the justifier.
3. **Infer `¬cond` during search, in two steps.** First the paper's §5.4
   bounds check: an implied edge whose bounds already falsify it fixes its
   condition false. That is what the decomposition's `LinearLessThanEqualIf`s
   do, what the 6× in nodes on the conditional RCPSP measures, and what the
   paper's final configuration keeps; its proof is a rule-1-shaped `pol` (the
   edge row plus the two bound definitions). Then `IncImp`, rule 8's path
   check during search, which `difference-logic.md` argues needs no new proof
   shape and which the paper's configuration study, in a lazy-clause-generation
   solver, found not worth its cost. A measurement each, then a decision; not
   filed.
4. **Make root simplification cheaper where it cannot pay.** On a dense
   unconditional system (Example 8, 82% of the solve) the stage can infer
   nothing — rule 8 needs a candidate condition — and only drops redundant
   edges. A structural gate (skip Johnson's when no edge is conditional, or
   when no candidate exists after the dead-edge pass) would not be a tuned
   budget, and would leave the conditional models, where the stage is the
   whole refutation, untouched. Measure what dropping redundant edges buys
   later in search first; not filed. `difference_logic.md` defers this item
   here.
5. **Derive the condition triggers from the operator**: `on_change` only for
   `≠` and `not_in_range`, and `on_bounds` otherwise. That is finer than the
   shared `add_trigger_for()` (`gcs/constraints/innards/triggers.cc:8-26`),
   which maps `=` and `in_range` to `on_change` as well, because for a
   reified dispatcher a hole can *disentail* an `=`
   ([`comparison.md`](comparison.md)); here disentailment only removes an arc,
   so it never needs a wake. Trivial; stops over-reporting hole sensitivity for
   non-Boolean conditions and saves interior wakes. Not worth an issue on its
   own.
6. **A cake keyword for `difference`**, and then chain cases. Upstream.
7. **#1072**, the predecessor bound already at the top. Low priority, as the
   issue says.
8. **#594**, zero-weight-cycle unification. The counters say it would fire on
   tight RCPSP/max; the model-side cost is recorded there.
9. **#1384 and #1385**, both small and both cost only. A membership mark per
   condition (or a sort, where order does not matter) for the two
   deduplication loops; and for the nodes simplification leaves isolated,
   either compacting them out, which also drops their `on_bounds` triggers
   (`difference_graph.cc:1165-1166`), or skipping them in the seeding and the
   `Vl` scan, which leaves the triggers and their wakes; either way keeping
   their conditional static bounds.

## Prior art

- **The graph formulation and its two facts** (a system is satisfiable iff its
  graph has no negative cycle; it entails `x − y ≤ d` iff the shortest path
  `x ⇝ y` weighs at most `d`) are Shostak's ("Deciding linear inequalities by
  computing loop residues", JACM 28(4), 1981) and Dechter, Meiri and Pearl's
  simple temporal problem ("Temporal constraint networks", *Artificial
  Intelligence* 49(1), 1991). Bellman-Ford and Johnson's reweighting are the
  textbook algorithms.
- **The propagator** is Kletzander, Dekker, Schutt and Stuckey, *Global
  Difference Constraint Propagation for Constraint Programming*
  (arXiv preprint 2607.20022, July 2026), the extended version of Feydy,
  Schutt and Stuckey, "Global difference constraint propagation for finite
  domain solvers" (PPDP 2008, pp. 226–235): `IncSat` (their Algorithm 1, from
  Cotton and Maler, "Fast and Flexible Difference Constraint Propagation for
  DPLL(T)", SAT 2006, LNCS 4121, and identical to Ramalingam et al., 1999),
  `IncLB`/`IncUB` (Algorithm 3), the root simplification (Algorithm 4), and
  the per-edge explanations (§4.3). Its never-trailed potential is the paper's
  §4.1 remark after Wang, Ivančić, Ganai and Gupta (LPAR 2005, LNCS 3835). The
  incremental difference-logic machinery of SMT solvers (Cotton and Maler;
  the DPLL(T) of Nieuwenhuis, Oliveras and Tinelli) is the same lineage.
- **This solver's adaptation**: the propagator for holey domains (the `Do`
  array records the bound propagated from, not the snapped one, and the
  propagator re-wakes itself); exact restoration of `Do` through an undo trail
  under one trailed number (the paper specifies the untrailed potential and
  the trailed edge sets, §4.1 and §5.1, but not how `Do` is restored); and,
  as transcription fixes rather than adaptations, the activation seeding that
  the paper gives in §4.2 and its §5.4 omits, and two corrections to its
  Algorithm 3's pseudocode ([`difference-logic.md`](../difference-logic.md),
  "Defects in the paper's pseudocode").
- **The certification: the idea is published, this instantiation is not, as
  far as this audit can find.** The paper does not mention proof logging.
  McIlree's thesis (2026) has no difference-logic procedure — a single push
  is its JP 3.15 on a two-term row — but its §8.2.2 ("Further General
  Justification Procedures", under "Justifications via Linear Programming")
  proposes exactly this kind of certificate in general: for a constraint with
  a totally unimodular linearisation, any implied linear inequality is a
  single linear combination of PB encoding constraints. Its example is
  `GlobalCardinality`, and it extends the point to network-flow constraints
  more broadly. That a negative cycle (and
  dually a feasible potential) certifies a difference system is classical
  too. What is new here is the instantiation: the negative-cycle and
  condition-fixing certificates as one `pol` over the model's own rows, the
  half-reified rows' big-M residuals left as a saturated PB constraint
  (equivalent to the clause when every coefficient, a condition's residuals
  summed, reaches the degree, and stronger otherwise) from which one RUP
  reads off the learned clause,
  views handled by canonicalisation and deview mode, and the root condition
  fixing certified the same way.

## Further reading

- [`difference-logic.md`](../difference-logic.md) — the long design note, and
  it stays: the graph and the two directions, the round bound and the
  totality of the cycle extraction, canonicalisation, both proof shapes with
  real output, half-reified edges and their triggers, the paper's pseudocode
  defects, root simplification and why it is an initialiser, the incremental
  algorithms with the `Do` invariants, the two oracles and the mutation table,
  and the presolver's half. Its measurements are from older commits and other
  machines.
- [`difference_logic.md`](../presolvers/difference_logic.md) — the
  presolver: what it lifts, from which classes, what it disables, its counters
  and entry points.
- [`view-proof-logging.md`](../view-proof-logging.md) — invariant 1 (why the
  rows are canonicalised) and invariant 3 (why a push needs a `pol`).
- [`justification-techniques.md`](../justification-techniques.md) — JP 3.15
  and Theorems 2.6, 2.7 and 2.9's `B ∈ {0, 1}` boundary, which a difference
  row is outside.
- `dev_docs/integer-ranges.md` (on main) — the range policy, and the
  documented nine-edge exception.
- [`optional-interior-pruning.md`](../optional-interior-pruning.md) — what the
  *Holes affect* column feeds.
- [`comparison.md`](comparison.md) and [`linear.md`](linear.md) — the
  per-edge spellings, and the presolver's donors.

## Developer commentary

The code's comments are unusually complete, and most of what a reader will get
wrong is answered at the site: the `Do` and backtracking argument over
`DifferencePropagatorMemory`, why the condition is not in the arc
(`difference_incremental.hh`), why the propagator is not idempotent, the
trigger choice, and the initialiser's placement.

Stale text found by this audit and its fact-check, recorded rather than fixed
here. #1389 and #1396 (both open, on main) correct the items marked so; the
rest still stand. Code comments first:

- `DifferenceSimplificationStats`'s brief ("filled in the first time the
  propagator runs", `difference_simplify.hh:15-16`) and
  `reporting_simplification_to`'s ("filled in during the first
  propagation", `difference_constraints.hh:161`) predate #659, which moved
  the stage into an initialiser. Corrected by #1396, open.
- `difference_constraints.cc:136-138` says the disallowed condition is handled
  "from the same row, so no initialiser is involved"; the root initialiser
  infers it (`difference_graph.cc:1274-1276`). Corrected by #1396, open.
- `difference_constraints.hh:62` calls the propagator "bounds consistent for
  the system as a whole", which is false once edges are half-reified (rule 1's
  Strength; corrected by #1396, open); `:72-75` call `IncImp` "deliberately
  not implemented", which rule 8 now is at the root (corrected by #1389, open);
  `difference_graph.hh:163-166` describes
  `install_difference_propagator` as running Bellman-Ford, where the default
  route is incremental Dijkstra (corrected by #1396, open).
- `difference_constraints.hh:173` and `difference_graph.cc:923` give the
  incremental route as `O(n log n + m)`, and `difference_simplify.hh:205`
  (and `difference-logic.md`, "The four sub-steps" and "This is `IncImp`")
  the simplification as `O(n² log n + nm)`: Fibonacci-heap bounds. The heaps
  are binary with lazy deletion, holding an entry per improving relaxation,
  so a Dijkstra is `O((n + m) log(n + m))` and a simplification round
  `O(n·m log(n + m))`; `log n` needs the parallel edges bounded by a
  polynomial in `n`. All corrected by #1389, open.
- The saturated sum "turns it into the clause" (`difference_graph.cc:527-531`,
  the cycle; `:330-332`, the root witness), "saturates into exactly the
  clause" (`difference_constraints.cc:216-219`), the root witness's
  "Emitted anyway so the derived line *is* the clause" (`:345-346`), and
  `difference-logic.md`, "The proof: one extra `saturate`, and that is all",
  which also says the `saturate` "makes the derived line *be* the clause".
  The line is equivalent to the clause only when every coefficient (a
  condition's residuals summed) reaches the degree, and literally the clause
  only when the degree is also 1
  ([negative-cycle](#rule-negative-cycle)). Corrected by #1389, open, along
  with the note's "The proof for condition fixing" and `IncImp` deferral
  item, which repeat it.
- The cycle comment's minimality claim (`difference_graph.cc:531-534`):
  "Every such condition therefore has to appear in the reason ... citing
  fewer would claim a contradiction the model does not entail". The reason
  is sufficient, not minimal, and in Codex's two-edge example each row alone
  entails its own condition false ([negative-cycle](#rule-negative-cycle),
  *Reason*). Corrected by #1389, open.
- The node-removal comment (`difference_graph.cc:405-409`: an isolated node
  "neither needs seeding nor counts towards the number of relaxation
  rounds"), `isolated_nodes_removed`'s brief ("dropped from the relaxation
  loop and from the round bound", `difference_simplify.hh:72-73`), and
  `difference-logic.md`, "The four sub-steps, and which are here", item 4:
  only the round bound changes; the nodes are still seeded, scanned and
  triggered (#1385). All three corrected by #1389, open.
- The two arithmetic checks called "O(cycle)" (`difference_graph.cc:289-292`,
  `:549-552`) share their loop with the condition deduplication, `O(k·c)`
  (#1384). Corrected by #1389, open.
- The activation-seeding recipe is attributed to the paper's "section 4.4"
  (`difference_incremental.hh:231`, `difference_incremental.cc:204`,
  `difference_graph.cc:950-951`, `difference_constraints_test.cc:1041`, and
  `difference-logic.md`, "Defects in the paper's pseudocode" and "Arc
  activation"); it is in §4.2, and §4.4 is "Possible Variations and
  Optimizations". All corrected by #1396, open.
- "Ten of the nineteen wraps negate" (`gcs/CMakeLists.txt:985`,
  `difference_constraints_test.cc:206`, and `difference-logic.md`, "The
  view-wrap sweep"): nine do. All corrected by #1396, open.
- The comment that an aliased edge "render[s] as a row whose left hand side is
  zero" (`difference_constraints.cc:209-213`, and the note) is true of the
  row's value; it is written with both copies of the bits. Corrected by
  #1396, open.

Then `difference-logic.md`, in sections as they stand on main (the copy beside
this document in the stack predates some of them):

- "The termination and extraction arguments still hold": "This version
  recomputes from scratch every wake anyway" predates incremental
  propagation. "RCPSP/max: the benchmark this was built for" points to a
  non-incrementality caveat under "Deliberately deferred" that is no longer
  there. "Rounds" describes `n` rounds, where the code now uses the live-node
  count after simplification and an early limit. All three corrected by
  #1396, open.
- "Switching that mechanism on: `--machine=difference`" and "RCPSP/max: the
  headline reproduces" put the conditional models' extra nodes down to
  `IncImp`'s absence, and "This is `IncImp`, restricted to the root" repeats
  it ("`IncImp`'s absence shows up in gcs as a *search-tree* cost, since
  `--variant=global` has no donors to infer `!cond` from bounds"). What the
  decomposition has and this propagator lacks is the paper's §5.4 bounds
  check (an implied edge the bounds falsify fixes its condition false), which
  the paper's final configuration keeps; `IncImp` is the separate path check
  it leaves off. `difference_constraints.hh:28-32` ("That is the paper's
  `IncImp` ... so it is deliberately absent", of a condition never fixed from
  the graph) has the same framing. All corrected by #1389, open.
- "Extreme weights" says the early-exit limits stop a negative cycle relaxed
  round after round from running out of range; true for the short cycle it
  tests, not for a cycle of nine heavy edges (#1371, #1372).
- "Extreme weights" calls nine heavy edges a genuine path sum past `Integer`,
  and "The three moving parts" says nothing has come close to the potential's
  drift. Both are qualified by #1371 and #1372: from scratch without
  simplification solves the nine-edge chain over the full range, and the
  incremental route throws at eight. The same nine-edge example is in
  `dev_docs/integer-ranges.md` (on main) as a sum the answer "genuinely
  needs", which it does not.
- "What this does not fix" gives the incremental route's per-wake cost as
  `O(n + |Vl| log n + reachable arcs)`, a decrease-key bound; with the lazy
  binary heap each pass is `O(n + (|Vl| + R) log(n + R))` for `R` arcs
  reached ([Mutable state and incrementality](#mutable-state-and-incrementality)).
  Corrected by #1389, open.
