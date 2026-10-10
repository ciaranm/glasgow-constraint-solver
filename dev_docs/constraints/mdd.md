# `MDD`: a sequence of variables spells a path through a layered decision diagram

> **Maturity** production ·
> **Audited** 2026-10-10 at `86caad24` ·
> **Open issues** filed by this audit: #1329 (a zero-variable diagram with an
> empty accepting list reports solutions; filed with `RegularBacchus`'s twin),
> #1333 (the constructor does not check node indices; with `Regular`'s), #1336
> (six kinds of MiniZinc shape the binding gets wrong), #1338 (the graph is
> deep-copied at every search node; with `Regular`'s), #1339 (a wide declared
> domain leaves one empty map entry per value for the rest of the search; with
> `Regular`'s). Commented on: #1070 (the always-true declared-bound literals in
> the whole-scope reason). Already open and touching
> this family: #842 (the OPB alphabet includes every domain value), #846 (its
> tracker), #833 (the large-domain policy), #200 (one layered-graph framework
> for `Regular`, `MDD`, `Knapsack` and `BinPacking`), #653 (`CostMDD`), #868
> (cross-solver comparisons; this document gives one, by hand), #1006
> (MiniZinc differential lanes, which scopes a non-1-based `x` as undefined).
> Tracked under #871.

`MDD(vars, layer_transitions, nodes_per_layer, accepting_terminals)` holds when
reading `vars[0], vars[1], …` from the root, node 0 of layer 0, follows a
transition at every step and ends on an accepting node of the last layer. It is
the constraint MiniZinc's `mdd` and XCSP3's `mdd` reach, it has one propagator,
an incremental generalised arc consistent algorithm over the diagram with in-
and out-degree counts, and one proof strategy,
`decision-diagram-proof-strategies.md`'s "upfront": per-value backward chains
written once at the root, then a lemma
`¬state[i][q]` for each node as it dies, then each removed value by RUP. The
encoding is Matthew McIlree's thesis's for `Regular`, adapted to per-layer node
sets as his Section 5.2.1 describes. `mdd.cc` carries its own copy of
`Regular`'s graph code; nothing is shared.

Four things to know before touching it.

- **It is generalised arc consistent on distinct variables, views included, and
  its proofs verify.** No failure at any of 73,723 search nodes of 30,000
  random diagrams over distinct variables, and 8,579 of 9,000 proofs are
  accepted, each at the one level it was run at (6,600 at `Off`, 800 at each
  assertion level); the 421 others are the first finding.
- **A diagram over no variables with an empty accepting list reports
  solutions** (#1329). Nothing propagates, since the propagator only removes
  values. VeriPB rejects the proof. Only the C++ API and the `.scp` reader can
  post it; MiniZinc's binding throws on the same shape instead (#1336).
- **It is 75 to 94 times Gecode's instructions at equal node and solution
  counts** (#1338). The graph is a nest of hash containers held as
  backtrackable state, and
  `State::new_epoch` deep-copies every one of them at every search node. A
  nonogram of 25 by 25 takes 9.1 s against Gecode's 0.067 s. This is the
  defect `regular.md` records for `Regular`, in a separate copy of the code.
- **Everything is per value of the declared domain.** `prepare()` puts every
  declared value into a `std::set`, proofs or not; the OPB has a row per node
  and value of each variable's declared domain (#842); the root removes
  out-of-alphabet values one at a time; and two lookups leave one empty map
  entry per declared value in the graph for the rest of the search (#1339):
  twelve variables over `0..10⁵` with a 0/1 diagram take 66.5 s where `0..1`
  takes 0.023 s, with the same numbers of nodes and solutions.

## What it is

### Semantics

`vars` has `n` entries; the diagram has `n + 1` layers, with
`nodes_per_layer[i]` nodes in layer `i`, and `nodes_per_layer[0]` must be 1.
`layer_transitions[i][q]` maps a value to a node of layer `i + 1`, so the
diagram is **deterministic** by construction: one target per node and value.
An assignment is accepted when, starting at node 0 of layer 0, every
`vars[i]`'s value has a transition from the current node, and the node reached
after `vars[n − 1]` is in `accepting_terminals`. Node 0 of layer 0 is the root;
there is no separate "true" node, and any subset of the last layer can accept.

The constructor (`mdd.cc:438–454`) checks that `nodes_per_layer` has `n + 1`
entries and starts with 1, that `layer_transitions` has `n` layers and each has
at least `nodes_per_layer[i]` node maps (extra maps are never read as nodes,
though their keys still enter the OPB alphabet, `mdd.cc:472–474`), and every
transition value against `±(2⁶⁰ − 1)` (`require_bounded`, since #1215). It does
**not** check targets or terminals against the node counts (#1333; see
[Robustness and limits](#robustness-and-limits)).

- **No variables:** `nodes_per_layer = {1}`, and the empty sequence is accepted
  exactly when 0 is accepting. With node indices in range that means an empty
  accepting list is unsatisfiable, and GCS reports solutions for it (#1329);
  an out-of-range terminal gives the same wrong answer with proofs off and
  undefined behaviour with proofs on, an out-of-range `flags[n][f]` (an
  exception in the probe; #1329 and #1333).
- **No accepting terminals**, or none reachable: unsatisfiable, found at the
  root when `n ≥ 1`.
- **A transition to `-1`** is read as no transition, because `find_transition`
  (`mdd.cc:56–62`) returns `-1` for a missing key. Undocumented, and harmless.
- **A repeated variable** is accepted, and the diagram reads each position
  separately; see [Robustness and limits](#robustness-and-limits) for what it
  costs in strength.
- **Constants** are ordinary operands.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `MDD` | `fzn_mdd` ✓ via `glasgow_mdd`[^mznmdd] | `mdd` ✓[^xcspmdd] | ?[^cpmpy] | ✓ `mdd` | one class |
| — | `mdd_nondet`, `cost_mdd`, `fzn_mdd_reif`: `decompose`[^mzndec] | nondeterministic `mdd`: `unsupported` | ? | `n/a` | no GCS class: a non-deterministic, cost or reified diagram |

[^mznmdd]: `minizinc/mznlib/fzn_mdd.mzn` redefines `fzn_mdd` as
    `glasgow_mdd`, and `fzn_glasgow.cc:1119–1184` maps MiniZinc's numbering
    onto layers: node `n` sits in layer `level[n] − 1`, the root (node 1) is
    pinned at index 0 of layer 0, the true node `T` (node 0) joins layer `L`,
    and `T` is the only accepting terminal. Set labels are expanded one value at
    a time (`fzn_glasgow.cc:531–540`, `1175–1180`). A non-deterministic edge set
    is refused with a pointer to `mdd_nondet`. Six kinds of shape that pass
    the standard library's assertions go wrong (#1336): an empty `x`, a
    second node at level 1, a node at a level outside `1..L+1` with or without
    edges (`level` 9, 5 or 0; with edges, MiniZinc warns "undefined result
    becomes false in Boolean context", and the decomposition makes them
    false), and `N = 0` with an empty `x` end `=====ERROR=====`, where Gecode
    solves them. Both `N = 0` shapes, with an empty `x` or not, first read
    `layer_of[1]` and write `idx_in_layer[1]` past the end of one-element
    vectors (`fzn_glasgow.cc:1141`, `1149`); with a non-empty `x` the Release
    build then happens to answer `=====UNSATISFIABLE=====`.

[^xcspmdd]: `buildConstraintMDD` (`xcsp_glasgow_constraint_solver.cc:463–559`)
    finds the root as the unique source, assigns layers by breadth-first
    search, and makes **every** node at depth `n` accepting. It reports
    `s UNSUPPORTED` for a non-deterministic transition set, an empty one, more
    than one source or none, a node at two depths, a path longer than the list,
    and a diagram whose paths are
    all shorter than the list (which is unsatisfiable rather than unsupported,
    and which ACE 2.6 answers `UNSATISFIABLE`).

[^mzndec]: These fall through to the standard library: `mdd_nondet` and
    `cost_mdd` to their own decompositions, and a reified or half-reified `mdd`
    to `fzn_mdd_reif`'s. `reif.mzn` in this audit's harness agrees with Gecode
    on all 27 assignments.

[^cpmpy]: `?` because CPMpy's own handling of `mdd` was not examined (it is
    not installed on the audit machine). What it would call is `gcspy`, which
    binds nothing in this family, so any route through it would be a
    `frontend gap`.

**Front-end differential.** Every route was compared against a reference
solver (Gecode for MiniZinc, ACE for XCSP3) and a brute-force oracle, with
every status marker classified so that `ERROR` and `UNKNOWN` never count as
agreement (`tmp/fd-dd/mdd/frontends/`, at
`86caad24`):

- **MiniZinc**, 2.9.7 and 2.10.1, both identical, against Gecode 6.3.0 and
  6.4.0 (which use the standard decomposition, since Gecode has no `mdd`) and
  the oracle: 15 hand-written models (`frontends/mzn/`) and 800 random ones
  (`genmzn.py` seed 1, `genmzn_sat.py` seed 2; scrambled node numbering, nodes
  at level `L + 1` other than `T`, set labels with gaps, empty labels, labels
  outside the domains, repeated and constant entries in `x`, holey domains).
  The random 800 all agree; the only reported differences are six all-constant
  `x` lists, where the oracle writes the one empty solution as an empty line and
  the reader drops it. Of the hand-written ones, `empty_x`, `extra_level1` and
  `n_zero` are in #1336, which the two fact-check rounds extended with
  `iso_level9`, `iso_level0`, `n_zero_empty`, `lvl0_edge`, `lvl0_edge2` and
  `lvl5_edge`, rerun here on both versions against Gecode and an oracle
  (`frontends/mzn_round2_shapes.txt`; the extra nodes are on no root path, so
  each oracle is the reference example's three words, or unsatisfiable for
  `N = 0`). `idx0`,
  an `x` indexed `0..2`, is a shape #1006 scopes as undefined: the standard
  decomposition (`std/fzn_mdd.mzn`) reads `x[level[from[e]]]`, so Gecode says
  `UNSATISFIABLE`, while `fzn-glasgow` reads `x` by position, as the oracle
  does; `std/mdd.mzn`'s documentation never says how `x` is indexed.
- **XCSP3**, against ACE 2.6 and the oracle: 11 hand-written instances
  (`frontends/xcsp/`) and 208 random ones (`genxcsp.py` seed 6). GCS agrees
  with the oracle on all 208. ACE agrees on the 142 it accepts and throws a
  `NullPointerException` on the other 66: ACE 2.6 builds the diagram in the
  order the transitions are listed and needs each source node to exist already
  (`MDD.java` carries a TODO saying so), and the generator shuffles the
  transitions after the first. On the hand-written set ACE also errors on two
  sinks, a dead end, transitions listed out of layer order, values outside the
  domains and a path longer than the list, and on a non-deterministic diagram,
  which GCS reports
  unsupported, ACE loses one of the two solutions.
- **`.scp`**: the probe below writes a `.scp` with every proof, and
  `glasgow_scp_solver --all` on it finds the expected number of solutions in
  every one of 530 plain, aliased and larger cases. With views, the reader
  cannot parse the writer's view terms (`expected an atom, found a list`), which
  is the reader's known limitation, recorded in `path.md` and `subgraph.md`.
- **CPMpy, `gcspy`:** no binding.

### Options

`None.` No consistency tag, and no proof strategy setter: the class header
explains why the per-call strategy was not carried over from #205
(`mdd.hh:43–55`), and `decision-diagram-proof-strategies.md` gives the
measurement it rests on.

### Variable kinds and views

Plain variables, constants, and views of either sign. The propagator reads
domains through `State` only, so a view is an ordinary operand. The proof
handles views: the forward chains name each operand's own equality literal, and
the random sweep's `view` and `bigview` shapes (`x + c` and `−x` at random
positions) have every proof accepted at the level it was run at, apart from
#1329's zero-variable cases.

### Reification

None. MiniZinc's `mdd_reif` decomposes through the standard library (see the
coverage table). A reified form would want the accepting row and the
exactly-one rows half-reified on the condition, as `Regular`'s would.

### Relation to other families

- **Decomposes into it:** nothing in the solver. MiniZinc's `mdd` and XCSP3's
  `mdd` reach it directly.
- **Child constraints:** none.
- **Shares code:** nothing. `mdd.cc` has its own `MDDGraph`, `DeadCache`,
  `decrement_outdeg`, `decrement_indeg` and `emit_dead_state`, which are
  copies of [`regular.md`](regular.md)'s graph code with layer-dependent node
  sets. #200 proposes one framework for both. Its hint, `hints::MDD`, is its
  own.
- **Presolvers:** none reads it.
- **The family list's question:** `Regular` is the special case in which every
  layer shares one node set and one transition function, and the thesis treats
  `MDD` as `Regular`'s generalisation. They stay separate documents because they
  are separate classes with separate copies of the code, and `Regular` has three
  propagators, a regex front end and a canonical run that `MDD` has none of.
  `decision-diagram-proof-strategies.md` stays the shared note for `Regular`,
  `MDD`, `Knapsack` and `BinPacking`; this document describes only `MDD`'s use
  of it.

## The proof model

### OPB encoding

With `N_i = nodes_per_layer[i]`, and `A_i` the layer's **alphabet**, the union
of layer `i`'s transition keys and `vars[i]`'s declared domain
(`mdd.cc:470–477`):

```
state[i][q] for i = 0..n, q < N_i              proof flags mddnode<i>is<q>
for i = 0..n:          Σ_q state[i][q] = 1                       (two rows)
                       state[0][0] ≥ 1
                       Σ_{f ∈ accepting} state[n][f] ≥ 1
for i < n, q < N_i, v ∈ A_i:
  if T_i(q, v) = q':   ¬state[i][q] ∨ vars[i] ≠ v ∨ state[i+1][q']
  otherwise:           ¬state[i][q] ∨ vars[i] ≠ v
```

This is the thesis's Encoding Procedure 5.1 for `Regular`, with the states of
each layer the diagram's nodes, as his Section 5.2.1 says to adapt it; his
disallowed transitions range over the whole alphabet, and these over `A_i`.

**It is definitional.** The rows say that exactly one node per layer is on the
path, that the path starts at the root, ends on an accepting node and moves only
along transitions labelled by the variable's value; nothing else. The flags
are determined by unit propagation on a solution, which `solx` relies on: the
root row sets `state[0][0]`, each forward chain with its variable's value sets
the next layer's node, and the at-most-one half of the exactly-one clears the
rest. That is why `Regular`'s non-deterministic failure above `Off` (#1332) cannot
happen here: a deterministic diagram leaves no flag
unassigned.

**Size**, from the emission code (`mdd.cc:482–519`):

- **rows:** `2(n + 1) + 2 + Σ_{i<n} N_i · |A_i|`;
- **terms:** `2 Σ_{i≤n} N_i + 1 + |accepting|`, plus 3 per transition and 2
  per `(q, v)` with no transition, so `3·E + 2·(Σ N_i |A_i| − E)` for `E`
  transitions;
- plus the **definitions of the equality atoms** the chains name, two rows per
  value of `A_i` that lies inside `vars[i]`'s domain, and the order atoms they
  are built from, whose rows carry one term per bit. A 0/1 variable needs none,
  since its atoms are its bit.

So the encoding is **linear in the declared domain width**, per node: #842.
Measured with a two-node-wide diagram over three variables and two symbols
(`tmp/fd-dd/mdd/probes/opbsize.cc`, at `86caad24`), the own rows and terms
match the formulas exactly:

| declared domain | own rows | own terms | atom-definition rows | terms |
|---|---|---|---|---|
| `0..1` | 20 | 47 | 0 | 0 |
| `0..9` | 60 | 127 | 126 | 510 |
| `0..99` | 510 | 1,027 | 1,206 | 6,648 |
| `0..999` | 5,010 | 10,027 | 12,006 | 84,066 |

Width ten times larger gives ten times the rows, and the atom definitions
outweigh the constraint's own rows about 2.4 to 1 here; `large-domains.md`'s
`Regular` breakdown gives about 2.0 (1,218 to 600).

Two rows are redundant: the root row repeats the exactly-one of a one-node
layer, and the accepting row does the same when the last layer has one node,
which is MiniZinc's case. Harmless.

### Labels

`None` load-bearing. No row carries a label, and no justification cites a row
by ID; every derivation is RUP over the database.

### Cake conformity

None. `cake_pb_cp` has no `mdd` keyword (its binary names `table`, `regular`
and the `lex_` forms among others), so there is no chain case. The `.scp`
writer's `mdd` term is GCS's own grammar (`mdd.cc:557–595`: the variables,
`nodes_per_layer`, per layer and node a sorted `(symbol target)` list, and the
terminals), and `gcs/scp_reader.cc:914–947` reads it back; `scp_reader_test` checks
an enumeration and a write, read, write round trip.

### Proof-time state

- **At the root, at `Off` only.** The initialiser (`mdd.cc:531–540`) writes,
  at `ProofLevel::Top`: one **backward chain** per layer `i < n`, node `q'` of
  layer `i + 1` and value `v` of `vars[i]`'s domain at that moment,
  `¬state[i+1][q'] ∨ vars[i] ≠ v ∨ ⋁ {state[i][q] : T_i(q, v) = q'}`, the
  disjunction empty when nothing reaches `q'` on `v`; then `¬state[i][q]` for
  every **statically dead** node, forward-unreachable ones in ascending layer
  order and the rest descending (`mdd.cc:354–429`). It records the static dead
  set in the `DeadCache`.
- **During search, at `Off` only.** Each time a node dies, `¬state[i][q]` under
  the call's reason, at `ProofLevel::Current`, unless the `DeadCache` already
  has it on this branch (`emit_dead_state`, `mdd.cc:103–112`). The cache is
  backtrackable state, so a lemma is re-derived after a backtrack has deleted
  it. A later inference's RUP leans on lemmas written by **earlier calls on the
  same branch**, under weaker reasons, so a trimmed proof that keeps an
  inference has to keep the lemmas above it.
- **At every level:** one line per removed value, the `a` line above `Off`.
  Above `Off` nothing else is written: no chains, no lemmas.
- **Deleted:** the lemmas and the inferences of a level, by `del range` on
  backtrack. The Top scaffolding is never deleted.
  `decision-diagram-proof-strategies.md` explains why deleting it is not safe in
  general; for `MDD` nothing tries.
- **Naming:** the flags are `f[k][mddnode<i>is<q>]`, with `k` a counter over
  the whole model, so two `MDD`s' flags never collide but the name does not
  carry the constraint ID. An external tool finds a constraint's flags by the
  OPB comment `* constraint mdd <id>` that precedes its rows, or by rebuilding
  the diagram from the `.scp` entry with that ID.
- **In the OPB versus the proof:** every flag is in the OPB
  (`create_proof_flag` in `define_proof_model`); no auxiliary is introduced
  inside the proof.
- **Dangling vectors:** `Bridge::state_at_pos_flags` is empty when proofs are
  off, and nothing reads it then: `emit_dead_state` returns first.

## The implementation

### Initialisation and global data

`prepare()` (`mdd.cc:461–480`) allocates the two backtrackable slots, an empty
`MDDGraph` and a `DeadCache` with one set per layer, and computes the OPB
alphabets: one pass over each layer's maps, and one `std::set<Integer>` insert
per declared domain value (`mdd.cc:470–477`). It does this **with proofs off as
well**, where nothing reads the alphabet, and it is the largest per-value walk
at the root then: two variables of `0..3·10⁶` take 3.45 s to the root at
`86caad24` (`probes/widestale.cc 2 1 3000000 root`), and the fact-check's copy
of `mdd.cc` that skips the alphabet when there is no proof model takes 1.76 to
1.81 s on the same shape against 3.44 to 3.54 s for the shipped library, with
32.7% of cycles in the set's insert (`tmp/fd-dd/factcheck/mdd/core/wsalpha`,
`mddNoAlpha.cc`, two rounds); on twelve variables of `0..10⁵` it cuts the root
from 0.655 to 0.406 s, and on two of `0..10⁸` from 128.6 to 57.5 s.

The initialiser runs only at `AssertionLevel::Off`. It recomputes forward and
backward reachability on the domains at that moment (`compute_static_dead`,
`mdd.cc:289–335`: per layer, per domain value times per reachable node, twice),
then writes the scaffolding, recomputing forward reachability a third time
(`mdd.cc:391–401`). The backward chains loop over every node of layer
`i` for each node of layer `i + 1` and value (`mdd.cc:361–375`), so they cost
`Σ_i N_i · N_{i+1} · |D_i|` lookups: **quadratic in the layer width with proofs
on.** Ten layers of width `w` over four values, root only, at `86caad24`
(`probes/widelayer.cc`):

| w | root, proofs off | root, proofs on |
|---|---|---|
| 400 | 0.015 s | 0.079 s |
| 800 | 0.029 s | 0.21 s |
| 1,600 | 0.058 s | 0.69 s |
| 3,200 | 0.11 s | 2.64 s |

Indexing the parents per target and value once would make it linear in the
edges ([Next steps](#next-steps)). An initialiser installed earlier by another
constraint can narrow the domains first, and the static dead set is then taken
on the narrowed domains; that still verifies, since the narrowing is in the
proof at the root (`proofs/initorder.cc`, with `Abs`'s bound before and after,
both verify).

The graph itself is built lazily by the propagator's first call
(`initialise_graph`, `mdd.cc:114–193`), the forward pass per domain value per
reachable node, the backward pass per domain value per supporting node.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| initialiser | — | — | none (scaffolding) | `AssertionLevel::Off` with a logger; `SimpleDefinition` priority | — | — |
| `propagate_mdd` | `on_change`, every variable | derived: **every variable** | `unsupported-value` | always | never claims | never |

**`on_change` is the truthful trigger.** Support is per value: a hole in
`vars[i]` removes the edges labelled with it, which can kill a node and with it
another variable's value. So the derived declaration is right.

**Idempotence.** Not claimed. It holds in effect **on distinct variables**:
when a call ends, every value left has a live edge, and a re-run removes only
edges whose value has already gone, which kills nothing. With a repeated
variable it does not: a value removed at one position is a missing value at the
other on the next run, and that run can infer more (the fact-check's
`core/idem.cc`, `[y, y]`, infers `y ≠ 0` and then `y ≠ 1` in two calls). A
claim would still be safe, because `Propagators` ignores `EnableButIdempotent`
from a propagator whose trigger positions alias one variable
(`propagators.cc:111–129`, `777–780`). A scratch build returning it passes
`mdd_test` with the claim checker on at seeds 1, 2 and 3 (and, in the
fact-check, 24,000 random instances with repeats, views and constants), and
removes 26% of the propagator's calls on the nonogram below (34,241 to 25,196,
the same 1,427 recursions) but only 0.9% of the instructions, since the time is
in the copy (#1338). A [Next steps](#next-steps) item.

### Mutable state and incrementality

Two slots, both backtrackable through `add_constraint_state`, and so both
**deep-copied at every search node** by `State::new_epoch`:

- **`MDDGraph`** (`mdd.cc:64–91`): per layer, `nodes_supporting` (value to the
  set of nodes with a live edge on it), per node `out_edges` and `in_edges`
  (neighbour to the set of labels), `out_deg` and `in_deg`, and the live nodes
  per layer, as `unordered_map`, `unordered_set` and `set`. Built on the first
  call; maintained incrementally after that, by the degree cascade.
- **`DeadCache`**: per layer, the nodes whose `¬state` lemma is in the proof on
  this branch.

The content is incremental; the restoration is a full copy of every node-based
container, which is where the time goes (#1338, and
[CPU performance](#cpu-performance)). Recomputed per call: the whole-scope reason
(`mdd.cc:245`), and a walk over every value of every variable's domain
(`mdd.cc:277–282`), touched or not. #1339 is a third: two lookups that insert
an empty entry per root domain value during the first call, which every later
copy then carries.

### Interior values and optional pruning

**Offers.** `None.` The propagator is generalised arc consistent and has one
arm.

**Observes.** **Holes in every sequence variable.** The family reads values,
not bounds, so an `MDD` over some variables is a reason for another family's
interior pruning on them to stay on, and it says so through its `on_change`
triggers.

### Robustness and limits

**Unbounded domains.** Hopeless: the root walks every value of every domain
several times, and the OPB names every value (see [Interval
efficiency](#interval-efficiency)). The large-domain lane's row is `KnownTrip`.

**Negative values and zero.** Nothing depends on sign. The random MiniZinc and
XCSP3 models use values from −3 to 9, and `multilabel.mzn` negative labels.

**Degenerate shapes.**

- *No variables:* wrong when the accepting list is empty (#1329). The random
  sweep produced 1,618 such instances, and every wrong solution set in it was
  one.
- *A single variable, constants, all-fixed sequences:* covered by the sweep.
- ***A repeated variable keeps the solutions but loses generalised arc
  consistency.*** The diagram reads each position as if it were a separate
  variable. `[y, y]` over the words `01` and `10` with `y ∈ 0..1` is
  unsatisfiable, but the root removes nothing and the search needs three nodes
  to find that out (`probes/aliasex.cc`). In the sweep's `alias` shape, 196 of
  3,474 checked nodes fail generalised arc consistency, in 141 of 6,000
  instances, with every solution set right and every proof accepted.
- ***Node indices are not validated*** (#1333). A target beyond
  `nodes_per_layer[i+1]` crashes with proofs off (`SIGFPE` in one probe, a
  segmentation fault in another) and throws "can't find literals for flag" with
  proofs on; a target of `-2` does the same (a segmentation fault with proofs
  off); an accepting terminal
  out of range is ignored with proofs off and read past the end of a vector with
  proofs on; a negative node count throws `std::length_error`. A duplicated
  terminal is harmless.

**Overflow.** Nothing to guard: the family does no arithmetic on values or node
indices. Transition values are checked against `±(2⁶⁰ − 1)` (#1215), and a view
offset is refused outside the same range (#1214).

### Interval efficiency

**Not fine at any width: every part of this family is per value of a domain.**

1. **The propagation side.** Every site walks values, and none uses an interval
   primitive.
   - `prepare()`'s alphabet, one `std::set` insert per declared value of every
     variable (`mdd.cc:470–477`), with proofs off too, where nothing reads it
     (see [Initialisation](#initialisation-and-global-data)). Once.
   - `initialise_graph`'s forward pass, per value of each domain times each
     reachable node (`mdd.cc:122–143`); its backward pass, per value
     (`mdd.cc:166–181`). Once, on the first call.
   - The final loop of **every call**, per value of **every** variable's
     domain, changed or not (`mdd.cc:277–282`), removing unsupported values
     one `infer_not_equal` at a time. At the root that is one inference per
     out-of-alphabet value.
   - The main loop of every call, per key of each layer's `nodes_supporting`
     map (`mdd.cc:250–275`). Those keys should be the layer's alphabet, but the
     two `operator[]` lookups at `mdd.cc:167` and `279` add a key for every
     value of the root domains during the first call, and nothing erases them
     (later calls find the keys present, and every epoch copies them), so after
     a wide root the loop and the per-node copy stay
     proportional to the declared width **for the rest of the search**
     (#1339). Twelve variables of `0..W` with a 0/1 diagram, the same 989
     recursions every time (`probes/widestale.cc 12 4 W`, serial, median of
     three): 0.023 s at `W = 1`, 0.030 s at 10, 0.78 s at 1,000, 6.6 s at
     10,000 and 66.5 s at 10⁵ (one run), of which the root is 0.0057 s at 1,000
     and 0.66 s at 10⁵. With the two lookups changed to `find()`, 0.027 s at
     1,000 and 0.55 s at 10⁵.
   - `compute_static_dead` and the backward chains, per value, with proofs on.

   Each walk is a genuine support scan over values and nodes, which is what an
   extensional diagram is; the part that is not is the walk over values that no
   transition mentions, which the complement of a layer's keys would remove as
   at most `|keys| + 1` ranges.
2. **The reason side.** The reason is `generic_reason` over the whole scope,
   one literal per bound and one per run of missing values, found one step per
   run since #937. It is **materialised on every call, unguarded by
   `want_reasons()`** (`mdd.cc:245`), with proofs off as well, where nothing
   reads it.
3. **The proof side.** Per value throughout, with no width gate: one RUP per
   removed value; one backward chain per node and value; and in the OPB one row
   per node and declared value (#842), plus the atoms each names. The per-value
   proof is legitimate where a value is a real symbol; it is the out-of-alphabet
   values that need not be named one at a time.
4. **The audit lane.** One row, `MDD`, pinned `KnownTrip`
   (`large_domain_audit_test.cc:755–758`): two variables of `0..10⁹` with a
   one-symbol diagram, root only, proofs off. It varies the width only. It does
   not vary holes, views, the number of layers or nodes, or reach anything past
   the root, so #1339's per-node cost is invisible to it. It very probably
   trips first in `prepare()`'s alphabet, which walks the declared domain
   through the guarded `each_value` generator (`state.cc:701`) before anything
   propagates; that is from reading the code, since the audit build has the
   guard off. In `large-domains.md`'s proof survey, `MDD` is in the "both
   grow" row, 10x OPB and 10x steps for 10x the width.

## Inference catalogue

One rule. The propagator makes one inference, `vars[i] ≠ v` for a value with no
live edge at layer `i`, through two phases of one algorithm: the sweep that
builds the graph on the first call, and the degree cascade that maintains it
after that. Both phases give the same reason, the same assertion, the same hint
and the same reconstruction, so they are one rule, whose **Algorithm** and
**Proof size** fields describe each phase. [`regular.md`](regular.md) describes
`Regular`'s copy of the same code the same way.

### Rule: unsupported-value

- **Infers** — `vars[i] ≠ v`, one `infer_not_equal` per value.
- **Fires when** — any call of `propagate_mdd`. On the **first call**, normally
  at the root, `initialise_graph` (`mdd.cc:114–193`) builds the graph: a forward
  pass marks the nodes reachable from the root along values in the domains, the
  last layer is restricted to reachable accepting nodes, and a backward pass
  keeps the edges into live nodes. On **every later call** (`mdd.cc:250–275`),
  each value that has left a domain but still has supporting nodes has its edges
  removed and the degrees decremented; a node whose out-degree reaches 0 removes
  its in-edges and recurses to its parents (`decrement_outdeg`), a node whose
  in-degree reaches 0 removes its out-edges and recurses to its children
  (`decrement_indeg`), each edge removal erasing the parent from the value's
  supporting set. Either way, the final loop (`mdd.cc:277–282`) then removes
  every value whose supporting set is empty.
- **Strength** — `GAC` on the sequence variables, when they are distinct, views
  included; `partial` with a repeated variable: GAC on the decomposition in
  which each position is a distinct variable. Checked by brute force at
  **every** search node, root included, on random layered diagrams over random
  holey domains
  (`tmp/fd-dd/mdd/strength/mddcheck.cc`, at `86caad24`; seeds 1 to 3, 2,000
  instances each): up to four variables (five layers) of up to three nodes,
  transitions on values −1 to 3 (to 6 for the `wide` shape) over domains drawn
  from −2 to 4, and three to five variables of up to four nodes over −1 to 3 for
  the `big` shapes; distinct variables, views (`x + c`, `−x`), and transitions
  on values outside every domain. No failure at any of 73,723 nodes of 30,000
  instances, and every solution set right apart from #1329's zero-variable
  cases. This document's fact-check ran an independent checker
  (`tmp/fd-dd/factcheck/mdd/core/sweep/fc.cc`, seeds 100 to 115, with `−x + c`
  views, constants, empty layers and a second `MDD` over the same variables):
  no failure at 185,246 nodes. `mdd_test` also checks generalised arc
  consistency at every node (see [Tests](#tests)). For a repeated variable see
  [Robustness](#robustness-and-limits). There are no other variables to cover:
  the node flags are OPB flags with no domain, not solver variables, so no
  strength claim is made about them.
- **Algorithm** — two phases.
  - *First call:* a forward then backward sweep over the layered graph, the
    recursive collection of root to terminal edges of Cheng and Yap's `mddc`:
    per layer, per value of the domain times per live node, so
    `O(Σ_i |D_i| · N_i)` hash and tree operations, **per value** of each
    domain, including values no transition mentions.
  - *Later calls:* a degree-counting cascade in the style of Pesant's `Regular`
    propagator, each edge removed at most once per branch; each removal costs
    a few hash-table and `std::set` operations (`nodes_supporting` holds a
    `set<long>`). On top of that, every call walks every key of every layer's
    `nodes_supporting` and every value of every domain, whatever changed.

  Both are dwarfed by the per-node copy of the graph (#1338).
- **Why it is true** — `vars[i] = v` extends to an accepted sequence within the
  domains only if some edge on `v` from layer `i` lies on a path from the root
  to an accepting node through edges whose values are all in the domains. The
  sweep computes exactly the edges on such paths. The cascade keeps that
  invariant: an edge stays live only while its value is in the domain, its
  source has a live in-edge (or is the root) and its target a live out-edge (or
  is accepting), and an edge is removed only when one of these fails. So a value
  with no live edge has no support.
- **Proof technique** — `chain scaffolding` and `RUP sequence`. Each removal
  closes with one RUP, which is Justification Procedure 5.1 of McIlree's thesis
  (Regular language membership propagation), which his Section 5.2.1 says
  applies to `MDD`. JP 5.1 assumes an "edge deletion justification"
  `R_e ⇒ ¬s_{i=k} ∨ x_i ≠ v` for every removed edge. This solver derives a
  **node-death lemma** `R ⇒ ¬state[i][q]` instead, and the forward chain turns
  it into the edge deletion by unit propagation, so the closing RUP is JP 5.1's.
  Node-death lemmas by RUP followed by value removal by RUP are what Demirović,
  McCreesh, McIlree et al. describe for GCS's knapsack diagram (CP 2024, §3.3;
  see [Prior art](#prior-art)); the lemmas here are derived three ways:
  - a node with **no live parent** (forward-dead): RUP against the backward
    chains of its layer and the lemmas of its dead parents. Assume
    `state[i+1][q']`; for each value `v` of `vars[i]`, the backward chain for
    `(q', v)` with every parent's `¬state` makes `vars[i] ≠ v`, and with the
    reason's literals that leaves `vars[i]` no value, a conflict by the thesis's
    Theorem 3.2 (an emptied domain is a conflict);
  - a node with **no live child** (backward-dead): RUP against the forward
    chains and the lemmas of its dead children, the same way forwards;
  - the **backward chains** themselves, written once at the root: RUP against
    the forward chains and the exactly-one rows. Assume the negation; the
    at-most-one at layer `i + 1` clears every other node there, each
    non-parent's forward chain on `v` then clears that non-parent, the parents
    are false by assumption, and layer `i`'s at-least-one has no true term.

  Each step is stated under the call's reason, which Theorem 2.6 reduces to the
  unreified step, and a lemma written by an earlier call on the same branch,
  under a weaker reason, still propagates under the current one by the thesis's
  Theorem 3.3 (complete propagation of implied atomic literals), as in JP 5.1's
  own proof. The order matters, and the code keeps it: each lemma is written
  before the lemmas that consume it. In the cascade a backward-dead node's lemma
  is written before its parents are visited (`mdd.cc:200–207`, be55c037), and a
  forward-dead node's before its children are (`mdd.cc:225`), so a parent's
  lemma finds its children's in the database and a child's its parents';
  the initialiser and the first call write forward-dead nodes in ascending layer
  order and backward-dead ones in descending order, for the same reason; and a
  lemma already in the `DeadCache` on this branch is skipped. At the root most
  dead nodes are statically dead and already have their Top lemma, so the first
  call writes lemmas only for nodes the root's domains kill beyond those
  (`mdd.cc:138–142`, `157–159`, `185–188`). Preconditions: the diagram is
  deterministic (one target per node and value, which the class guarantees),
  every value of a variable's domain at the root is in its layer's alphabet
  (which `prepare()` guarantees), and every lemma the cascade relies on is on
  the branch (which the cache's backtracking guarantees).
- **Reason** — `generic_reason(vars)`, materialised at the start of the call:
  every variable's bounds (one equality literal if it is fixed) and its runs of
  missing values. Not minimal: a removal at layer `i` needs only the layers
  whose domains killed the nodes in question. One literal per run, so per run of
  each domain, not per value; the work of finding the runs is one step per run.
  Each lemma carries the whole reason too (`emit_rup_proof_line_under_reason`).
- **Assertion** — `vars[i] ≠ v ∨ ¬reason`. There is no explicit contradiction:
  a conflict is a variable's last value being removed, in the same shape, and
  the backtrack closes it. When no accepting node is reachable, the first
  variable loses all its values and the loop stops at the wipeout; the other
  variables are never touched. Measured at `Inferences` (`proofs/shape.cc`):
  - on the XCSP3 reference diagram at the root, where `x[1]` cannot be 1
    anywhere (first call):
    ```
    a 1 ~i[x[1]][eq1] 1 ~i[x[0]][ge0] 1 i[x[0]][ge3] 1 ~i[x[1]][ge0] 1 i[x[1]][ge3] 1 ~i[x[2]][ge0] 1 i[x[2]][ge3] >= 1::mdd:((constraint_id _1));
    ```
  - after the branch `x[0] = 2`, with `x[1]`'s 1 already gone (the cascade); at
    `Off` the same inference is preceded by three lemmas, `¬mddnode1is1`,
    `¬mddnode1is0` and `¬mddnode2is0`, each under the same reason:
    ```
    a 1 ~i[x[1]][eq2] 1 ~i[x[0]][eq2] 1 ~i[x[1]][ge0] 1 i[x[1]][ge3] 1 i[x[1]][eq1] 1 ~i[x[2]][eq0] >= 1::mdd:((constraint_id _1));
    ```
  - with no accepting terminal (`shape.cc unsat`): three `a` lines for
    `x[0] ≠ 0, 1, 2`, then `a >= 1 ::backtrack`.
- **Hint** — `hints::MDD` (`mdd/hints.hh`), `(constraint_id <id>)` under the
  hint name `mdd`, with one field: `originator`, the `ConstraintID`. On the 25
  by 25 nonogram below, 44,740 of the proof's 46,171 `a` lines at `Inferences`
  carry it; the rest are 1,427 `backtrack` and 4 `solx_block`.
- **Offline reconstructibility** — `offline`. The procedure is fixed by the
  rule and needs nothing chosen: read the diagram from the `.scp` entry with the
  hint's ID, and the domains from the reason; compute forward and backward
  reachability under those domains; derive the backward chains (each RUP, as
  above), the forward-dead lemmas in ascending layer order, the backward-dead
  lemmas in descending order, each under the reason, and then the clause by
  RUP. Every step is guaranteed by the argument above, since the reason's
  domains are the ones the propagator found `v` unsupported in: all of a call's
  removals follow from the domains at its start, and the reason is materialised
  then. It rebuilds every lemma under the asserted reason, so it needs neither
  the lemmas earlier calls wrote nor the cache, nor the order the solver visited
  nodes in, nor which phase made the removal.
- **Proof size** — per removal, one line of at most `1 + |reason|` literals,
  `|reason|` being at most two per variable (one if fixed) plus one per run of
  missing values. Lemmas: in the first call, at most one per node the root's
  domains kill, beyond the static dead set; in the cascade, one per node newly
  dead on this branch, each of `1 + |reason|` literals. Over a root to leaf path
  a node's lemma is written at most once, so a branch costs at most `Σ_i N_i`
  lemmas; after a backtrack they are written again. At the root, the Top
  scaffolding adds `Σ_i N_{i+1} · |D_i|` backward chains of `2 + (parents on v)`
  literals and at most `Σ_i N_i` unit lemmas. On the nonogram below, the lemmas
  are 313,612 of the proof's 413,975 lines and 179.5 MB of its 207 MB.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No mutation lane.

## Evidence

### Tests

- **`mdd_test`** (`mdd_constraint`): six hand-written diagrams over three or
  four variables (the XCSP3 reference example, "exactly one 1", non-uniform widths,
  two paths, no accepting terminals, domains narrower than the alphabet),
  against a brute-force acceptor, under `solve_for_tests_checking_gac`, so
  generalised arc consistency at every node, with and without proofs, VeriPB
  when it is on the path. Seeded (`--seed=N`).
- **`scp_reader_test`**: `read_scp: mdd enumerates correctly`, and the write,
  read, write round trip.
- **MiniZinc:** `minizinc-mdd` runs `tests/mddtest.mzn`, the XCSP3 reference
  example, against MiniZinc's default solver, with proofs. No `--fzn-pattern`.
- **XCSP3:** `xcsp_mdd`, `tests/mdd.xml`, against ACE's cached solutions, with
  proofs.
- **`integer_ranges_test`** posts an `MDD` (`integer_ranges_test.cc:151`) to
  check that a transition value outside the range is refused (#1215).
- **Audit lane:** the one row above.

**Runtime caps.** No lane sets or clears one. The default caps do not fire on
`mdd_test`: its largest cases have 27 assignments, with three and five
solutions.

**Tightness:** no mutation lane.

**What the tests do not cover.**

- **No variables**, which is #1329, and **node indices out of range**, #1333.
- **Holey initial domains**: every tested domain is an interval.
- **Views, repeated variables and constants**: none tested.
- **Any assertion level but `Off`.** The audit's sweep ran the other three
  (below); the suite does not.
- **Anything larger than four variables or three nodes a layer**, and anything
  with a search: every test diagram is solved nearly without branching.
- **A wide declared domain past the root**, #1339's shape.
- **The MiniZinc shapes of #1336**, and non-1-based `x`.
- **Real instances:** none ported; no MiniZinc Challenge model (every year in
  the `mzn-challenge-a8448864` checkout, 2008 to 2026) or local XCSP3 series
  posts `mdd`.

**What this audit ran** (all at `86caad24`, Release, fataepyc-10; results in
`tmp/fd-dd/mdd/strength/`):

- the strength sweep above, 36,000 instances, proofs off;
- the same probe writing proofs, each run at one level: 6,600 at `Off` (VeriPB
  must say `VERIFIED` with no assertion) and 800 at each of `Definitions`,
  `Links` and `Inferences` (`UNDER ASSERTIONS`); 8,579 accepted, and the 421
  rejected (292 at `Off`, 43 at each of the other three levels) are exactly
  the 421 zero-variable instances with a wrong solution set;
- the `.scp` round trip on 530 of them.

This document's fact-check ran its own checker
(`tmp/fd-dd/factcheck/mdd/core/sweep/fc.cc`):
48,000 instances proofs off and 6,400 at each of the four levels, every
variable count at least one, with holes, views, repeats, constants, empty
layers and a second `MDD` over the same variables; no wrong solution set, no
exception, and no proof rejected at any level.

### Benchmarks and examples

- **In the repository:** no example posts `MDD`, and no benchmark.
- **Corpus:** none (see above). The family is reached through XCSP3 and
  MiniZinc models written for it.
- **For CPU:** random nonograms, one `MDD` per row and column
  (`tmp/fd-dd/mdd/perf/nonogram.hh`, `nono_gcs.cc`, `nono_gecode.cc`), 25 by
  25 at density 0.5; seeds 3 and 5 explore about a thousand nodes. Gecode's
  `extensional` with a `DFA` over the same layered nodes is generalised arc
  consistent too, and the two find the same numbers of nodes and solutions.
- **For proof verification:** the same instance, 25 by 25 seed 3: 207 MB fully
  justified, 28 s to check. Larger nonograms take minutes to solve here (30 by
  30 seed 5, 4,521 nodes, did not finish in 100 s) and should not be run with
  proofs uncapped.

### CPU performance

*Release build of `86caad24` (GCC 15.2.0, `-O3 -march=native`); Gecode 6.3.0,
built locally; fataepyc-10, `taskset -c 60`, fixed malloc thresholds, serial;
2026-10-10. Median of three runs; the `instructions:u` spread is under 0.1%.*

**Against Gecode, at equal node and solution counts.** Nonograms, input order,
smallest value first, all solutions, proofs off. GCS recursions equal Gecode's
nodes, and the solution counts agree (the failure counts are defined
differently, so they are not compared); node and solution counts are what was
checked, not the trees themselves.

| instance | solutions | nodes | propagations, GCS / Gecode | GCS | Gecode | `instructions:u` ratio |
|---|---|---|---|---|---|---|
| 25 × 25, seed 3 | 4 | 1,427 | 34,241 / 29,001 | 9.11 s, 30.77·10⁹ | 0.067 s, 0.343·10⁹ | 90 |
| 25 × 25, seed 5 | 20 | 1,173 | 28,303 / 25,686 | 11.09 s, 37.71·10⁹ | 0.081 s, 0.403·10⁹ | 94 |
| 30 × 30, seed 2 | 1 | 691 | 21,391 / 19,086 | 11.11 s, 38.73·10⁹ | 0.103 s, 0.517·10⁹ | 75 |

About 6 to 16 ms per node. A `perf` profile of the first instance
(`perf/nono25.data`, frame pointers) puts 47% of self time in `_int_malloc`,
`_int_free_merge_chunk` and `free`, 28% inclusive under `~MDDGraph` and 19%
in the hash-table copy; with DWARF call graphs (`perf/nono25d.data`), 92% of the
samples whose stack reaches `main` are under `State::new_epoch`. That is a
hotspot share, not a measured saving (#1338). For comparison, `Regular` over
the same automaton with its states numbered per layer (the solver's other way
to post this model, `NONO_REGULAR=1`) took 27.7 s on the first instance, at the
same node and solution counts; `regular.md` measures `Regular` over the compact
automaton.

**What the benchmark does not exercise.** Only 0/1 variables, so neither the
wide-domain costs nor holes; one shape of diagram (a run-length automaton
unfolded); no views or repeats. It exercises both phases of the rule, the
sweep only at the root.

### Proof performance

*Same build and machine, 2026-10-10; VeriPB 3.0.2 with
`--force-checked-deletion`.*

**The nonogram, 25 by 25, seed 3** (four solutions, 1,427 nodes; OPB 33,830
lines, 2.76 MB; solved serially in 9.11 s without proofs):

| level | proof lines | bytes | solve | VeriPB | result |
|---|---|---|---|---|---|
| `Off` | 413,975 | 207 MB | 13.2 s | 27.9 s, 96 MB | `VERIFIED` |
| `Inferences` | 50,249 | 26.0 MB | 9.3 s | 0.74 s | `UNDER ASSERTIONS` |

**Where the fully justified proof goes**, by line type:

| lines | bytes | what |
|---|---|---|
| 313,612 | 179.5 MB | per-call node-death lemmas, each carrying the whole reason |
| 47,418 | 24.7 MB | the removals and the backtracks |
| 32,334 | 2.1 MB | Top backward chains, 50 constraints |
| 8,583 | 0.3 MB | unit `¬state` lines, all of them the Top static dead nodes |
| 12,029 | 0.32 MB | the rest: `red` and `core` lines of the atom definitions, `pol`, deletions, comments, `solx` |

So the family's own share is nearly all of it, and the lemmas are 87% of the
bytes: they are re-derived after every backtrack, and each carries the line's
whole reason, 25 to 49 literals and 35.7 on average (the fact-check's count,
`tmp/fd-dd/factcheck/mdd/core/nono/classify.py`; the removals and backtracks average 34.2). A
fixed cell costs one literal and an unfixed one two, its declared bounds
`x ≥ 0` and `x < 2`, which say nothing: 60% of all lemma reason literals are
those. The ratio of verification to solve is 2.1 at `Off`, and asserting the
inferences cuts the proof by 8 times and its check by 38. Since
every lemma carries the whole scope's reason while the forward chains need only
the layers in question, a minimal reason would shrink both the lemmas and the
removals ([Next steps](#next-steps)).

**Assertion levels.** On the random sweep, every proof but #1329's is
accepted at whichever of `Definitions`, `Links` and `Inferences` it was run at
(800 runs each, above; and 6,400 each in the fact-check), and
`Regular`'s non-deterministic failure (#1332) does not arise: an
`MDD` is deterministic, so unit propagation assigns every flag on a solution.
Nor does #1210 (`Links` rejects the first solution line when a variable wider
than `{0, 1}` has undefined order atoms) reach `MDD`'s variables, by reading
its mechanism rather than line by line: the forward chains name each value's
equality atom, so the OPB defines those atoms and the order atoms under them.
The fact-check did see #1210 at `Links` on a free variable `y` in `0..2`
beside a zero-variable `MDD`, as it predicts, and on `NotEquals` alone.

**Measured elsewhere** — `decision-diagram-proof-strategies.md` reports the
upfront strategy 7 to 9 times smaller and 4 to 5 times faster to verify than the
per-call one, as ranges over its `MDD` instances; its `MDD n12` row is a 4.2
times line ratio and 5.2 times faster. Those were measured on the rebased
decision-diagram PR stack (#211) with VeriPB 3.0.2. Those figures are not
comparable with the
tables above, should not be mixed with them, and could not be re-taken: the
per-call strategy is not in the tree.

## Status, gaps, and next steps

### Proof-logging gaps

`None` in the inferences: every removal is justified at `Off`, and the
propagator is the same with proofs on or off. But a zero-variable diagram with
an empty accepting list is a wrong answer that the proof cannot justify, and
VeriPB rejects it (#1329).

### Known limitations

- **An `MDD` over no variables can report solutions it should not** (#1329).
- **An out-of-range node index crashes the solver or corrupts the proof**
  instead of being refused (#1333).
- **MiniZinc's `mdd` with an empty `x`, a second node at level 1, a node at a
  level outside `1..L+1`, or no nodes gives an error or undefined behaviour**
  (#1336).
- **It is slow:** two orders of magnitude more instructions than Gecode at the
  same node and solution counts, mostly in copying its graph at every node
  (#1338).
- **A variable declared much wider than the diagram's alphabet costs time at
  every search node**, not only at the root (#1339), and its proof model is
  linear in the declared width (#842).
- **A repeated variable propagates less than it could.**
- **Non-deterministic diagrams are unsupported:** `mdd_nondet` decomposes in
  MiniZinc, and XCSP3 reports them unsupported.
- **With proofs, writing the root scaffolding takes time quadratic in the
  layer width**, though the scaffolding itself is linear in it.
- **No reified form.**

### Next steps

1. **Refuse the zero-variable unsatisfiable diagram, and validate node
   indices** (#1329 and #1333). In `prepare()`, when `n = 0` and 0 is not
   accepting, set a flag and still return `true`, so that `define_proof_model`
   writes the rows the contradiction is RUP against, and install the
   contradiction from `install_propagators` with
   `Propagators::install_initial_contradiction`, as `all_different.cc:68–74`,
   `element.cc:191–194`, `In` and `Table` do; return `false` only when 0 is
   accepting. The fact-check built both placements: the empty accepting list
   then gives no solution, `VERIFIED UNSATISFIABLE` at `Off` and accepted at
   every assertion level. In the constructor, every target and terminal in
   range. Tiny; buys a wrong answer and a crash. Add both shapes to
   `mdd_test`.
2. **Fix the MiniZinc binding's shapes** (#1336): post a contradiction for
   `L = 0` or `N = 0`; drop every edge whose source level is outside `1..L`,
   then every node at a level outside `1..L+1`, and the nodes other than node 1
   at level 1 with their out-edges, since no root path uses any of them. Small, with new `minizinc/tests` lanes (#1006 is
   the issue for such lanes).
3. **Stop the per-value map entries** (#1339): `find()` at `mdd.cc:167` and
   `279`. Two lines; 66.5 s to 0.55 s on the probe. Build `prepare()`'s
   alphabet only when there is a proof model, which cuts the root with proofs
   off by 38 to 55% on the probes. Then remove the root's
   out-of-alphabet values as ranges, one `infer_not_in_range` per gap in a
   layer's keys, which takes the root's per-value walk and its per-value proof
   off too; and, with #842, state out-of-alphabet values as a domain
   restriction in the OPB.
4. **Make the graph cheap to restore** (#1338): flat edge arrays with degree
   counters, then a trail of removed edges, shared with `Regular` if #200 lands
   first. Moderate to large; buys most of the two orders of magnitude. Check
   solutions and node counts unchanged.
5. **Claim idempotence** and **build the reason only when an inference reads
   it** (not filed; the second is the pattern #1338 mentions and #1070's comment
   counts). One line and a few; the first removes a quarter of the calls but saves
   little until item 4, and holds only on distinct variables, which
   `Propagators` already enforces by ignoring the claim when trigger positions
   alias; the second saves a whole-scope materialisation per call with proofs
   off.
6. **A per-layer reason.** A dead node at layer `i` depends on the domains
   between it and the root (forward) or the last layer (backward), so a lemma's
   reason could be those layers' literals, and a removal's the union over its
   edges; and a reason need not name a bound that is still the declared one,
   which `generic_reason` does for every family that uses it (commented on
   #1070; not filed separately). That shrinks the
   lemmas, which are 87% of the nonogram proof. Which lemmas the closing RUPs
   need is an empirical question, settled with VeriPB.
7. **Index the backward chains' parents** once per layer, so the Top scaffolding
   is linear in the edges rather than `Σ N_i N_{i+1} |D_i|`. Small.
8. **Tests:** a random differential lane in the style of this audit's sweep,
   with holes, views and constants, and an `mdd_test` run above `Off`.

## Prior art

**Propagation.** Generalised arc consistency on a layered graph with in- and
out-degree counts is Pesant's algorithm for `Regular` (*A Regular Language
Membership Constraint for Finite Sequences of Variables*, CP 2004, LNCS 3258).
For an explicit multi-valued decision diagram, Cheng and Yap give `mddc`
(*Maintaining Generalized Arc Consistency on Ad Hoc r-Ary Constraints*, CP 2008,
LNCS 5202), which, as the thesis describes it, recursively collects the edges on
root to terminal paths, as this family's first call does; Gange, Stuckey and
Szymanek give an incremental propagator with explanations for lazy clause
generation (*MDD propagators with explanation*, Constraints 16(4), 2011); and
Perez and Régin's `MDD-4R` (*Improving GAC-4 for Table and MDD Constraints*,
CP 2014, LNCS 8656, pp. 606–621) maintains supports incrementally under
deletions with per-layer, per-value arc lists rather than degree counters. This
family's cascade is a degree-counting one in Pesant's style. Nothing in the
propagation is new here. The first three citations are the thesis's own [163],
[41] and [74], checked against its bibliography; the fact-check confirmed all
four.

**Certification.** The encoding is McIlree's thesis's Encoding Procedure 5.1
for `Regular` (*Pseudo-Boolean Proof Logging for Constraint Propagation
Algorithms*, Chapter 5), and his Section 5.2.1 argues that an `MDD` propagator
is justified by the same procedures, JP 5.1 with Subprocedure 5.3, adapting the
state flags to the diagram's nodes; it states the adaptation without an
implementation or experiments. The shape of this family's derivation is
published too: Demirović, McCreesh, McIlree, Nordström, Oertel and Sidorov
(*Pseudo-Boolean Reasoning About States and Transitions to Certify Dynamic
Programming and Decision Diagram Algorithms*, CP 2024, LIPIcs 307, §3.3) give,
for GCS's knapsack decision diagram, RUP steps showing that each infeasible
node's state is false, followed by each value's removal by RUP, and note that
this resembles McIlree and McCreesh's steps for `Regular` (*Proof Logging for
Smart Extensional Constraints*, CP 2023). That is the node-death lemma and
closing RUP used here. So certified `MDD` propagation, and its derivation, are
not new. The arrangement around them, backward chains derived once at the root
and kept, with a per-branch cache that writes each node's lemma once per branch
(`decision-diagram-proof-strategies.md`'s upfront strategy, from #210 to
#213), is shared by `Regular`, `MDD`, `Knapsack`'s upfront form and
`BinPacking`, and its
novelty is assessed once, in [`regular.md`'s Prior art](regular.md#prior-art);
`MDD`'s copy (#211) claims nothing beyond it.

## Further reading

- [`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md):
  the upfront and per-call proof strategies for `Regular`, `MDD`, `Knapsack` and
  `BinPacking`, its displacement times DB-tax cost model, and why `MDD` ships
  upfront only. Its `MDD` figures are from the PR stack. Three of its
  statements do not hold for `MDD` at `86caad24`: the scaffold is tiny only for
  narrow diagrams (on the nonogram it is 32,334 lines, and the per-call lemmas,
  not the scaffold, are most of the proof); an upfront call writes one lemma per
  newly dead node, not "at most one cache-gated" line (313,612 lemma lines on
  the nonogram); and `MDD` has no `with_proof_strategy` setter, which the note
  says all four constraints expose (and contradicts itself on later). For `MDD`
  the scaffold is backward chains and static dead lines only.
- [`regular.md`](regular.md): `Regular`, whose graph code `mdd.cc` copies, and
  whose audit found the same per-node copy cost.
- [`large-domains.md`](../large-domains.md): the encoding-growth survey and
  #842's re-encoding argument, which covers `MDD` with `Regular`.
- [`justification-techniques.md`](../justification-techniques.md): Theorem 2.6
  (a step under a reason), Theorem 3.2 (an emptied domain is a conflict) and
  Theorem 3.3 (complete propagation of implied atomic literals, which lets a
  lemma written under a weaker reason fire under a stronger one).
