# `Circuit` and `SubCircuit`: the successors form one tour, of every node or of some

> **Maturity** production (`Circuit` under both algorithms, `SubCircuit` under
> `Check` and `Prevent`); experimental (`SubCircuit` under `SCC`, with or
> without its two shaving rules) ·
> **Audited** 2026-10-09 at `86caad24` ·
> **Open issues** filed by this audit: #1307 (a `Circuit` over an empty
> array crashes), #1306 (with `with_prune_skip(false)`, VeriPB can reject the
> `SCC` proof, because two rules' certificates need prune skip to have run),
> #1317 (the `SCC` propagator builds its whole-scope reason on every call,
> proofs off too, and with proofs defines a short-reason flag on every call),
> #1318 (three of `Circuit`'s setters do nothing, and several `SubCircuit`
> comments are stale), #1319 (a question: a one-node `circuit` answers
> differently from MiniZinc's own decomposition). Already open and touching
> this family: #1228 (`with_required_node()` rejects an anchor whose own index
> is an interior hole), #833 (the large-domain policy), #868 (cross-solver
> comparisons; this document gives one, by hand), #1006 (MiniZinc shape
> lanes), #364 (incrementality survey). **Held, not filed** (Ciaran to decide):
> `SubCircuit`'s pigeonhole grows with a wide-declared successor's declared
> width (see [Known limitations](#known-limitations)).
> **Not filed, by decision**: `Circuit`'s `SCC` propagator asserts three of its
> rules as bare unit clauses at the `Definitions`, `Links` and `Inferences`
> assertion levels, the defect `smart_table` has from the same commit
> (*assertion reasons*); Matthew will run into it when the hints-only mode is
> taken up for the justifier. Tracked under #871.

`Circuit(succ)` says that `succ[i]` is the node after `i` on a single tour
through every node; `SubCircuit(succ)` says the same of the nodes that do not
point at themselves, the rest being off the tour. They are two classes in one
directory with two encodings, five propagators (three for `Circuit`, two for
`SubCircuit`) and a root contradiction, and they share only the
value consistent all-different pass and its clique encoding, both from
[`all_different`](all_different.md). The `Circuit` proofs are McIlree,
McCreesh and Nordström's (CPAIOR 2024, and Chapter 6 of McIlree's thesis): a
position labelling, a cutting-planes telescope for a short cycle, and a
pigeonhole over shifted positions for every strongly-connected-component rule.
The `SubCircuit` proofs are this solver's own, and the long design note
[`subcircuit-proof-logging.md`](../subcircuit-proof-logging.md) records how
they were built and what they cost.

Four things to know before touching it.

- **It finds the right answers everywhere this audit looked, bar one crash,
  and one option makes its proof wrong.** Random holey instances up to six
  nodes, with constants, offset views and values outside `0..n-1`, through
  every algorithm and option: no lost and no spurious solution in 2,000 trials
  per configuration. MiniZinc on both versions, XCSP3 against ACE and the
  `.scp` reader agree with their references at two nodes and more. The crash
  is the empty array: `Circuit{}` segfaults under its default algorithm and
  fails on an integer overflow whenever a proof is written (#1307).
  `SubCircuit{}` is fine, and MiniZinc guards the shape before it reaches
  either. The wrong proof is `Circuit`'s `SCC` with
  `with_prune_skip(false)`: the answers stay right, but the certificates of
  *fix required* and *no back edge* assume skip edges are already pruned, and
  VeriPB rejects them when a skip edge is what makes the argument fail (13 of
  900 `circuit_random --no-prune-skip` proofs; #1306). At the
  defaults, no proof was rejected in this audit or its fact-checks.
- **The `SCC` propagator's per-call overhead is mostly not the algorithm.** It
  materialises a reason over every successor on every call, with proofs off
  too: building it only when a proof will read it takes 12.8% of the
  instructions off a MiniZinc Challenge `p1f-pjs` solve to optimality, and
  11.4% off the `tsp` benchmark run with `--propagator scc` (its default is
  `Prevent`, which does not build it), with the same recursion and
  propagation counts and the same output. With proofs on it also
  defines a short-reason flag on every call, which is 39% of the proof's bytes
  on a 12-node enumeration and 52% on a 14-node one; defining it on first use
  halves the 14-node proof (#1317).
- **`Circuit`'s `SCC` hints-only proof is wrong in three rules.** At the
  assertion levels, *fix required* and the two *prune skip* rules assert their
  conclusion as a bare unit clause, which is not a consequence of the model:
  over 40 random enumerations, 5 of the 400 `circuit`-hinted assertions are
  falsified by a solution the same proof logs later, all five from *fix
  required*; the prune-skip units go through the same code path, but none was
  seen falsified. Every other rule in both classes carries its reason. Left
  unfiled by decision (*assertion reasons*), as in
  [`smart_table.md`](smart_table.md).
- **`Prevent` is the cheaper `Circuit` and the default `SubCircuit`; `SCC` is
  the default `Circuit`.** On Hamiltonian-cycle enumeration from 12 to 18
  nodes, `Circuit`'s `SCC` explores 3 to 20% fewer nodes than `Prevent` and
  takes 3.1 to 3.5 times as long; the `tsp` benchmark defaults to `Prevent`.
  Neither is GAC, which is NP-hard for this constraint.

## What it is

### Semantics

**`Circuit(succ)`**, `n = |succ|`: `succ` is a permutation of `0..n-1` whose
single cycle visits every node. Values are 0-based; each successor's domain
is narrowed to `0..n-1` before search (`define_bound`, `circuit.cc:126–132`),
so a domain declared wider is accepted.

- **`n = 1`**: `[0]`, the self loop, is the one solution, deliberately (#254;
  `circuit_test` checks it). The no-self-loop propagator is installed only for
  `n > 1`. `cake_pb_cp` agrees, and so does Gecode. MiniZinc's standard
  library decomposition does not: it posts `x[i] != i` for every `i`, so a
  one-node `circuit` is unsatisfiable there and in Chuffed, and satisfiable
  through Glasgow (#1319).
- **`n = 2`**: `[1, 0]` only.
- **`n = 0`**: the empty array. Meant to be vacuously true, as MiniZinc's
  decomposition has it, but it crashes (#1307): see
  [Robustness](#robustness-and-limits).
- **A repeated variable** in two slots cannot be all different, and is
  answered with a contradiction at the root (#1047, `circuit.cc:55–61`). Two
  slots pinned to the same **constant** are left to the propagators.

**`SubCircuit(succ)`**: `succ` is a permutation of `0..n-1`, and the nodes
with `succ[i] ≠ i` form **at most one** cycle; a node off the tour points at
itself. So all-different holds over the whole array.

- **The empty tour**, every node a self loop, is a solution. The smallest
  non-empty tour has two nodes; there is no one-node cycle.
- **`n = 0`** has one solution, and with a tour size pins the size to 0;
  **`n = 1`** has only `[0]`.
- A repeated variable is a root contradiction, as for `Circuit`.
- **`with_tour_size(k)`**: `k` equals the number of nodes with `succ[i] ≠ i`.
  It is a semantic argument, written to the `.scp`. Its domain may reach
  outside `0..n`.
- **`with_required_node(r)`** names a node already declared on the tour,
  `r ∉ dom(succ[r])` in the declared domains. It throws
  `InvalidProblemDefinitionException` at the call if `r` is outside the
  array, and when the problem is prepared, at solve time, if its own index is
  still in its domain. It does not change the meaning, under any algorithm.
  It does change the encoding (see [OPB encoding](#opb-encoding)), and under
  `SCC` the walks' start node. It wrongly rejects a node whose own index is an
  interior hole made by `create_integer_variable(vector)`, because the holes
  are not in the initial state yet when `prepare()` checks (#1228); the fuzz
  below hit that in 396 of 2,000 trials. The automatic anchor search misses
  the same nodes silently, and so do MiniZinc's set domains, which
  `fzn_glasgow.cc:504–516` creates as an interval plus one `Or` per hole: the
  fact-check's `subcircuit` over `1..5` with `x[3] != 3` gets the unanchored
  encoding, where `x[5] != 5`, a bound, gets the anchored one
  (`tmp/fd-graph/factcheck/circuit/b/mzn/`). With no anchor, `subcircuit::SCC`
  is silently `Prevent`.

`Circuit` is not a special case of `SubCircuit` with a size of `n`, nor the
reverse, in the code: they share no propagator and no position encoding.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Circuit` | ✓ `fzn_circuit` → `glasgow_circuit`[^mzn] | n/a as a class[^xcircuit] | ?[^gcspy] | ✓ `circuit` | reified: n/a[^reif] |
| `SubCircuit` | ✓ `fzn_subcircuit` → `glasgow_subcircuit`[^mzn] | ✓ `<circuit>`, all three forms[^xsub] | ?[^gcspy] | ✓ `subcircuit`, optional size | reified: n/a[^reif] |

[^mzn]: Both redefinitions (`minizinc/mznlib/fzn_circuit.mzn`,
    `fzn_subcircuit.mzn`) pass `min(index_set(x))` as an offset, and
    `fzn_glasgow.cc:944–954` applies it as a view, so domains narrowed in the
    model survive (#802, after #803 found the comprehension shift discarding
    every hole). Both guard `length(x) = 0` as `true`, which is what keeps the
    empty-array crash out of reach of MiniZinc.

[^xcircuit]: XCSP3-core's `<circuit>` allows isolated vertices and asks for
    exactly one circuit, so it is `SubCircuit`, and the `Circuit` class is
    unreachable from XCSP3 (#167, closed by PR #794). A full Hamiltonian
    circuit is still expressible there, as `<circuit>` with a size of `n`,
    which arrives as `SubCircuit` with that size.

[^xsub]: No size: `SubCircuit` with a fresh size variable over `2..n`.
    Constant or variable size: `SubCircuit` with that size, plus
    `size ≥ 2` (`xcsp_glasgow_constraint_solver.cc:784–810`). A non-zero
    `startIndex` is `s UNSUPPORTED`, as it is for ACE ("unimplemented case for
    circuit"). A one-node `<circuit>` with no size is also `s UNSUPPORTED`
    ("variable has lower bound > upper bound": the size variable would be
    `2..1`), where the answer is unsatisfiable (#1319).

[^gcspy]: CPMpy was not examined. What it would call is `gcspy`, which
    binds `post_circuit`, posting `Circuit` over the ids unchanged, 0-based,
    and binds nothing for `SubCircuit`. The audit tree is built with
    `GCS_ENABLE_PYTHON=OFF`, so the binding was read, not run.

[^reif]: There is no reified form. MiniZinc's `fzn_circuit_reif` is an abort
    in the standard library (`std/fzn_circuit_reif.mzn`: "Reified circuit/1 is
    not supported."), so every solver fails the same way.

**The front ends were checked against references, not only through `cake`.**
The chain starts at the `.scp`, so a mistranslation upstream of it would
verify. At `86caad24`, on fataepyc-10, 2026-10-09:

- **MiniZinc**, 2.9.7 and 2.10.1, 192 models each
  (`tmp/fd-graph/circuit/probes/mzndiff.py`): `circuit` and `subcircuit` over
  index sets starting at 0, 1, 3 and −2, sizes 0 to 5, full and holey
  domains, and domains two wider than the index set at each end. Every
  solution set through Glasgow equals Gecode's, Chuffed's and the standard
  library decomposition's for `n ≥ 2`, on both versions. The decomposition is
  inlined and solved by Gecode; for `subcircuit` it is the standard
  library's without its `alldifferent(order)`, which leaves the projection
  onto `x` unchanged. At `n = 0` Glasgow and the decomposition both find the
  empty solution, Gecode errors on `circuit` and finds it for `subcircuit`,
  and Chuffed finds none for either. At `n = 1`, `circuit` differs, as under
  [Semantics](#semantics); Chuffed also rejects some of the wide one-node
  `subcircuit` models with a syntax error (4 of 8 on 2.9.7, 1 of 8 on
  2.10.1).
- **XCSP3**, 200 random instances against ACE 2.6
  (`probes/xcspdiff.py`): all 147 with `startIndex` 0 and two nodes or more
  agree, over no size, a constant size from 0 to `n + 1` and a variable
  size. The other 53 are refused by ACE, and Glasgow refuses or answers
  unsatisfiable, as in the footnote.
- **`.scp`**, 300 random documents (`probes/scpdiff.py`): `circuit`,
  `subcircuit` and `subcircuit` with a size, domains reaching −1 and `n`,
  holes by `in`. Every solution count equals a Python brute force, which
  counts `[0]` as a one-node circuit, so at `n = 1` it encodes Glasgow's
  semantics rather than an independent reference.

**These three harnesses were weaker than they look**: on the Glasgow side,
and for MiniZinc's reference solvers, they treated a run as failed only on a
nonzero exit (the ACE side ignored the exit code and looked only for
solutions or `UNSATISFIABLE`), never on `=====ERROR=====` or
`=====UNKNOWN=====` or a missing `s` line, and never required a complete
enumeration (`==========`, `=====UNSATISFIABLE=====`, or ACE's complete
exploration), so an error with exit status 0 would have read as an empty
solution set. The fact-check re-ran all three strictly
(`tmp/fd-graph/factcheck/circuit/a/mzn/mzndiff_strict.py`, `a/xcsp/strict.py`,
`a/scp/scpdiff.py`; results in `REPORT-A.txt`): no masked error and no
incomplete run on any route. Every `n ≥ 2` MiniZinc model, 128 per version,
has the same complete solution set from all four solvers; the 147 XCSP3
cases are complete on both sides and agree, and of the 53 ACE refuses Glasgow
answers 27 `s UNSUPPORTED` and 26 complete `UNSATISFIABLE`; the 300 `.scp`
documents again differ in none. The claims above stand on those re-runs.

### Options

**The algorithm**, `with_algorithm()`, a closed `std::variant`:

| Class | Variant | Default | What each installs |
|---|---|---|---|
| `Circuit` | `CircuitAlgorithm = std::variant<circuit::SCC, circuit::Prevent>` | `circuit::SCC` | `SCC`: the value consistent pass, the strongly-connected-component check with its pruning rules, then the from-scratch small-cycle pass. `Prevent`: the value consistent pass and an incremental small-cycle pass, alternated to a fixpoint |
| `SubCircuit` | `SubCircuitAlgorithm = std::variant<subcircuit::Check, subcircuit::Prevent, subcircuit::SCC>` | `subcircuit::Prevent` | `Check`: the value consistent pass and the closed-cycle rule. `Prevent`: adds the chain lookahead. `SCC`: adds the two reachability walks, and only when an anchor exists; without one it is `Prevent` |

There is no `consistency::` tag; neither class has `with_consistency()`.
Neither choice changes the OPB, which is written by `define_proof_model()`
before the algorithm is consulted.

**`with_gac_all_different()`**, both classes, off by default: also posts a
child [`AllDifferent`](all_different.md) at `consistency::GAC`, with this
constraint's ID (#449). The value consistent pass runs regardless. The OPB is
byte-identical with and without it, once sorted (the child writes the same
clique rows under the same ID; `opb/circuit_5.opb` against `circuit_gac_5.opb`).
`circuit_random-gac-all-different` runs it (#642, #651).

**`Circuit`'s `SCC` knobs**, all no-ops under `Prevent`, none changing the OPB:

| Setter | Default | Read? |
|---|---|---|
| `with_prune_root` | on | yes |
| `with_prune_skip` | on | yes |
| `with_fix_req` | on | yes |
| `with_prove_am1_by_contradiction` | on | yes: at-most-ones by a `red` subproof, else by a clique of pairs |
| `with_short_reasons` | on | yes: one reified flag stands for the reason |
| `with_prune_within` | on | **no**: nothing in `circuit_scc.cc` reads it |
| `with_prove_using_dominance` | off | **no** |
| `with_enable_comments` | on | **no**: comments are written either way |

The three unread ones are documented in `circuit.hh` as doing something
(#1318). Francis and Stuckey's *prune within* exists for
`Circuit` in the thesis (JP 6.6) but not in this propagator.

**`SubCircuit`'s `SCC` knobs**: `with_prune_root()` and `with_prune_within()`,
both off, both ignored without `subcircuit::SCC` and an anchor. They change
propagation only.

**`with_required_node()`**, `SubCircuit`, every algorithm: see
[Semantics](#semantics). It changes which node anchors the encoding, so it
can change the OPB. Under `Check` and `Prevent` it changes no propagation:
the propagator receives the anchor only under `SCC` (`subcircuit.cc:1219`,
`:1263–1267`), and the named node, its own index already gone, is an evidence
node with or without the option; what changes is the certificate, since a
closed cycle that misses the anchor becomes one telescoping `pol`
(`subcircuit.cc:209–219`). Under `SCC` it also moves the walks' start. It
never changes the constraint.

### Variable kinds and views

Plain variables, constants and views of either sign, in either class, and a
plain variable or view as `SubCircuit`'s size. The MiniZinc front end posts
an offset view on every successor whose index set does not start at 0; at
offset 0, `zero_based()` hands over the plain variable, and constants stay
constants (`variable_id.cc:9–16`). The proofs handle views: `circuit_test`,
`subcircuit_test` and the scenario tests all run their `view_mixed` and
`view_mixed_late` lanes, and the fuzz below used offset views on a fifth of
its positions. **Constants** in the successor array are ordinary: the
Challenge's `cvrp` posts 36 in an array of 108, `vrplc` 15 and 20, and every
`mario` instance one, which is what once broke `SubCircuit`'s `SCC`
certificate (#812, fixed by #814). Two equal constants are left to the
propagators, which contradict at the root; with the GAC child, `AllDifferent`
reports them as "the same variable more than once", which is the right answer
under a wrong word.

### Reification

`None.` See the footnote above; nobody has asked for one.

### Relation to other families

- **Decomposes into it:** nothing in the solver. MiniZinc's `circuit` and
  `subcircuit` arrive at it, and XCSP3's `<circuit>`.
- **Child constraints:** the optional GAC `AllDifferent`, above. `prepare()`
  also narrows every successor with `define_bound`, which writes a model row
  and installs an initialiser, but posts no constraint.
- **Shares code with `all_different`.** `propagate_non_gac_alldifferent` and
  `NonGacAllDifferentUnassigned` (`all_different/vc_all_different.hh`), and
  `define_clique_not_equals_encoding` (`all_different/encoding.hh`), run inside
  every propagator here or write its encoding;
  [`all_different.md`](all_different.md) owns them and lists this family as a
  caller. **And with every user of `recover_am1_from_pairs`**
  (`innards/proofs/am1_from_pairs.hh`), which `SubCircuit`'s pigeonhole calls.
  Within the family, `circuit_base.cc` (`prevent_small_cycles`,
  `output_cycle_to_proof`) is shared by the two `Circuit` algorithms, and
  `SubCircuit` shares nothing with `Circuit` but the directory, the hint
  header and the two all-different helpers.
- **Not shared with the other graph families.** `path`, `tree`, `dag`,
  `reachable` and `subgraph` mention `Circuit` only in comments (`path.cc:57`,
  `tree.cc:60`), and none of them uses the position labelling. Their
  reachability proofs are the breadth-first unfolding of
  [`connectivity-proofs.md`](../connectivity-proofs.md), which `SubCircuit`
  deliberately does not use: it needs a labelling to count the tour.
- **Presolvers:** none reads or writes either class.
- **Reachable only by decomposition?** No: both are posted directly by
  MiniZinc and `.scp`, `Circuit` by `gcspy`, `SubCircuit` by XCSP3.

## The proof model

### OPB encoding

**`Circuit`**, Encoding Procedure 6.1 of McIlree's thesis, after Zhou. With
`pos[i]` a proof-only variable over `0..n-1` written in bits (`p[<k>_pos0]` in
the proof, every node's carrying the suffix `pos0`), and `c` the constraint's
ID:

```
define_clique_not_equals_encoding(succ)       n(n-1)/2 selector flags x[c][i_j],
                                              two rows each: succ[i] ≠ succ[j]
pos[0] ≤ 0
succ[0] = 0  ⇒ 0 = n - 1                      @c[c][pos_suc_0_0_le/ge]
succ[0] = j  ⇒ pos[j] = 1          (j ≥ 1)    @c[c][pos_suc_0_j_le/ge]
succ[i] = 0  ⇒ pos[0] - pos[i] = 1 - n (i ≥ 1) @c[c][pos_suc_i_0_le/ge]
succ[i] = j  ⇒ pos[j] - pos[i] = 1  (i, j ≥ 1) @c[c][pos_suc_i_j_le/ge]
```

each equality as a `≤` and a `≥` row half-reified on the edge literal. The
`i = j` rows say `succ[i] ≠ i`, and are written with `pos[i]` twice in one row
rather than simplified. **Definitional**: on a full assignment, unit
propagation from `pos[0] = 0` fixes every `pos` along the cycle through 0, and
fails exactly when that cycle is short, which is the thesis's argument for
checking (§6.3). **Size**: `n²` row pairs of `O(log n)` terms, the clique, and
`n` position variables of `⌈log₂ n⌉` bits. It does not grow with domain width,
because every successor's range is `0..n-1`.

**`SubCircuit`**, this solver's (`subcircuit.cc:1084–1208`). `pos[i]` over
`0..n-1` (`p[<k>_subpos]`), and `L = Σᵢ [succ[i] ≠ i]` the tour length as a sum
of literals, not a variable:

```
define_clique_not_equals_encoding(succ)
k = L                                         @c[c][tour_size_le/ge]  (with a size)
succ[i] = i ⇒ pos[i] ≤ 0                      @c[c][off_pos_i]
anchored on a:
  pos[a] ≤ 0                                  @c[c][anchor_pos]
  succ[i] = j ⇒ pos[j] - pos[i] = 1     (j ≠ a, i ≠ j)   @c[c][pos_step_i_j_le/ge]
  succ[i] = a ⇒ pos[a] - pos[i] + L = 1 (i ≠ a)          @c[c][pos_wrap_i_a_le/ge]
unanchored:
  first[i] ⇔ succ[i] ≠ i ∧ ⋀_{j<i} succ[j] = j            x[c][i][first], fully reified
  first[i] ⇒ pos[i] ≤ 0                       @c[c][first_pos_i]
  succ[i] = j ∧ ¬first[j] ⇒ pos[j] - pos[i] = 1      (every i ≠ j)   pos_step
  succ[i] = j ∧ first[j]  ⇒ pos[j] - pos[i] + L = 1  (every i ≠ j)   pos_wrap
```

The anchor is `with_required_node()`'s node, else the lowest-numbered node
whose own index is out of its successor's declared domain, else none
(`subcircuit.cc:1068–1074`). Off-tour nodes sit at position zero, so the
positions are not a permutation and `pos[x] ≥ 1` means "on the tour"; the
design note explains why that is load-bearing. **Definitional**, with one
deliberate exception the note argues for: the unanchored wrap rows exist so
that a closed cycle can bound `L` in a bounded derivation, not because the
meaning needs them. **Size**: anchored, `n(n-1)` row-pair families, `n − 1` of
them wrap rows, each `n` terms longer than a step row for carrying `L`;
unanchored, `2n(n-1)` families, half of them wrap rows, plus `n` first flags. So `O(n²)` rows either way, with `O(n³)`
terms unanchored and `O(n² log n)` anchored, the step rows carrying
bit-encoded positions. Independent of width.

### Labels

- **`pos_suc_i_j_le` / `_ge`**: `Circuit`'s position rows. The justifications
  cite them by line number (`PosVarData::plus_one_lines`), not by label; the
  labels are `cake_pb_cp`'s names, and the chain checks against them. Every
  rule that sums a cycle (rules 4 and 6) and every reachability argument
  (rules 7 to 13) uses these rows.
- **`pos_step_*`, `pos_wrap_*`, `anchor_pos`, `off_pos_i`, `first_pos_i`,
  `tour_size_le/ge`**: `SubCircuit`'s. Rules 14 and 15 cite the step and wrap
  rows by line number (`EdgePosLines`); `first_is_zero` is recorded and never
  read, and `anchor_pos`, `off_pos` and `first_pos` are reached only by unit
  propagation. The walks of rules 16 to 19 lean on the rows through unit
  propagation and cite nothing. Rules 20 to 23 are RUP against
  `tour_size_le/ge`. No consumer
  outside the solver reads these labels: `cake_pb_cp` has no `subcircuit`.
- **`c[id][i lt j]` / `[i gt j]`** and **`x[id][i_j]`**: the clique, as
  [`all_different.md`](all_different.md) documents.

### Cake conformity

**`Circuit`**: three chain cases, all `none` and all passing at `86caad24`:
`circuit_sat` (the two 3-node cycles), `circuit_unsat` (successors confined
to `{0, 1}`), and `circuit_aliased_unsat` (a repeated variable, #1047). They
chain-verify because the solver's writer emits cake's `(id circuit (succ...))`
and the row labels match cake's `pos_suc_*`; they stay `none` because the
successors' `=` and `≥` literal encodings still diverge (#358) and the position
variables are named differently. An extra case run by hand, `n = 1`, also
chain-verifies with its one solution.

**`SubCircuit`**: no chain case. `cake_pb_cp` rejects the keyword
("unsupported constraint: subcircuit"), so its certification ends at VeriPB
against the solver's own OPB.

### Proof-time state

- **At the root:** nothing for `Prevent` or `SubCircuit`. `Circuit`'s `SCC`
  writes, the first time any of its justifications needs a precedence flag,
  `Θ(n³)` lines recovering an all-different over the positions
  (`prove_pos_alldiff_lines`): at-least-one and at-most-one rows over every
  `pos[i] = j`, at `ProofLevel::Top`.
- **Kept for the rest of the proof** (`ProofLevel::Top`, cached so as never to
  be re-derived): `Circuit`'s precedence flags `d[r][i]` ("`pos[r] > pos[i]`",
  defined by redundance with a subproof that the two positions differ), its
  shifted-position flags `q[r][i]ge<k>` and `q[r][i]eq<k>` (the thesis's
  `dist(r, i)`), the "not both" pairs and the at-most-ones over them;
  `SubCircuit`'s per-value at-most-ones and at-least-ones, and its
  "no variable takes `c`" rows for pinned values (`SCCProofCache`).
- **Per call, at `ProofLevel::Current`**, so deleted on backtrack: `Circuit`
  `SCC`'s short-reason flag `sr` (one per propagator call while proofs are on,
  used or not; #1317), its ordering flags `ord1` and `ord2` for
  *prune skip*, and each layer's lemmas, which have to survive the layer that
  follows. Temporaries inside a derivation are at `ProofLevel::Temporary`.
- **Naming:** the flags above by their prefixes, the position variables by
  `pos0` / `subpos`, the first flags as `x[c][i][first]`. An external tool
  finds the position rows by label.
- **Proof-only auxiliaries determined on a solution:** yes. `Circuit`'s
  `pos` by unit propagation from `pos[0] = 0` along the tour; `SubCircuit`'s
  `pos` from the anchor or the fully reified `first` flag, with off-tour nodes
  at 0. The flags defined in the proof are extension variables and are not in
  `solx`.
- **A proof-only vector that dangles when proofs are off:** `_pos_var_data`
  and `_pos_data` are empty then, and both propagators expect that; the
  `SCCPersistentData` caches are reached only through a context built when a
  logger exists.

## The implementation

### Initialisation and global data

`prepare()`, both classes: `define_bound` each successor to `0..n-1`, which
writes a model row and installs an initialiser only when the declared domain
is wider (`propagators.cc:654–677`; its assertion carries the generic
`initial_bound` hint, not this family's); posts the GAC child if asked; and
allocates the backtrackable unassigned list the value consistent pass works
from. `Circuit` under `Prevent` also allocates its chain endpoints
(`PreventChainData`, four `n`-vectors), and only then, since every
constraint-state slot is copied at every search node. `SubCircuit::prepare()`
also settles the anchor, `O(n)` domain lookups.

`define_proof_model()` writes the encoding above, `O(n²)` rows; `SubCircuit`'s
unanchored form `O(n³)` terms. Nothing else is computed at the root, and no
shape makes the root dominate: at `n = 108` (`cvrp`) the `.opb` is written
once, and every per-call cost is below.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| `define_bound` initialisers | — | — | (not this family's: `initial_bound`) | a successor declared outside `0..n-1` | — | — |
| root contradiction | — | — | 1 | a repeated variable, either class | — | installed instead of everything below |
| `Circuit` no self loop | none: runs once | derived: **nothing** | 3 | `Circuit`, `n > 1` | yes, trivially | `DisableUntilBacktrack` at the root, so for the whole search |
| `Circuit` `SCC` | `on_change`, every successor | derived: **every successor** | 2, 4–13 | `circuit::SCC` (default) | not claimed | never |
| `Circuit` `Prevent` | `on_instantiated`, every successor | derived: **nothing** | 2, 4–6 | `circuit::Prevent` | **claimed** (`EnableButIdempotent`) | never |
| `SubCircuit` main | `on_instantiated`; under `Prevent` also a refined watch on each `succ[i] ≠ i`; under `SCC` with an anchor, `on_change` instead | derived: **nothing** under `Check`; **every successor** otherwise | 2, 14 (`Check`); 15 (`Prevent`, `SCC`); 16–19 (`SCC` with an anchor) | always | not claimed | never |
| `SubCircuit` tour size | `on_change` successors, `on_bounds` size | derived: **every successor**, not the size | 20–23 | `with_tour_size()` | not claimed | never |

**The holes column is accurate as derived, in every row.** `Circuit`'s
`Prevent` and `SubCircuit`'s `Check` read nothing but fixed successors (the
value consistent pass, the chain walk, `optional_single_value`), so
`on_instantiated` tells the truth. `SubCircuit`'s lookahead needs an evidence
node, one whose own index has left its domain, which is usually an interior
value; until #998 it woke only on instantiation and missed those (#966), and
now the refined watch on `succ[i] ≠ i` wakes it on exactly that removal. The
watch is not on a bound literal, so the derived declaration includes every
successor. `SCC` in either class walks whole domains, and the tour-size
propagator reads `in_domain(succ[i], i)` and only the size's bounds. Checked
with the analysis itself (`tmp/fd-graph/circuit/holes/holes.cc`, a probe
optional pruning on one successor or the size): needed under `Circuit` `SCC`,
`SubCircuit` `Prevent`, `SCC` with and without an anchor and the tour-size
propagator; not needed under `Circuit` `Prevent` or `SubCircuit` `Check`, nor
for the size.

**Idempotence.** `Circuit`'s `Prevent` alternates the value consistent pass
and the chain fold until a fold fixes no successor
(`circuit_prevent.cc:110–115`), so a re-run finds nothing, and claims it. The
claim held under the engine's checker (`GCS_CHECK_IDEMPOTENT_CLAIMS=1`) on
2,000 random instances, full search each, and under every test that uses
`solve_for_tests`. Nothing else claims. `SubCircuit`'s main propagator says
why in a comment: forcing a node off the tour fixes a successor, which changes
the chain structure the pass walked. `Circuit`'s `SCC` does not claim either,
and a forced back edge or a pruned edge changes the graph its walk saw, so a
second call can find more.

### Mutable state and incrementality

- **The unassigned list** (`NonGacAllDifferentUnassigned`), backtrackable, in
  every propagator: the value consistent pass's worklist, swap-and-pop.
- **`Prevent`'s chain endpoints**, backtrackable: `orig`, `dest`, `len` and
  the list of nodes whose fixed edge is not yet folded in. Each newly fixed
  edge is folded in `O(1)`; a pass over the unfolded list is `O(n)`.
- **`Circuit` `SCC`'s proof caches** (`SCCPersistentData`), not backtrackable
  and deliberately so: a proof line stays valid at every later node. Proof
  only.
- **`SubCircuit`'s proof cache** (`SCCProofCache`), likewise.

**Recomputed per call, that could be maintained.** `Circuit` `SCC` runs
Tarjan's walk from scratch, rebuilds two `n`-vectors, allocates a vector of
back edges per node visited, and re-walks every chain in
`prevent_small_cycles`; Gecode's propagator does the same walk over
region-allocated arrays. `SubCircuit` walks the fixed edges from scratch every call (a
comment says so and calls the incremental fold the obvious next step), and
its `SCC` arm rebuilds both reachability walks every call. A comment on
`with_prune_root()` (`subcircuit.hh:197–201`) records that the plain walk,
without shaving, was already 87–98% of all propagation time on the Challenge
`subcircuit` families, a figure from #788's development and not re-measured
here. And `Circuit` `SCC` materialises a
whole-scope reason on every call, proofs off too, which is the largest of
these that is not the algorithm: see [CPU performance](#cpu-performance)
(#1317).

### Interior values and optional pruning

**Offers.** `None.` Neither class installs an optional-interior-pruning pair;
neither has a consistency tag for `Auto` to resolve.

**Observes.** **Every successor's holes**, under `Circuit`'s default `SCC`,
under `SubCircuit`'s default `Prevent` and under its `SCC`, and through the
tour-size propagator; **nothing** under `Circuit`'s `Prevent` or
`SubCircuit`'s `Check`, whose whole vocabulary is fixed values. So a default
`Circuit` keeps another constraint's interior pruning on its successors alive
(`optional_interior_pruning_test`'s `tsp` case shows exactly this with
`Element`), and choosing `circuit::Prevent` releases it. The tour size is
observed only through its bounds.

### Robustness and limits

**Unbounded domains.** Fine for propagation: `prepare()` narrows every
successor to `0..n-1`, so no width survives into search, and `circuit_test` and
`subcircuit_test` each run a lane whose declared domains reach two either
side. A tour size's domain is not narrowed and need not be: only its bounds
are read, and the fuzz used sizes from −1 to `n + 1` with every proof
verifying.

**Negative values and zero.** Negative successors are narrowed away;
`output_cycle_to_proof` keeps a bug check for one surviving (#201, #810).
Index sets starting below zero arrive from MiniZinc as offset views and are
correct (the differential above).

**Degenerate shapes.**

- ***An empty `Circuit` crashes.*** With the default `SCC`, proofs off,
  `Circuit{}` is a segmentation fault: `SCCPropagatorData(0)` writes
  `lowlink[0]` of an empty vector (`circuit_scc.cc:81`). With proofs on,
  under either algorithm, `define_proof_model()` creates a position variable
  over `0..-1` (`circuit.cc:181`), which throws `IntegerOverflow: power2 63`
  before the read of `_succ[0]` at `:187` is reached; through the C++ API the
  exception is uncaught and the process aborts. `Prevent` without proofs gives
  the right answer. The `.scp` reader reaches it (`(_1 circuit ())` segfaults
  `glasgow_scp_solver --all`, and with `--prove` exits 1 with "Error:
  unexpected problem: Integer overflow: power2 63"),
  so does `gcspy`'s `post_circuit([])`, and so does the C++ API; MiniZinc's
  guard does not let it through. #254 audited empty arrays, and added the
  one- and two-node `Circuit` cases, not this one. `SubCircuit{}` is handled
  and tested. Probe: `tmp/fd-graph/circuit/empty/empty.cc` (#1307).
- *One node:* `Circuit` accepts the self loop, `SubCircuit` has the empty
  tour; see [Semantics](#semantics) for where the front ends disagree.
- *A repeated variable:* a root contradiction in either class, under every
  algorithm and with or without the GAC child (`circuit_dup_test`,
  `subcircuit_dup_test`, `solve_test`, two MiniZinc aliasing lanes, and the
  `circuit_aliased_unsat` chain case).
- *Constants:* see [Variable kinds](#variable-kinds-and-views).
- *`with_required_node()` on an interior hole:* rejected, #1228.

**Overflow.** Nothing to guard: every successor value and position in
either encoding is at most `n` in magnitude, the wrap rows' coefficients are
1, and the shifted-position flags multiply by `n`. The tour size is the
user's variable and may be wide, but it appears with coefficient 1 in one
row and is read only through its bounds. The bounded-range policy reaches this family only
through the views MiniZinc posts, whose offsets are index-set minima.

### Interval efficiency

**Fine at any width for propagation, because no width survives the root;
not for `SubCircuit`'s `SCC` proofs.** Every successor is
`define_bound`-ed to `0..n-1`, so a successor's domain has at most `n` values
and every per-value loop here is bounded by the node count. The large-domain
lane pins both rows `NoWidePosition` at `86caad24`; see point 4. This holds
for propagation, not for every proof: a successor declared wide makes
`SubCircuit`'s pigeonhole name every declared value (point 3).

1. **The propagation side.** Per-value walks everywhere, all bounded by `n`:
   `Circuit` `SCC`'s Tarjan walk and its small-cycle pass
   (`each_value_mutable`, `each_value_immutable` over successors);
   `SubCircuit`'s reachability layers, reverse graph and candidate snapshot
   (`for_each_walkable_value`); and the value consistent pass. None is over a
   domain wider than the array.
2. **The reason side.** Every reason is `generic_reason` over the whole
   successor array (plus the size, for the tour-size rules), one literal per
   fixed variable and two bounds plus one per hole run otherwise, and found one
   step per run (#935). `Circuit` `SCC` materialises it on every call,
   **unguarded** by `want_reasons()` and with proofs off
   (`circuit_scc.cc:1110`); everything else builds it at the inference site.
   Not minimal anywhere: see the rules.
3. **The proof side.** Per value. `Circuit`'s position at-least-ones and
   at-most-ones are over values `0..n-1`. `SubCircuit`'s pigeonhole names
   every value deliberately (`large-domains.md` records the exception), on the
   premise, in the comment at `subcircuit.cc:546–548`, that a successor's
   definition range is the node set. **That premise is false for a successor
   declared wide.** `need_value_at_least_one` (`subcircuit.cc:538–549`) takes
   each successor's at-least-one line, which has one term for every value of
   the **declared** range (`names_and_ids_tracker.cc:566–576`), each needing
   its own equality literal; `define_bound` has narrowed the domain but not
   the definition range. So under `subcircuit::SCC`, during search, the proof
   grows linearly in the declared width: on five nodes with two unreachable
   from the anchor, 452 proof lines at the node range, then 5,257, 50,257 and
   500,257 at declared widths of 100, 1,000 and 10,000, with the same four
   solutions and seven recursions and the same `.opb`; those at 100 and 1,000
   verify (`tmp/fd-graph/file/E16.txt`, measured for PR #1302's review at
   `86caad24`). Neither the guarded audit lane (point 4) nor a root-level
   proof survey sees it. Unfiled (held for Ciaran); PR #1302 records it in a
   comment and in `large-domains.md`. The fix is to name only the node values,
   or use #939's cover form.
4. **The audit lane.** Two rows, `Circuit` and `SubCircuit` over four plain
   variables in `0..3`, both pinned `NoWidePosition` at `86caad24`. They vary
   nothing. The audit case is registered as a ctest only under
   `-DGCS_LARGE_DOMAIN_GUARD=ON` (`gcs/CMakeLists.txt:212`), which no CI lane
   sets (#920), and this audit did not run a guarded build. PR #1302 (open)
   pins them `Clean`, with rows that declare the successors wide, as the safer
   choice, following Ciaran's decision ("whichever is safer until we have data
   that argues otherwise"), and does the same for every index-valued position
   (`Inverse`, `SymmetricAllDifferent`, `Tree`, `DTree`, `Path`, `DPath`,
   `Reachable`, `DReachable`, and wide-index rows for `Element`, `ArgSort`,
   `MinDistance` and `SeqPrecedeChain`); its guarded run trips nothing. The
   lane asserts no per-value work at the root with proofs off, so it cannot
   see the proof growth of point 3.

## Inference catalogue

Twenty-three rules: two shared by both classes (1, 2), eleven for `Circuit`
(3 to 13, of which 4 to 6 run under both algorithms and 7 to 13 only under
`SCC`), and ten for `SubCircuit` (14 to 23).

Facts that hold for all of them.

**No arm is generalised arc consistent, and none could be cheaply.** Enforcing
GAC on `Circuit` is NP-hard (it decides Hamiltonicity), and `SubCircuit`
contains it. So every **Strength** below is `partial`, and the measured gap is
per propagator, not per rule, because the rules only reach their fixpoint
together. Root fixpoints against a brute force over 2,000 random instances
each (`n` from 1 to 6, holey domains including −1 and `n`, a tenth of the
positions constants and a fifth offset views; seed 1;
`tmp/fd-graph/circuit/probes/circcheck.cc`, `fuzz1/`), instances with at least
one unsupported value left at the root, and how many such values:

| Configuration | Instances | Values |
|---|---|---|
| `Circuit`, `SCC` | 201 | 516 |
| `Circuit`, `SCC`, random knobs[^knobs] | 194 | 506 |
| `Circuit`, `Prevent` | 232 | 724 |
| `Circuit`, either algorithm, GAC child | 111 | 177 |
| `SubCircuit`, `Check` | 365 | 908 |
| `SubCircuit`, `Prevent` | 295 | 700 |
| `SubCircuit`, `SCC` | 273 | 556 |
| `SubCircuit`, `SCC`, prune root | 268 | 551 |
| `SubCircuit`, `SCC`, prune within | 252 | 454 |
| `SubCircuit`, `SCC`, both | 247 | 447 |
| `SubCircuit`, `SCC`, both, required node | 124 of 822 | 204 |
| `SubCircuit`, `Prevent`, tour size | 724 | 2,070 (541 of them the size's) |
| `SubCircuit`, `SCC`, tour size | 718 | 2,006 (530 the size's) |
| `SubCircuit`, `Prevent`, GAC child | 173 | 247 |

The required-node row checked only 822 instances: 782 drew no candidate, and
396 hit #1228's rejection. No configuration lost a solution or kept a
non-solution, in these 28,822 searches over fifteen configurations, nor in
10,000 more at seed 7 over five of them with the idempotence checker on, nor
in 4,600 with tour sizes reaching from −1 to `n + 1` (`fuzz3/`).
With proofs, seed 2, 300 instances per configuration (113 for the
required-node one, the rest drawing no candidate or hitting #1228): every
proof verifies with VeriPB 3.0.2 (`--force-checked-deletion`; `fuzz2/`).
**That is not true of every knob setting**: the random-knobs configuration
switched prune skip off in about half its instances and still never met the
rejection of #1306, which the fact-check found at 2 of 300 and 0 of 300
instances under default branching with prune skip off, and 9 of 300 under
random branching (`tmp/fd-graph/factcheck/circuit/b/r6/`); at the defaults it
found none in 600.

[^knobs]: Each instance drew prune root, prune skip, fix required, prune
    within, the at-most-one method and short reasons at random.

**The reason is the whole successor array** (`generic_reason(succ)`), plus the
size for rules 20 to 23, everywhere except the root contradiction (no reason)
and the bare units of rules 10 to 12 at the assertion levels. Under
`Circuit` `SCC` with short reasons on (the default), rules 7 to 13 state it
through one flag `sr`, defined per call as equivalent to it. Two literals per
unfixed successor and one per hole run, found one step per run; never
minimal; built at the inference site, except under `Circuit` `SCC`, which
builds it on every call (#1317).

**Hints.** `hints::Circuit` (`circuit`) and `hints::SubCircuit`
(`subcircuit`), each carrying only `originator`, the `ConstraintID`. The value
consistent pass's assertions carry `hints::AllDifferent` (`all_different`)
under this constraint's ID, and so do the GAC child's.

**Assertions.** At `AssertionLevel::Inferences`, the inferring rules (2 to
5, 13 to 23) assert `inferred literal ∨ ¬reason`, one `a` line per literal of
an `infer_all`; when the literal is already false that is the conflict, and
the line keeps the same shape, with the literal dropped if it is constant.
The explicit contradictions (rules 1, 6 to 9) assert `¬reason`, which for
rule 1 is empty. Rules 10 to 12 assert a bare unit, the *assertion reasons*
defect. Lines below were read off
real proofs at `Inferences` (`tmp/fd-graph/circuit/rules/`, `fire/`,
`assert/`), cut where marked `…`.

**Mutation lanes.** None in tree for this family. The design note records
hand-run mutations of the `SubCircuit` certificates at the time they were
written; they are cited per rule as history, not as lanes.

### Rule: duplicate-variable

- **Infers** — a contradiction, at the root.
- **Fires when** — the constructor finds the same non-constant variable in two
  slots, in either class (`circuit.cc:55–61`, `subcircuit.cc:974–980`); the
  root contradiction is installed instead of every propagator.
- **Strength** — `GAC` on this shape: there is no solution.
- **Algorithm** — `O(n²)` handle comparisons, once.
- **Why it is true** — the successors are all different in both classes.
- **Proof technique** — `RUP`: the clique's two rows for the pair collapse to a
  unit and its negation (JP 3.1's shape, Theorem 2.8).
- **Reason** — empty.
- **Assertion** — `a >= 1 ::circuit:((constraint_id _1));`, and the same with
  `subcircuit` (`chain/dupinf.pbp`, `subdupinf.pbp`).
- **Hint** — `hints::Circuit` / `hints::SubCircuit`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` The `circuit_aliased_unsat` chain case verifies
  it through `cake_pb_cp`.

### Rule: value-consistent-all-different

- **Infers** — for a newly fixed `succ[i] = v`, `succ[j] ≠ v` for every other
  `j`.
- **Fires when** — first in every propagator of both classes, each call.
- **Strength** — `partial`: the value consistent all-different; see
  [`all_different.md`](all_different.md), which owns the rule.
- **Algorithm** — `propagate_non_gac_alldifferent`, a worklist over newly
  fixed variables, `O(n)` per fixed variable.
- **Why it is true** — the successors are all different.
- **Proof technique** — `RUP`, JP 3.1, Theorem 2.8, against the clique.
- **Reason** — `{succ[i] = v}`, minimal.
- **Assertion** — `a 1 ~i[_2][eq0] 1 ~i[_3][eq0] >= 1
  ::all_different:((constraint_id _7));`, the `_7` being the `Circuit`
  (`fire/circuit_prune_root_test_inf.pbp`).
- **Hint** — `hints::AllDifferent`, with this constraint's ID.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — as `all_different.md` records.

### Rule: no-self-loop

- **Infers** — `succ[i] ≠ i`, every `i`.
- **Fires when** — once, at the root, `Circuit` with `n > 1`.
- **Strength** — `partial` (one unary consequence each).
- **Algorithm** — `n` inferences.
- **Why it is true** — a node pointing at itself closes a one-node cycle, which
  is a tour only when `n = 1`.
- **Proof technique** — `RUP` against the node's own position rows: for
  `i ≥ 1`, `succ[i] = i ⇒ pos[i] − pos[i] = 1` has an infeasible consequent;
  for `i = 0`, `succ[0] = 0 ⇒ 0 = n − 1`. Theorem 2.6.
- **Reason** — the whole-scope reason, though the conclusion needs none.
- **Assertion** — `a 1 ~i[s[0]][eq0] 1 ~i[s[0]][ge0] 1 i[s[0]][ge3] 1
  ~i[s[1]][ge0] 1 i[s[1]][ge3] 1 ~i[s[2]][ge0] 1 i[s[2]][ge3] >= 1
  ::circuit:((constraint_id _1));` (`rules/c_selfloop_inf.pbp`).
- **Hint** — `hints::Circuit`.
- **Offline reconstructibility** — `offline`: unit propagation on the model.
- **Proof size** — one line per node.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: prevent-forbid-closing

- **Infers** — `succ[e] ≠ s` for a chain of fixed edges from `s` to `e` with
  fewer than `n − 1` edges.
- **Fires when** — `Prevent`, when a newly fixed edge is folded in
  (`circuit_prevent.cc:67–82`, the inference at `:78`); `SCC`, in its
  from-scratch small-cycle pass after the component check
  (`circuit_base.cc:118–132`, the inference at `:127`).
- **Strength** — `partial`. Francis and Stuckey's *prevent*.
- **Algorithm** — `Prevent`: `O(1)` per folded edge, but each pass also
  scans the whole list of unfolded nodes, `O(n)`, after the value consistent
  pass. `SCC`: a walk of every chain from every value of every unfixed
  successor, `O(n + Σ|dom|)` per call.
- **Why it is true** — closing the chain makes a cycle of fewer than `n`
  nodes, which cannot be the single tour.
- **Proof technique** — `pol` then `RUP`: JP 6.1 (McIlree, McCreesh and
  Nordström; thesis §6.3). The `≥` halves of the chain's position rows and the
  closing edge's are summed (`output_cycle_to_proof`); the positions telescope
  to `0 ≥ k` under the edge literals, which then RUPs the conclusion. JP 6.1's
  precondition is a cycle of at least two edges in the current domains, which
  the chain and the candidate edge are.
- **Reason** — the whole-scope reason; the chain's fixed edges are what it
  needs.
- **Assertion** — `a 1 ~i[s[1]][eq0] 1 ~i[s[0]][eq1] 1 ~i[s[1]][ge0] 1
  i[s[1]][ge4] 1 i[s[1]][eq1] 1 ~i[s[2]][ge0] … >= 1
  ::circuit:((constraint_id _1));` (`rules/c_prevent_inf.pbp`). When the
  closing successor is a constant already equal to `s`, the literal drops out
  and the line is `¬reason`: with constants `succ[0] = 1` and `succ[1] = 0` the
  root asserts `a 1 ~i[s2][eq3] 1 ~i[s3][eq2] >= 1` (`c_prevent_contra_inf`).
- **Hint** — `hints::Circuit`.
- **Offline reconstructibility** — `offline`: the chain is readable off the
  reason's fixed literals, and JP 6.1 is then fixed.
- **Proof size** — one `pol` of `k + 1` terms and one RUP carrying the reason,
  per firing, `k` the chain length. On the 12-node enumeration below, 3,047
  firings under `SCC` and 4,522 under `Prevent`.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: prevent-force-closing

- **Infers** — `succ[e] = s` for a chain of fixed edges from `s` to `e` that
  visits every node.
- **Fires when** — as rule 4, when the chain has `n − 1` edges
  (`circuit_prevent.cc:85`, `circuit_base.cc:130`).
- **Strength** — `partial`.
- **Algorithm** — as rule 4.
- **Why it is true** — `e` must have a successor, every value but `s` is
  already some other node's successor, and the tour must close.
- **Proof technique** — `RUP` against the clique and the at-least-one row of
  `succ[e]`: every other value of `succ[e]` is a fixed successor in the reason.
- **Reason** — the whole-scope reason.
- **Assertion** — `a 1 i[_2][eq5] 1 ~i[_1][eq1] 1 ~i[_2][ge4] 1 i[_2][ge6] 1
  ~i[_3][eq3] 1 ~i[_4][eq0] 1 ~i[_5][eq2] … >= 1
  ::circuit:((constraint_id _10));` (`assert/fcx.pbp`). It fires: inside one
  fold, a forbidding inference can fix a successor before the value consistent
  pass runs again; 921 of 8,250 `circuit` assertions on 30 nine-node `Prevent`
  enumerations were positive equalities, which only this rule asserts
  (`assert/force/counts.txt`).
- **Hint** — `hints::Circuit`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: short-cycle-contradiction

- **Infers** — a contradiction.
- **Fires when** — a fixed edge closes a chain of fewer than `n` nodes into a
  cycle (`circuit_prevent.cc:58–64`, `circuit_base.cc:104–109`).
- **Strength** — `checker` on the closed part.
- **Algorithm** — as rule 4.
- **Why it is true** — a cycle on fewer than `n` nodes.
- **Proof technique** — `pol` then `RUP`, JP 6.1's check case; the `pol` is
  written only at `AssertionLevel::Off`.
- **Reason** — the whole-scope reason.
- **Assertion** — `¬reason`, from `contradiction()`. **It fires under the
  default `SCC`**, though no run of the audit itself saw it: `check_sccs`'s
  pruning can reduce a successor to one value after the value consistent pass
  has run, and `propagate_circuit_using_scc` then drops fixed variables from
  the unassigned list and calls the small-cycle pass without running that
  pass again (`circuit_scc.cc:1071–1083`), so a closed short cycle reaches the
  `j == j0` walk. The fact-check found it in 5 and 7 of 300 random-branching
  proofs at default settings, every one verifying; its reproducer
  (`tmp/fd-graph/factcheck/circuit/b/r6/rej.cc`, arguments `1 0 random
  460132016`) has rule 13 leave `succ[0] = 5`, closing `0 → 5 → 2 → 0`, and
  the `Contradicting sub-cycle` derivation follows. Under `Prevent` it fired in
  none of 300: there rule 4 forbids every closing edge as soon as its chain
  exists, after the value consistent pass of the same loop.
- **Hint** — `hints::Circuit`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one `pol` of `k` terms and the contradiction.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

The remaining `Circuit` rules run only under `SCC`, from one depth-first walk
from node 0 (`check_sccs`, `explore`), which is Gecode's and Francis and
Stuckey's: Tarjan's lowlinks, the subtrees hanging off the root, and
Carlsson's condition that each subtree after the first has a back edge into
the one before. All seven share one certificate, the thesis's `ReachTooSmall`
(JP 6.20, with Subprocedures 6.7 to 6.14 and 6.18 to 6.19): from a vertex `w`
whose reachable set in the reason's graph (optionally under one assumed edge,
and optionally under an ordering assumption) is smaller than `n`, derive by
layers that each of the first `|Reach(w)| + 1` shifted positions is held by a
reached node, and that each reached node holds at most one of them; the sum
is the pigeonhole. Positions relative to `w ≠ 0` are the thesis's
`dist(w, i)`, defined as flags `q[w][i]ge<k>` / `eq<k>` over precedence flags
`d[w][i]`, each introduced by redundance with a subproof that two positions
differ, which needs the `Θ(n³)` position all-different of
[Proof-time state](#proof-time-state). At-most-ones are by a `red` subproof
(the default) or a clique of pairs. Per firing: `O(n · Σ|dom|)` lines in the
worst case (a layer per reached node, a lemma per edge out of it), each
carrying the reason or `sr`; on the 12-node enumeration, 857 firings wrote
9,474 `Next implies` lemmas and 7,316 layer sums.

### Rule: scc-more-than-one

- **Infers** — a contradiction.
- **Fires when** — a vertex other than the root is the root of a strongly
  connected component (`explore`, lowlink equals visit number).
- **Strength** — `partial`: a contradiction on the current domains, which
  may be far from fixed.
- **Algorithm** — Tarjan's walk, `O(n + Σ|dom|)` per call.
- **Why it is true** — the tour visits every node from every node, so there is
  one component; this one cannot reach the root.
- **Proof technique** — `counting argument`, built as a `RUP sequence` of
  layer lemmas summed by `pol`, over flags introduced by `redundance`, with
  each at-most-one by `proof by contradiction` (the default) or a `pol` over
  pairs: JP 6.2, `ReachTooSmall` from the component's root. Thesis Chapter 6;
  McIlree, McCreesh and Nordström, CPAIOR 2024. The procedure's precondition
  is A1, a vertex whose reachable set in the reason's graph is smaller than
  `n`, which Tarjan's walk supplies.
- **Reason** — the whole-scope reason, through `sr`.
- **Assertion** — `a 1 ~f[36][sr] >= 1 ::circuit:((constraint_id _10));`
  (`fire/circuit_multiple_sccs_test_inf.pbp`): `¬sr`, where `sr` is defined in
  the proof as the reason.
- **Hint** — `hints::Circuit`.
- **Offline reconstructibility** — `search`: rerun Tarjan's walk on the graph
  the reason describes and take any vertex whose reachable set is too small;
  `O(n · (n + Σ|dom|))` at most, and nothing chosen beyond that vertex.
- **Proof size** — one `ReachTooSmall`. 19 firings on the 12-node enumeration.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` `circuit_multiple_sccs_test` and
  `circuit_disconnected_test` fire it and verify.

### Rule: scc-no-back-edge

- **Infers** — a contradiction.
- **Fires when** — a subtree of the root after the first has no edge back into
  the subtree before it.
- **Strength** — `partial`, as rule 7.
- **Algorithm** — as rule 7.
- **Why it is true** — the tour has to leave that subtree towards the earlier
  ones, and no edge does except edges that skip a subtree, which no tour can
  use (rules 11 and 12).
- **Proof technique** — as rule 7, JP 6.17, from the subtree's root. **JP
  6.17's precondition is that the skip edges have already been pruned**, and
  the code meets it only when `with_prune_skip` is on: rules 11 and 12 run in
  the same walk, before this rule, and their conclusions are in the database
  when `ReachTooSmall` needs them. With `with_prune_skip(false)` the rule
  still fires and the skip edges stay in the reason's graph; when one of them
  is a way out of the subtree, its reachable set is not too small and VeriPB
  rejects the derivation (#1306).
- **Reason** — the whole-scope reason, through `sr`.
- **Assertion** — `a 1 ~f[28][sr] >= 1 ::circuit:((constraint_id _9));`
  (`fire/circuit_no_backedges_test_inf.pbp`).
- **Hint** — `hints::Circuit`.
- **Offline reconstructibility** — `search`, as rule 7.
- **Proof size** — one `ReachTooSmall`.
- **Gaps** — at the defaults, `None.` With `with_prune_skip(false)`, a
  derivation VeriPB can reject (#1306), with prune skip the only
  change: two of the 13 rejected `circuit_random --no-prune-skip` proofs in
  the second fact-check fail inside `No back edges`, with fix required and
  prune root on (`tmp/fd-graph/factcheck2/circuit/cr/cr_10_54.pbp`,
  `cr_8_145.pbp`); the reproducer in #1306 reaches it with fix required and
  prune root off as well (`tmp/fd-graph/circuit/fc/r3_000.pbp:1268`).
- **Tightness** — `Not shown.` `circuit_no_backedges_test` fires it with
  prune skip off and live skip edges (`5 → 0`, `6 → 0`, `6 → 3`), which the
  derivation walks; it verifies because no domain contains node 7, so every
  reachable set misses 7 whatever the skip edges do. It runs rule 8 with skip
  edges present, but it cannot catch #1306.

### Rule: scc-disconnected

- **Infers** — a contradiction.
- **Fires when** — the walk from node 0 reaches fewer than `n` nodes.
- **Strength** — `partial`, as rule 7.
- **Algorithm** — as rule 7.
- **Why it is true** — the tour reaches everything from node 0.
- **Proof technique** — as rule 7, JP 6.3, from node 0, where positions need no
  shifting.
- **Reason** — the whole-scope reason, through `sr`.
- **Assertion** — `a 1 ~f[6][sr] >= 1 ::circuit:((constraint_id _5));`
  (`rules/c_scc_contra_disconnected_inf.pbp`).
- **Hint** — `hints::Circuit`.
- **Offline reconstructibility** — `offline`: from node 0, fixed.
- **Proof size** — one `ReachTooSmall`; 502 firings on the 12-node
  enumeration.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` `circuit_prune_skip_test` fires it twice.

### Rule: scc-fix-required

- **Infers** — `succ[v] = u`, when exactly one edge `(v, u)` goes back from a
  subtree into the one before.
- **Fires when** — `with_fix_req` (on), and `succ[v]` not already fixed.
- **Strength** — `partial`.
- **Algorithm** — as rule 7.
- **Why it is true** — that edge is the subtree's only way back, edges that
  skip a subtree aside, and no tour can use those (rules 11 and 12).
- **Proof technique** — as rule 7, JP 6.16, `ReachTooSmall` under the
  assumption `succ[v] ≠ u`, run from `v`, the edge's tail
  (`circuit_scc.cc:1023–1024`), where the thesis runs it from the subtree's
  root. **Like rule 8, its precondition is that skip edges are already
  pruned**, which the code meets only with `with_prune_skip` on. With it
  off, the rule still fires and its derivation can be rejected (11 of the 13
  rejected `circuit_random --no-prune-skip` proofs in the second fact-check
  fail here): the fact-check's six-node instance
  (`tmp/fd-graph/factcheck/circuit/b/r6/rej2.cc`, default branching) finds its
  five solutions, and VeriPB rejects line 1356, a `Next implies` step inside
  the root's `Fix required back edge (2, 5)` derivation; the same instance
  verifies with prune skip on, and with prune skip and fix required both off
  and prune root on (`tmp/fd-graph/circuit/fc/r3_*`). #1306.
- **Reason** — at `Off`, the whole-scope reason through `sr`, inside the
  derivation, and the inference itself is recorded with `NoReason` and no
  justification, since the derivation has already written it. **At the
  assertion levels, no reason at all.**
- **Assertion** — at `Off` there is no `a` line: the derivation ends in a
  `pol` under the assumption, and the inference is recorded without a further
  line. At `Definitions`, `Links` and `Inferences`, **the bare unit**
  `a 1 i[_2][eq0] >= 1 ::circuit:((constraint_id _7));`
  (`fire/circuit_prune_root_test_inf.pbp`), because the assertion path passes
  `NoReason` (`circuit_scc.cc:1029`). The clause is not a consequence of the
  model: over 40 random nine-node enumerations, 5 of the 400 `circuit`
  assertions were falsified by a later `solx` in the same proof, every one a
  positive equality, so every one from this rule; none of `Prevent`'s 441 was,
  nor any of `SubCircuit`'s 998, though those were checked at `Inferences`
  only, and the fact-check found none of 225 falsified at `Links`
  (`assert/`, `probes/assertcheck.py`). VeriPB accepts them, since it does
  not check assertions. Deliberately unfiled
  (*assertion reasons*); the fix is to pass `reason` there, as rule 13 does.
- **Hint** — `hints::Circuit`.
- **Offline reconstructibility** — `search` once the assertion carries its
  reason: the subtree root and the edge are found by rerunning the walk. The
  bare unit the rule does assert at the assertion levels has no derivation.
- **Proof size** — one `ReachTooSmall`; 336 firings on the 12-node
  enumeration.
- **Gaps** — at the defaults and `Off`, `None.` With `with_prune_skip(false)`,
  a derivation VeriPB rejects (#1306). At the assertion levels,
  the assertion is wrong.
- **Tightness** — `Not shown.` `circuit_prune_root_test` fires it once.

### Rule: scc-prune-skip-to-root

- **Infers** — `succ[v] ≠ 0`, for `v` in a subtree after the first.
- **Fires when** — `with_prune_skip` (on), an edge into the root from a later
  subtree.
- **Strength** — `partial`.
- **Algorithm** — as rule 7.
- **Why it is true** — if `v` went to the root, the earlier subtree could not
  reach `v`'s subtree, nor the root without that edge.
- **Proof technique** — as rule 7, JP 6.4, `ReachTooSmall` from the previous
  subtree's root under the assumed edge.
- **Reason** — as rule 10: `sr` inside the derivation at `Off`; **none** at the
  assertion levels.
- **Assertion** — at the assertion levels, the bare unit `a 1 ~i[_5][eq0] >= 1
  ::circuit:((constraint_id _8));` (`fire/circuit_prune_skip_test_inf.pbp`),
  through `circuit_scc.cc:979`. Wrong in the same way as rule 10
  (*assertion reasons*), from a call site of the same shape (`:979`, shared
  with rule 12, against rule 10's `:1029`); the 40 enumerations above
  produced only one or two of these units, and none was seen falsified.
- **Hint** — `hints::Circuit`.
- **Offline reconstructibility** — `search` once the reason is passed, as
  rule 10.
- **Proof size** — one `ReachTooSmall`.
- **Gaps** — at `Off`, `None.` At the assertion levels, as rule 10.
- **Tightness** — `Not shown.` `circuit_prune_skip_test` (three firings) and
  `circuit_prune_root_test` (two).

### Rule: scc-prune-skip-subtree

- **Infers** — `succ[v] ≠ w`, for an edge from a node `v` in the subtree being
  explored to a node `w` visited before the previous subtree began
  (`circuit_scc.cc:963`): an edge that skips at least one subtree backwards.
- **Fires when** — as rule 11, for a target other than the root.
- **Strength** — `partial`.
- **Algorithm** — as rule 7.
- **Why it is true** — taking the edge would require visiting the root both
  between `w` and the skipped subtree's root and between that root and `v`.
- **Proof technique** — JP 6.15: two `ReachTooSmall`s under the assumed edge,
  each under an ordering flag (`ord1`, `ord2`, defined by `redundance`), then a
  `pol` combining the two with the position rows, and the conclusion by RUP
  (`prove_skipped_subtree`).
- **Reason** — as rule 10.
- **Assertion** — at the assertion levels, the bare unit `a 1 ~i[_7][eq3] >= 1
  ::circuit:((constraint_id _8));` (`fire/circuit_prune_skip_test_inf.pbp`).
  Wrong as rule 10.
- **Hint** — `hints::Circuit`.
- **Offline reconstructibility** — `search`, over which subtree is skipped, a
  choice the walk determines.
- **Proof size** — two `ReachTooSmall`s, two flags and five more lines.
- **Gaps** — at `Off`, `None.` At the assertion levels, as rule 10.
- **Tightness** — `Not shown.` `circuit_prune_skip_test` fires it once.

### Rule: scc-prune-root

- **Infers** — `succ[0] ≠ w` for `w` in any subtree but the last.
- **Fires when** — `with_prune_root` (on), the root has more than one subtree.
- **Strength** — `partial`.
- **Algorithm** — as rule 7, plus a pass over the root's domain.
- **Why it is true** — `w` can reach only its own subtree and earlier ones, and
  with the root's edge spent on `w` nothing reaches the later subtrees.
- **Proof technique** — JP 6.5, `ReachTooSmall` from node 0 under the assumed
  edge.
- **Reason** — the whole-scope reason, through `sr`, at every level.
- **Assertion** — `a 1 ~i[_1][eq1] 1 ~f[15][sr] >= 1
  ::circuit:((constraint_id _7));` (`fire/circuit_prune_root_test_inf.pbp`).
- **Hint** — `hints::Circuit`.
- **Offline reconstructibility** — `offline`: from node 0, under the asserted
  edge.
- **Proof size** — one `ReachTooSmall`.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` `circuit_prune_root_test` fires it twice.

The `SubCircuit` rules' certificates are described at length in
[`subcircuit-proof-logging.md`](../subcircuit-proof-logging.md); what follows
states each one's shape. **No published procedure covers them**: they are this
solver's, and their soundness is argued in **Why it is true** and in the note.

### Rule: sub-closed-cycle

- **Infers** — `succ[m] = m` for every node `m` off a closed cycle of two or
  more fixed edges, as one `infer_all`.
- **Fires when** — the fixed-edge walk finds such a cycle, any algorithm
  (`subcircuit.cc:879–895`).
- **Strength** — `partial`. Francis and Stuckey's *check*. With an anchor off
  the cycle, one of the literals is `succ[a] = a`, already false, so the rule
  is a contradiction.
- **Algorithm** — the walk, `O(n)` per call, from scratch.
- **Why it is true** — a closed cycle is the whole tour, so nobody else is on
  it.
- **Proof technique** — `pol` then `RUP`, ours (`derive_tour_at_most`).
  Anchored, one `pol`: the cycle's step rows, with the wrap row for the edge
  into the anchor if the cycle contains it, telescope to `L ≤ k` (or `0 ≥ k`
  when it does not). Unanchored, `k + 2` `pol`s: the all-step sum, one per
  candidate first node, and one combining them so that the `first` flags
  resolve away. Then each conclusion by RUP against `L ≤ k` and the
  membership literals.
- **Reason** — the whole-scope reason.
- **Assertion** — one line per forced node: `a 1 i[s[2]][eq2] 1 ~i[s[0]][eq1]
  1 ~i[s[1]][eq0] 1 ~i[s[2]][ge2] 1 i[s[2]][ge4] 1 ~i[s[3]][ge2] 1 i[s[3]][ge4]
  >= 1 ::subcircuit:((constraint_id _1));` (`rules/sub_check_inf.pbp`,
  unanchored).
- **Hint** — `hints::SubCircuit`.
- **Offline reconstructibility** — `offline`: the cycle is in the reason and
  the anchor in the model.
- **Proof size** — anchored, one `pol` of `k` terms; unanchored, `k + 2` of `k`
  each, `O(k²)` terms; plus one RUP per forced node.
- **Gaps** — `None.`
- **Tightness** — `Not shown` as a lane. The design note records that, at the
  time, replacing the certificate with a plain `RUP` was rejected by VeriPB at
  `n = 5` with the seed pinned, and passed at `n = 3` and `4`.

### Rule: sub-prevent-closing

- **Infers** — `succ[e] ≠ s` for a chain of fixed edges from `s` to `e`, when
  some node off the chain is known to be on the tour.
- **Fires when** — `Prevent` and `SCC`; the evidence node is the
  lowest-numbered node off the chain whose own index has left its domain
  (`subcircuit.cc:946–963`).
- **Strength** — `partial`. Francis and Stuckey's *prevent*.
- **Algorithm** — `O(n)` per chain to find evidence, so `O(n²)` per call at
  worst.
- **Why it is true** — closing the chain would make it the whole tour,
  stranding the evidence node, which cannot point at itself.
- **Proof technique** — as rule 14: `derive_tour_at_most` over the chain plus
  the closing edge, then RUP, where the evidence node's missing own index is
  in the reason.
- **Reason** — the whole-scope reason.
- **Assertion** — `a 1 ~i[_6][eq3] 1 ~i[_1][ge0] 1 i[_1][ge8] 1 i[_1][in4_5] …
  >= 1 ::subcircuit:((constraint_id _5));`, stopping `3 → 4 → 5` from closing
  (`fire/subcircuit_prevent_test_w0_pall.pbp`).
- **Hint** — `hints::SubCircuit`.
- **Offline reconstructibility** — `offline`: chain and evidence are in the
  reason.
- **Proof size** — as rule 14.
- **Gaps** — `None.`
- **Tightness** — `Not shown` as a lane; the same historical probe as rule 14.

### Rule: sub-unreachable-from-anchor

- **Infers** — `succ[m] = m` for every node the anchor cannot reach, as one
  `infer_all`.
- **Fires when** — `SCC` with an anchor (`subcircuit.cc:902–907`).
- **Strength** — `partial`, the forward half of Francis and Stuckey's rule for
  the component containing a required node.
- **Algorithm** — `reachable_layers`: `n` layers, each a pass over the reached
  nodes' domains, `O(n · Σ|dom|)` per call, from scratch, with an `n × n`
  table.
- **Why it is true** — the tour is a cycle through the anchor, so everything
  on it is reachable from the anchor.
- **Proof technique** — `RUP sequence` with one `counting argument`, ours
  (`derive_unreachable`): for each layer `t` and unreached `x`, the lemma
  `pos[x] = t ⇒ succ[x] = x`, from one RUP per candidate predecessor and the
  pigeonhole "somebody takes value `x`", derived once per value at
  `ProofLevel::Top` (`need_value_at_least_one`, over `recover_am1_from_pairs`'
  at-most-ones, each pinned by an `ia` step, with constants counted
  separately, #812).
- **Reason** — the whole-scope reason, in every lemma.
- **Assertion** — one line per forced node: `a 1 i[_1][eq0] 1 ~i[_1][ge0] 1
  i[_1][ge2] 1 ~i[_2][ge1] 1 i[_2][ge3] … >= 1
  ::subcircuit:((constraint_id …));` (`fire/subcircuit_scc_test_scc_w0_pall.pbp`).
- **Hint** — `hints::SubCircuit`.
- **Offline reconstructibility** — `offline`: the walk is fixed by the reason
  and the anchor.
- **Proof size** — up to `n²` layer facts with up to `n` candidate lemmas each,
  so `O(n³)` lines, each carrying the reason. The pigeonhole is derived once
  per value and cached: each value's at-most-one is `m(m−1)/2` pairwise RUPs,
  `m` the non-constant successors, plus `recover_am1_from_pairs`' induction,
  and the first at-least-one pulls in `n − 1` of them, so `O(n²)` lines per
  value and `O(n³)` in all; only the final at-least-one `pol` has `O(n)`
  terms. The comment at `subcircuit_base.hh:71` says "O(n) rows per value",
  which is the `pol`, not the derivation. Each successor's at-least-one line in
  the pigeonhole has a term per value of its **declared** range, so a
  successor declared wide makes the proof grow linearly in the declared width
  during search (see [Interval efficiency](#interval-efficiency), point 3;
  unfiled, held for Ciaran).
- **Gaps** — `None.`
- **Tightness** — `Not shown` as a lane. Historically, a plain `RUP` in place
  of the walk, and dropping the pigeonhole, were both rejected.

### Rule: sub-cannot-reach-anchor

- **Infers** — `succ[m] = m` for every node that cannot reach the anchor.
- **Fires when** — `SCC` with an anchor, after rule 16, on the state it leaves.
- **Strength** — `partial`, the backward half.
- **Algorithm** — `reaches_anchor`: a reverse graph and one backward search,
  `O(n + Σ|dom|)`.
- **Why it is true** — everything on the tour reaches the anchor back.
- **Proof technique** — `RUP sequence`, ours (`derive_cannot_reach_anchor`):
  `pos[x] = t ⇒ succ[x] = x` for `t` from `n − 1` down, from one RUP per
  candidate successor; every fact used is a model row, so no counting.
- **Reason** — the whole-scope reason.
- **Assertion** — `a 1 i[_1][eq0] 1 ~i[_1][ge0] 1 i[_1][ge2] … 1 ~i[_8][ge0] 1
  i[_8][ge12] … >= 1 ::subcircuit:((constraint_id …));`
  (`fire/subcircuit_scc_reaches_anchor_test_scc_w0_pall.pbp`, where only the
  backward walk can fire).
- **Hint** — `hints::SubCircuit`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — `O(n³)` lines at worst, as rule 16, without the pigeonhole.
- **Gaps** — `None.`
- **Tightness** — `Not shown` as a lane; historically as rule 16.

### Rule: sub-prune-root

- **Infers** — `succ[a] ≠ v`, for the anchor `a`, when assuming the edge
  `a → v` would strand a node that must be on the tour, in either direction.
- **Fires when** — `SCC` with an anchor and `with_prune_root()` (off).
- **Strength** — `partial`: singleton arc consistency of the anchor's
  successor with respect to rules 16 and 17, which prunes at least what
  Francis and Stuckey's prune root does (their rule 3, explained by their
  clause 6; the code comment's "rule 6" mixes the two numberings).
- **Algorithm** — one forward walk, and if that strands nothing one backward
  walk, per candidate value: `O(n² · Σ|dom|)` per call at worst.
- **Why it is true** — rules 16 and 17 under the assumed edge.
- **Proof technique** — rule 16's or 17's sequence with `succ[a] ≠ v` added to
  every row as a guard, then the conclusion by RUP.
- **Reason** — the whole-scope reason, judged against the domains the pass
  started from; the note argues why a narrower later state only strengthens
  it.
- **Assertion** — `a 1 ~i[succ0][eq1] 1 ~i[succ0][ge1] 1 i[succ0][ge5] 1
  i[succ0][in2_3] … >= 1 ::subcircuit:((constraint_id …));`
  (`fire/subcircuit_prune_root_test_scc_prune_root.pbp`).
- **Hint** — `hints::SubCircuit`.
- **Offline reconstructibility** — `offline`: the assumed edge is the negated
  conclusion.
- **Proof size** — rule 16's or 17's, plus one guard literal per row. The note
  measured, at its time, 1.0 to 3.7 times `SCC`'s proof on complete
  enumerations.
- **Gaps** — `None.`
- **Tightness** — `Not shown` as a lane. Historically, dropping the guard was
  caught by `subcircuit_prune_root_test`, `subcircuit_prune_within_test` and
  the anchored sweep in `subcircuit_test`.

### Rule: sub-prune-within

- **Infers** — `succ[m] ≠ v`, for every node `m` other than the anchor, by the
  same shave.
- **Fires when** — `SCC` with an anchor and `with_prune_within()` (off).
- **Strength** — `partial`, as rule 18, over every successor.
- **Algorithm** — rule 18's per node: `O(n³ · Σ|dom|)` per call at worst.
- **Why it is true** — as rule 18.
- **Proof technique** — as rule 18.
- **Reason** — as rule 18.
- **Assertion** — `a 1 ~i[succ2][eq1] 1 ~i[succ0][ge2] 1 i[succ0][ge7] 1
  i[succ0][in4_5] … >= 1 ::subcircuit:((constraint_id …));`
  (`fire/subcircuit_prune_within_test_scc_prune_within.pbp`).
- **Hint** — `hints::SubCircuit`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — as rule 18, per pruned value. The note measured 13 to 95
  times `SCC`'s proof on complete enumerations from 6 to 11 nodes, every one
  verifying.
- **Gaps** — `None.`
- **Tightness** — as rule 18.

### Rule: size-lower

- **Infers** — `k ≥ on`, `on` the number of nodes whose own index has left
  their domain.
- **Fires when** — the tour-size propagator, every call.
- **Strength** — `partial` on `k`: it does not know `k ≠ 1`, deliberately
  (`subcircuit.cc:258–261`), nor anything a tour's feasibility implies.
- **Algorithm** — `O(n)`.
- **Why it is true** — each such node is on the tour.
- **Proof technique** — `RUP` against `tour_size_le/ge`, Theorem 2.9.
- **Reason** — the whole-scope reason over the successors and `k`.
- **Assertion** — `a 1 i[k][ge2] 1 ~i[s0][ge1] 1 i[s0][ge4] 1 ~i[s1][ge0] 1
  i[s1][ge4] 1 i[s1][eq1] … 1 ~i[k][ge0] 1 i[k][ge5] >= 1
  ::subcircuit:((constraint_id _5));` (`rules/sub_size_bounds_inf.pbp`).
- **Hint** — `hints::SubCircuit`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: size-upper

- **Infers** — `k ≤ n − off`, `off` the number of fixed self loops.
- **Fires when** — as rule 20.
- **Strength** — `partial`, as rule 20. Over 2,000 random instances, 541 of
  the 2,070 unsupported values at the root are the size's.
- **Algorithm** — `O(n)`.
- **Why it is true** — those nodes are off the tour.
- **Proof technique** — `RUP` against `tour_size_le/ge`.
- **Reason** — as rule 20.
- **Assertion** — `a 1 ~i[k][ge3] 1 ~i[s0][eq1] 1 ~i[s1][eq0] 1 ~i[s2][eq2] 1
  ~i[s3][eq3] 1 ~i[k][ge2] 1 i[k][ge5] >= 1 ::subcircuit:((constraint_id _5));`
  (`rules/sub_size_bounds_inf.pbp`).
- **Hint** — `hints::SubCircuit`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: size-force-off

- **Infers** — `succ[m] = m` for every undecided node, when `ub(k) = on`.
- **Fires when** — as rule 20.
- **Strength** — `partial`.
- **Algorithm** — `O(n)`.
- **Why it is true** — no room is left on the tour.
- **Proof technique** — `RUP` against `tour_size_le/ge`.
- **Reason** — as rule 20.
- **Assertion** — `a 1 i[s2][eq2] 1 ~i[s0][ge1] 1 i[s0][ge4] … 1 ~i[k][eq2] >=
  1 ::subcircuit:((constraint_id _5));` (`rules/sub_size_off_inf.pbp`).
- **Hint** — `hints::SubCircuit`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per node.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: size-force-on

- **Infers** — `succ[m] ≠ m` for every undecided node, when `lb(k) = n − off`.
- **Fires when** — as rule 20.
- **Strength** — `partial`.
- **Algorithm** — `O(n)`.
- **Why it is true** — everyone not already off has to be on.
- **Proof technique** — `RUP` against `tour_size_le/ge`.
- **Reason** — as rule 20.
- **Assertion** — `a 1 ~i[s[1]][eq1] 1 ~i[s[0]][eq0] 1 ~i[s[1]][ge0] … 1
  ~i[k][eq3] >= 1 ::subcircuit:((constraint_id _1));`
  (`rules/sub_size_inf.pbp`).
- **Hint** — `hints::SubCircuit`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per node.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

- **`circuit_test`**: both algorithms, full domains `0..n-1` at `n = 3, 4, 5`
  and the degenerate `n = 1, 2` (#254), plus a lane whose declared domains run
  from −2 to `n + 1` (#201, #810), each enumerated against a brute force under
  plain `solve_for_tests` (no per-node consistency check), with and without
  proofs. `view_mixed` and `view_mixed_late` lanes.
- **`circuit_*_test` scenario tests** (`disconnected`, `multiple_sccs`,
  `no_backedges`, `prune_root`, `prune_skip`): hand-built graphs of six to
  nine nodes under `SCC`, each solved once with a proof that VeriPB must
  accept. They compare no
  solution set. What each fires, read off its proof at `86caad24`:
  `disconnected` and `multiple_sccs` rule 7 (not rule 9, whatever the name);
  `no_backedges` rule 8; `prune_root` rules 10, 11, 13 and 4; `prune_skip`
  rules 9, 11, 12 and 4.
- **`circuit_dup_test`, `subcircuit_dup_test`, `solve_test`**: a repeated
  variable, every algorithm, with and without the GAC child.
- **`subcircuit_test`**: `Check` and `Prevent` over full domains up to
  `n = 5`, the empty array, wide declared domains, tour sizes over ranges
  (XCSP3's "at least two" among them), and anchored sweeps, named and found,
  under every algorithm (`SCC` runs only here, since without an anchor it is
  `Prevent`), at `n = 3, 4, 5` with the anchor at 0 or at `n − 1` only
  (`subcircuit_test.cc:358–359`), which is the gap #1228 came through; all
  against a brute force under `solve_for_tests`; and view lanes.
- **`subcircuit_*_test` scenario tests**: `scc`, `scc_reaches_anchor`,
  `prune_root` and `prune_within` are each built so that one rule is the only
  route to a root state the test asserts, the design note's lesson that
  recursion counts alone show nothing; `scc` and `scc_reaches_anchor` also
  enumerate their 325 solutions. `constant` asserts solution counts (2, and 0
  for its counting scenario), and its eight-node fixture was generated to
  fail under one specific mutation (#812). `prevent` asserts neither a root
  state nor a solution set: it prints solutions and verifies the proof, and
  its header says it is no longer the mutation test.
- **`hole_wakes_test`**: `SubCircuit`'s lookahead woken by a hole punched by
  another propagator, directly and through an offset view, across a backtrack
  (#966, #998).
- **`optional_interior_pruning_test`**: the `tsp` shape, where a default
  `Circuit` observes its successors' holes.
- **`scp_reader_test`**: both keywords enumerate; `subcircuit` with a size
  survives a write–read–write round trip and still constrains.
- **Chain**: `scp_chain_circuit_sat`, `_unsat`, `_aliased_unsat`.
- **MiniZinc**: `minizinc-circuit` (0-based), `-subcircuit` (0-based),
  `-subcircuit-evidence` (1-based, a pinned node), `-circuit-aliased`,
  `-subcircuit-aliased`; each with `--fzn-pattern` on the builtin, without
  which it would pass against the decomposition.
- **XCSP3**: `xcsp_circuit`, `_size`, `_size_var`, against ACE's cached
  solutions.
- **Examples**: `circuit_small`, `circuit_random`,
  `circuit_random-gac-all-different` (#651) and `tour`, with VeriPB.
- **Audit lane**: the two `NoWidePosition` rows, registered as a ctest only
  under `-DGCS_LARGE_DOMAIN_GUARD=ON`, which no CI lane sets (#920); see
  [Interval efficiency](#interval-efficiency) for PR #1302's re-pin.

**Runtime caps.** No lane in this family sets or clears a cap, and the
default caps **never fire** on it: every family binary, bare and in both view
lanes, under `GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500` and
`--seed=1` at `86caad24`, reports no truncated run
(`tmp/fd-graph/circuit/tests/`). The largest enumeration under the caps is
`subcircuit_test`'s 85 solutions at `n = 5`; the scenario tests call
`solve_with` directly and are not capped at all, which is how `subcircuit_scc_test`
and `subcircuit_scc_reaches_anchor_test` enumerate 325 solutions each. So the
capped run checks exactly what the uncapped one does. `subcircuit_test` takes
1.8 s with VeriPB on the path, the two 325-solution tests 1.4 s bare and
3.3 s in their view lanes, and everything else under half a second. All
seeded.

**Tightness:** no mutation lane; see the catalogue's preamble.

**What the tests do not cover.**

- **Holey domains in an enumeration.** `circuit_test` and `subcircuit_test`
  enumerate full domains; holes come only from the scenario tests' `In`
  constraints and from search. The audit's fuzz covered holey random domains,
  constants and views against a brute force (no failure), but nothing in tree
  does, nor checks the root fixpoint against GAC.
- **The empty `Circuit`**, which crashes (#1307).
  `subcircuit_test` has the empty case; `circuit_test` stops at one node.
- **The assertion levels.** No lane runs any of this family at
  `Definitions`, `Links` or `Inferences` and checks the asserted clauses,
  which is how rules 10 to 12's bare units went unnoticed.
- **Whether the `Circuit` scenario tests fire their rules.** They check only
  that the proof verifies; `circuit_disconnected_test` fires a different rule
  from the one its name gives, and nothing would notice if a rule stopped
  firing.
- **Rule 6** fires in no in-tree test; the fact-check reached it only with
  random branching.
- **#1306's knob setting.** `circuit_no_backedges_test` runs rule 8 with
  prune skip off and skip edges live, but its instance is infeasible for
  another reason (no node has 7 as a successor), so the skip edges never
  decide the argument; and nothing runs rule 10 with prune skip off.
- **Enumerations beyond five nodes** in tree. The `Circuit` scenario tests
  have six to nine nodes and the `SubCircuit` ones up to twelve, one instance
  each, and the `circuit_random` and `tour` examples are larger.
- **`gcspy`**, which is not built in CI's default configuration either.

### Benchmarks and examples

- **In the repository:** `examples/circuit_small`, `examples/circuit_random`
  (random TSP, `Circuit` with every knob exposed), `examples/tour` (a
  20-location bottleneck tour on a sparse graph, after Francis and Stuckey's
  circuit benchmarks: minimise the longest leg), and `minicp_benchmarks/tsp` (`gr17`, `Circuit` and one `Element` per
  node, `Prevent` by default).
- **Corpus:** in the MiniZinc Challenge repository
  (`mzn-challenge-a8448864`), 25 model directories mention `circuit` or
  `subcircuit`; 22 have data, and 20 of those flatten with this audit's
  `glasgow.msc`, first data file each (`tmp/fd-graph/circuit/corpus/`;
  `2009/p1f` declares its own `circuit`, which clashes with the library's,
  and `2021/yumi-dynamic` fails to flatten). Fourteen post
  `glasgow_circuit`: `p1f` and `p1f-pjs` 36 to 55 posts of 10 to 12 nodes,
  `cvrp` 2015 two of 108 with 36 constants, `vrplc` 60 and 80 nodes, `tsptw`
  2025 101, `is` three models of 6 to 25 nodes with offset 0, `yumi` three of
  21 to 23, `vrp-submission` two of 16. Five post `glasgow_subcircuit`:
  `mario` (15 and 30 nodes, one constant each) and
  `tpp` (9 and 20). `2023/multi-agent-graph-coverage` posts neither.
- **Where the family dominates** (20 s runs, `GCS_PROPAGATOR_STATS=time`, its
  share of propagation time): `p1f` 2015 62%, `p1f-pjs` 2021 61% and 2020 57%,
  `vrplc` 2023 58% and 2018 53%, `cvrp` 2015 46% (43 µs a call at 108 nodes),
  `mario` 2017 43% (4.1 µs a call), `tsptw` 2025 40% (46 µs a call),
  `vrp-submission` 2021 31%. Negligible on `tpp`, `is` and `yumi`.
- **For CPU:** `p1f-pjs` 2020, which solves to optimality in 7 s with
  `Circuit` 57% of propagation; `tsp` for a single larger `Circuit`; the
  Hamiltonian enumeration below against Gecode.
- **For proof verification:** the Hamiltonian enumeration at 10 to 14 nodes
  (0.3 to 43 s to check), and the design note's cut-down `mario` for
  `SubCircuit`. Prune within, with proofs, must not be run on complete
  enumerations above about 11 nodes: the note records 10.8 GB of proof at 12
  before it was abandoned.

### CPU performance

*Release build of `86caad24` (GCC 15.2.0, `-O3 -march=native`); Gecode 6.3.0,
static; fataepyc-10, `taskset -c 8`, fixed malloc thresholds; 2026-10-09.*

**Against Gecode, on Hamiltonian-cycle enumeration.** A random digraph with a
planted Hamiltonian cycle, each other arc present with the given probability,
all cycles enumerated, input order, smallest value first
(`tmp/fd-graph/circuit/bench/ham_gcs.cc`, `ham_gecode.cc`, `graph.hh`).
Median of three runs, whole solve, proofs off. Gecode's `IPL_VAL` circuit runs
the same depth-first rules as `Circuit`'s `SCC` (Carlsson's back-edge
condition, prune skip, fix required, prune root) but moves its root between
calls, and `IPL_DOM` adds a domain consistent all-different; so **the trees
differ**, and the nodes column is part of the comparison.

| n, arc % | Solutions | `SCC` | `Prevent` | `SCC` + GAC child | `Prevent` + GAC child | Gecode val | Gecode dom |
|---|---|---|---|---|---|---|---|
| 12, 30 | 1,936 | 0.057 s, 5,330 | 0.018 s, 5,786 | 0.051 s, 3,545 | 0.024 s, 3,545 | 0.011 s, 6,467 | 0.013 s, 4,305 |
| 14, 30 | 6,832 | 0.223 s, 17,932 | 0.066 s, 18,557 | 0.243 s, 14,883 | 0.110 s, 14,883 | 0.038 s, 20,533 | 0.054 s, 17,117 |
| 16, 25 | 13,941 | 0.753 s, 67,559 | 0.229 s, 77,806 | 0.567 s, 29,001 | 0.242 s, 29,001 | 0.152 s, 83,475 | 0.126 s, 34,591 |
| 18, 20 | 18,337 | 0.939 s, 64,723 | 0.270 s, 80,950 | 0.818 s, 39,377 | 0.324 s, 39,383 | 0.140 s, 67,199 | 0.157 s, 43,347 |

Second figure: GCS recursions, Gecode nodes. Per node at 16 nodes, `SCC`
costs 11.1 µs, `Prevent` 2.9 µs, Gecode's value propagator 1.8 µs and its
domain one 3.6 µs. Gecode's value propagator, with the same rules as `SCC`,
explores more nodes than either GCS algorithm from 12 to 16 nodes and falls
between them at 18 (its root moves between calls; `SCC`'s stays at node 0).
Per node, `Circuit`'s `SCC` takes about six times as long as Gecode's
equivalent. With the GAC child the two GCS algorithms explore the same tree up
to 16 nodes, so `SCC`'s rules add nothing to a domain consistent all-different
there, at 2.1 to 2.4 times the time from 12 to 16 nodes.

**The reason built on every call** (#1317). A/B against a
control: `circuit_scc.cc` copied unchanged, and the same copy with the reason
materialised only when a logger exists (`circuit_scc.cc:1110`, one line;
`tmp/fd-graph/circuit/ab/`), each linked ahead of the library into the same
binaries. Proofs off, so nothing reads the reason in either.

| Instance | Work | Control | Reason only with proofs | Instructions |
|---|---|---|---|---|
| Hamiltonian, 16 nodes, 25% | 67,559 recursions | 0.759–0.767 s | 0.601–0.617 s | −13.7% |
| `tsp` (`gr17`), `--propagator scc`, to proven optimum | 1,930,485 recursions | 54.4 s | 44.9 s | −11.4% |
| `p1f-pjs` 2020, to proven optimum | 25,729 nodes | 7.02–7.04 s | 5.84–5.91 s | −12.8% |
| `tsptw` 2025, first solution | 2,040 nodes | 2.95–2.97 s | 2.62–2.65 s | −7.1% |
| `cvrp` 2015, four solutions | 5,473 nodes | 4.94–5.01 s | 4.64–4.72 s | −3.7% |

Recursions, propagations and the printed solutions are identical in each
pair; five runs per arm for the enumeration, three for the corpus models, one
for `tsp`. The shipped binary measures the same as the control (0.755–0.785 s,
`tsp` 54.3 s). `Prevent` does not build it, and its `tsp` run barely moves:
29.2 s for the control and 28.8 s for the variant, one run each, with
147.29e9 instructions either way (`ab/tsp_ab.txt`). A profile of the enumeration under `SCC` puts the
domain-value coroutines (`each_value_*`) at about 18% self time and
`malloc`/`free` at about 10%, which is where the rest of the gap to Gecode is.

**What the benchmarks do not exercise.** `SubCircuit` beyond the design note's
`mario` and `tpp` sweeps, which this audit did not repeat; `Circuit`'s rule 6;
`SubCircuit`'s shaving rules on anything real.

### Proof performance

*Same build and machine; VeriPB 3.0.2 with `--force-checked-deletion`; the
Hamiltonian enumeration above, 30% arcs, seed 1, with proofs.*

| n | Algorithm | Lines, `Off` | Bytes, `Off` | VeriPB, `Off` | Bytes, `Inferences` | VeriPB, `Inferences` | `circuit` / `all_different` assertions |
|---|---|---|---|---|---|---|---|
| 8 | `SCC` | 5,018 | 273 KB | 0.06 s | 75 KB | 0.01 s | 30 / 169 |
| 8 | `Prevent` | 960 | 39 KB | 0.02 s | 37 KB | 0.01 s | 39 / 198 |
| 10 | `SCC` | 14,759 | 868 KB | 0.30 s | 445 KB | 0.04 s | 144 / 957 |
| 10 | `Prevent` | 3,474 | 160 KB | 0.12 s | 189 KB | 0.02 s | 153 / 1,023 |
| 12 | `SCC` | 285,086 | 19.08 MB | 11.0 s | 12.38 MB | 1.29 s | 3,904 / 22,442 |
| 12 | `Prevent` | 69,329 | 4.43 MB | 4.37 s | 5.56 MB | 0.92 s | 5,016 / 23,140 |
| 14 | `SCC` | 710,536 | 54.47 MB | 43.5 s | 47.07 MB | 6.70 s | 11,966 / 82,282 |
| 14 | `Prevent` | 230,935 | 15.48 MB | 20.0 s | 20.65 MB | 5.16 s | 15,174 / 84,809 |

The `.opb` is 117 KB at 12 nodes and 162 KB at 14. Every `Off` proof
verifies; every `Inferences` one is accepted under assertions. The assertion
column counts the `a` lines carrying each hint, both under this constraint's
ID; the rest are 5,330 to 18,557 backtracks, one `solx_block` per solution,
and a few `in` lines from the vector-built domains (24 at 12 nodes).
So at `Inferences`, the value consistent pass is two thirds of the proof's
assertions and the circuit rules a ninth to a seventh. `Prevent`'s
`Inferences` proof is the larger of its two at 10 nodes and more, because
every `a` line carries the whole-scope reason where the `Off` derivation's
lemmas are shorter.

**Own against shared**, by line shape (`probes/attribute.py`): on `SCC` at 12
nodes, the short-reason flag definitions are 39.1% of the bytes (21,170 `red`
lines, two per propagator call), the circuit derivations and value consistent
RUPs 34%, subproof bodies 8%, deletions 6%, comments 5%, precedence,
shifted-position and other flag definitions 4%, backtracking and solutions
4%, and the shared literal-definition layer 0.05%. At 14 nodes the
short-reason flags are 52.1%.
On `Prevent` at 12 nodes the family's RUPs and `pol`s are 69%, backtracking
and solutions 19%, the literal layer 0.2%. The shared layers are negligible
here because every successor's domain is a handful of values whose literals
the `.opb` already defines.

**The short-reason flag defined on every call** (#1317). Rules
7 to 13 need it on about one call in twelve (at 12 nodes, 10,585 calls define
it, and defining it lazily leaves 842 that do), but it is defined on every
call with a logger. Defining it on first use instead
(`ab/circuit_scc_lazysr.cc`, same control as above):

| n | Bytes, control | Bytes, flag on first use | VeriPB | Solve with proofs | `sr` definition lines |
|---|---|---|---|---|---|
| 10 | 868 KB | 622 KB | 0.30 → 0.28 s | 0.038 → 0.033 s | 886 → 100 |
| 12 | 19.08 MB | 12.22 MB (−36%) | 10.98 → 10.36 s | 0.42 → 0.30 s | 21,170 → 1,684 |
| 14 | 54.47 MB | 28.19 MB (−48%) | 43.46 → 40.65 s | 1.17 → 0.71 s | 71,064 → 5,222 |

Each definition is two `red` lines. Same recursions, and every proof
verifies. Checking time moves by only 6%,
because the flags are cheap to check; bytes and solve time are what they cost.
With short reasons off altogether the 12-node proof is 18.48 MB and checks in
10.48 s. So as shipped, short reasons are a net loss on this proof: the
per-call flag costs 6.86 MB (19.08 against 12.22), and short reasons with the
flag defined on first use save 6.26 MB against full reasons (18.48 against
12.22);
McIlree's thesis (§6.5) reports short reasons a benefit on random TSP, and
does not say how its flag was defined.

**Measured elsewhere, not to be mixed with the tables above.** The design note
gives `SubCircuit` figures from its own development (`mario_easy_2` at 15
houses, a 186 MB proof checked in 176 s; anchoring halving the position rows;
the shaving rules' proof multipliers), at commits before `86caad24` and on a
different harness. They are not re-measured here.

## Status, gaps, and next steps

### Proof-logging gaps

- **`with_prune_skip(false)` makes the `SCC` proof wrong.** Rules 8 and 10
  still fire, but their certificates, JP 6.16 and 6.17, require the skip
  edges to have been pruned first, which only rules 11 and 12 do. VeriPB
  rejects the derivation when a skip edge matters, 13 times in 900
  `circuit_random --no-prune-skip` proofs from 5 to 10 nodes; the search and
  its answers are unaffected. At the
  defaults no proof was rejected (#1306).
- **`SubCircuit`'s pigeonhole and a wide-declared successor.** Not a gap in
  what is justified, but a proof-size defect: under `subcircuit::SCC` the
  pigeonhole (`subcircuit.cc:538–549`) writes one term per declared value of
  each successor, so the proof grows linearly in the declared width during
  search (500,257 lines at a declared width of 10,000 against 452 at the node
  range). Neither the guarded audit lane nor a root-level survey sees it.
  Unfiled (held for Ciaran); PR #1302 records it in a comment and in
  `large-domains.md`.
- **Assertion levels:** rules 10 to 12 assert bare unit clauses at
  `Definitions`, `Links` and `Inferences`; the clauses are not consequences of
  the model. Not filed, by decision (*assertion reasons*). At `Off`, every
  inference is justified at the defaults; the exception is the knob setting
  above.
- **The propagators are not weakened by proofs.** Search is the same with
  proofs on or off; the `SCC` arm's proof-only work (the flag, the caches) does
  not change an inference.

### Known limitations

- **A `Circuit` over an empty array crashes the solver,** under the default
  algorithm, and under either algorithm with a proof (#1307).
- **`Circuit` with `with_prune_skip(false)` can write a proof VeriPB rejects**
  (#1306).
- **A one-node `circuit` is satisfiable** in Glasgow, Gecode and `cake_pb_cp`,
  and unsatisfiable in MiniZinc's own decomposition and Chuffed; a one-node
  XCSP3 `<circuit>` without a size is reported unsupported rather than
  unsatisfiable (#1319).
- **`with_required_node()` rejects a valid anchor** whose own index was left
  out of a vector-built domain (#1228); the automatic anchor search misses the
  same nodes, and MiniZinc set-domain holes, silently, and so builds the
  larger unanchored encoding and runs `subcircuit::SCC` as `Prevent`.
- **`Circuit`'s `with_prune_within()`, `with_prove_using_dominance()` and
  `with_enable_comments()` do nothing** (#1318).
- **A `SubCircuit` successor declared wide makes `SCC` proofs grow with the
  declared width**, during search, though propagation is unaffected
  (unfiled, held for Ciaran; [Interval efficiency](#interval-efficiency),
  point 3).
- **Neither class is generalised arc consistent**, and `SubCircuit` does not
  infer that a tour size cannot be 1.
- **`Circuit`'s default propagator is slow,** about six times Gecode's
  equivalent per node on enumeration, and a fifth of its time there is a
  reason nobody reads when proofs are off.

### Next steps

1. **Fix the empty `Circuit`** (#1307). Install nothing but the
   always-true case when `succ` is empty, in `prepare`, `define_proof_model`
   and `install_propagators`, as `SubCircuit` does, and add `n = 0` to
   `circuit_test`. Small; the only crash this audit found.
2. **Make rules 8 and 10 safe without prune skip** (#1306).
   Either run them only when `prune_skip` is on, as JP 6.16 and 6.17's
   preconditions require, or prune the skip edges in the proof (the rule 11
   and 12 derivations) whenever rule 8 or 10 needs them, even with the option
   off. The first is a one-line guard and weakens propagation under that
   option; the second keeps it. Add a lane with prune skip off on an instance
   where a skip edge is the only way out of a subtree, such as #1306's.
3. **Build the `SCC` reason only when a proof will read it, and define the
   short-reason flag on first use** (#1317). Both are a few
   lines in `circuit_scc.cc`; the A/B above is the evidence: up to 13.7% fewer
   instructions with proofs off at equal recursion and propagation counts, and
   half the proof at 14
   nodes. Per #907's lesson, it wants a proof diff, which the A/B already
   shows is limited to the flag lines.
4. **Pass the reason in rules 10 to 12's assertion path** (*assertion
   reasons*), when the hints-only mode is taken up; two lines, and the same
   finding as `smart_table`'s. Add a lane running this family at
   `GCS_ASSERTION_LEVEL=Inferences` with a check that no asserted clause is
   falsified by a later `solx` (`probes/assertcheck.py` is one).
5. **Remove or implement the three dead `Circuit` setters, and fix the stale
   `SubCircuit` comments** (#1318). Removing is an
   API change; implementing prune within means JP 6.6.
6. **Decide the one-node semantics** (#1319): either make
   `fzn_circuit.mzn` return `false` at one node, as the standard library
   does, or record the divergence as deliberate; and have the XCSP3 binding
   answer unsatisfiable for a one-node `<circuit>` without a size.
7. **#1228**: the issue's three directions (remove a vector-built domain's
   holes from the initial state, read the declared value set, or check after
   `In` has run) all address the C++ route. MiniZinc's set domains arrive as
   an interval plus `Or` constraints, so only the first, extended to those
   `Or`s, or having `fzn_glasgow.cc` create set domains with their holes,
   would reach them. The anchor choice also fixes the encoding, which is
   written before any propagation, so "after `In` has run" would need the
   check to move without the anchor search.
8. **Make the `Circuit` scenario tests assert what they fire**, for instance by
   counting the rule's proof comment, and bring holey random domains into an
   in-tree enumeration lane. Moderate.
9. **The per-call cost of `SCC` beyond the reason**: the per-node vectors in
   `explore` and the coroutine domain walks. A profile item, worth measuring
   against Gecode's propagator, which does the same work in about a sixth of
   the time per node.
10. **Name only the node values in `SubCircuit`'s pigeonhole** (unfiled, held
    for Ciaran): the counting needs every node value, not every declared
    value, so either the range `0..n-1` or #939's cover form keyed on the node
    values. Small; when done, the comment at `subcircuit.cc:546–548` and
    `large-domains.md`'s `subcircuit` paragraph change with it, and a
    proof-size lane over a wide-declared successor under `subcircuit::SCC`,
    run through search, would pin it.

## Prior art

The propagators are Francis and Stuckey's (*Explaining circuit propagation*,
Constraints 19(1), 2014: `check`, `prevent`, and `scc` with its pruning rules
prune root, prune skip, fix required and prune within, for both `circuit` and
`subcircuit`). The depth-first rules go back to Carlsson's condition, as
implemented in Gecode and described by Schulte and Tack (*Weakly monotonic
propagators*, CP 2009); `Circuit`'s `SCC` arm has the same structure as
Gecode's `connected()`, root aside. The `Circuit` encoding is Encoding Procedure 6.1 of
McIlree's thesis, after Zhou's SAT encoding (*In pursuit of an efficient SAT
encoding for the Hamiltonian cycle problem*, CP 2020). **Certified `Circuit`
is published**: McIlree, McCreesh and Nordström, *Proof Logging for the
Circuit Constraint* (CPAIOR 2024, LNCS, pp. 38–55), expanded as Chapter 6 of
McIlree's thesis, *Pseudo-Boolean Proof Logging for Constraint Propagation
Algorithms*, which gives JP 6.1 to 6.6 and 6.15 to 6.17 and `ReachTooSmall`
and reports this solver's implementation as the first certifying `Circuit`
propagator. Prune within (JP 6.6) is in the thesis and not in this
propagator.

**`SubCircuit`'s certificates are this solver's own and, as far as this audit
knows, unpublished**: the anchored and unanchored labelling with off-tour
nodes at position zero and the tour length as a sum of literals; the
closed-cycle bound split over the candidate first node; the forward
reachability induction with its pigeonhole, the backward induction that needs
none, and the shaving rules as those inductions under one guarded edge.
Francis and Stuckey give the propagation rules, with explanations for lazy
clause generation, not checkable proofs.

## Further reading

- [`subcircuit-proof-logging.md`](../subcircuit-proof-logging.md): the
  `SubCircuit` design note (657 lines, stays). Why the encoding is a position
  labelling, anchored or not, and why off-tour nodes sit at zero; the
  certificates for `check`, `prevent` and both reachability walks, and what in
  them was shown to be load-bearing; the measurements of `scc` against
  `prevent` on the Challenge families, the offset fix (#802) that recovered
  most of the pruning, the constants fix (#812), and the shaving rules' cost.
  Three statements in it have drifted: it says `Circuit` is reachable from
  MiniZinc, C++ and `.scp` only, where `gcspy` posts it too; it says the
  anchored sweep runs "at every size and anchor" (lines 591–592), where it
  uses the anchors 0 and `n − 1` only; and its figures are from before
  `86caad24`.
- [`connectivity-proofs.md`](../connectivity-proofs.md): why an arithmetic
  labelling makes reachability expensive to certify, and the breadth-first
  unfolding the other graph families use instead.
- [`all_different.md`](all_different.md): the value consistent pass and the
  clique encoding every propagator here runs.
- [`smart_table.md`](smart_table.md): the same *assertion reasons* defect.
- McIlree's thesis, Chapter 6 (`tmp/thesis/` holds a copy on the cluster):
  the published procedures behind rules 4 and 6 to 13.
