# `inferred_disjunctive`: capacity-one Cumulatives from conflict cliques across resources

> **Maturity** experimental (C++ API and the `rcpsp` example only; no front
> end reaches it) ·
> **Audited** 2026-10-04 at `7e1c4178` ·
> **Open issues** filed by this audit: #1258 (a misleading Important note on
> job shops). Already open and touching this presolver: #983 (no front end reaches any presolver
> but `DifferenceLogic`), #705 items 3 and 4 (uncached row reductions in the
> recipe, and the recipe's whole-model captures, measured here), #706
> (`dropped_subset` has no fixture; this audit finds it cannot fire on an
> honest run), #702 (`CumulativeStrengthening` has no `with_makespan`; its last
> paragraph is about the makespan bound a dominated clique here loses), #704
> (apparently superseded by #1136), #868 (cross-solver). At every assertion
> level above `Off`, the derived constraint it installs breaks. Over a posted
> donor, under the default start-checkpoint encoding, VeriPB rejects the
> proof. Over a `Disjunctive2D` projection, under any encoding, nothing is
> installed. That is #1234, owned by
> [`cumulative.md`](../constraints/cumulative.md). It also shares #1257
> (silent detection degradation), measured here.
> Tracked under #871.

`InferredDisjunctive` reads every posted `Cumulative`, and every axis a
`Disjunctive2D` publishes as one, as a resource. It builds the graph of tasks
that some resource cannot hold together, grows maximal cliques in it, and
installs each clique of three or more as a **derived** capacity-one
`Cumulative`. Nothing is written to the OPB. Each per-time capacity row of the
derived constraint is proved inside the proof, from the witnessing resources'
rows, the first time something cites it. It is the first stage of Sidorov
(CP 2026), restricted to capacity one and unit coefficients. The long design
note is [`inferred-disjunctive.md`](../inferred-disjunctive.md). This document
audits it against the presolver variant of the
[template](../constraints/TEMPLATE.md#the-presolver-variant).

Four things to know before touching it.

- **It sees only posted `Cumulative`s and `Disjunctive2D` projections.** A
  unary machine written as a `Disjunctive`, as reified pairwise non-overlap, or
  as conditional difference constraints is invisible to it. On 30 generated
  RCPSP instances that halves the conflict graph (643 conflicting pairs against
  325). It changed the posted cliques on 3 of the 30 and the capacity bound on
  none, and nothing says so. See
  [Detection and its failure modes](#detection-and-its-failure-modes).
- **No front end can turn it on** (#983). `fzn-glasgow`, the XCSP3 solver and
  `glasgow_scp_solver` have no switch, and `gcspy` has no presolver plumbing
  at all. Only the C++ API and `examples/rcpsp --infer-disjunctive`
  reach it.
- **The pass's memory is quadratic in the task count, whether or not
  anything is posted.** The conflict matrix is 104 bytes per ordered task
  pair, and installing a clique copies it twice more, so the peak is about
  three copies: 3,148 MiB at 3,200 tasks. With proofs off, all of it is freed
  when the pass returns. With proofs on, each posted clique keeps one copy for
  the rest of the solve (#705 item 4).
- **Under the default encoding, its proofs verify only at
  `AssertionLevel::Off`.** With the start-checkpoint encoding, at
  `Definitions`, `Inferences` and `Backtracking`, VeriPB rejects every proof
  that contains a derived Cumulative over a posted donor, because the donor's
  per-time flag definitions are never emitted. Over a `Disjunctive2D`
  projection the presolver installs nothing at those levels (#1234). Those levels are the mode the external justifier is meant to
  consume. Under `GCS_CUMULATIVE_ENCODING=time-indexed` or `both-recovering`,
  `sample.dzn` verifies `UNDER ASSERTIONS` at `Inferences`.

## What it is

### Semantics

`InferredDisjunctive{stats}` is a `Presolver`, added with
`Problem::add_presolver`. Its `run` is called once, from `solve_with`, after
the posted constraints are installed and their initialisers have run. It may
install propagators and initialisers. It never removes or rewrites a posted
constraint, and it always returns `true`: it never declares the model
infeasible itself.

What it installs, per accepted clique `K`, is a Cumulative with one task per
member, height 1 and capacity 1, over the members' own start, length and
presence. In words: at every time point, at most one member of `K` is running.

- Two tasks **conflict** when some one resource, posted or published, has
  usable entries for both and `h_u + h_v > C` there. Here `h` is a constant
  height, or the lower bound of a variable one, and `C` is the capacity as a
  number.
- A **task** is a node keyed by its `(start variable, presence literal)` pair.
  The same start on two resources is one node when both agree on the length
  variable and the presence. Since #1136, a different presence makes a
  different node.
- A **clique** is grown greedily from each candidate pair, taking common
  neighbours in decreasing `least_length` order. `least_length` is the
  length's lower bound, or zero for an optional task. The result is always a
  maximal clique.

Degenerate cases:

- Fewer tasks than the minimum clique size (three by default): returns
  before the conflict graph is built. `donors_seen`, `tasks` and the per-donor
  view counters (`declined_irreducible_capacity`,
  `resources_with_set_aside_tasks`, `converted_heights`, and the two
  appearance drops) are filled in; nothing else is.
- No donors: the stats summary says `no posted Cumulative to look at`. The
  summary says "Cumulative" for both kinds of donor: a `Disjunctive2D`
  projection counts in `donors_seen` too.
- No conflicting pair: returns before ranking.
- A pair whose demands both exceed the capacity: still a conflict. The
  at-most-one comes out at degree zero ("neither may run"), and the merge
  still pins (the `pair_both_over` fixture).
- A task demanding more than its resource has, on its own: kept, and if its
  length must be positive it pads the reported `largest_capacity_bound`.
  `CumulativeStrengthening` and `InferredCumulative` both filter this case out;
  this presolver does not. The design note records the asymmetry. With a
  positive least length the donor is infeasible at the root anyway. With a
  variable length whose lower bound is zero, the donor is feasible (the
  length is forced to zero), and the task's `least_length` of zero adds
  nothing to the bound.
- An optional task whose guaranteed demand alone exceeds its capacity: set
  aside by the donor view, since its presence is about to be falsified.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `InferredDisjunctive` (presolver) | `frontend gap (#983)` | `frontend gap (#983)` | `frontend gap (#983)` | `frontend gap (#983)` | C++ API; `examples/rcpsp --infer-disjunctive` |

For `.scp` the gap is in the solver, not the format. A `.scp` file is a model,
and a presolver is a solve option, so `glasgow_scp_solver`
(`scp/glasgow_scp_solver.cc`) would need a flag, and it adds no presolver. At
`7e1c4178`, `--help` on `fzn-glasgow` and
`xcsp_glasgow_constraint_solver` mentions only the `--difference-logic`
presolver, and on `glasgow_scp_solver` it mentions no presolver. Both
`fzn-glasgow` and the XCSP3 reader already post `Cumulative` for `cumulative`
(`fzn_glasgow.cc:989`, `xcsp_glasgow_constraint_solver.cc:613`), so wiring a
switch would hand the presolver the right donors. MiniZinc's `disjunctive` and
`disjunctive_strict` post `Disjunctive`, which it cannot see (below).

### Options

None of the options changes the OPB. They choose what is searched for and what
the installed constraint runs.

- **`with_budgets(max_candidates, max_posted)`**, defaults 100 and 5:
  Sidorov's `N_cover` and `N_out`. Candidate pairs are sorted by
  `least_length` sum, best first, before the prefix is taken, so the budget
  keeps the best pairs rather than the first ones created. Every drop is
  counted. Each budget that is hit reports one `StatsLevel::General` note,
  with the figures and the option. A run that hit either or both also reports
  one `StatsLevel::Important` note in words.
- **`with_minimum_clique_size(k)`**, default 3. A two-member clique is a
  conflicting pair, which its witness already keeps apart. #707 measured
  lowering it to two and found no certified bound moved; the default stands.
  The `disjunctive_2d_presolver` test runs at two.
- **`with_rules(CumulativeRules)`**, default `time_table = false,
  overload = true, profile_overload = true`. Time-tabling is off because it
  is redundant: every conflicting pair is already kept apart by its witness.
  The test asserts that redundancy node for node. What the derived constraint
  adds is energy over the clique.
- **`with_makespan(v)`**: names a makespan. Each posted clique then also
  derives a lower bound on `v` at the root, from the model's
  `start + length <= v` rows, which
  [`find_makespan_links`](#rewrite-makespan-bound-from-a-clique) looks for.
  Naming a variable that is not a makespan gives a weaker bound, never a
  rejected proof.
- **`with_proof_mutation(...)`**: test-only corruptions, in
  `gcs/presolvers/innards/inferred_disjunctive_mutations.hh`. See
  [Tests](#tests).

There is no `with_consistency()`. Neither `consistency::Auto` nor
`consistency::Dynamic` applies.

### Variable kinds and views

What a donor can contribute is decided by `cumulative_donor_view`, which all
three scheduling presolvers share and [`cumulative.md`](../constraints/cumulative.md)
documents. In short, per task:

- **constant height**: usable;
- **plain-variable height with a positive lower bound**: converted to that
  lower bound (`converted_heights`), so the task's conflicts are those of its
  *guaranteed* demand, and fewer than its real ones;
- **view height, or one whose lower bound is zero**: set aside
  (`resources_with_set_aside_tasks`), so the task takes no part in conflicts
  on that resource, and every row the resource witnesses is weakened over it;
- **variable length with a variable start**: with proofs on, usable where the
  donor published the end proxy that pins need, and set aside where it did
  not. With proofs off, always usable (`donor_view.cc:214-215`), so the
  counters can differ between the two. A variable length on a constant start
  is always usable, since it needs no proxy. Separately, any length that is a
  variable *by type*, a single-valued one included, keeps its member out of
  the makespan bound (`derived_cumulative.cc:334`); see the makespan
  rewrite;
- **capacity a view**: the whole donor is declined
  (`declined_irreducible_capacity`). A plain-variable capacity is read at its
  upper bound at presolve time.

The **start** is not restricted. A view start is a node like any other, but a
different node from the variable underneath it: `x` on one resource and
`x + 0` on another do not meet. The **makespan link** search does want a
plain start variable on the linear side; see the makespan rewrite.

The proof handles views wherever the donor does. Every line the recipe writes
is over the donors' activity flags, never over a start variable.

### Reification

None. A reified "these tasks are pairwise exclusive" has no use here.

### Relation to other families

- **What it reads.** Posted `Cumulative`s
  (`Problem::each_constraint_of_type<Cumulative>`), and the per-axis
  projections a `Disjunctive2D` publishes with `publish_cumulative_donor`
  (#973). Nothing else: not `Disjunctive`, not linear or reified pairwise
  non-overlap, not `DifferenceConstraints`.
- **What it installs.** A derived `Cumulative` per clique, via
  `install_derived_cumulative`, under `CurrentlyUnnamedConstraint`. Its
  propagator, its rules, its decline behaviour and its makespan initialiser
  are [`cumulative.md`](../constraints/cumulative.md)'s.
- **Shared code.** `cumulative_donors` and `cumulative_donor_view`
  (`donor_view.hh`), `recover_constant_argument_row`, `build_am1_from_row`
  (`innards/proofs/am1_from_row.hh`; `CumulativeStrengthening` calls the
  `recover_am1_from_row` wrapper around it),
  `recover_conjunction_flag_bridge` (`innards/proofs/flag_bridge.hh`, shared
  with `InferredCumulative`), `recover_am1_from_pairs`
  (`innards/proofs/am1_from_pairs.hh`, also used by `all_different`,
  `disjunctive`, `sort`, `min_distance` and `subcircuit`), and `find_makespan_links`
  (`presolvers/innards/makespan_links.hh`, shared with `InferredCumulative`).
- **Other presolvers, and order.** It runs in the order the presolvers were
  added. `examples/rcpsp` adds it before `InferredCumulative`. A derived
  constraint is not a posted `Cumulative`, so a later presolver never reads
  this one's cliques as donors, and this one never reads anyone else's. The
  cliques it posts do not depend on order. Its **certified makespan bound**
  does: `solve_with` runs a presolver's initialisers before the next
  presolver runs, so a makespan an earlier presolver raised is already in
  `known`, and this one's bound counts only if it beats it. On KSD15_D
  `j3033_9` (`tmp/fd-sched/inferred_disjunctive/e11/vid.cc`, both with the
  makespan named, 2026-10-05):
  - this presolver alone certifies 361;
  - with `InferredCumulative` first, it certifies 0, while `InferredCumulative`
    certifies 361;
  - in the other order, `InferredCumulative`'s is 0 and this one's 361.

  The model ends with the same bound either way. Only which block reports it
  changes, and `largest_capacity_bound` stays 361 in this block throughout. The
  `DifferenceLogic` presolver lifts precedences, not resources. The one place
  the two meet is the makespan links: `find_makespan_links` reads the posted
  rows, and their labels stay in the `.opb` whichever propagators
  `DifferenceLogic` disables. This audit did not test that combination.
- **Candidate merge.** With `InferredCumulative`: no. That presolver lifts
  covers to non-unit coefficients by a knapsack per resource. This one merges
  pairwise at-most-ones, which is scale-free and so works only at unit
  coefficients. The two share the donor plumbing and the makespan argument,
  and nothing else.

## The proof model

### OPB encoding

None. The presolver writes nothing to the OPB, and the test asserts the `.opb`
is byte-identical with and without it. The donors' encodings are
[`cumulative.md`](../constraints/cumulative.md)'s (the start-checkpoint block)
and [`disjunctive_2d.md`](../constraints/disjunctive_2d.md)'s.

### Labels

It writes no labels of its own. It cites:

- each witnessing donor's **per-time capacity row**, asked for through the
  donor's `capacity_row_family` deriver and handed to the recipe in
  `DerivedCumulativeRows`. Under the start-checkpoint encoding these rows are
  not in the OPB. They are recovered in the proof on demand
  (`checkpoint_recovery.cc`);
- each member's **per-(task, time) flags** on its home donor and on its
  witnesses, keyed `v[donor][i_t][cb]`, `[ca]` and `[cact]`. They are asked
  for with `ensure_flag_defined` before they are cited (`flags_for`);
- with `with_makespan`, each **makespan link row**: a posted
  `LinearLessThanEqual` or comparison row, cited by its label in the `.opb`.

### Cake conformity

There are no rows to conform. Neither `.scp` nor `cake_pb_cp` has any notion of
a presolver, so no SCP chain case runs one. A workflow-2 run would check the
presolver's derivation against cake's OPB, which carries the same
start-checkpoint block ours does. That has not been tried.

### Proof-time state

**Root versus lazy.** A derived row for time `t` is built by the recipe the
first time something cites it (#1130). It is built eagerly in two places
only. One is at install, once at the first time point of each stretch between
the derived constraint's own window edges, to find out whether it would
decline. The other is the makespan initialiser, which derives every row
below the window it argues over. During search, a recipe call is emitted
wherever the propagator happens to be, at `ProofLevel::Top`.

**What one recipe call emits, at time `t`**, over the members whose windows
cover `t`:

1. A comment, `% presolve disjunctive clique at time t`.
2. Inside a `ProofScaffoldingScope` (one proof level deeper, forgotten on
   exit; #666):
   - per member and witnessing resource, one bridge
     (`recover_conjunction_flag_bridge`, `Temporary`): three `pol`s, one each
     for `cb` and `ca` and one combining them for `cact`. It is cached per
     `(member, witness)` within the call;
   - per pair, one `pol` that opens with the at-most-one out of the witness's
     row and continues with that pair's bridges, at `Temporary`. Where the
     witness has a variable capacity, a converted height or a set-aside task,
     a `recover_constant_argument_row` `pol` comes first. That reduction is
     uncached, once per pair (#705 item 3).
3. The merge induction (`recover_am1_from_pairs`), ending on an `ia` pin to
   `Σ_{p ∈ K, active} cact_{p,t} ≤ 1` at `Top`.

A time point with one member present emits a single RUP `cact ≤ 1` at `Top`
instead, with no comment marker.

**Deletion.** Everything but the pin is deleted when the scaffolding scope
closes. The pin lives at `Top` for the rest of the proof, unless a later
stretch makes the install decline, in which case every row already derived
for the constraint is deleted (`cumulative.md`).

**Naming.** No derived row has a label. A reconstructor finds them by the
comment markers and by position. The per-clique line `% presolve disjunctive:
inferred a clique of k tasks, total duration L` is written after install.
There is no comment listing which tasks are members; the pin's terms say so.

**Hints-only content.** The derived constraint is installed under
`CurrentlyUnnamedConstraint`. At an assertion level, its own inferences
therefore carry `::cumulative:((constraint_id unnamed) (subhint ...))`. Two
were seen: `(subhint overload)` on the test file's family (k = 5, refuted at
the root), and `(subhint makespan)` for the makespan push on `sample.dzn`.
Both runs were under `GCS_CUMULATIVE_ENCODING=time-indexed`, where such
proofs verify `UNDER ASSERTIONS`. Nothing in the hint says which clique, so a
reconstructor has to match the asserted clause's literals against the pinned
rows. The recipe's own lines are never asserted.

**Auxiliaries.** None of its own. Every flag cited is the donor's, defined by
the donor's definer on first ask, and determined by unit propagation on a
solution like any donor flag.

**At assertion levels above `Off`, under the default start-checkpoint
encoding,** the donors' definers are never published (`cumulative.cc:935`
returns early). So the recovery and the recipe cite labels like
`@v[_6][0_0][ca][r]` that nothing defines, and VeriPB stops with a syntax
error. This was reproduced at `7e1c4178` on `examples/rcpsp/sample.dzn`:
`GCS_ASSERTION_LEVEL=definitions` and `=inferences` both fail with the
presolver, and both verify `UNDER ASSERTIONS` without it. The unit test fails
the same way under `GCS_ASSERTION_LEVEL=inferences`. With
`GCS_CUMULATIVE_ENCODING=time-indexed` or `both-recovering`, where the flags
are OPB rows, `sample.dzn` with the presolver verifies `UNDER ASSERTIONS` at
`inferences`. Over a `Disjunctive2D` projection, the derived constraint
declines above `Off` instead, so nothing is posted. Both symptoms are
#1234. The recipe itself writes the same
`pol`/`ia`/`rup` lines at every level: it never asserts.

## The implementation

### Initialisation and global data

The pass, in order:

1. Register the stats block, always (#723).
2. If `with_makespan`, run `find_makespan_links` once over every posted linear
   and comparison constraint.
3. Per donor: build its view, then add its usable positions as appearances,
   merging by `(start, presence)`.
4. The conflict matrix: for every task pair, compare every pair of
   appearances on the same donor until one conflicts. The first conflicting
   resource found is the witness.
5. Sort the candidate pairs, then grow up to `max_candidates` of them,
   deduplicating with a `set<vector<size_t>>`.
6. Rank the cliques by capacity bound, then drop the dominated, the
   over-budget and the subsumed (in that order).
7. Install one derived Cumulative per accepted clique.

Costs, in task count `n`, appearances per task `a`, candidate budget `B` and
clique size `k`:

- conflict matrix: `O(n²·a²)` time (each pair stops at its first
  conflicting resource), at least `n²`, and `n²` entries of 104 bytes
  (`sizeof(optional<Conflict>)`, measured), allocated whatever the density;
- growth: `O(B·n·k)`;
- ranking: `O(c log c)` over `c ≤ B` cliques.

Measured at `7e1c4178` (Release, fataepyc-08, 2026-10-05, pinned to one
core, proofs off, seed 1). The pass alone was timed between two marker
presolvers (`tmp/fd-sched/inferred_disjunctive/e4/scan.cc`). Task lengths are
uniform in 1..4, and the horizon is their sum. Peak is the process's `VmHWM`,
read after the trim. The kernel updates it lazily, so treat it as a lower
bound: at n = 100 it reads below the RSS left. Left is the RSS once the pass
has returned, before and after `malloc_trim(0)`.

| shape | n | pass | peak RSS | left | left after trim |
|---|--:|--:|--:|--:|--:|
| complete conflict graph (one resource, cap 2, heights 2), 1 clique posted | 100 | 5 ms | 7.6 MiB | 8.5 MiB | 5.4 MiB |
| | 400 | 77 ms | 54 MiB | 54 MiB | 5.7 MiB |
| | 800 | 344 ms | 201 MiB | 198 MiB | 6.3 MiB |
| | 1,600 | 3.4 s | 792 MiB | 517 MiB | 7.4 MiB |
| | 3,200 | 13.9 s | 3,148 MiB | 2,045 MiB | 9.5 MiB |
| random RCPSP-like (2 resources, cap 5, demands 0..3), 1 posted | 800 | 157 ms | 177 MiB | 178 MiB | 6.7 MiB |
| same, 2 posted | 1,600 | 712 ms | 693 MiB | 691 MiB | 8.3 MiB |

One copy of the matrix at 3,200 tasks is 3,200² × 104 B = 1,016 MiB. The peak
of 3,148 MiB is about three copies:

- the matrix itself;
- `auto conflicts = conflict;` (`inferred_disjunctive.cc:569`);
- the recipe lambda's by-value capture of that copy (`:575`).

The lambda also captures the whole task vector and every donor view. With
proofs off, `install_derived_cumulative` keeps no recipe
(`derived_cumulative.cc:149`, everything that holds it being under
`if (logger)`). So every copy is freed when the pass returns. The "left"
column is freed heap that glibc has not handed back, which `malloc_trim`
does. With proofs on, the recipe is kept in the derived constraint's row
deriver for the whole solve (`derived_cumulative.cc:212`), so each posted
clique retains one copy and the peak grows to about two plus the number
posted. That is read from the code; it was not measured at these sizes,
because proofs on at these sizes cost the cubic recovery below. #705 item 4
asks for the captures to be trimmed.

With proofs on, the install's probes recover each witness's capacity row at
one time point per stretch. On a fresh donor that is the first row it has
recovered, and recovery derives the donor's pairwise order lemmas at `Top`,
cubic in the donor's task count (`cumulative.md`). On the random shape (lengths
uniform in 1..4) that
is 0.19 M proof lines at n = 50, 1.5 M at 100, 11 M at 200 and 52 M (4.2 GB,
141 s) at 400, all emitted during the presolver's span. 99% of those lines are
pair-order lemmas. The clique derivations themselves are 178, 695 and 2,528
lines (n = 50, 100, 200). The donors pay that recovery anyway once they
justify anything. To the first solution at n = 100 (this probe, seed 1,
lengths uniform in 1..4,
`posted` budget 0 against 5), the whole proof was 54.6 M lines without the
presolver and 52.9 M with it. With lengths in 1..5 instead, the fact-check
measured 66.7 M and 61.9 M. So the presolver brings the cost forward
rather than adding it.

### Propagator inventory

The pass itself installs nothing that runs during search. Each clique gets the
two things [`cumulative.md`](../constraints/cumulative.md) documents, and the
rows below summarise them for this presolver's configuration.

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| derived Cumulative propagator (`propagate_cumulative` over the clique) | `on_bounds` starts, variable lengths; `on_instantiated` presences | derived (none) | `cumulative.md`'s overload and profile-overload rules (time-tabling off by default) | always, per accepted clique | as `cumulative.md` | as `cumulative.md` |
| makespan-bound initialiser | none (initialiser, `InitialiserPriority::Expensive`) | n/a | [makespan bound](#rewrite-makespan-bound-from-a-clique) | `with_makespan` | n/a | n/a |

### Mutable state and incrementality

The pass keeps no state between solves. The stats block is shared with a clone,
so a caller's handle reads what this solve did. Notes count "this run's" drops
separately, so a block shared over two solves is not double-counted in the
Important note. With proofs on, each recipe closure holds the copies described
above for the whole solve; with proofs off, none is kept. The derived
constraint's own state is `cumulative.md`'s.

### Interior values and optional pruning

**What this presolver offers:** none. It installs no optional-interior-pruning
pair.

**What it observes:** its pass runs before `choose_optional_interior_pruning()`,
which `solve_with` calls after the last presolver so that what presolvers
install is counted. Its derived constraints trigger on bounds and
instantiation only, so they report no hole sensitivity, and they keep nobody
else's interior pruning alive. The pass itself reads bounds only (task
windows, height lower bounds, a capacity's upper bound). Its whole vocabulary
is bounds.

### Robustness and limits

- **Unbounded domains and the integer range.** The pass's own arithmetic is
  checked `Integer`: `h_u + h_v` is at most `2·(2^60 − 1)`. The capacity
  bound `Σ least_length` over a clique can overflow from nine members of
  length about `2^60`, and would throw `IntegerOverflow` while ranking, even
  for a clique later dropped as dominated. That is unreachable today, because
  the donor fails first. A Cumulative with lengths of `2^60 − 1` throws
  `cannot create std::vector larger than max_size()`, and one at `2^40`
  throws `std::bad_alloc`, both before any presolver runs. At `2^30` the donor
  alone needs 64 GiB and 73 s. With this presolver added that becomes 80 GiB
  and 100 s, proofs off (9 tasks of length `2^30` in `[0, 2^30]`, peak RSS
  from `/usr/bin/time`, one run each, 2026-10-04).
- **Negative times.** Fine. The cross-resource family shifted by −1,000 and
  by −10⁶ verifies both ways (k = 5, satisfiable and unsatisfiable).
- **Zero.** A zero-length or zero-height task, or a constantly absent one, is
  not usable. A zero capacity makes every positive pair conflict.
- **Degenerate shapes.** See [Semantics](#semantics). A donor posting one
  `(start, length)` at two positions keeps the first appearance only
  (`dropped_duplicate_appearance`). Without that, a conflict recorded on the
  second would be pinned against the first's flags and the `ia` would fail.
  Two resources giving one start different length variables keep the first
  (`dropped_disagreeing_length`).
- **Proof errors.** A witness that has a row at `t` but no flags for one of
  the pair throws `ProofError`. No run in this audit reached it.

### Interval efficiency

1. **Propagation side (the pass).** Nothing walks a domain or a horizon. The
   pass reads window bounds (`cumulative_task_window`) and constants. Its work
   is in tasks and appearances, as above. "Reaches for `State`'s per-value
   iterators nowhere at all" is true of `inferred_disjunctive.cc`.
2. **Reason side.** The pass gives no reasons. The derived constraint's are
   `cumulative.md`'s.
3. **Proof side.** Per derived time point, the recipe writes
   between `(k² + 7k)/2` and `k(7k − 11)/2` lines on the two families
   measured: the test file's, and a pairwise one built as a probe (see the
   clique rewrite's Proof size). Each at-most-one line names every
   usable task of its witness, so its *length* is linear in that donor's task
   count. How
   many time points get derived is decided by what the propagator cites,
   never by the horizon (#1130). Over a horizon the installed constraint
   costs memory at install, proofs off: its overload rule's per-time slot
   prefix, 8 bytes per time point (the presolver's span added 513 MiB at a
   window of about `6.7·10⁷`, and that is kept, since the propagator holds
   it). That is `cumulative.md`'s structure.
4. **Audit lane.** No row in `gcs/large_domain_audit_test.cc`. The axes no
   test varies are the horizon, the task count past a dozen, and the donor
   kind (no test uses a `Disjunctive2D` donor at the default minimum clique
   size).

## Rewrite catalogue

Facts for both entries: the presolver adds nothing to the OPB, every inference
it enables is certified in the proof, and nothing it writes is an assertion.

### Rewrite: clique-to-unary-resource

- **Pattern** — `k ≥ min_clique_size` tasks, pairwise conflicting on some
  posted or published resource. The clique is maximal, grown from one of the
  best `max_candidates` pairs, ranked among the best `max_posted` by
  `Σ least_length`, and not exactly dominated. A clique is exactly dominated
  when one donor of capacity ≤ 1, posted or published, has every member at
  height ≥ 1.
- **Posts** — `install_derived_cumulative` with one task per member: donor and
  position from the member's first appearance, its own start, length and
  presence, height 1, capacity 1. `row_donors` are the pairs' witnesses, and
  the rules default to energy only.
- **Derived mode** — yes. No OPB row, and the rows are proved per time point.
- **Why it is true** — if `u` and `v` conflict on resource `R`, then
  `h_u + h_v > C_R`, so at any time `t` at which both run, `R` is
  overloaded. So at most one of any conflicting pair runs at `t`. A set of
  tasks that conflict pairwise therefore has at most one member running at
  `t`, which is the row `Σ_{p ∈ K} active_{p,t} ≤ 1`. Using a height's lower
  bound is sound, since a task demands at least that whenever it runs. An
  optional task's row is conditional on its presence, because its activity
  flag is.
- **Proof technique** — per time point: `pol` (the pairwise at-most-one, by
  weakening, saturation and division by the margin `h_u + h_v − C`, per
  `build_am1_from_row`; one `pol` with the pair's bridges stacked on it), then
  a `pol` sequence (the clique merge, the classical induction in
  `am1_from_pairs.hh`), then `ia` (the pin). Where the two at-most-one demands
  both exceed `C`, the line comes out at degree zero and is strictly
  stronger; the induction still advances and the `ia` still passes
  (`pair_both_over`). A single member present gives `RUP`. The procedure is
  ours: the at-most-one recovery and the bridge are from this codebase. The
  merge is textbook clique-from-pairs cutting planes. The preconditions are
  that the members are pairwise distinct and that each pair line really is
  that pair's at-most-one; the pin checks the conclusion's shape, not those.
- **Neutral?** Time-table neutral, which is why time-tabling is off. A pair is
  already apart on its witness, so the derived profile adds nothing. The test
  asserts node-for-node equality with energy rules off everywhere (17 nodes
  either way on its fixture). It is not neutral for energy, which is the point
  of it.
- **Offline reconstructibility** — the derivation is present at every level,
  so nothing is asserted to reconstruct. The derived constraint's *own*
  assertions carry `cumulative:((constraint_id unnamed) ...)`, since it is
  installed under `CurrentlyUnnamedConstraint`. A reconstructor has to find
  its rows by the comment markers and the pin's terms. That makes it `search`
  over the proof's pinned rows, cheap but unhinted. It is moot until
  #1234 is settled.
- **Proof size** — per derived time point, quadratic in `k`, and how many
  bridges there are decides the constant. Each line is linear in its witness
  donor's task count. Measured on two families, both with length 2 and
  horizon `2k − 1` (unsatisfiable), odd `k`:
  - the **test file's family**: `k` resources, every one posted over all
    `k` starts with capacity 1, task `i` at height 1 on resource `r` when
    some `j ≠ i` has `(i + j) mod k = r`. So each resource holds `k − 1`
    tasks at height 1, and every pair among them conflicts there. The witness
    is the first shared resource in posting order
    (`inferred_disjunctive.cc:309-323`). Resource 0 witnesses
    `(k − 1)(k − 2)/2` pairs, resource 1 witnesses `k − 2`, resource 2
    witnesses one, and the rest witness none (6, 3 and 1 at `k = 5`). Only
    `k − 1` pairs need bridging (`cross_donor_pairs`), and there are `k`
    bridges per time point. It writes exactly `(k² + 7k)/2` lines per time
    point;
  - the **pairwise family**, a probe and not in the test file: one two-task
    Cumulative per pair, so every
    pair has its own witness and most need bridges at both ends. It writes
    exactly `k(7k − 11)/2` lines per time point
    (`tmp/fd-sched/inferred_disjunctive/e8/pairfam.cc`, the fact-check's
    probe).

  Both were measured at `7e1c4178`, fataepyc-08, 2026-10-05. VeriPB 3.0.2
  ran with `--force-checked-deletion`, pinned, median of three; "—" means
  not timed. Times vary by around 15% between sessions; the fact-check
  measured 1.00 s for the pairwise `k = 11`. The whole proof is given:

  | family | k | time points derived | lines per point | bridges | whole proof | VeriPB |
  |---|--:|--:|--:|--:|--:|--:|
  | test file's | 3 | 5 | 15 | 15 | 942 lines | — |
  | | 5 | 9 | 30 | 45 | 4,945 lines, 327 KB | 0.06 s |
  | | 7 | 13 | 49 | 91 | 16,584 lines | — |
  | | 9 | 17 | 72 | 153 | 42,675 lines | — |
  | | 11 | 21 | 99 | 231 | 92,338 lines, 7.0 MB | 4.6 s |
  | pairwise | 3 | 5 | 15 | 15 | 942 lines | — |
  | | 5 | 9 | 60 | 135 | 4,883 lines, 297 KB | 0.04 s |
  | | 7 | 13 | 133 | 455 | 14,172 lines | — |
  | | 9 | 17 | 234 | 1,071 | 31,113 lines | — |
  | | 11 | 21 | 363 | 2,079 | 58,010 lines, 4.1 MB | 0.87 s |

  At `k = 3` the two families coincide. The clique derivations are 2.2% of
  the k = 11 proof in the test file's family and 13% in the pairwise one. The
  rest is the donors' row recovery and the solve. On `sample.dzn`, 6
  derivations of 13.5 lines on average make 81 of the 1,452 lines (5.6%). The
  whole proof is 1,279 lines without the presolver. The other 92 lines of the
  difference fall outside the derivations' markers, and this audit did not
  break them down.
- **Gaps** — none at `Off`. Above `Off`, the whole proof is rejected over a
  posted donor under the default encoding, and over a projection nothing is
  installed under any encoding (#1234).
- **Tightness** — `ClaimRhsZero`, `BridgeWrongTask` and
  `IncludeNonConflicting` (the camouflage task, compatible by exactly one
  unit) are rejected at the `ia` pin ("not syntactically implied"). These
  three corrupt the conclusion, since a conflict-shaped route forgives a
  corrupted route. `ForgetPresence` corrupts the installed constraint rather
  than its rows. The pin still holds, and the derived propagator's
  presence-free reasons then fail a later RUP. The
  camouflage fixture is the reusable part: a fourth task on a capacity-two
  resource, whose pairwise demands all sum to exactly two.

### Rewrite: makespan-bound-from-a-clique

- **Pattern** — `with_makespan(m)` was given, and a clique was posted. Per
  member, `find_makespan_links` looks for a row saying the member finishes by
  `m`. It accepts an unconditional two-term `LinearLessThanEqual` with
  coefficients `+1` on a plain start and `−1` on `m`, or a comparison row
  `start + c ≤ m` (or `<`) over offset views, deviewed. The strongest such row
  per start wins.
- **Posts** — a `makespan` and per-member `makespan_links` in the spec. The
  derived constraint then runs one root initialiser that may raise `m`'s lower
  bound. The rule and its certificate are `cumulative.md`'s (the
  `makespan_energy` argument). See also
  [`certified-makespan-bounds.md`](../certified-makespan-bounds.md).
- **Derived mode** — yes. It is an inference, certified in the proof.
- **Why it is true** — the members run one at a time, so their durations
  add up within a window that the links confine to before `m`. Hence `m` is
  at least the earliest start plus the summed least lengths, or better, as
  the window-energy argument finds.
- **Proof technique** — `cumulative.md`'s makespan rule. This presolver
  contributes only the link rows, which the derivation sums.
- **Neutral?** No: it is a bound push. It is reported only when it beats what
  the links and `m`'s bound already say, and that bound includes anything an
  earlier presolver pushed (see [Relation to other
  families](#relation-to-other-families)).
- **Proof size** — the certificate is `cumulative.md`'s, and it sums the
  derived constraint's capacity row at **every time point** from the earliest
  window start up to the bound. Each of those rows is a recipe call, plus
  whatever row recovery its witnesses need. So it is linear in the span of
  the window from the earliest window start to the bound, and not in the
  horizon: a wider declared horizon adds nothing. Nor does it depend on what
  the propagator ever cites. Measured at `7e1c4178` (fataepyc-08,
  2026-10-05) on **root proofs**, with the five posted cliques. `vid.cc` with
  no search argument stops at the root: recursions 1, solutions 0,
  `conclusion NONE`. The canonical model was used, and the counts were
  re-measured identically in a second run
  (`tmp/fd-sched/inferred_disjunctive/e11/root/sizes.log`):

  | instance | certified bound | proof without the makespan named | with it |
  |---|--:|--:|--:|
  | Pack `pack008` | 44 | 36,042 lines, 13 derived rows | 351,845 lines, 54 rows |
  | Pack_d `pack008` | 1274 | 36,048 lines, 13 rows, 2.8 MB | 9,838,751 lines, 1,284 rows, 822 MB |

  The two `pack008` files have the same demands and capacities. Pack_d's
  durations are longer on some tasks: 2 against 115, 5 against 288, and so
  on. The ratios:
  - Pack_d with the makespan named against without it: 273 times the lines
    (9,838,751 / 36,048) and 99 times the derived rows (1,284 / 13);
  - Pack_d against Pack, both with it: 28 times the lines and 24 times the
    rows (1,284 / 54), because Pack_d's window has that many more time
    points.

  VeriPB 3.0.2 (`--force-checked-deletion`, pinned) checks Pack_d's root
  proof without the makespan in 1.5 s (`VERIFIED NO CONCLUSION`). With it,
  VeriPB had not finished after 1,800 s, when it was stopped
  (`e11/veripb-timing.log`, one run; VeriPB's own log held only its banner).
- **Detection failure modes** — a model whose finish rows are not two-term
  `±1` rows on a plain start gets no link for that task, and the bound loses
  that task's energy silently. That covers:
  - an end variable `e = s + d` with `e ≤ m` (the link lands on `e`, which is
    no member's start);
  - `m = max(ends)` posted as `ArrayMax`;
  - a scaled row (`2s − 2m ≤ −2d`);
  - a three-term row with a variable duration;
  - a view start;
  - the precedences lifted into one `DifferenceConstraints`
    (`rcpsp --variant=global`);
  - a length that is a variable by type, even a single-valued one
    (`create_integer_variable(d, d)`). The makespan rule tests
    `is_constant_variable` (`derived_cumulative.cc:334`), so that member is
    left out of the energy argument, though its link is found.

  #1257 says the same spellings degrade this presolver
  too. Checked here over all 110 Pack and Pack_d instances with `vid.cc`. The
  canonical model posts on 78 and certifies a bound on 75. Then:
  - single-valued length variables shared across resources: the same cliques
    and `L`, and a certified bound on none;
  - end variables `e = s + d` with `m ≥ e`: the same, a certified bound on
    none;
  - each resource given its own single-valued length variables: the same
    start now disagrees about its length variable, so later appearances are
    dropped (`dropped_disagreeing_length > 0` on all 110). `L` is lower on 4,
    and a bound is certified on none. Unlike `InferredCumulative`, this
    presolver *counts* that drop;
  - links written as `LessThanEqual{s + d, m}`: identical to canonical.

  So #1257 applies, apart from its second fix item, which this presolver
  already has as `dropped_disagreeing_length`.

  None is counted. The only symptom is `certified_makespan_bound` falling
  below `largest_capacity_bound`, which can also happen for geometric
  reasons. A `certified_makespan_bound` of zero means no bound was pushed.
  Either the energy argument did not beat what the links already say, or no
  task could be counted, as when every member is optional and undecided at
  the root (`derived_cumulative.cc:379`). The
  two figures agreed on 53 of 55 Pack instances and 51 of 55 Pack_d (proofs
  off, `rcpsp --dzn`, default `--variant=decomposed`). The disagreements
  (`L` against certified) are:
  - certified zero: Pack 3 (7 / 0), Pack_d 3 (7 / 0), Pack_d 55 (1130 / 0);
  - certified higher, the window argument doing better than `L`: Pack 55
    (40 / 58), Pack_d 21 (1134 / 1312);
  - certified lower: Pack_d 2 (230 / 212).
- **Tightness** — `ClaimHigherMakespanBound` is rejected (a RUP failure), on
  the test's makespan fixture (`k = 3`, length 2, horizon 8, optimum 6) and on
  `rcpsp_dzn_inferred_disjunctive_mutated`.

## Detection and its failure modes

What the scan recognises: posted `Cumulative` (any constructor, optional or
not), and `Disjunctive2D` per-axis projections, which are published when their
window fits (#973). Over a projection, at an assertion level above `Off`,
the cliques are found but none is installed (#1234's second
symptom). At `Definitions`, `Inferences` and `Backtracking` the proof
verifies. At `Links` it is rejected for an unrelated reason: there every proof of a satisfiable model is rejected at its first `solx` (#1210), and the fixture is satisfiable. The stats do say so: `cliques_found = 1`,
`cliques_posted = 0`, `declined_by_install = 1`, with the summary `nothing
inferred` (the fact-check's `d2.cc`, at `definitions` and `inferences`). No
note is raised. The scan does not recognise anything else, and fails silently
on anything else:

1. **A unary machine written any other way.** `examples/rcpsp` can post its
   machine four ways (`--machine`). Over seeds 1 to 30 at `--size 14`, three
   ways gave identical stats, and they are the three it cannot see:
   `disjunctive` (a `Disjunctive`), `pairwise` and `difference`. `cumulative`
   gave 643 conflicting pairs where the others gave 325. The posted set
   differed on 3 of the 30, and the capacity bound on none. So a MiniZinc
   `disjunctive`, an XCSP3 `noOverlap` in one dimension, or a hand-written
   `s_i + d_i ≤ s_j ∨ s_j + d_j ≤ s_i` contributes no conflicts.
2. **Job shops and open shops have nothing to give, by construction.** Every
   conflict is inside one machine (or one job), so every maximal clique is one
   capacity-one resource's own, and is dropped as dominated. Measured on `ft06`,
   `la01` and `ft10` (`rcpsp --jss`, default `--unary=cumulative`):
   90/225/450 conflicting pairs, 6/5/10 cliques found, 0 posted. Under
   `--unary=disjunctive` the summary is `no posted Cumulative to look at`.
   - On `la01` and `ft10`, the candidate budget leaves 125 and 350 pairs
     ungrown. The Important note then says "search may be slower", which is
     false here. In a job shop, two tasks on one machine and every common
     neighbour of theirs lie on that machine, so growing the pair can only
     reproduce the machine's own clique, which is dropped as dominated
     (#1258). That a pair lies inside a capacity-one resource is
     *not* enough on its own: with two triangles whose every pair has its own
     capacity-one Cumulative, a candidate budget of 3 leaves the second
     triangle ungrown, and a budget of 6 posts it (the fact-check's
     `subset.cc`).
3. **Task identity is by `(start, presence)`.** The same task through a view
   on one resource is a different node. A different length *variable* for the
   same start drops the later appearance (`dropped_disagreeing_length`), as
   does a second appearance on one donor (`dropped_duplicate_appearance`).
4. **Heights and capacities.** A view capacity loses the donor. A view height,
   or a variable one with a zero lower bound, removes that task from that
   resource. A variable height counts its lower bound only. Each has a counter
   (see [Variable kinds and views](#variable-kinds-and-views)).
5. **Greedy cliques.** One maximal clique per candidate pair, longest first. A
   bigger-energy clique that no top pair grows into is not found. With
   `max_candidates = 100` and 225 pairs, as on `la01`, more than half the
   pairs never seed anything.
6. **Front ends.** None can reach it (#983).

`dropped_subset` cannot fire on an honest run. The greedy growth returns
maximal cliques, and deduplication removes repeats, so no grown clique is a
proper subset of another. On 900 random runs (3 resources, capacity 4, demands
0..3, lengths uniform in 1..4, n ∈ {8, 15, 30}, seeds 1 to 300) it was 0
every time, and 593 of those
runs posted five cliques, the posting budget's maximum. It fires only under the
`IncludeNonConflicting` mutation, which grows one clique past a second that
is then its subset: 1 on the fact-check's `subset.cc`. #706 asks for a fixture
for it, and an honest fixture cannot exist. The counter could go, or its
fixture could be the mutation. Duplicate cliques are skipped with no counter at all, so the
pair accounting identity is `considered = dropped_too_small + cliques_found +
(uncounted duplicates)`.

## Evidence that it fired

The `InferredDisjunctiveStats` block is registered whether or not the caller
passed one (#723). It reaches `Stats::components()`, so a front end would print
it, if one ran the presolver. Its summary line distinguishes the three cases:

- `no posted Cumulative to look at`;
- `nothing inferred, of P conflicting pairs over T tasks from D posted
  Cumulatives looked at`;
- `N cliques posted over M task appearances, ..., the best of them worth a
  makespan bound of L`.

The counters that tell "ran and found nothing" from "ran and did nothing" are
`conflicting_pairs`, `cliques_found` and `cliques_posted`. `bridges_derived` is
the one that says the certificate spanned resources (proofs on only). The proof
carries `% presolve disjunctive: inferred a clique of k tasks, total duration L`
per posted clique, and one `% presolve disjunctive clique at time t` per
derived row with two or more members present. A row with one member has no
marker. A recipe call that declines after writing its marker leaves the
marker behind with no derivation after it. One was seen over a projection
above `Off`: `% presolve disjunctive clique at time 0` as line 2 of `d2.cc`'s
proof. So a marker is not proof that a row was derived; the pin is. The
summary's "posted Cumulatives" counts `Disjunctive2D` projections
too.

Expected values on named instances, at `7e1c4178`:

- `examples/rcpsp/sample.dzn`, `rcpsp --dzn sample.dzn --infer-disjunctive`:
  3 conflicting pairs, 1 clique of 3 posted, capacity bound 6, certified bound
  6, optimum 6, proof verified (`rcpsp_dzn_inferred`).
- **Pack and Pack_d** (`/cluster/ciaran/claude/scheduling-instances/rcpsp/`, 55
  each). The two collections give the same structural counts:
  - something posted on 39 of 55;
  - the posting budget of 5 reached on 33;
  - the candidate budget's note on 20;
  - `cross_donor_pairs > 0` on only 2 (`pack043`, `pack044`), so the bridges
    are almost never exercised by this benchmark.

  The twenty capacity-one targets of the design note give these `L` values:
  - Pack 4, 5, 8, 9, 11, 13, 16, 23, 28, 29 → 44, 42, 44, 72, 41, 34, 55, 50,
    59, 43;
  - Pack_d 8, 9, 12, 15, 16, 17, 18, 20, 24, 43 → 1274, 1951, 1241, 1198,
    1813, 1591, 1480, 1591, 1623, 2438.

  This audit re-measured our values only. It did not re-check them against
  Sidorov's logs, which the design note's 2026-08-11 cross-check (#708) did.
- **How often the install declines** (a decline is possible only with proofs
  on; `cumulative.md` owns why). Re-running all 110 Pack and Pack_d instances
  with `--prove` gave the same `cliques_posted` and capacity bound as proofs
  off on every one. So there were no declines on that benchmark. The
  generated sweep (seeds 1 to 30, `--size 14`, machine as `Disjunctive` and
  as `Cumulative`) posted the same cliques with the same bound, all 60 runs,
  with `--prove` as without.

## Can it weaken the model?

**Lose solutions:** no. Nothing reaches the OPB, which the test checks byte for
byte. Every derived row is a consequence of the posted rows, and VeriPB checks
each. Solution sets match brute force on cases that post a clique: the
differential fixture's sharp twin (6 solutions), two of the three family shapes
(`k = 3`), variable heights and lengths, and all-optional tasks (328
solutions). They also match on three cases that post nothing, which
therefore test nothing about the derived constraint: the `k = 4` family
shape, mixed optional tasks (140 solutions) and the dominated clique.

**Lose propagation strength:** no. It only adds a propagator. It disables no
donor. The one way its effect varies is install declining with proofs on,
which makes the proofs-on model propagate *less than the proofs-off one*, but
never less than without the presolver. None were seen on Pack or on the
generated sweep (above). Above `Off`, over a `Disjunctive2D` projection, it
installs nothing at all (#1234).

**The wrong line, soundly derived:** guarded by the `ia` pin at the end of
every recipe call, which checks the conclusion is exactly
`Σ_{p ∈ K} cact_{p,t} ≤ 1` over the members' home flags. The mutations above
are what show it bites. A derivation reaching some other true line would fail
there rather than silently giving the propagator a row it does not cancel
against.

## Evidence

### Tests

- **`inferred_disjunctive_presolver`** (`gcs/presolvers/inferred_disjunctive/
  inferred_disjunctive_test.cc`, `run_test_only.bash`) and its
  **`_recovering`** twin (`GCS_CUMULATIVE_ENCODING=both-recovering`, which
  re-derives the donors' per-time rows and checks them against the time-indexed
  block). Both pass at `7e1c4178` (0.94 s). Cases:
  - the differential (a root refutation that no single donor makes),
    `cross_donor_pairs` and `bridges_derived` non-zero, and the capacity bound
    asserted at 6;
  - the certified bound, the same with proofs off, and
    `ClaimHigherMakespanBound` rejected;
  - the sharp twin and three solution-preservation shapes, all against brute
    force (the `k = 4` shape posts no clique);
  - neutrality (node-for-node equality under time-tabling);
  - budgets, and two disjoint edges giving `dropped_too_small = 2`;
  - optional tasks, all-optional and mixed (the mixed case posts no clique),
    plus `ForgetPresence` rejected;
  - the stats names in order, the always-allocate path, caller-handle
    identity, and the note levels for a view-capacity decline and both budgets;
  - variable arguments, converted height, variable duration, a dominated
    clique, and `pair_both_over`;
  - the OPB byte-identical with and without the presolver;
  - the camouflage fixture's three mutations, the proof markers, the
    scaffolding being deleted, and the undefined-flags regression (#1111).
  
  VeriPB runs on every proof the test writes. The enumerations use
  `solve_with` with brute-force comparison, not
  `solve_for_tests_checking_gac`. The test sets no caps of its own, and
  compares complete solution sets, so a cap that truncated would fail it. The
  instances are fixed, and the test's output was identical under `--seed=1`
  and `--seed=2`.
- **`rcpsp_dzn_inferred`** (verified), **`rcpsp_dzn_inferred_disjunctive_mutated`**
  (expected rejection: `--mutate-makespan-bound`), and
  **`rcpsp_dzn_inferred_min_clique_size`** (at 5, so nothing is posted, and the
  mutation must still verify because there is no bound to corrupt).
- **`disjunctive_2d_presolver`**: the presolver over `Disjunctive2D`
  projections, at minimum clique size 2. Its seed-dependent coverage check was
  fixed by PR #1232 (merged 2026-10-04).

**Not covered:**

- any assertion level above `Off`, which is where it breaks (#1234);
- a real instance whose cliques need bridges, other than `sample.dzn`. Pack
  has cross-donor pairs on two instances of 110;
- more than about a dozen tasks, so the quadratic memory and the cubic recovery
  cost are seen by no test;
- a wide horizon;
- a `Disjunctive2D` donor at the default minimum clique size, or mixed with
  posted `Cumulative`s;
- `dropped_over_posting_budget` together with `dropped_dominated`;
- a front end.

### Benchmarks and examples

`examples/rcpsp` is the only driver. For **CPU** benchmarking of the pass, use
the scan probe above at a few hundred to a few thousand tasks. A real
instance's pass is milliseconds: Pack's instances have 15 to 33 tasks. For
**proof verification**, use `sample.dzn` (1,452 lines, 0.02 s) and the two
families at k = 5 to 11 (0.04 to 4.6 s; see the clique rewrite's table). Never run the scan probe
with proofs on above about 200 tasks: the donor recovery it triggers is cubic
(52 M lines and 4.2 GB at 400).

### CPU performance

Only the pass was measured; see [Initialisation](#initialisation-and-global-data).
Nothing compares it against another solver. No other solver infers these
cliques at presolve, and Sidorov's preprocessor is a separate program. #868
covers cross-solver comparison generally.

### Proof performance

See the proof-size table under the clique rewrite. Own against shared, on the
cross-resource family: the presolver's derivations are `21 × 99 = 2,079` of
92,338 lines at k = 11 (2.2%), and the rest is the donors and the search. On
`sample.dzn` they are 81 of 1,452 lines (5.6%), and in the pairwise family
at k = 11, 13%. Nothing was measured at the
assertion levels, because none verifies.

## Status, gaps, and next steps

### Proof-logging gaps

At `Off`: none. Every line the presolver emits is checked, and none is an
assertion. Above `Off`: a proof over a posted donor is rejected under the
default encoding, and over a `Disjunctive2D` projection nothing is installed
under any encoding (#1234). At `Off`, the derived constraint's strength differs
with proofs on only through install declines, which did not occur on Pack or
on the generated sweep.

### Known limitations

- "I enabled it and nothing happened": your machine is a `Disjunctive`, or
  pairwise clauses, or the resources are not `Cumulative`s. Or it is a job
  shop, where nothing can be inferred.
- "I can't turn it on from MiniZinc": no front end has a switch (#983).
- "It used gigabytes on a big instance": the conflict matrix is quadratic and
  the pass holds about three copies at its peak. With proofs on, each posted
  clique keeps one for the whole solve (#705 item 4).
- "The bound I got is lower than `largest_capacity_bound`": some members had no
  makespan link in a shape `find_makespan_links` matches.
- "Hints-only proofs fail with a label error" (under the default
  start-checkpoint encoding), or "with assertions on, a `Disjunctive2D` model
  gets no cliques" (under any encoding): #1234.
- "My model certifies no makespan bound": its lengths are variables (even
  single-valued ones), or its finish rows go through end variables
  (#1257). Or an earlier presolver already pushed the
  same bound.
- "With proofs on and the makespan named, the proof is huge": the bound's
  certificate derives a row at every time point up to it. Pack_d `pack008`
  writes an 822 MB root proof.

### Next steps

1. **Fix the assertion levels** (#1234, owned by `cumulative.md`).
   Small. It makes this presolver usable with the justifier at all.
2. **Trim the recipe's captures and replace the matrix with an adjacency over
   conflicting pairs** (#705 item 4). Small. It takes the pass's peak from
   about three copies of the `n²·104 B` matrix with proofs off, and two plus
   the number posted with proofs on, to `O(pairs + Σ k²)`. Add #705 item 3's
   per-`(witness, t)` cache in the same change.
3. **Wire a front-end switch** (#983, a design call about how presolvers are
   exposed). Both readers already post `Cumulative`.
4. **Fix the Important note's false alarm** (#1258). Small. An
   ungrown pair is harmless when both tasks *and every common neighbour of
   theirs* appear at height ≥ 1 on one donor of capacity ≤ 1. Then it can
   only grow into that donor's own clique, which is dropped as dominated.
   Raise the note only when some ungrown pair fails that test, or filter
   such pairs out of the candidate list before the budget is applied. Checking
   only that the pair itself lies inside such a resource is not enough (see
   failure mode 2).
5. **Drop `dropped_subset`, or keep it with the mutation as its fixture, and
   answer #706.** Trivial. No honest run can fire it.
6. **Accept a posted `Disjunctive` as a capacity-one donor.** Large. It needs a
   flag bridge to Disjunctive's encoding. It would make MiniZinc
   `disjunctive` machines visible (failure mode 1). Measure first: on the
   generated sweep it changed the posted set on 3 of 30 instances and the
   bound on none.
7. **The `c_j ≤ C` discovery filter** the other two presolvers have. Trivial.
   It changes only the reported `L` on an already infeasible donor.
8. **A test above a dozen tasks**, to put the pass's cost and the recovery's
   under a lane.

## Prior art

The inference is Sidorov's (CP 2026), stage one: disjunctive cliques read off
the cross-resource conflict graph, with capacity bound `L` and budgets `N_cover`
and `N_out`. This audit did not survey earlier uses of conflict cliques as
implied unary resources. It knows of no earlier certification of the
inference. Here it is certified per time
point in cutting planes, with the clique merge being the textbook induction
from pairwise at-most-ones.

## Further reading

- [`inferred-disjunctive.md`](../inferred-disjunctive.md): the design note. It
  covers the conflict graph, ranking, the three-member floor and #707's
  measurement, dominance, the certificate in three steps, the #666 scaffolding
  deletion with its table, the camouflage mutations, and the Pack/Pack_d
  cross-check against Sidorov's logs (#708). Two details there predate #1136:
  it says tasks are keyed by start variable alone, where the key is now
  `(start, presence)`, and its mutation table lacks `ForgetPresence` and
  `ClaimHigherMakespanBound`.
- [`certified-makespan-bounds.md`](../certified-makespan-bounds.md): the
  makespan argument and the Pack sweep.
- [`cumulative-proof-logging.md`](../cumulative-proof-logging.md): the
  flag-bridge and derived-row machinery.
- [`cumulative.md`](../constraints/cumulative.md): the derived Cumulative's
  rules, declines and makespan initialiser.
