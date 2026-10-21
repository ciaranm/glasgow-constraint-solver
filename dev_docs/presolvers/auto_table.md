# `auto_table`: search a caller-named scope at the root, and propagate the table of what survives

> **Maturity** production, opt-in: reached from the C++ API and four examples
> only · **Audited** 2026-10-20 at `86caad24` · **Open issues** filed by
> this audit (see [Next steps](#next-steps)):
> - #1378: its throwaway root search strands other propagators' first-call
>   state. An incremental difference propagator throws, and
>   `propagate_extensional`'s root width trim is lost, for a posted `Table`
>   and for every tabulated constraint;
> - #1379: the proof's backtrack clauses grow with the square of the tuple
>   count.
>
> Commented on by this audit: #816 (the subproblem search ignores the abort
> flag, a case #816 already claims), and #1374, now asked to cover every
> presolver (`glasgow_scp_solver` can add none, this one included; the
> comment was written with
> [`parity_system_gathering.md`](parity_system_gathering.md)'s audit).
> Already open and touching it: #983 (no front end can add it), #1210
> (`AssertionLevel::Links`), #1309 (installs under one unnamed constraint
> grow its scope), #868 (cross-solver). Filed in review of this document:
> #1387 (a zero-tuple run on a reused stats block keeps the previous
> `compact_table`). Machinery owned by
> [`table.md`](../constraints/table.md): #1116. Tracked under #871.

`AutoTable{vars}` is told a scope by its caller and does no detection of its
own. Before search, it runs a complete search over the scope's variables,
propagating **the whole model** at every node, and records every assignment
of the scope that propagation does not refute. It then installs one
extensional propagator (`propagate_extensional`) over that table, **beside**
every posted constraint, none of which it touches. With proofs on, each table
entry is defined in the proof by two `red` lines over a proof-only selector,
and the logged subproblem search derives the at-least-one that makes the
table a consequence of the model. Nothing is written to the OPB. The
extensional propagator, its proof rules, its state, its idempotence and its
hole sensitivity are [`table.md`](../constraints/table.md)'s. This document
owns what is tabulated, the subproblem search and its cost, the proof of
each entry, what the presolver does to the rest of the model, and its entry
points. There is no design note. This document audits the presolver against
the presolver variant of the
[template](../constraints/TEMPLATE.md#the-presolver-variant).

Five things to know before touching it.

- **The table is "what root propagation leaves", not "the solutions of some
  constraint".** It contains every assignment of the scope under which a full
  propagation of the model does not fail. Constraints wholly inside the scope
  are respected exactly. Constraints that reach outside it contribute only as
  far as propagation notices, and constraints elsewhere contribute through
  propagation chains. So the table lies between the projection of the
  model's solutions and the solutions of the constraints inside the scope.
  On 10,000 random models, the tuple count was always within those two
  bounds, and the domains were generalised arc consistent over the scope's
  variables, relative to the constraints inside it, at every one of 75,370
  branching nodes. See [Rewrite:
  install-table-propagator](#rewrite-install-table-propagator).
- **Its throwaway root search breaks a premise other propagators rely on.**
  The subproblem's first `propagate()` enqueues every installed propagator,
  so their first call happens there, below a `TrueLiteral` guess, and then
  `AutoTable` backtracks out of it. A propagator that keeps a "first call
  done" marker outside backtrackable state is left believing the root work
  is done. #1106 was this (`NegativeTable` and refined `Nogoods`), and
  fixed. This audit found two more members of the class (#1378):
  - an incremental difference propagator, posted or installed by an earlier
    `DifferenceLogic`, **throws `UnexpectedException`**;
  - `propagate_extensional`'s root width trim is lost. On a posted `Table`
    with a wide column, a 191-line proof became 3.6 million lines and 20 GB
    at width 10⁵. A tabulated `Power` over a wide variable went from 4 ms to
    no answer in 60 s.

  A code read and a 485-lane sweep under an injected pseudo-root `AutoTable`
  (the fact-check's) found no other member.
- **No front end can add it** (#983). It is reached from C++, from
  `examples/auto_table`, and from three examples' `--autotable` or
  `--variant auto-table` flags. Since the `.scp` is a model and this is a
  solve option, `glasgow_scp_solver` cannot reach it either (#1374, which
  asked for that binary's difference-logic switch and is now asked to cover
  every presolver).
- **Its cost is a search, with no budget and no stop.** It is proportional
  to the subproblem's nodes, plus `T` tuples of storage. The subproblem's
  root is a full propagation of the model, and every other node propagates
  incrementally. It ignores the abort flag (#816).
  With proofs, the backtrack clauses carry every selector value found so
  far, so proof bytes grow at least as `T²/2`. That is 238 MB at 4,032
  tuples, against 2.2 MB for a few-line fix (#1379).
- **Its proof is written only at `AssertionLevel::Off`.** Above `Off` it emits
  nothing of its own: no entries, no backtracks. So a model whose subproblem
  has no solution, and that root propagation does not refute, gets a proof
  VeriPB rejects at `Definitions` and `Links`. Above-`Off` levels are not
  fully designed, so this is recorded, not filed. See
  [Proof-time state](#proof-time-state).

## What it is

### Semantics

`AutoTable{vars, stats = nullptr}` is a `Presolver`, added with
`Problem::add_presolver`, which stores a clone. `solve_with` calls the
clone's `run` once. A caller that passes no stats block still gets one.

**When it runs.** As every presolver does: after `create_propagators`, after
the proof model is finalised, and after the posted constraints' initialisers
(`solve.cc:373`). Nothing has propagated yet. If an initialiser refuted the
model, no presolver runs. After `run` returns, `solve_with` initialises
whatever it installed before the next presolver runs (`:377-397`). This one
installs no initialiser. `choose_optional_interior_pruning()` runs after the
last presolver (`:407`).

**What it does** (`auto_table.cc:110-173`):

1. It registers its stats block and sets `ran` and `variables`
   (`:114-116`).
2. It builds a brancher over the scope: `dom_then_deg(vars)` with
   `value_order::smallest_first()`, one child `x = v` per value (`:122`).
3. It opens a sub-search epoch, `new_epoch(true)`, and guesses `TrueLiteral`
   (`:124-125`). It reserves the next `State` variable identifier for the
   selector (`:131`).
4. It runs `solve_subproblem` (`:40-107`). At every node it calls
   `propagators.propagate()` over **every installed propagator**, with no
   abort flag. If that fails, the node is a dead end. If it succeeds and the
   brancher has nothing left to branch on, every scope variable is fixed, and
   the node's assignment of the scope is a new tuple (`:60-86`). Otherwise it
   branches on each value of the chosen variable.
5. It backtracks out of the epoch (`:137`), which undoes every domain change
   the subproblem made and drops the extra proof conditions.
6. With no tuples it returns `false` (`:139-140`). `solve_with` then
   concludes unsatisfiable without searching.
7. Otherwise it allocates the selector as a `State` variable over
   `0 .. T − 1`, where `T` is the number of tuples, and checks that it got the
   reserved identifier (`:142-144`). It offers the compact-table arm when
   `T ≥ 64` (`create_for_auto`, `extensional_utils.cc:69-72`). It installs
   `propagate_extensional` over the table under `CurrentlyUnnamedConstraint`,
   with `on_change` triggers on the scope (`:158-170`), and returns `true`.

**What is tabulated.** Write `S` for the scope's positions and `D` for the
domains at the time the presolver runs. The table is

> `Tab = { t ∈ D(S) : propagating the model with S fixed to t does not fail }`

as reached by that search, and `T = |Tab|`. A node whose propagation fixes
the whole scope is a leaf whether or not a branch was taken, and a partial
assignment that propagation refutes refutes every tuple below it. Two bounds
follow, and the brute-force probe checks both:

- `Tab ⊇ π_S(solutions of the model)`. A tuple is dropped only when
  propagation refutes it, and propagation is sound.
- `Tab ⊆ solutions of C_in over D(S)`, where `C_in` is the set of constraints
  whose variables all lie among the scope's variables. A tuple fixes every
  variable of such a constraint, and a propagator must reject a full
  assignment of its own scope that violates it. For a constraint with
  internal auxiliaries (`Divide`, `Modulus`, `Power`, `ArgSort` and
  `SmartTable` allocate them), fixing the scope does not fix the auxiliaries,
  so this rests on the constraint's own propagation deciding it. The
  tabulated constraints' selector (`tabulation.cc:179`) is one more such
  auxiliary: decided by the scope only on the proof side, and left
  unnarrowed in the `State`, but no propagator reads it
  (`tabulation.cc:182-183`), so it cannot keep a refuted tuple alive. The
  bound held on all four constraints the fact-check tried, with the scope
  over every user variable:
  the tuple count equalled the brute-force solution count for `Divide` (65),
  `Modulus` (66), `Power` (60) and `ArgSort` (27).

Between those, which tuples survive depends on what the propagators of
constraints only partly inside the scope can see with the scope fixed.

**What it never does.** It never removes, disables or rewrites a posted
constraint. It writes nothing to the OPB, since `Presolver::run` is handed no
`ProofModel`. It leaves the domains as they were before it ran: the
subproblem's root propagation is undone too, and the search repeats it.

**Degenerate cases** (probe `shapes/shape.cc`, every row with and without the
presolver against the same solution set, both declaration styles):

| Scope | What happens |
|---|---|
| empty, `AutoTable{{}}` | one tuple over zero variables. A propagator with no triggers is installed; it runs once, at the root, and does nothing |
| one variable | the table is the values root propagation leaves it, e.g. 2 tuples for `x ∈ 0..3`, `x ≠ 2`, `x < y` |
| a variable no constraint mentions | the table is its whole domain: 4 tuples for one variable over `0..3`, 16 for two |
| every variable of the model | the table is the solution set, 8 tuples on the `auto_table` example's model |
| a constant, `AutoTable{{x, 2_c}}` | the constant's column is constant. Its literal is `TrueLiteral`, which the renderer folds into the rows' degree: `red 2 ~s 1 [x = 0] >= 1` |
| a repeated variable, `{x, x, y}` or `{x, x + 1, y}` | the repeated columns agree in every tuple |
| a view, `{x + 1, −y}` | the tuple holds the views' values. The entry rows are written over the underlying variables: `x + 1 = 1` as `[x = 0]`, `−y = −3` as `[y = 3]` |
| one tuple | e.g. `x + y = 4` over `0..2` gives `(2, 2)`, found at the subproblem's root, in one node |
| a subproblem with no solution | `run` returns `false`, the stats say `found no satisfying assignment`, and the solve is unsatisfiable |

### Concrete constraints and frontend coverage

The entry-point table, with one row because there is one class:

| Entry point | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `AutoTable` (presolver) | `frontend gap (#983)` | `frontend gap (#983)` | `frontend gap (#983)`¹ | `frontend gap (#1374)`² | C++ API; `examples/auto_table` (always on), `examples/skyscrapers --autotable`, `examples/shikaku --autotable`, `examples/table_layout --variant auto-table` |

1. `python/gcspy.cc` has no presolver plumbing, so CPMpy, which drives the
   solver through it, cannot reach any presolver. Checked by grep at
   `86caad24`: no front-end source names `AutoTable`. #983's table calls
   this column `gcspy`.
2. A `.scp` is a model and a presolver is a solve option, so this is
   `glasgow_scp_solver`'s gap, not the format's. #1374 records it: it asked
   for the difference-logic switch, and a comment now asks it to cover every
   presolver (#983's table has no `.scp` column). `glasgow_scp_solver.cc` and `scp_reader.cc`
   never call `add_presolver`. A switch for this presolver would also need
   a way to name the scope.

A front end would also need a way to **name the scope**, which none has.
That is the design question in #983 for this presolver. The nearest
vocabulary is the `::presolve(autotable)` predicate annotation of Dekker et
al.'s 2017 MiniZinc extension ([Prior art](#prior-art)). It is not in
current MiniZinc: 2.9.7 and 2.10.1 both reject it ("undefined identifier
`autotable`"), and their standard library never mentions `presolve`.

### Options

None. The constructor takes the scope and an optional `AutoTableStats`
block to share with the caller. There is no budget, no node limit and no
algorithm choice; the installed propagator takes `table::Auto`'s behaviour
through `create_for_auto`. Nothing changes the OPB.

### Variable kinds and views

The scope is a `vector<IntegerVariableID>`, so plain variables, views and
constants are all accepted, and so is a repeated variable. The subproblem's
brancher branches on views as on any variable, and skips anything fixed, so
a constant is never branched on. Each tuple records `state(var)`, the
position's own value. The installed propagator takes the same positions.

**The proof handles all of them.** An entry's rows are written over
`var == value` for each position. A view's literal is rendered over its
underlying variable, and a constant's is `TrueLiteral`, folded into the
degree. A repeated variable contributes its literal twice. An empty scope
gives `red >= 0` and `red 1 s >= 1`. All of these verify at `Off`: in the
shapes probe, in 300 random instances with views, constants and repeats,
and through the cake chain for the view and constant shapes ([Cake
conformity](#cake-conformity)).

### Reification

None. There is no conditional form, and none is wanted: the table is a
consequence of the model, so it holds unconditionally.

### Relation to other families

- **Decomposes into this presolver:** nothing.
- **What it installs:** `propagate_extensional`, the propagator of
  [`table.md`](../constraints/table.md), over a table the presolver builds,
  with no hint and no owning constraint. Its rules 2–5 are that document's.
- **Shares its code.** `propagate_extensional`, `ExtensionalData`,
  `ExtensionalLiveTuples` and `ExtensionalCompactTable::create_for_auto`
  are `extensional_utils`'s, shared with `Table` and `install_tabulation`.
  `State::add_extra_proof_condition` exists for this presolver, per its
  header comment ("for use in autotabulation and similar"), and nothing else
  calls it or `new_epoch(true)`.
- **What it does to every other family.** Its subproblem calls every
  installed propagator, and the first of those calls is at the subproblem's
  root, below a `TrueLiteral` guess, inside an epoch it then pops. Three
  members of this bug class are known; (a) and (b) are this audit's, filed
  together as #1378:
  - `NegativeTable` and the refined `Nogoods` lost every watch (#1106,
    fixed by #1107). `logical.md` and `table.md` record the lesson, as does
    `refined-triggers.md` on main. `negative_table_test`, `nogoods_test` and
    `logical_test` run lanes behind a "pseudo-root" `AutoTable` over a fixed
    variable to hold it: a fresh one in the first two, and in `logical_test`
    the constant-valued `one` that a clause set mentions.
  - **(a) The incremental difference propagator throws.** Its first call
    checks that `state.guesses()` is empty (`difference_graph.cc:1312-1316`)
    and throws if not (`:905-908`), and `AutoTable`'s `TrueLiteral` guess is
    yielded. That covers a posted `DifferenceConstraints` and a
    `DifferenceLogic` added before the `AutoTable`, both in their default
    incremental mode; `incrementally(false)` on either solves. A scratch
    build without the guess stops the throw, and shows what the throw was
    protecting: the first-call memory survives the backtrack, the
    reproducer takes 40 recursions instead of 30, and the propagator's own
    audit reports lost propagation. The premise is written down in the code
    (`difference_graph.cc:1309-1310`, "Search propagates everything before
    it guesses anything, so this cannot happen") and in
    [`difference.md`](../constraints/difference.md) (:414-417, open PR
    #1376): "cannot happen because root propagation runs before any guess".
    With an `AutoTable` it can.
  - **(b) `propagate_extensional`'s root trim is lost.** It runs once, behind
    `residues.initialised` (`extensional_utils.cc:755-836`), and its
    removals are undone by the backtrack. The real root never re-trims, so
    the support scan walks the domain. That reaches every caller: a posted
    `Table`, every tabulated constraint (`install_tabulation`), and an
    earlier `AutoTable`'s own table (by the same code path; not measured).
    This is not #1116, whose paths are a
    trim that runs after the rasteriser has already walked the domain and a
    trim that never runs; here the trim runs, in the wrong epoch.
  - **What the class survey covered** (the fact-check's, recorded in
    #1378). It read every `shared_ptr` captured by a propagator or initialiser,
    every mutable lambda, flag members, statics, refined-watch users and
    cached `ProofLevel::Current` lines. It found nothing else, and cleared
    `Regular`'s and `MDD`'s graphs (constraint state), `AllDifferent`'s value
    lookup (built from fixed values) and the extensional bitmaps and support
    masks (built from the tuples). It also relinked 485 `ctest` lanes against
    a `solve_with` that runs a pseudo-root `AutoTable` first (not
    `solve_test`, which includes `solve.cc`). The only real differences were
    (a) and (b); the rest were harness artefacts, such as counted proof
    markers, propagator counts, `Stats::propagations`, and root-unsatisfiable
    presolver fixtures whose presolver then never ran. That cannot rule out state that matters only on
    models no lane posts, or effects on cost and heuristics alone, such as
    `table::Auto`'s 32-wake decision, which counts the throwaway search's
    wakes.
- **Other documents' descriptions.** `table.md` (:244-246) said the
  presolver "enumerates the solutions of its donor constraints over a
  scope". It has no donors, and the table is what propagation leaves, which
  can be a superset of the projected solutions ([Semantics](#semantics)).
  `element.md` (:265-266) said `gcs/constraints/table/` "is what an
  `Element` becomes under `AutoTable`". The `Element` stays posted and
  propagating; the table is added beside it. Both were stack text, fixed
  by this round's corrections to the older documents, as is
  [`difference.md`](../constraints/difference.md)'s premise quoted under (a).
- **Presolvers, and order.** A presolver added earlier has installed its
  propagators by the time this one runs, so they prune its subproblem. One
  added later has not. So the order matters:
  - **Two `AutoTable`s over overlapping scopes.** The later one's
    subproblem runs the earlier one's table. On 2,000 random pairs over
    linear equalities (`order/order.cc`, seed 1), the tuple counts depended
    on the order in 89, the node counts in 1,712, and the solution counts
    (counts, not sets) in none.
    An earlier table with no tuples refutes the model, and the later presolver
    does not run.
  - **`DifferenceLogic` before `AutoTable` throws** in its default
    incremental mode whenever it installs a propagator (two edges or more;
    #1378); with `incrementally(false)`, or added after the `AutoTable`,
    the solve is correct.
  - `CumulativeStrengthening`, `InferredDisjunctive` and `InferredCumulative`,
    each before and after an `AutoTable`, on one small model with a
    `Cumulative`, a `Disjunctive` and a `ParityOdd` (`sched/sched.cc`). This
    gave the same 2,040 solutions throughout, and every proof verified. Only
    `InferredCumulative` installed anything there (5 inferred constraints);
    the other two found nothing, so for them the probe says little.
  - `ParitySystemGathering` found nothing on that model. Its own order probe
    ([`parity_system_gathering.md`](parity_system_gathering.md)) gathers the
    same 2 rows over 3 atoms into 1 system with an `AutoTable` before or
    after it, with the same solutions and recursions, and every proof
    verifies (re-run by the cross-document check).
  - Of the other presolver documents, only `parity_system_gathering.md`
    mentions `AutoTable`: its order probe, and that an `AutoTable` refuting
    the model first leaves it no stats block. `difference_logic.md` records
    that its presolver added before an `AutoTable` throws (#1378), in its
    order list, Known limitations and header, through this round's
    corrections to the older documents.
- **Reachability:** C++ and the examples only (#983).

## The proof model

### OPB encoding

Nothing. The OPB and the `.scp` are byte-identical with and without the
presolver (the `auto_table` example's model, compared with `cmp`).

### Labels

None. The entry rows are proof lines, cited by unit propagation rather
than by name.

### Cake conformity

There is nothing to conform, since nothing is written to the OPB. The cake
chain still re-checks the presolver's proof lines, because they are in the
`.pbp`. Run by hand at `86caad24` on the shapes probe's `.scp` and `.pbp` at
`Off` (`cake/`), steps 2 to 4 of `run_scp_chain.bash` (cake re-derives the
OPB, VeriPB elaborates against it, cake re-checks the core) passed for every
one tried:

- the example's model, ranges and value lists;
- the two-`AutoTable` shape;
- the empty-subproblem shape (`VERIFIED UNSATISFIABLE`);
- the 268-tuple compact-table shape;
- the view and constant scopes;
- an optimisation.

No chain lane exists for it, and none can be added: `glasgow_scp_solver`
has no presolver switch (#1374), and a switch for this presolver would
also need a way to name the scope.

### Proof-time state

**At `AssertionLevel::Off`**, the only level at which the presolver writes
anything of its own (`auto_table.cc:46`, `:65`, `:99`):

- **A proof-only selector.** Its identifier is reserved before the search and
  allocated as a `State` variable after it. Each selector value `j` becomes a
  literal when its tuple is found, through
  `create_literals_for_introduced_variable_value`. Its name is the
  `State` index followed by `intr_autotable`, e.g. `i[5intr_autotable][eq0]`
  (`names_and_ids_tracker.cc:915-923`). It has no bits and no
  order literals.
- **Two `red` lines per entry**, at `ProofLevel::Top`, after a comment `new
  table entry found` (`:66-82`):

  ```
  red 3 ~i[5intr_autotable][eq0] 1 i[v[0]][eq1] 1 i[v[1]][eq3] 1 i[v[2]][eq2] >= 3 : i[5intr_autotable][eq0] -> 0;
  red 1 i[5intr_autotable][eq0] 1 ~i[v[0]][eq1] 1 ~i[v[1]][eq3] 1 ~i[v[2]][eq2] >= 1 : i[5intr_autotable][eq0] -> 1;
  ```

  That is `n·¬s_j + Σ_i [x_i = t_j[i]] ≥ n` and
  `s_j + Σ_i [x_i ≠ t_j[i]] ≥ 1`: `s_j ⇔ (x = t_j)`, in the style of
  Encoding Procedure 3.10. Then `¬s_j` (the selector `≠ j`) is added as an
  extra proof condition (`:83`).
- **One backtrack line per subproblem node**, a `rup` written at level
  `depth` (its parent's propagation level) on the way out, over the negated
  guesses and **every** selector literal found so far (`:99-106`,
  and `innards/state.cc:821-828`, which yields the extra conditions first).
  The line at the subproblem's root is
  `s_0 ∨ … ∨ s_{T−1}`, the table's at-least-one, at level 0, which the
  search never forgets. Each node's propagation lines go at level
  `depth + 1` and are deleted on the way out. Of the presolver's own lines,
  only the selector definitions and the at-least-one survive it. The
  literal-layer definitions the subproblem caused (the `=` and `≥` atoms
  first named there, at `Top`) survive too.
- **In the OPB or in the proof?** In the proof only, per
  `variable-encodings.md`. Not in `preserved:`. Each `s_j` is determined by
  unit propagation on any full assignment of the scope, both ways, so a
  `solx` line never needs it.
- **What a reconstructor can find by name.** The selector literals, by the
  `intr_autotable` suffix. Nothing labels the at-least-one, and the
  installed propagator's RUPs cite nothing: they propagate through the
  forward halves and the at-least-one.
- **Nothing dangles with proofs off.** The selector `State` variable is
  allocated either way, as one unused variable.

**Above `Off`** (`Definitions`, `Links`, `Inferences`, `Backtracking`), the
presolver writes no comment, no selector literal, no entry row and no
backtrack. The subproblem's propagation still runs with the logger, so at
`Definitions`, `Links` and `Inferences` **the other propagators' inferences
in the subproblem are written** as `a` lines, and are never deleted. At
`Backtracking` no inference is written at all, so the subproblem leaves
nothing: the example's proof there holds only its 15 `::backtrack:` and 8
`::solx_block:` assertions. The installed propagator's inferences are asserted with **no
annotation at all**. This is the wire form `table.md` calls "empty"; the
`a` lines in the example's proof at `Inferences` look like
`a 1 ~i[v0][ge4] 1 ~i[v0][ge1] 1 i[v0][ge6] 1 ~i[v1][ge1] 1 i[v1][ge6] 1 ~i[v2][ge1] 1 i[v2][ge6] >= 1;`
(a bound push under the generic reason) and
`a 1 ~i[v2][eq3] … >= 1;` (an unsupported value). None is a bare unit
clause without a reason.

What that does at each level (`shapes/`, the example's model and 18 more
shapes, each declared as ranges and as value lists; `gacbf/pf/`, 300 random
instances, of which 68 unsatisfiable):

| Level | With at least one tuple | With no tuple, and the subproblem's root not refuted |
|---|---|---|
| `Off` | `VERIFIED` (all) | `VERIFIED` |
| `Definitions` | `UNDER ASSERTIONS` (`VERIFIED` when nothing is asserted, as on two free variables) | **rejected** at the final `rup >= 1` |
| `Links` | rejected at the first `solx` or `soli` for a range-declared variable, with or without the presolver (#1210); otherwise `UNDER ASSERTIONS` | **rejected** at the final `rup >= 1` |
| `Inferences` | `UNDER ASSERTIONS` | `UNDER ASSERTIONS` |
| `Backtracking` | `UNDER ASSERTIONS` | `UNDER ASSERTIONS` |

The no-tuple rejection is the presolver's. `ProofLogger::backtrack` RUPs a
backtrack at levels up to `Links` and asserts it above, and
`conclude_unsatisfiable` does the same with the empty clause. The presolver
skips its backtracks at every level above `Off`, so at `Definitions` and
`Links` the final RUP has nothing to stand on. The same model without the
presolver is `UNDER ASSERTIONS` at both. Four of the 300 random instances,
and both `unsat` shapes, hit it: the fact-check confirmed that the four are
exactly the zero-tuple instances whose subproblem branched (4 or 5 nodes);
every other zero-tuple instance was refuted at the subproblem's root, in
one node. Higher
assertion levels are "not fully designed or implemented", so this is
recorded rather than filed. Delegating to `logger->backtrack` at every
level, as the main search does, looks like the shape of a fix.

## The implementation

### Initialisation and global data

The four costs the template asks to keep apart:

1. **The presolver's own pass: the subproblem search.** It visits `N` nodes,
   reported as `search_nodes`. The root is a full propagation of the model,
   enqueuing every propagator, which the search then repeats; every other
   node wakes only what its guess triggers. `N` is at most the size of the
   `smallest_first` tree over the scope, `1 + d + d² + … + dⁿ` for `n`
   positions over domains of at most `d` values: exponential in the scope's
   size in the worst case. Storage is `T · n`
   integers for the table. 2,162,160 tuples over six variables peaked at
   267 MB (`abort/`). There is no budget, by design, and no stop: the
   abort flag is not consulted (#816).
2. **Initialisers it installs:** none.
3. **The installed propagation during search:** `table.md`'s, over `T`
   tuples. The first call, at the real root, trims and rasterises as that
   document says, unless a later `AutoTable`'s subproblem made that first
   call (#1378). Installing it under the shared
   `CurrentlyUnnamedConstraint` adds its scope to that constraint's
   scope, whose deduplication is linear per trigger (#1309); negligible
   at these sizes (`skyscrapers 9`: 18 tables of 9 positions).
4. **Certificate generation**, at `Off` only. There are two `red` lines per
   tuple of `n + 1` terms each, plus the `=` and `≥` atom definitions of
   any value first named there. There is one backtrack line per node, of (decisions on the
   path) + (tuples found so far) literals. The second term puts the
   presolver's own selector literals between `T(T+1)/2` and `N · T`,
   depending on where the dead ends fall: about `T²/2` when they are few or
   come before the tuples, up to `N · T` when they come after (#1379;
   [Proof performance](#proof-performance)).
   The subproblem's other propagators log their inferences at every node,
   as they would in search.

The subproblem's propagation is counted in `Stats::propagations` and its
effectful and contradicting siblings, but not in `recursions` or `failures`
([Evidence that it fired](#evidence-that-it-fired)).

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| the presolver's pass (`AutoTable::run`) | — (runs once, before search) | — | the rewrites below | always, once per solve | n/a | n/a |
| `propagate_extensional` for `AutoTable` | `on_change` on every scope position | derived, truthfully | `table.md` rules 2–5 | the pass found at least one tuple | claimed (`EnableButIdempotent`); the engine drops the claim when two positions share a variable | no |

The second row is `table.md`'s, restated so that this document's inventory
is whole; that document argues the idempotence claim and the strength with a
repeated variable. For this caller the repeated-variable weakness cannot
arise, because every tuple is a consistent assignment of the scope's
variables (see [Rewrite: install-table-propagator](#rewrite-install-table-propagator)).

### Mutable state and incrementality

The pass keeps nothing between solves except its stats block, which it
fills by assignment. The search count is accumulated in a local, so a block
shared across two solves that both reach `run` reports the later solve's own
nodes beside its own tuples (`:128-130`). That holds for `ran`, `variables`,
`tuples` and `search_nodes`, with two exceptions:

- a run that finds no tuple returns (`:139-140`) before it assigns
  `compact_table` (`:159`), so a reused block keeps the previous run's
  value (#1387);
- a solve that never reaches `run` leaves every field as the last run that
  did left it (see [Evidence that it fired](#evidence-that-it-fired)).

Two `AutoTable`s sharing one block in one solve report the later run only,
apart from `compact_table` when the later run finds no tuple (#1387 again),
and the solve's `Stats` lists the block once (`stats.cc:47-50`). These
cases are `e4-stats/stats.cc`'s A to E, one of this document's review-round
probes (at `86caad24`, fataepyc-08, 2026-10-21): A the zero-tuple exception,
B a solve that never reaches `run`, C and E two `AutoTable`s on one block
(E with a zero-tuple later run), and D a later run with tuples. The installed
propagator's state is `table.md`'s, and the selector `State` variable, which
the propagator no longer reads, costs one domain copy per epoch.

What the pass does to **other** propagators' state is the point of the
[Relation to other families](#relation-to-other-families) list: its
sub-search epoch is popped, and everything a propagator keeps outside
backtrackable state survives that.

### Interior values and optional pruning

**What this presolver offers.** None: it installs no
optional-interior-pruning pair.

**What it observes.** The installed propagator's `on_change` triggers make
holes in every scope variable (for a view, its underlying variable; for a
constant, nothing) affect its propagation, and that is true. A table support
can depend on any value. So adding an `AutoTable` keeps alive any other
constraint's optional interior pruning on the scope's variables when
`choose_optional_interior_pruning()` runs after the last presolver.

The subproblem itself runs **before** that choice, with every optional
pruning on, as `solve_with` and
[`optional-interior-pruning.md`](../optional-interior-pruning.md) say. So
`T` may be smaller than what the search's final propagators would refute.
That is only ever stronger, and sound either way, since every refutation is
a propagation.

### Robustness and limits

- **Unbounded domains.** The search branches on every value of every scope
  variable. A scope variable over `0..10⁹` is `10⁹` children at its level,
  and that many tuples if nothing prunes it. This is tabulation's cost by
  definition, not a scan that could be interval-shaped.
- **Negative values and zero.** Nothing special. The random instances use
  `−2..3`.
- **Degenerate shapes.** See [Semantics](#semantics): every one gives the
  same solutions as without the presolver, and verifies at `Off`.
- **Overflow.** The pass does no arithmetic on values. Each tuple holds
  values already in a domain, so already within the range policy. The entry
  rows' coefficients are `n` and `1`. The selector's domain `0 .. T − 1` goes
  through `allocate_integer_variable_with_state`'s range check; reaching
  that limit needs more tuples than memory holds.
- **The identifier check** (`:143-144`) throws `UnexpectedException` if
  anything allocates a `State` variable during the subproblem. Nothing can:
  propagators receive a `const State &`, and initialisers do not run inside
  `propagate()`.

### Interval efficiency

1. **The propagation side.** The pass walks values by design: the brancher's
   `smallest_first` yields one child per value through `s.each_value(var)`
   (`search_heuristics.cc:473-481`). The table it builds is per tuple, and
   enumerating tuples is what the presolver is for. It is the
   `consistency::Tabulated` trade, chosen by the caller naming a scope,
   with no weaker arm behind it. No other site in the pass walks values. The
   installed propagator's sites are `table.md`'s (#1116), plus the trim lost
   to this presolver's throwaway search, on every `propagate_extensional`
   caller (#1378).
2. **The reason side.** The pass builds no reasons. A backtrack clause has one
   literal per decision on the path, not per value, plus the selector literals
   (#1379). Reason assembly for the installed propagator is `table.md`'s.
3. **The proof side.** Every entry is per tuple, which is per value
   combination. There is no width gate, and none is possible: an entry is a
   value combination. An entry names one `=` literal per position, whose
   definition is emitted on first use over the variable's encoding, so the
   bit encodings survive any clamp.
4. **The audit lane.** `large_domain_audit_test.cc` has no `AutoTable` row
   and none in its proof-size case. So it varies none of the axes: not the
   width, not the scope, not what the scope's variables carry, and not the
   effect of the throwaway search on other rows' first calls, which is where
   #1378's trim case lives. [Next steps](#next-steps) has an item.

## Rewrite catalogue

These facts hold for every entry:

- The presolver adds nothing to the OPB.
- Everything it writes to the proof is at `AssertionLevel::Off`, and nothing
  it writes there is an assertion. Above `Off` it writes nothing, so the
  hints-only form of every entry is empty.
- The installed propagator's later inferences are certified by `table.md`'s
  rules 2–5, which are RUP against this presolver's rows.

The four entries are one mechanism split where the template asks: a
selector introduced, a cover derived, a propagator installed, and a refutation.

### Rewrite: define-table-entry

- **Pattern.** A leaf of the subproblem search: a node whose propagation
  succeeded and left every scope position fixed (`auto_table.cc:60`).
- **Posts.** Tuple `t_j`, appended to the table. With proofs at `Off`, the
  selector literal `s_j` and its two defining `red` lines.
- **Derived mode.** Nothing is posted as a constraint. The definitions are
  proof lines only.
- **Why it is true.** `s_j` is a fresh symbol, and the two lines say exactly
  `s_j ⇔ ∧_i (x_i = t_j[i])`. A definition of a fresh symbol by an
  equivalence adds no consequence over the original variables.
- **Proof technique.** `redundance`, twice: the forward half with witness
  `s_j → 0`, the reverse half with witness `s_j → 1`. Licensed by Theorem 2.4
  (extension variables); the `s_j` are fresh because their identifier was
  reserved from `State` and named on first use. This is the standard
  reification pair, and Encoding Procedure 3.10's tuple flags have this shape.
- **Neutral?** Yes, alone: nothing propagates from a definition.
- **Offline reconstructibility.** `search`: a reconstructor can introduce
  such definitions itself, but which tuples to define is not in the baseline
  context. It is the presolver's own search, of the cost in
  [Initialisation](#initialisation-and-global-data), rerun over the whole
  model. Nothing in a hints-only proof points at it. Only a reconstructor
  that rebuilds the table needs the entries: the installed propagator's
  assertions can be derived without them ([Rewrite:
  install-table-propagator](#rewrite-install-table-propagator)).
- **Proof size.** Three lines (a comment and two `red`s) of `n + 1` terms
  each, plus the `=` and `≥` atom definitions for values first named here.
- **Gaps.** None at `Off`. Above it, the entries do not exist in the proof.
- **Tightness.** By hand on the example's proof (`mut/`, not a committed
  lane):
  - dropping entry 0's reverse half is refused at that leaf's backtrack;
  - naming the wrong value in its forward half is refused at the reverse
    `red`;
  - naming the same wrong tuple in both halves, a self-consistent wrong
    definition, is refused at the leaf's backtrack (see [Can it weaken the
    model?](#can-it-weaken-the-model));
  - replacing the forward half with a tautology (keeping the line ids) is
    refused at the installed propagator's first root RUP, `mut/m5b.pbp:755`
    in the fact-check. Deleting the line outright is refused earlier, but only
    because the next `pol`'s relative ids then point at a deleted line, which
    shows nothing.

### Rewrite: cover-the-scope

- **Pattern.** Every node of the subproblem search, on the way out.
- **Posts.** At `Off`, one backtrack clause per node:
  `¬(decisions on the path) ∨ s_0 ∨ … ∨ s_k`, over every tuple found so far.
  At the subproblem's root that is `s_0 ∨ … ∨ s_{T−1}` (the cover), kept at
  level 0 for the whole proof. The deeper clauses are deleted with their
  level.
- **Derived mode.** Proof lines only.
- **Why it is true.** By induction up the tree. At a leaf, the decisions fix
  the scope to `t_j`, so `s_j` holds. At a dead end, propagation refuted the
  decisions. At an inner node the children's clauses cover every value of
  the branching variable, and some value must hold. So every assignment of
  the model satisfies some `s_j`: the solutions project into the table.
- **Proof technique.** A `RUP sequence`, one step per node, in the order the
  search finishes them, which is the solver's own backtracking-search
  certificate. At a leaf the RUP is the reverse half of the new entry
  against the propagation lines on that path, by unit propagation. At an
  inner node it is the children's clauses
  plus the branching variable's at-least-one over its values from the
  literal layer. At a dead end it is the logged refutation at that node.
  The procedure is the one every backtrack in the solver uses; what is
  particular here is the extra disjuncts, which come from assuming `¬s_j`
  for each tuple found. This is a different mechanism from CP 2022's, which
  used one flag `g ⇔ ∨ s_j` and an extra guess about `g` in a logged search
  that ends in a proof of `g`. For that, the guess has to be `¬g` (no tuple
  selected), though the paper prints a plain `g` (see [Prior
  art](#prior-art)).
- **Neutral?** Yes, alone. The cover is what makes the next rewrite's
  propagation certifiable.
- **Offline reconstructibility.** `search`, as the entries: the cover needs
  the subproblem's own search to rebuild. Above `Off` none of its lines
  exist, not even as assertions. Nothing marks where the subproblem began,
  apart from the `a` lines its propagators left at `Definitions`, `Links`
  and `Inferences` (with the literal-layer definitions it caused, at
  `Definitions` and `Links`); at `Backtracking` it leaves nothing.
- **Proof size.** One line per node, plus the deletions. Each line holds
  the path's decisions (`O(N · n)` in all) and **every selector literal found
  before it closes**. A tuple's own leaf line already holds its selector, so
  the total is between `T(T+1)/2` and `N · T`, depending on where the dead
  ends fall: about `T²/2` when they are few or come before the tuples (as in
  `growth/`, where every leaf is a tuple), up to `N · T` when they come
  after. On a scope with 4 tuples found first and 1,000 dead ends after them,
  the fact-check counted 4,022 selector literals, against 18 with the
  branches swapped. The derivation needs only each node's own subtree's,
  one per tuple per node on its path, `O(T · n)` in all (#1379; measured
  in [Proof performance](#proof-performance)).
- **Gaps.** None at `Off`. Above it the cover is absent, which is what
  breaks the [refutation](#rewrite-refute-empty-table) at `Definitions` and
  `Links`.
- **Tightness.** By hand (`mut/`): dropping one selector from the cover is
  refused at the cover itself, and dropping a leaf's own selector from its
  backtrack is refused there.

### Rewrite: install-table-propagator

- **Pattern.** At least one tuple.
- **Posts.** `propagate_extensional` over the table, `on_change` on the
  scope, under `CurrentlyUnnamedConstraint`, with the compact-table arm on
  offer when `T ≥ 64`. No posted constraint is disabled.
- **Derived mode.** Not a posted constraint at all: no OPB row and no label.
  Its rows are the entries and the cover.
- **Why it is true.** Every solution of the model projects onto some
  tuple (previous entry), so removing a value that no live tuple supports
  loses no solution.
- **Proof technique.** None for the install itself. The propagator's rules
  are `table.md`'s rules 2–5: JP 3.3 and 3.4, one RUP each against the
  entries' forward halves and the cover, by the argument in that document's
  catalogue preamble. That document states the procedure for EP 3.10's
  encoding, and uses only its forward halves and an at-least-one, which is
  what these rows provide; there is no at-most-one here either.
- **Strength contributed.** `GAC` over the scope's variables, relative to
  `C_in`, the constraints whose variables all lie in the scope, by the
  argument that follows. At the
  propagator's fixpoint every remaining value of a scope variable lies in a
  live tuple. A live tuple is an assignment of the scope's variables within
  their current domains, and every tuple satisfies every constraint in
  `C_in`. It can be **stronger** than that, by whatever root propagation of
  the constraints reaching outside the scope refuted, but only as of the
  root, because the table never shrinks. It is **not** GAC on the model's
  projection, which would need the subproblem to search to solutions rather
  than to propagation fixpoints. Unlike a posted `Table`, a repeated
  variable costs nothing here: a tuple is an assignment of the scope's
  *variables*, so its repeated columns always agree, and pass 1's
  position-by-position test is exact.

  Checked by brute force (`gacbf/gacbf.cc`, seeds 1–20 × 500, at
  `86caad24`). The 10,000 random models had:
  - 2 to 4 base variables over random subsets of `−2..3`, half declared as
    value lists and half as ranges with `NotEquals` holes;
  - 1 to 4 constraints, drawn from `Table`, `NotEquals`, `LessThan`, linear
    `=` and `≤` and `AllDifferent`, many partly outside the scope;
  - scopes of 1 to 3 positions: plain, `x + c`, `−x` or a constant, with
    repeats (3,191 instances).

  The checks: the solution set, with and without the presolver, against
  brute force; the tuple count against both bounds of
  [Semantics](#semantics); and whether the domains were GAC over the scope's
  base variables relative to `C_in` at every branching node, after every
  propagator's fixpoint. There were no mismatches, no bound violations and
  no non-GAC node among 75,370. That observes the combination, not the
  table's propagator in isolation: a posted `Table` in `C_in`, say, is GAC
  by itself. The argument above is what attributes it.
- **Neutral?** No. It is a strengthening, so a node-for-node tripwire is not
  available. A solution-set tripwire is, and the probes above use it. Under
  the default `dom_then_deg` brancher it also changes the search through the
  degree count ([Can it weaken the model?](#can-it-weaken-the-model)).
- **Offline reconstructibility.** `search`, provisionally (see the last
  paragraph); `table.md`'s rules 2–5 also give `search` for this caller. The
  assertions
  carry no hint, and the rows the solver's own derivation uses (the
  entries' forward halves and the cover) exist only at `Off`. What has to be derived is the assertion itself,
  `inference ∨ ¬R`, where `R` is the generic reason over the scope: every
  scope variable's current domain. **Rebuilding the table, by replaying this
  presolver's enumeration, is one sufficient derivation, not a necessary
  one.** Any refutation of `R ∧ ¬inference` from the model will do.
  - **No tuple or selector is needed.** An assignment of the scope inside
    `R` that falsifies the inference is in no live tuple, so the subproblem's
    path for it ended at a dead end, refuted by the subproblem's
    propagation. A split over the scope's variables inside `R` is therefore
    sufficient when each case is refuted the way the subproblem refuted it:
    by re-running the model's propagators, or by unit propagation against
    the subproblem's own `a` lines (below). It is the subproblem's search
    confined to that box, without the entries or the cover.
  - **It can be far smaller than the enumeration.** In Codex's example from
    review of this document (`e1-codex-far/far8.cc`): `x ∈ 0..2`,
    `y, w ∈ 0..1`, `x ≠ y`, `x ≠ w`, `y ≠ w`, and eight unconstrained
    Booleans in the scope with `x`. The subproblem finds 256 tuples in 1,279
    nodes, and the table's `x ≥ 2` follows from the OPB and the literal
    definitions by three RUPs, `¬[x = 0]`, `¬[x = 1]` and `[x ≥ 2]`, which
    VeriPB 3.0.2 accepts (`s VERIFIED NO CONCLUSION`; this and the probes
    below at `86caad24`, fataepyc-08, 2026-10-21). The Booleans never
    appear.
  - **But nothing in the assertion says which constraints refute the box,
    and a refutation from the model alone can need a search of its own.**
    The constraint may be over none of the reason's variables: with the
    scope `{x}` alone, the same `x ≥ 2` needs `y ≠ w` (`fixup1/far.cc`).
    It may also need an argument that no RUP finds. In `e3-split/split.cc`
    (`AllDifferent{x, a, b, c}` over `0..3`, `a + z1 ≤ 3`, `b + z1 ≤ 3`,
    `c − z2 ≤ 2`, `3·z2 − x ≤ 0`, scope `{x, z1, z2}`), the table removes
    `0`, `1` and `2` from `x` under `z1 = 1`, with `z2` open. Against the
    OPB and the definitions, `x ≠ 0` is not RUP, nor after a split on `z2`:
    it needs a Hall argument over `a, b, c`, none of them in the scope.
  - **The subproblem's own `a` lines carry that search's results.** At
    `Definitions`, `Links` and `Inferences` its propagation stays in the
    proof as assertions, and is never deleted: presolvers run at the
    logger's initial proof level 0 (`solve.cc:377-378`,
    `proof_logger.cc:179`), above `Off` the subproblem enters no level
    (`auto_table.cc:46`, `:99`), and the main search forgets only deeper
    ones. At `Backtracking` no inference is written. Once those lines are
    justified, each case of the split should be refuted by unit propagation
    along the subproblem's path to its dead end: argued from the subproblem
    being exhaustive, and checked on the lane below, not proved for every
    propagator. In `e3-split` the same `x ≠ 0` is
    one RUP against them, and is not without the `AllDifferent`'s three
    Hall lines.

    The lane `e6-prefix/` (adapted from this round's fact-check) checks that
    the subproblem's lines are enough. It makes 3,000 runs with an
    `AutoTable` over 1,195 distinct random models (full encoding):
    - 600 models under four settings, at `Definitions`, at `Links`, and at
      `Inferences` with two branchers (ranges of 3 to 5 values, scopes of 1
      to 3 variables);
    - 600 more at `Inferences`, with ranges of up to 6 values and scopes of
      up to 4 (595 of them distinct from the first 600).

    Each proof is cut right after presolve, and every `AutoTable` assertion
    of the full proof is derived from that prefix alone, by a split over the
    scope's root ranges. The reconstructor adds two kinds of line it may
    introduce itself:
    - two root-bound units per variable, `[v ≥ lo]` and `¬[v ≥ hi + 1]`, each
      RUP;
    - the two defining `red` lines of each range literal (`i[v][inA_B]`, `v`
      in `A..B`) that an assertion uses and nothing defines, since
      `Inferences` writes no definitions.

    An assertion is an unhinted `a` line with the generic-reason shape over
    the scope. A regeneration with `GCS_VERBOSE_LOGGING=1`, whose stack
    traces name the line's source, confirms the filter exactly: it matches
    all 1,648 lines written from `auto_table.cc` and none of the 30,669
    other unhinted `a` lines. The split derived all 1,648 assertions, in the
    610 runs that made one, with no failure and 178,717 leaf cases. No `del`
    in the 3,600 full proofs touches a prefix line.
    - Both additions are needed at `Inferences`. Without the units the split
      failed in 8, 8 and 6 runs of the three settings, and never at
      `Definitions` or `Links`. Without the range definitions it failed in 1
      run (`inf-dtd-3-5` `q9_25`, whose reason is `b0 ∉ −1..0`).
    - Controls: one bare RUP per assertion against the prefix failed in 15
      or 16 runs per setting, and the same split against the OPB alone, with
      no prefix, failed in 28 to 35.
    - With the inference dropped from its first assertion, the split was
      refused in all 119 runs of one `Inferences` setting.

  **Which verdict this is, is Ciaran's call: `search` is provisional.** There
  are two readings.
  - **On the template's letter it reads `offline`** at `Definitions`,
    `Links` and `Inferences`. Appendix C's starting point includes the proof
    so far, which holds the subproblem's `a` lines. The split is over the
    variables the assertion's own clause names, within the domains it states,
    so the assertion fixes it. Every case is guaranteed. And Appendix C
    counts length as no objection.
  - **Against that,** the guarantee rests on two things:
    - lines that are themselves assertions, to be justified first, and kept
      only at those three levels;
    - every step of the subproblem's propagation being replayable by unit
      propagation from them. That is argued from the subproblem being
      exhaustive, and checked on the lane above, not proved for every
      propagator.

    The split also costs up to the product of the scope's domains for each
    assertion, as much as the one enumeration or more, and the short
    derivations of the first example have to be found. The template sets no
    bound on a fixed split. That looseness would also make any implied clause
    `offline` by a split over every variable of the model, but that split
    names variables the clause does not, so it does not settle this case.

  At `Off` the question does not arise: there the table's inferences are RUPs
  against the entries and the cover.
- **Proof size.** None for the install. The rules' sizes are `table.md`'s.
- **Gaps.** None. Propagation strength does not change with proofs on.
- **Tightness.** `table.md`'s rules have no lanes; its hand mutations were on
  `Table`. `auto_table_presolver_test`'s compact-arm case is the standing
  check that the compact filtering runs for this caller: sabotaging
  `seed_compact_table_from_live_set()` makes its enumeration disagree, per
  the test's header.

### Rewrite: refute-empty-table

- **Pattern.** No tuple: the subproblem search found no assignment of the
  scope that propagation leaves standing.
- **Posts.** Nothing. `run` returns `false`, `solve_with` skips the search
  and `choose_optional_interior_pruning()`, and concludes unsatisfiable
  (`solve.cc:378-381`, and the `else` branch after the search).
- **Derived mode.** n/a.
- **Why it is true.** The cover with no disjuncts is the empty clause: every
  assignment of the scope was refuted by propagation somewhere in the
  subproblem, so the model has no solution.
- **Proof technique.** At `Off`, the subproblem's root backtrack is
  `rup >= 1` itself (a `RUP sequence` as in the cover, ending in the empty
  clause). `conclude_unsatisfiable` then RUPs the empty clause again, at
  `Off`, `Definitions` and `Links`, and asserts it at `Inferences` and
  above.
- **Neutral?** n/a.
- **Offline reconstructibility.** `search`: the only line a hints-only proof
  holds for it is the bare `a >= 1;` that closes the proof, with the
  subproblem's propagation `a` lines before it at `Inferences` (none at
  `Backtracking`). Nothing records the subproblem's search.
- **Proof size.** As the cover, without the entries.
- **Gaps.** None at `Off`. At `Definitions` and `Links` the proof is
  **rejected** when the subproblem's root propagation did not already fail
  ([Proof-time state](#proof-time-state)). Above `Off` only, so recorded and
  not filed.
- **Tightness.** `Not shown.`

## Detection and its failure modes

**There is no scan.** The caller names the scope, so detection cannot fail
the way a donor scan does. What can fail silently is the caller's
expectation of what is tabulated:

- **A scope that does not cover the constraint meant.** The table is still
  built, over what propagation leaves of the named variables. `AutoTable{{x}}`
  beside `x + y = 3` tabulates `x`'s root domain: a table that propagates
  nothing new. Nothing warns. The stats show `tuples`, but not the product of
  the domains to compare it against.
- **A scope that covers more than the constraint meant.** Every constraint
  over the scope's variables is in the table, and so is whatever constraints
  reaching outside it refuted at the subproblem's nodes. That is sound, but
  the table can be much larger than the caller's constraint's own, e.g.
  three unconstrained extra variables multiply it by their domain sizes.
- **A scope with no constraint over it** tabulates the product of the
  domains: 16 tuples for two free variables over `0..3`. That is pure
  overhead.
- **What the subproblem actually propagates.** Every propagator installed
  so far: every posted constraint's, and every earlier presolver's. It does
  so at full strength, with every optional interior pruning on. The table is
  as strong as that, and no stronger: a tuple that a deeper search would
  refute stays in the table.
- **Views, constants, repeated variables and holes** are all handled ([Variable
  kinds and views](#variable-kinds-and-views)). In 10,000 random instances
  with all four, no solution was lost or gained.
- **Constraints only partly inside the scope** prune only as far as their
  propagators can with the scope fixed and the rest open. A `LessThan{x, z}`
  with `x` in the scope and `z` free removes a tuple only once `x`'s value
  leaves `z` no support.
- **A subproblem with no solution** refutes the model ([Rewrite:
  refute-empty-table](#rewrite-refute-empty-table)). At `Off` that is
  certified. At `Definitions` and `Links` it is rejected unless the
  subproblem's root propagation already failed.
- **A subproblem with a huge number of solutions** is enumerated to the end:
  2,162,160 tuples took 4.8 s and 267 MB, ignoring an abort at 200 ms
  (#816). With proofs, the proof's bytes grow at least as `T²/2`
  (#1379).
- **The variables it was given are all but decided by propagation.** Then
  the table is one tuple and the search short. In `shikaku`'s small instance each
  of the five rectangles tabulates to 1 tuple: one at the subproblem's root
  in 1 node, the other four one level down, in 3 nodes.

## Evidence that it fired

`AutoTableStats` is registered on every run that reaches `run`, before
anything else happens (`auto_table.cc:114`), so it reaches
`Stats::components()` and the `--stats` printers. Its five entries are:

| Entry | Meaning |
|---|---|
| `ran` | 1 once `run` is entered, in this solve or in an earlier one that used the same block; nothing sets it back to 0. So 0 means "did not run" only in a fresh block, e.g. a caller's own block whose presolver never ran because an initialiser or an earlier presolver refuted the model first. A block whose presolver is not reached is not registered in that solve's `Stats` |
| `variables` | the scope's length, counting constants and repeats |
| `tuples` | `T` |
| `search_nodes` | the subproblem's `N` |
| `compact_table` | 1 when the run that installed a table had `T ≥ 64`, so the compact arm was offered. A run with no tuple leaves it as it was, so a reused block can say `tuples` 0 beside `compact_table` 1, in the solve's `Stats` too (#1387). Whether `table::Auto` then takes the arm is decided after 32 wakes and reported nowhere |

The summary line tells the cases apart:

- `did not run`;
- `found no satisfying assignment of n variables, in N nodes`: the model is
  then unsatisfiable;
- `T tuples over n variables, found in N nodes`, ending `, large enough for
  the compact table` when it is.

That holds for a fresh block, and for the block in a solve's `Stats`, which
only a run of this solve registers. **A caller's reused block cannot tell
"did not run this time" from its previous run**: it keeps that run's values
in every field, `ran` included, and its summary repeats them. As in
[`parity_system_gathering.md`](parity_system_gathering.md#evidence-that-it-fired),
whether the solve's `Stats` lists the block is what tells the two apart.
Re-run here (`e4-stats/stats.cc`): a 64-tuple solve, then a solve whose first
`AutoTable`, on its own block, refutes the model before the reused block's
presolver is reached, leaves the reused block saying `ran` 1 and 64 tuples,
and the second solve's `Stats` has only the first block.

There is no "ran and installed nothing" case with tuples: any tuple means a
propagator. A table equal to the product of the domains looks like any
other. `solve_test` pins the entries by name and count (`field_count`), and
pins the sharing of a caller's block through `clone()`. The proof's only
marker is the `new table entry found` comment at `Off`.

**The stats channel and the search counters.** The subproblem's
`propagate()` calls are counted in `Stats::propagations` (and its effectful
and contradicting counts). Its nodes are not counted in `recursions` or
`failures`. So a `propagations` column beside an `AutoTable` includes the
pass:

- `table_layout`'s 4 × 4 instance takes 339 recursions under each variant,
  with 537 propagations for `element` and 4,056 for `auto-table`;
- two free variables over `0..3`, tabulated, go from 0 propagations to 21
  when declared as ranges, and from 22 to 65 when declared as value lists.

Search-shape comparisons across the presolver should use `recursions`.

**Expected values** at `86caad24` (fataepyc-09, 2026-10-20):

| Instance | Blocks | Summary, or sums over blocks |
|---|---|---|
| `examples/auto_table` | 1 | `4 tuples over 3 variables, found in 27 nodes`; 8 solutions, 15 recursions (32 without) |
| `solve_test`, `a + b = 3` over `0..3` | 1 | `tuples` 4, `compact_table` 0 |
| `auto_table_presolver_test`, `big` | 1 | 268 tuples, 335 nodes, `compact_table` 1 |
| `auto_table_presolver_test`, `small` | 1 | 16 tuples, `compact_table` 0 |
| `skyscrapers 5 --autotable` | 10 | 58 tuples, 194 nodes; 1 recursion (207 without) |
| `skyscrapers 7 --autotable` | 14 | 842 tuples, 4,301 nodes, 3 offered the compact arm; 1 recursion (1,232,741 without) |
| `skyscrapers 9 --autotable` | 18 | 29,037 tuples, 70,000 nodes, 5 compact, the largest 15,072 tuples; 1 recursion |
| `shikaku --instance human --autotable` | 10 | 1 to 3 tuples each, 4 to 7 nodes; 10 recursions (2,793 without) |
| `table_layout --variant auto-table` (4 × 4, seed 0) | 16 | 339 recursions, as `element` and `table` |

The `small` figure is the test's own comment's; the fact-check re-ran it
(16 tuples, 31 nodes). Every other figure was re-run here.

## Can it weaken the model?

**Lose solutions: no.** Nothing reaches the OPB, which is byte-identical
with and without it. The table is a superset of the projection of the
solutions ([Semantics](#semantics)). No posted propagator is disabled. The
solution sets were checked against brute force on 10,000 random instances
and the 19 shapes, in both declaration styles. Through the cake chain, the
eight shapes tried verify ([Cake conformity](#cake-conformity)).

**Lose propagation: no.** Three things qualify that.

- Every posted propagator keeps running, and the table only adds
  inferences. Under a static variable order the tree can only shrink: a
  `Cumulative`, `Disjunctive` and `ParityOdd` model took 3,485 recursions
  under `in_order` with and without the presolver.
- Under the default `dom_then_deg` brancher, the installed propagator raises
  each scope variable's degree, so the variable order changes and the tree
  can grow. The same model took 2,747 recursions without the presolver and
  2,859 with it. That is a search-order effect, not a loss of propagation,
  and `difference_logic.md` records the same for its propagator.
- The throwaway root search can damage other propagators' first-call state
  ([Relation to other families](#relation-to-other-families)). That has
  meant lost watches (#1106, fixed), an exception (#1378, whose obvious
  workaround loses propagation) and lost work on a wide `Table` or
  tabulated constraint (#1378, cost only, but unbounded at extreme width).

**What pins the rows to the intended table.** There is no `ia` step and
none is needed, because the leaf backtrack is the pin. Each entry's two
`red` lines define `s_j` as some tuple, and VeriPB accepts any tuple there,
a wrong one included. But the leaf's backtrack clause,
`¬(path decisions) ∨ … ∨ s_j`, is RUP only if the path's propagation fixes
the scope to exactly the tuple `s_j` was defined as. A self-consistent
definition of the wrong tuple (both halves edited) is refused there
(`mut/` M3). In the other direction, the in-memory table must not lack a
tuple the proof's cover has. The installed propagator's RUPs need every
covered tuple dead, so a value removed with a support in a proof-only tuple
would be refused. An in-memory tuple that the proof lacks is impossible:
both are written from the same `state(var)` reads (`:61-63`, `:75-78`).

## Evidence

### Tests

| Lane | What it covers |
|---|---|
| `auto_table_presolver_test` | the compact-table threshold from both sides (268 and 16 tuples, `compact_table` set and clear), each with its solution set against the plain model; one proof past the threshold, verified. Catch2 unit test |
| `solve_test`: "AutoTable reports what it did, with no stats block asked for" and "A caller's AutoTable stats block…" | the five entries by name and count, and the caller's block being the one filled in through `clone()` |
| `solve_test`: "Solve unsat optimisation presolving" | a scope whose subproblem fails at its root (`v ≥ 200` over `0..100`; despite the name, no objective is posted); the proof verified |
| `auto_table`, `skyscrapers-5-autotable`, `table_layout-auto-table` (`run_test_and_verify.bash`) | the examples, verified, plus the `.scp` writer/reader check |
| `negative_table_test`, `nogoods_test`, `logical_test` | their lanes behind a pseudo-root `AutoTable` over a fixed variable (fresh in the first two, `logical_test`'s constant-valued `one`), for #1106: a test of other families' first-call state, not of this presolver |

VeriPB runs in the example lanes and in `auto_table_presolver_test`'s proof
case, at `Off` only. No lane sets an assertion level for this presolver.

**Runtime caps.** The first four rows are not data-driven constraint lanes:
the examples and `auto_table_presolver_test` call `solve` directly, so the
suite's solution and node caps (`GCS_TEST_CAP_DEFAULTS`), which only
`solve_for_tests` reads, never apply to them. The lanes in the last row do
run under the caps, and their caps are those documents' business. The
results here came from the binaries and probes run
directly, uncapped, as recorded under each figure.

**Seeding.** The examples and the presolver's search are deterministic.
The random probes are seeded by their own arguments.

**Real instances.** None is ported. The examples are the only real models.

**Mutation lanes.** None committed. The six hand mutations in [the
catalogue](#rewrite-catalogue) were run once against the example's proof,
with an unmutated control that verifies.

**What the tests do not cover.**

- **Any assertion level above `Off`.** The no-tuple rejection at
  `Definitions` and `Links` is untested.
- **A subproblem with no tuple that is not refuted at its root.** The only
  zero-tuple test fails at the root.
- **Views, constants, repeated variables, an empty scope, and constraints
  partly outside the scope.** No lane has any; this audit's probes did.
- **A brute-force or GAC check of the table.** The presolver test compares
  solution sets only.
- **The order dependence**, with another `AutoTable` or another presolver,
  and in particular the two first-call failures (#1378).
- **Cost.** No lane would notice #1379's quadratic proof, or a subproblem
  that ran away.
- **Front ends**, which cannot reach it (#983).

### Benchmarks and examples

- **In the repository:** `examples/auto_table` (five variables, one scope);
  `examples/skyscrapers N --autotable` (a scope per row and per column,
  `N` = 5, 6, 7 or 9); `examples/shikaku --autotable` (each rectangle's
  width and height, `small` or `human`); and `examples/table_layout
  --variant auto-table` (each cell's configuration, width and height,
  beside the `Element` pair it tabulates). No benchmark driver adds one.
- **For CPU:** `skyscrapers 7` and `9` with `--autotable`, where tabulation
  is nearly the whole cost and the search is one recursion; `shikaku --instance human`,
  where it decides the search. `skyscrapers 9` **without** the flag did not
  finish in 600 s, and should never be run uncapped.
- **For proof verification:** `skyscrapers 5 --autotable` (16,000 lines,
  0.15 s to check) and `skyscrapers 7 --autotable` (246,000 lines, 3.5 s).
  `growth/growth.cc` scales the tuple count on its own.

### CPU performance

Release, `86caad24`, fataepyc-09, 2026-10-20, pinned, serial,
`GLIBC_TUNABLES=glibc.malloc.mmap_threshold=33554432:glibc.malloc.trim_threshold=4294967295`.
Instructions and task-clock are the median of five runs, except
`skyscrapers 7` without the presolver (one run) and `skyscrapers 9` (wall
clock, one run each).

| Instance | Without `AutoTable` | With it | Recursions without → with |
|---|---|---|---|
| `shikaku --instance human` | 248.4 M instr, 43.2 ms | 13.0 M instr, 5.0 ms | 2,793 → 10 |
| `skyscrapers 5` | 26.8 M instr, 8.1 ms | 33.0 M instr, 9.5 ms | 207 → 1 |
| `skyscrapers 6` | 49.7 M instr, 12.2 ms | 71.9 M instr, 17.0 ms | 58 → 1 |
| `skyscrapers 7` | 174.7 G instr, 34.9 s | 738.4 M instr, 130.5 ms | 1,232,741 → 1 |
| `skyscrapers 9` | > 600 s wall (capped) | 3.72 s wall | — → 1 |
| `table_layout`, 4 × 4, seed 0 | `element` 7.44 M instr, 4.0 ms; `table` 7.87 M | 13.9 M instr, 5.2 ms | 339 → 339 |

The figures under 10 ms should be read on instructions. On `skyscrapers 5`
and `6` the presolver costs more than it saves (1.23× and 1.45× the
instructions), although the search drops to one recursion. The comparison
is the model with and without tabulation. No cross-solver row is given: the
comparable technique is Dekker et al.'s MiniZinc auto-tabling extension,
which rewrote the model before any solver saw it and is not in current
MiniZinc ([Prior art](#prior-art)). What these instances do not exercise: a
long search over a tabulated scope (the longest here is `table_layout`'s
339 recursions), and a table large enough for the compact arm to matter to
the search (`skyscrapers 9`'s largest, 15,072 tuples, is used at one node).

### Proof performance

VeriPB 3.0.2 `--force-checked-deletion`, same commit, machine and date,
`AssertionLevel::Off`, one run each.

**On the examples:**

| Instance | Proof | VeriPB |
|---|---|---|
| `skyscrapers 5`, without | 12,450 lines, 0.72 MB | 0.14 s |
| `skyscrapers 5 --autotable` | 15,913 lines, 1.06 MB | 0.15 s |
| `skyscrapers 7 --autotable` | 245,605 lines, 27.9 MB | 3.48 s |

The breakdown for `skyscrapers 7 --autotable`:

- The presolve phase, up to the last tabulation's cover, is 244,223 of the
  245,605 lines.
- The presolver's own lines are 1,684 `red` and 4,301 backtracks: 2.4% of
  the lines, but 13.3 MB, 48% of the bytes.
- The rest of the presolve phase, 14.4 MB, is the other propagators'
  justifications inside the subproblems: 133,253 `rup`, 61,920 `del`,
  27,872 `pol` and 4,606 more `red`, of the literal layer.

So the shared layers dominate the line count and the presolver dominates
the bytes, through #1379's clauses. The candidate fix takes the whole
proof to 15.5 MB, and VeriPB to 3.19 s. Without the presolver,
`skyscrapers 7` searches 1.2 million nodes, and that proof was not written.

**Scaling with the tuple count** (`growth/growth.cc`: `k` variables over
`0..d−1`, `x₀ ≠ x₁`, scope all `k`):

| `k`, `d` | `T` | nodes | lines | selector literals in backtracks | bytes | VeriPB | candidate bytes | candidate VeriPB |
|---|---|---|---|---|---|---|---|---|
| 2, 4 | 12 | 17 | 306 | 120 | 12.9 KB | 0.02 s | | |
| 2, 8 | 56 | 65 | 1,002 | 1,904 | 83.9 KB | 0.03 s | | |
| 2, 16 | 240 | 257 | 3,642 | 31,200 | 974 KB | 0.09 s | 143 KB | 0.07 s |
| 2, 32 | 992 | 1,025 | 13,914 | 509,888 | 14.6 MB | 0.91 s | 558 KB | 0.58 s |
| 3, 16 | 3,840 | 4,097 | 52,290 | 7,873,920 | 226 MB | 11.4 s | 2.49 MB | 6.4 s |
| 2, 64 | 4,032 | 4,097 | 54,426 | 8,265,600 | 238 MB | 12.7 s | 2.22 MB | 7.0 s |

Lines grow linearly in `T`, about 13.5 per tuple, which counts the two
`red`s, the backtracks, the deletions and the main search's solution
lines. Every leaf here is a tuple, so the selector literals are at the low
end of their range, about `T²/2`. The candidate keeps every line and cuts
the literals to one per tuple per node on its path.

**At the assertion levels** the presolver contributes nothing of its own.
On the example's model, declared as ranges as the example does, the proof
is 913 lines at `Off`, 539 at
`Definitions`, 234 at `Inferences` and 73 at `Backtracking`; at `Links`
it is #1210's rejection. Of the 169 `a` lines at `Inferences`, the
installed propagator's are the seven unannotated ones (five at the root,
two during search), and the rest are other constraints', the subproblem's
included, and the backtracks and solution blocks. No assertion
carries a hint of this presolver's, because there is none.

## Status, gaps, and next steps

### Proof-logging gaps

- At `Off`, none: every entry, the cover and every installed inference are
  derived.
- Above `Off`, the presolver writes nothing, so the subproblem's search
  leaves only its propagators' `a` lines (at `Definitions`, `Links` and
  `Inferences`), the literal-layer definitions it caused (at `Definitions`
  and `Links`), and nothing at `Backtracking`. A model with no tuple and no root
  refutation is **rejected** at `Definitions` and `Links`. Recorded, not
  filed; delegating the subproblem's backtracks to `logger->backtrack` at
  every level would match the main search.
- The installed propagator's assertions carry no hint (`NoHint`), so a
  hints-only reconstructor has to find a refutation of the reason with the
  inference negated. Replaying the presolver's enumeration is one way. A
  split over the reason's box, against the subproblem's own `a` lines, is
  argued to be another (checked on a lane, not proved for every
  propagator), at up to the product of the scope's domains for each
  assertion, and some assertions need only a few RUPs ([Rewrite:
  install-table-propagator](#rewrite-install-table-propagator)). The verdict
  is `search`, provisionally: whether that split makes it `offline` is
  Ciaran's call. Whether a hint would pay is the justifier's question.
- Propagation strength does not change with proofs on, and there is no
  proof-only budget.

### Known limitations

- **Your model throws `difference logic incremental state was initialised
  below a decision`.** It has a `DifferenceConstraints`, or a
  `DifferenceLogic` presolver added before the `AutoTable` that lifted two
  edges or more. Add the `DifferenceLogic` after the `AutoTable`, or use
  `incrementally(false)` on either (#1378).
- **A `Table` or a tabulated constraint over a wide variable is slow, never
  finishes, or writes an enormous proof once an `AutoTable` is added**, even
  one over unrelated variables (#1378).
- **The proof is far larger than the table**, quadratically in the tuple
  count (#1379).
- **`--timeout`, or the abort flag, has no effect until the tabulation
  finishes** (#816; no front end reaches this presolver, #983).
- **Nothing tells you the scope was a poor choice.** A table over free
  variables, or over variables whose constraint lies outside the scope, is
  built and propagated anyway.
- **Not reachable from MiniZinc, XCSP3, CPMpy or a `.scp`** (#983; for the
  `.scp`, #1374).
- **Above `AssertionLevel::Off`**, an unsatisfiable subproblem can give a
  proof VeriPB rejects at `Definitions` and `Links`. At `Links`, #1210
  rejects most satisfiable models anyway.

### Next steps

1. **Stop the throwaway root search stranding first-call state** (#1378).
   This is the only crash, and the class has three known members. There
   are two directions, not chosen here:
   - **Per propagator:** the difference propagator's first-call memory must
     survive, or be redone after, a backtrack past the call; and
     `propagate_extensional`'s trim marker must live in backtrackable state,
     sharing an existing slot rather than adding a deep-copied one, or use
     the trail-mark technique `ExtensionalCompactTable` uses. Each
     wants a pseudo-root `AutoTable` lane (`difference_test`,
     `difference_logic_presolver_test`, `table_test` with a wide column).
   - **In the engine:** `solve_with` propagates once at the real root
     before each presolver, so that no propagator's first call happens in a
     presolver's sub-search. The fact-check's five-line scratch build clears
     both instances, and its proofs verify. It costs a root fixpoint per
     presolver, and later presolvers would see root-propagated domains.

   Cost: small to moderate either way. Buys: correctness and width
   independence for any model mixing `AutoTable` with these families.
2. **Subtree-local backtrack clauses** (#1379). About eight lines,
   measured: 100× fewer proof bytes at 4,000 tuples, VeriPB about 1.8×
   faster. The argument shows every proof stays valid, and every proof it
   was tried on verifies.
3. **Keep the class survey honest.** It found nothing else by a code read
   and a 485-lane sweep. A future propagator with first-call state would be
   caught only by a pseudo-root lane; making such a lane a standard part of
   a family's tests is cheap. `ExtensionalCompactTable::decided` counts the
   subproblem's wakes toward `table::Auto`'s decision, which can change both
   when and which way it decides (speed only, unmeasured).
4. **Observe the abort flag** (#816, where this audit commented). This is an
   interface change to `Presolver::run`, and an aborted presolver must
   return `true` having installed nothing, because `false` means
   unsatisfiable.
5. **Write the presolver's backtracks at every assertion level**, through
   `logger->backtrack`, when the assertion levels are designed. That closes
   the no-tuple rejection.
6. **Tests:** a brute-force lane with views, constants, repeats and
   partly-outside constraints (`gacbf.cc` is the shape); a no-tuple case
   not refuted at its root, with proofs; the order dependence; a
   `large_domain_audit_test` row behind an `AutoTable`; and one stats block
   reused across a compact-table run and a zero-tuple run, which a fix to
   #1387 needs, whether it assigns every per-run field on entry or only
   initialises `compact_table` before the early return (the issue offers
   both).
7. **A front-end route** is #983's design question. It needs a way to name
   the scope as well as a switch.
8. **Report what the table pruned.** A `max_tuples` entry, the product of the
   scope's domain sizes, would show a useless table at a glance. Cheap.

## Prior art

- **Tabulation as a reformulation is published.** The closest is Dekker,
  Björdal, Carlsson, Flener and Monette, *Auto-tabling for subproblem
  presolving in MiniZinc*, Constraints 22(4):512–529, 2017
  (doi:10.1007/s10601-017-9270-5). Their extension of the MiniZinc toolchain
  lets the modeller annotate a predicate `::presolve(autotable)`, as this
  presolver's caller names a scope. It solves the predicate as a separate
  submodel over its arguments' declared domains, and **replaces** the call
  with a `table_int`, before any solver sees it. The extension is not part
  of current MiniZinc: 2.9.7 and 2.10.1 reject the annotation. Akgün, Gent,
  Jefferson, Miguel, Nightingale and Salamon,
  *Automatic Discovery and Exploitation of Promising Subproblems for
  Tabulation*, CP 2018, LNCS 11008, pp. 3–12
  (doi:10.1007/978-3-319-98334-9_1), find the subproblems automatically, by
  heuristics in Savile Row, with a cache. Its journal extension, TabID
  (JAIR 82, 2025, pp. 1999–2056, with Kiziltan and Ulrich-Oltean), evaluates
  it across CP, learning and SAT solvers.
- **What is this solver's.** Two things are adaptations rather than new
  algorithms:
  - The subproblem is solved **inside the solver, with the whole model
    propagating**, so the table is filtered by constraints outside the scope
    as well. MiniZinc's submodel sees only the predicate.
  - The table is **added beside** the posted constraints rather than replacing
    them.
- **Certification.** Gocht, McCreesh and Nordström, *An Auditable Constraint
  Programming Solver*, CP 2022, LIPIcs 235, 25:1–25:18, §4.5
  ("Autotabulation and Other Reformulations"), describe certifying a
  tabulation in VeriPB:
  - one extension variable per solution, as the selector literals here;
  - one flag `g` for "some tuple is selected";
  - a logged search with an extra guess about `g` at every node, ending in
    a proof of `g` and so the at-least-one. For the search to end in a proof
    of `g`, the guess has to be `¬g`, "no tuple is selected": at a solution
    leaf the tuple's `t_s` holds, so `g` does, and the guess is refuted. The
    published sentence reads "we use g as an additional guessed assignment";
    in the LIPIcs PDF (p. 25:10, rendered and checked here) that `g` carries
    no overbar, though the page's other negations do, so the `¬` is the
    argument's and not the printed text's. Because `g`'s definition names
    every `t_s`, the scheme is two-pass: the solutions are found first, and
    the logged search is a second one.

  McIlree's thesis (*Pseudo-Boolean Proof Logging for Constraint Propagation
  Algorithms*, ch. 4) cites it as "an auto-tabulation proof as a
  pre-processing step" and gives the table encoding (EP 3.10) and the
  justifications (JP 3.3, 3.4) the installed propagator's rules rest on. The
  code differs from the CP 2022 description, and always has: from its first
  commit (`087a6cc1`, 2022-12-22) it has used no `g`, and adds each found
  tuple's `¬s_j` as an extra condition instead (`auto_table.cc:83`), the
  per-tuple counterpart of `¬g`, in one pass. That is what
  makes the clauses quadratic (#1379). The published `g` keeps them short
  at the price of the second search; #1379's candidate keeps them short in
  one pass. Beyond the two adaptations above, nothing here is
  new.

## Further reading

- [`table.md`](../constraints/table.md): the propagator this presolver
  installs, its rules 2–5, its state and idempotence, and its
  reconstructibility verdict for this caller.
- [`refined-triggers.md`](../refined-triggers.md), on main (not yet in this
  document's tree), "But the first run is not always at the real root": the
  #1106 pitfall for watch markers, the general form of this document's
  [Relation to other families](#relation-to-other-families) list.
- [`difference.md`](../constraints/difference.md): the incremental route's
  first call (#1378).
- [`optional-interior-pruning.md`](../optional-interior-pruning.md): why a
  presolver's probing runs with every pruning on, and what its installed
  propagators contribute to the choice.
- [`variable-encodings.md`](../variable-encodings.md): proof-only
  auxiliaries, of which the selector is one.
