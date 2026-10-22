# `Nogoods`: the restart-learning store, which forbids conjunctions of literals (search machinery, not a user constraint)

> **Maturity** production as restart machinery; not a supported user
> constraint (see [What this is, and what it is not](#what-this-is-and-what-it-is-not)) ·
> **Audited** 2026-10-22 at `86caad24` ·
> **Open issues** filed by this audit: #1390 (under optimisation with
> restarts, the refined store arms the nogoods learned in a pass that improved
> the incumbent only at a later root that leaves the objective bound
> unchanged), #1391 (a restart scale of 0 never terminates and ignores the
> abort flag, and the own `--timeout` of XCSP3, the examples and the MiniCP
> benchmarks, which accept it), #1392 (the refined propagator declares no
> scope: it never adopted #506's `scope_only`, so under dom/wdeg with
> restarts the store's
> conflicts weight no variable), #1393 (a `NogoodStore` grown by user code
> mid-search: the two paths disagree, and the scan path's proof is rejected)
> and #1394 (the engine's refined-watch undo, 59% of the profile samples of
> `tsp --restarts=100`). Already open and touching this family: #131 (a
> generic watched-clause propagator, the natural
> home for this one, `NegativeTable`'s and the logical family's), #310 (range
> literals cannot be written into the model, so a range literal in a posted
> nogood throws with proofs on), #1210 (the generic `Links`-level
> solution-line rejection for range-declared variables, which restart proofs
> meet too), #1085 (deep search overflows the stack in `solve_with_state`,
> the recursion the restart loop drives), #1309 (`install_returning_id` is
> quadratic in a propagator's trigger count; the scan path subscribes to every
> variable) and #868 (cross-solver comparison). Tracked under #871.

## What this is, and what it is not

**`Nogoods` exists for one job: holding the nogoods that restart learning
records, and propagating them in later passes.** When a
`SolveCallbacks::restarts` schedule is set, `solve_with` builds a
`NogoodStore`, installs one `Nogoods` over it with every problem variable as
its trigger set, and grows the store at each restart unwind
(`solve.cc:345-358`, `:245-275`). That is the only use in the tree, and the
only one this audit treats as supported. **It is not meant to be a
user-facing constraint**, and it would probably need work before anything other
than restarts relied on it: see [Known limitations](#known-limitations) and
[Next steps](#next-steps), where every such item is framed that way.

It is nevertheless reachable, and this document says exactly how, without that
being an endorsement:

- **The C++ API.** `gcs/gcs.hh:55` includes `gcs/constraints/nogoods/nogoods.hh`,
  so `Nogood`, `NogoodStore` and both `Nogoods` constructors are public:
  `Nogoods(vector<Nogood>, bool refined = true)`, a fixed set, and
  `Nogoods(shared_ptr<NogoodStore>, vector<IntegerVariableID>, bool refined = false)`,
  a store someone else grows (`nogoods.hh:93`, `:103`). The header says the
  store is "owned by the search driver ... never by user code"
  (`nogoods.hh:26-27`); nothing enforces that, and the Doxygen comments put
  both `NogoodStore` and `Nogoods` in `\ingroup Constraints` (`:29`, `:67`), so
  the API documentation lists them as constraints.
- **The `.scp` reader**, and so `glasgow_scp_solver`.
  `(label nogoods (((V op v) ...) ...))` posts the fixed
  form (`scp_reader.cc:979-996`, `:1551-1552`), because `s_expr()` writes that
  form whenever a proof-logged run writes its `.scp`, and the reader has to read
  back what the writer writes (#716). `cake_pb_cp` has no such rule.
- **Nothing else.** No MiniZinc, XCSP3, `gcspy` or CPMpy constraint posts it.

What would need work before any other use, in short: a nogood added to a store
mid-search is enforced only at the next root propagation on the refined path,
and never appears in the proof on either path, so the scan path's proof is
rejected (#1393); under the default `dom_then_deg` brancher a
posted store can change the tree depending on the path, because the refined
one adds nothing to any variable's degree (#1392); a posted nogood
with a range literal throws with proofs on (#310); the store is not thread-safe
and `clone()` shares it.

Five things to know before touching it.

- **Two propagators, one encoding.** The *scan* path wakes on every change to
  any trigger variable and visits every clause; the *refined* path is two
  watched literals over the engine's refined per-literal watches
  ([`refined-triggers.md`](../refined-triggers.md)). The learned store uses
  refined unless `GCS_LEARNED_NOGOODS_SCAN` is set (`solve.cc:354`); the fixed
  constructor defaults to refined, the growable one to scan. The header's and
  the source's comments that the learned store "stays coarse until ... stage
  C-2" (`nogoods.hh:74-79`, `:95-102`, `nogoods.cc:131-133`) are stale on
  arrival: the commit that wrote them, 9c2a0500, also made `solve.cc` pass
  `refined = true`.
- **Strength is unit propagation on each clause separately**, which is GAC on
  that clause when its literals are over different variables, and weaker when
  two of them share one. Checked by brute force on 26,000 random instances,
  both paths, with views, constants, holes, empty and one-literal nogoods.
- **The scan and refined paths are not the same search, despite both design
  notes saying so.** For the learned store they agree in satisfaction and
  enumeration under every brancher tried except dom/wdeg. Under optimisation
  with restarts the refined store delays its catch-up whenever the root is
  seeded by an improved objective bound (#1390), and its empty
  scope means its conflicts weight no variable under dom/wdeg (#1392). With both
  fixed in a scratch build the two still differ under dom/wdeg, on
  `langford --branch dom-wdeg --restarts=1` and on some random optimisation
  instances. In every case traced, a failed node charged to a different
  constraint comes before the first different decision: the two paths order
  propagation differently, and dom/wdeg weights the constraint charged. Given
  the same decisions (Langford sizes 7 to 10), both paths reach the same
  domains at every branch callback.
- **Every learned nogood is a RUP line at `Top`**, derived during the restart
  unwind while the ancestors' backtrack clauses are still live, and moved to
  core when the abandoned level held a solution's blocking clause. Proofs
  verify at `Off` on all 1,185 restarting random runs proved and on Langford
  11's 35,584-solution enumeration; three mutations of that derivation are
  refused.
- **The cost of a long restart run is the engine's watch bookkeeping, not this
  propagator.** On `tsp --restarts=100`, 59% of samples are in the refined-watch
  undo, which searches a variable's watch list linearly for each watch it
  removes; searching from the back halves that run.

## What it is

### Semantics

A `Nogood` is a `vector<IntegerVariableCondition>`: a conjunction of literals
`x = v`, `x ≠ v`, `x ≥ v`, `x < v`, `x ∈ [lo, hi]` or `x ∉ [lo, hi]`, on
variables, views or constants. `Nogoods(N)` holds when, for every `n ∈ N`, at
least one literal of `n` is false; that is, it posts the clause `∨_{ℓ ∈ n} ¬ℓ`
for each. The header (`nogoods.hh:53`) lists four scalar operators, writing the
fourth as `≤` where the operator is `<`; the two range operators are accepted
and propagate correctly (below). In a posted nogood they throw with proofs on
(#310); in a learned one they reach the proof (below).

- **No nogoods** (`Nogoods{vector<Nogood>{}}`): nothing to forbid.
- **An empty nogood** forbids the empty conjunction, which is true, so the
  model is unsatisfiable. The initialiser contradicts at the root, the OPB
  carries a row `>= 1` with no terms, and the proof verifies `UNSATISFIABLE`
  (`tmp/fd-nogoods/nogoods/scp/scpview.cc`, shape 4).
- **A one-literal nogood** `{ℓ}` is `¬ℓ`, propagated by the initialiser.
- **Repeated variables** are accepted and correct: `{x = 1, x = 2}` forbids
  nothing, `{x ≥ 1, x < 3}` forbids `x ∈ {1, 2}` (shape 5: 8 solutions of 16,
  verified).
- **Constants** and **views** are accepted: `{2 = 2, y = 1}` is `y ≠ 1`, and
  `{x + 1 = 2, y = 1}` forbids `x = 1 ∧ y = 1` (shapes 1 to 3, verified).

The learned store's nogoods are **reduced nld-nogoods** (Lecoutre et al., see
[Prior art](#prior-art)): at a restart cutoff, for each frame on the abandoned
path and each sibling `s` that frame had fully refuted, the nogood is the
frame's positive decisions plus `s` (`solve.cc:237-275`). A second sibling that
is the negation of the first (for instance `x = v` then `x ≠ v`, `x ≠ v` then
`x = v`, `x < v` then `x ≥ v`, `x ∉ I` then `x ∈ I`) is a negative decision and
is left out of the prefix passed down (`solve.cc:179-202`); every other
descended sibling is kept, including a first sibling `x ≠ v` or `x ∉ I`.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Nogoods` (fixed) | n/a | n/a | n/a[^gcspy] | ✓ `nogoods`[^scp] | not a user constraint; see above |
| `Nogoods` (growable store) | n/a | n/a | n/a | n/a[^grow] | installed by `solve_with` when restarts are on |

[^gcspy]: `gcspy` binds neither the class nor a restart schedule.

[^scp]: Read and written by us only. `cake_pb_cp` prints `unsupported
    constraint: nogoods` and writes an empty OPB, exiting 0, so there is no
    chain case. A view in a literal is written as `((x + 1) = 2)`, which the
    reader refuses (`expected an atom, found a list`); that is the reader's
    general view limitation ([`workflow2_testing.md`](../workflow2_testing.md)),
    not this family's. Range literals throw in `s_expr()`
    (`names_and_ids_tracker.cc:2872-2876`).

[^grow]: The learned store is installed on the propagators, not posted, so
    `write_scp` never sees it, and its nogoods are derived in the proof rather
    than written to the OPB.

**Restarts, which are what reach the learned store,** have these entry points:

| Route | Flag | Notes |
|---|---|---|
| C++ | `SolveCallbacks::restarts = RestartSchedule::luby(scale)` | `luby(0)` never terminates (#1391) |
| `fzn-glasgow` | `--restarts=N` | `N = 0` means off (`fzn_glasgow.cc:1424-1429`); the help text (`:371-373`) and the `.msc` flag text (`minizinc/glasgow.msc.in:10`) still say "find-one / optimisation only", though enumeration with restarts is supported (`solve.cc:146-150`) |
| `xcsp_glasgow_constraint_solver` | `--restarts[=N]` | bare means 100; prints `d RESTARTS` and `d LEARNED NOGOODS`; `N = 0` hangs through its own `--timeout` and SIGTERM (#1391) |
| examples | `--restarts` on `langford`, `colour`, `ortho_latin`; MiniCP `tsp`, `qap`, `magic_series`, `magic_square`, `n_queens` | each passes `N` straight to `luby()`, and each hangs at 0 |
| `gcspy`, `glasgow_scp_solver` | none | |

**Front-end differentials, with restarts against without.** XCSP3: every
instance in `xcsp/tests` (56), `--all`, with `--branch dom-then-deg` and
`dom-wdeg`, Luby scales 1 and 4: 224 runs, 32 of which restarted, all with the
same `s` line and solution count as the no-restart run
(`tmp/fd-nogoods/nogoods/xcsp/xdiff.txt`); the fact-check's re-run compared the
sorted solution sets, duplicates, the last `o` line and the exit code too, and
found no difference (`tmp/fd-nogoods/factcheck/doc/xcsp/xd.sh`). MiniZinc 2.9.7
through
`fzn-glasgow -a`: 7-queens (40 solutions, 29, 14, 9 and 2 restarts at scales 1,
2, 4 and 16) gives the same solution set; a QAP-like minimisation
(`qapm.mzn`, 7,163, 3,978, 2,045 and 588 restarts at the same scales) gives the
same three solutions, and a smaller one (`opt.mzn`, 3, 2, 2 and 0 restarts) the
same final optimum, with fewer intermediates at the three scales that
restart; and
`==========` throughout (`tmp/fd-nogoods/nogoods/fzn/fzndiff.sh`). No Gecode
comparison was run; the C++ differential below compares against brute force
instead.

### Options

- **`refined`** (both constructors). `true` installs the two-watched-literal
  propagator, `false` the scan. The fixed constructor defaults to `true`; the
  growable constructor defaults to `false` (`nogoods.hh:93`, `:103`), but
  `solve_with` passes `true` for the learned store.
- **`GCS_LEARNED_NOGOODS_SCAN`**, an environment variable read once per solve
  by `solve_with` (`solve.cc:354`): if set, even to the empty string, the
  learned store uses the scan path. It exists as the differential oracle.

Neither changes the OPB model, which is the same rows either way; they choose
the propagator only. There is no `with_consistency()`.

### Variable kinds and views

Literals may be on plain variables, views (`x + c`, `−x + c`) and constants.
`State::literal_is_entailed` and the engine's watch index see through views
(a watch on a view is armed on the underlying variable,
`propagators.cc:314-334`), and a watch on a constant is not armed at all, which
is right, since a constant literal never changes. The proof handles views too:
every view shape above verifies (`scpview.cc`, shapes 1 and 2), and the
strength sweep below includes views on both paths.

### Reification

`None`, and none is wanted: `Nogoods` is not a user constraint. A half-reified
nogood would be one more literal in the clause.

### Relation to other families

- **Decomposes into it:** nothing.
- **Child constraints:** none.
- **Shares code:** none. `NegativeTable` and the logical family's watched
  clause (`propagate_watched_clause`) carry their own copies of the same
  two-watched-literal design (see [`table.md`](table.md) and
  [`logical.md`](logical.md)); #131 proposes one generic propagator for all
  three. A `Nogoods` clause is, semantically, an `Or` with a true reification,
  and `logical.md` reaches the same strength verdict for it. Not a candidate
  merge with either: the family list marks none, and #131 is where the shared
  scheme would go.
- **Presolvers:** none reads or writes it. An `AutoTable` presolver runs every
  propagator at a throwaway root and backtracks, which once stranded this
  family's set-up mark (#1106, fixed by #1107 for both `NegativeTable` and
  `Nogoods`).
- **Engine coupling, which is most of this family:** `solve.cc` installs and
  grows the store and derives every learned clause in the proof
  (`ProofLogger::emit_learned_nogood`, `proof_logger.cc:447-461`), and
  `Stats::learned_nogoods` is the store's size at the end of the solve
  (`solve.cc:501-502`).

## The proof model

### OPB encoding

For each nogood `n` present when the constraint is installed:

```
∑_{ℓ ∈ n} ¬ℓ ≥ 1          unlabelled
```

over the literals' order and equality atoms, which the shared literal layer
defines (`nogoods.cc:80-91`). **Definitional**: the row is the clause the
nogood means. One row per nogood, `|n|` terms, independent of any domain. An
empty nogood writes a row with no terms, `>= 1`. A range literal cannot be
written at all (#310). The learned store contributes **no rows**: it is empty
when installed, and its nogoods are derived in the proof.

### Labels

`None.` The rows carry no label and no rule cites a row by name.

### Cake conformity

None: `cake_pb_cp` has no `nogoods` rule (see the frontend footnote), and no
`verified_encodings/scp_cases` fixture exists. `scp_reader_test` is what checks
the reader, by enumerating one instance and round-tripping another
(`scp_reader_test.cc:1725-1739`, `:1741`).

### Proof-time state

- **At the root:** for the fixed form, the OPB rows above, and nothing else.
- **Per learned nogood:** a comment and one line at `ProofLevel::Top`,
  ```
  % learned nogood
  rup 1 ~i[_13][eq8] 1 ~i[_11][eq9] 1 ~i[_5][eq5] >= 1;
  core id -1;
  ```
  written by `emit_learned_nogood` during the restart unwind, one per refuted
  sibling of every frame on the abandoned path. The `core id -1` follows only
  when the abandoned level held a core clause (a `solx` blocking clause, or a
  child's promoted backtrack clause), which happens exactly when an enumeration
  found a solution below it, and only at `AssertionLevel::Definitions` or below
  ([`solution-clause-deletion.md`](../solution-clause-deletion.md), "Restarts").
  On Langford 7's enumeration with `--restarts=1`, 44 of 109 were moved.
- **Deleted:** never. Learned lines live at `Top` for the rest of the proof, as
  the store keeps every nogood for the rest of the search. Under enumeration
  some of them are what excludes the solutions already reported, so deleting
  any would have to meet the conditions under [Next steps](#next-steps), item 7.
- **Naming:** no label; a learned line is found by the `% learned nogood`
  comment before it, or by its line number. Its literals are atoms the shared
  layer has already defined, since they were branching decisions.
- **Auxiliaries:** none, in the OPB or in the proof.
- Nothing is indexed by anything that dangles when proofs are off.

## The implementation

### Initialisation and global data

`NogoodStore::add` records the nogood and the distinct variables it mentions,
by linear search (`nogoods.cc:46-53`), so adding a nogood of `k` literals costs
`O(k²)`. The fixed constructor builds the trigger list the same way, in
`O(literals · variables)`. Both are negligible
against search for any store this audit saw (at most 7 literals per learned
nogood on `qap 8`).

Both paths install an initialiser that visits every nogood present at install
and either finds two non-entailed literals, propagates the one survivor, or
contradicts (`init_watches_for`, `nogoods.cc:102-129`). The scan path keeps
the watches it finds; the refined path throws them away
(`initial_scratch`, `:237-243`) and arms its real watches at the first root
propagation. For the learned store, which is empty at install, the initialiser
does nothing.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| initialiser | — | — | 1, 2 | always | — | — |
| scan (`install_scan_nogoods`) | `on_change`, every trigger variable | derived: every trigger variable; **really** only the variables of `≠` and `∉` literals | 1, 2 | `refined = false`, or `GCS_LEARNED_NOGOODS_SCAN` for the learned store | not claimed | never |
| refined (`install_refined_nogoods`) | none at install; two `ctx.watch` per clause at run time | declared: every trigger variable (`holes_affect_propagation`); **really** only the variables of `≠` and `∉` literals | 1, 2 | `refined = true` (the learned store's default) | not claimed | never |

**What holes can do here.** A literal becomes newly entailed by an interior
removal only if it is `x ≠ v` (removing `v`) or `x ∉ [lo, hi]` (removing the
last value inside); `x = v`, the bounds operators and `x ∈ [lo, hi]` change
only on a bounds or instantiation event, which is the engine's own trigger mask
for them (`propagators.cc:343-376`). So the true sensitivity is the variables
of `≠` and `∉` literals. Both paths overstate it for the fixed form. For the
learned store, declaring every variable is right in general: `smallest_out`,
`largest_out` and `random_out` put `x ≠ v` first, so it is a kept decision, and
`reject_random_interval` puts `x ∉ I` first. The reasons given elsewhere are
wrong, though the conclusion stands. The source comment (`nogoods.cc:370-374`)
says "A nogood may hold x == v, which a hole in x falsifies", but falsifying a
nogood's literal satisfies its clause and allows no new inference; it is
`x ≠ v` in a nogood that a hole entails.
[`optional-interior-pruning.md`](../optional-interior-pruning.md) says, at
`:52-54` on `86caad24`, only "a nogood may hold `x == v`", and at `:301-306`
that "a nogood holds the negation of each decision on a path, so any brancher
that can decide `x != v` --- `smallest_in`'s right branch does --- can put
`x == v` in a nogood". A nogood holds the kept decisions themselves, not their
negations, and `smallest_in`'s right branch `x ≠ v` is exactly the negative
decision that is dropped (`solve.cc:196-198`).

**Scope.** The refined propagator declares none: no coarse trigger, no
`Triggers::refined` and no `scope_only` (`nogoods.cc:375`).
`propagators.hh:388-401`
describes this case (a propagator arming its watches at run time "would
otherwise have an empty scope and so be invisible to degree-based heuristics")
and says to list the variables in `scope_only`, which #506 added for exactly
this; `NegativeTable` adopted it, `Nogoods` did not. `refined-triggers.md`
says the same at `:80-84`, two lines after describing this client as arming
everything at run time and leaving `Triggers` empty (`:76-78`), and asks
clients to "watch only variables declared in scope" (`:55-57`), which this one
does not. So the propagator adds nothing to any variable's degree or to the
variable-to-constraint adjacency. Under dom/wdeg's `classic` and default `chs`
schemes the weighting credits its conflicts to the constraint, but a variable's
weighted degree is summed over its adjacent constraints, so the credit never
reaches a variable; the other schemes return early on the empty scope (#1392).
For the learned store, whose scan path watches every variable, the
missing degree is a uniform shift and leaves `dom_then_deg` unchanged; for a
posted store it can change the tree under `dom_then_deg`, the solver's default
brancher (47 of 500 random fixed stores whose nogoods use only the first half
of the variables, `tmp/fd-nogoods/nogoods/fixeddeg/`).

**Which constraint a failure is charged to.** With the scope declared, the
two paths still branch differently under dom/wdeg, through the conflicts the
weighting is told about rather than through what is propagated. The scan
propagator subscribes to every variable, so any inference queues it for the
next round, where it also sees what that round has inferred before it runs.
The refined one is queued only by the inference that entails one of its
watched literals, when the round boundary replays it
(`propagators.cc:1002-1029`, `:1226-1297`). So at one node the store's unit
inferences land at different points in the propagation. Propagation stops
at the first propagator to meet a wipeout, and the conflict observers are
told that propagator's constraint (`:1336-1341`, `:1382-1390`). `classic`
and `chs` weight that constraint (`variable_weighting.cc:155-178`); `ia`,
`ca`, `id`, `cd` and `ca.cd` weight its scope's unfixed variables, at the
partly propagated domains of that moment (`:213-240`). In a scratch build of
`86caad24` that adds `scope_only` behind an environment switch
(`tmp/fd-nogoods/codex/c3-attribution/`, fataepyc-08, 2026-10-22), on
`langford --branch dom-wdeg --restarts=1 8` (default `chs`, refined with
`scope_only` against scan), every branch state and decision agrees, and every
conflict is charged to the same constraint, up to the 16th conflict, at
`position[7] = 9`, `position[6] = 10`, `position[2] = 12`. There the scan
store, queued a round earlier, makes a unit inference, and in the next round
the tabulated `Plus` over `position[3]` and `position[11]` fails. On the
refined path the store is queued a round later, behind the `AllDifferent`,
which fails before the store runs. The first decision to differ is at the
60th branch callback. Sizes 7, 9 and 10 also first differ at such a
conflict, not always one the store is charged with. With scan's and the
scope-fixed path's decisions each replayed on the other, and scan's on
unfixed refined, at sizes 7 to 10, all three reach the same domains at every
branch callback, with the same restarts, learned nogoods and solutions, and
charge 2.8% to 4.9% of conflicts to a different constraint (35 of 956 at
size 8, scan's tree replayed on the scope-fixed path). On the random
differential with both scratch fixes (the end-to-end harness on
`tmp/fd-nogoods/nogoods/src-rootfix`; seeds 1 to 40, intervals and value
lists, `dom_wdeg` with `smallest_in`), no restarting pair of the 1,392 in
enumeration and find-one differs in recursions or learned nogoods, and 14 of
7,891 in optimisation do; in each of the 14 the first difference in the
trace is a conflict charged to a different constraint. Lee, Schulte and Zhu
report the same effect in Gecode ([Prior art](#prior-art)).

**Idempotence.** Neither path claims it, and one call is not a fixpoint in
general. With `c0 = {y = 1, z = 1}` and `c1 = {x = 1, y ≠ 1}`, fixing `x = 1`
makes the scan force `y = 1` at `c1` after it has passed `c0`, which is now
unit; the refined path hears of it only through the watch that inference
fires, on its next run. Both rely on being woken again, the scan by its own
`on_change`, the refined path by that watch. Argued from the code, not
measured.

**Self-disabling.** Never. A satisfied clause is left with its watches; the
propagator returns `Enable` on every call.

### Mutable state and incrementality

- **Scan:** a `vector<pair<size_t, size_t>>` of watched positions per clause,
  **not backtrackable** (`nogoods.cc:141-143`). That is safe only because the
  scan never trusts it: every call re-tests both watched literals against the
  current state, and moves or acts accordingly. It is grown by a catch-up at the
  top of every call (`:158-159`), so a nogood added to the store is armed at the
  next wake, wherever in the tree that is.
- **Refined:** the watched positions per clause packed into `watch_state(ni + 1)`,
  and the number of clauses set up in `watch_state(0)`, both backtrackable and
  restored with the watches (`:249-254`). Catch-up runs only when the propagator
  is called with no fired payloads, which happens only at a root propagation
  that runs every propagator (`:268-308`): once for the fixed form, and once per
  restart pass for the learned store, except when that pass's root is seeded by
  an improved objective bound instead (#1390). On a fire it visits only the
  clauses whose watches fired, deduplicated by a sort (`:310-316`).

What is recomputed that could be kept: `find_unbroken` searches each clause
from position 0 (`:258-266`), not from after the watch it is replacing, so a
long clause whose leading literals are entailed is rescanned from the front on
every move. Learned nogoods are short (at most 7 literals on `qap 8`), so this
was not measured. The logical family's watched clause made the other choice,
searching forwards from after both watches ([`logical.md`](logical.md),
since #1060).

### Interior values and optional pruning

**Offers.** `None.` There is no optional pruning; every inference is a unit
clause's survivor.

**Observes.** See *What holes can do here* under [Propagator
inventory](#propagator-inventory): the variables of `≠` and `∉` literals, and
both paths declare more. The learned store declares every problem variable, so
with restarts on, every other constraint's optional interior pruning stays on.

### Robustness and limits

**Unbounded domains.** Fine: no inference reads a domain except through
`literal_is_entailed`, which is a bound read, a single-value read, a membership
test or an interval intersection.

**Negative values and zero.** Fine; the random sweeps below use values from
−4 to 5 and domains from −2.

**Degenerate shapes.** An empty nogood, a one-literal nogood, constants, views,
repeated variables, a nogood with two literals on one variable, an empty set of
nogoods, and an empty learned store: all correct, and the proofs verify (see
[Semantics](#semantics)). Repeated variables cost strength, not soundness.

**Overflow.** No arithmetic, except the packing of two positions into 64 bits
and nogood indices into 32-bit payloads and keys (`nogoods.cc:249-254`):
`state_key(ni) = ni + 1` wraps to 0, the set-up key, at the `2³²`-th nogood.
Not reachable in practice.

**Store size.** The learned store is never pruned. `tsp --restarts=100 --timeout
120` stopped at 120 s with 29,579 nogoods and 53.9 MB resident, where `tsp`
without restarts completes its whole search in 28.7 s at 6.2 MB
(`/usr/bin/time`, audit build, fataepyc-08, 2026-10-22); the two runs do not do
the same work, and restarts make this instance slower to finish, not just
larger. What the store costs per node is under [CPU
performance](#cpu-performance).

**Threads.** `NogoodStore` is a pair of `shared_ptr<vector<…>>` with no
synchronisation, and `Nogoods::clone()` shares it (`nogoods.cc:74-78`). Search
is sequential today, so nothing races; a parallel search would need a store per
worker, as the header anticipates.

### Interval efficiency

**Fine at any width.**

1. **Propagation.** No site walks values. Each literal test is
   `literal_is_entailed`: `optional_single_value`, `in_domain`, a bound, or
   `domain_intersects_with` for `∉` (`state.cc:916-937`). Work per wake is
   proportional to literals tested, never to width.
2. **Reason.** `generic_reason(vars)` over the nogood's distinct variables: one
   literal per bound and one per run of holes, found by intervals (#935), and
   materialised only by a proof-logging tracker. It is not minimal: the minimal
   reason is the other literals of the clause themselves, where this one is
   every such variable's whole domain plus the survivor's own variable's bounds,
   so a unit on `z` carries `z ∈ 0..3` as well (measured at `Inferences`, under
   [Rule: unit](#rule-unit)).
3. **Proof.** One line per inference, one form, no width gate needed. A learned
   nogood's line is one literal per decision.
4. **Audit lane.** One row, `Nogoods`, pinned `Clean`: the fixed form over two
   wide variables, `{v0 = 0, v1 = 0}` (`large_domain_audit_test.cc:838-841`). It
   varies width only: not holes, views, `≠` or range literals, the scan path, or
   the learned store, and whether it reaches a reason was not checked. The
   learned store has no row; [Next steps](#next-steps) has an item.

## Inference catalogue

Three rules: two inferences of the propagator, on both paths, and the
derivation of a learned nogood, which the search driver makes rather than the
propagator but which is this family's only proof rule that is not a single
clause step.

Facts that hold for rules 1 and 2:

- **The licence.** The clause is either an OPB row (fixed form) or a learned
  `Top` line (rule 3). Each entailed literal `ℓ_j` follows from the reason's
  literals on its own variable by Theorem 3.3 (complete propagation of implied
  atomic literals on one variable), the clause row is then unit or falsified,
  and the reason comes along by Theorem 2.6. That is plain clause propagation;
  the thesis has no procedure named for it, because it needs none beyond 3.3
  and 2.6. See [`justification-techniques.md`](../justification-techniques.md).
  A range literal goes through the range-literal layer instead. In a learned
  nogood it reaches the proof today: `reject_random_interval` makes `x ∉ I` a
  kept decision, and `solve_test`'s reject-interval case writes and verifies
  `rup 1 i[_1][in1_2] 1 i[_1][eq3] 1 i[_2][eq2] >= 1;`. In a posted nogood it
  cannot be written into the model, and throws with proofs on (#310).
- **The reason** is `generic_reason` over the clause's distinct variables, as
  under [Interval efficiency](#interval-efficiency), and not minimal.
- **No hint.** `JustifyUsingRUP{}` with no annotation, so at
  `AssertionLevel::Inferences` the family's `a` lines carry no `::name:` at all
  (on `qap --restarts=1 8`, 367 of the proof's 35,507 assertions, every
  unannotated one). There is no `hints::` type for this family; see [Next
  steps](#next-steps).
- **No justification reads `state`.**

### Rule: unit

- **Infers** — `¬ℓ_i`, for the one literal of a nogood that is not entailed
  when every other is.
- **Fires when** — the initialiser, for a nogood unit at install; the scan,
  when a watched literal is entailed and no replacement exists; the refined
  path, at set-up (a clause unit on first sight, `nogoods.cc:292-297`) and when
  a fired watch has no replacement (`:337-361`).
- **Strength** — `partial`: unit propagation on each clause separately, which
  is GAC on that one clause when its literals are over different underlying
  variables, and weaker when two share one, since each literal is an atom:
  `{x ≥ 3, x < 6}` over `x ∈ 0..10` removes nothing, where GAC on the clause
  would remove `3..5`. It is not GAC on the conjunction of the clauses, which
  the header rightly says would be co-NP-hard. The claim covers every variable
  of every clause. Checked by
  brute force (`tmp/fd-nogoods/nogoods/strength/strength.cc`): 14,000 random
  instances with the four scalar operators and 12,000 with the range operators
  as well, one to four variables over holey value-list domains in `−2..5`, one
  to five nogoods of zero to four literals on variables, views (`x + c`,
  `−x + c`) and constants, refined and scan (scalar operators: seed 1 at 2,000
  instances and seeds 2 to 5 at 3,000; range operators: seeds 2 to 5 at 3,000).
  On both paths and
  every instance, the root fixpoint equals the unit-propagation fixpoint of the
  clauses computed independently over explicit value sets, every search node is
  closed under it, and the solutions equal brute force. The unit-propagation
  fixpoint differs from the fixpoint of per-clause GAC on 426 instances, every
  one with a repeated underlying variable in some nogood, and on none of the
  6,040 without one. This covers the fixed form; the learned store runs the
  same code, and the differential below covers it end to end.
- **Algorithm** — scan: every clause, two literal tests unless a watch is
  entailed, then a search for a replacement: `O(N + moved · k)` per wake for
  `N` nogoods of up to `k` literals. Refined: the fired clauses only,
  `O(f log f + f · k)` for `f` fired watches, plus the engine's firing loop over
  the watches on each changed variable and its undo of every watch moved (see
  [CPU performance](#cpu-performance)). Two watched literals is Moskewicz et
  al.'s scheme. Gecode's nogoods from restarts already subscribe to
  non-Boolean nogood literals and test them by entailment, bound overshoot
  included, and a watch that is restored on backtrack is what Gent, Jefferson
  and Miguel call a dynamic trigger rather than a watched one; what this path
  chose is listed under [Prior art](#prior-art).
- **Why it is true** — the clause says at least one literal of the nogood is
  false; every literal but `ℓ_i` holds, so `ℓ_i` does not.
- **Proof technique** — `RUP`, against the clause row or line, by Theorem 3.3
  per entailed literal and Theorem 2.6 for the reason. No published procedure
  names it. Preconditions: the clause's row (fixed form) or learned line is
  live, which it is for the rest of the proof, and each entailed literal is
  implied by its own variable's reason literals, which `generic_reason`
  guarantees by covering each variable's whole domain.
- **Reason** — the domains of the clause's distinct variables, per run, lazily
  materialised.
- **Assertion** — `¬ℓ_i ∨ ¬reason`. At `Inferences`
  (`tmp/fd-nogoods/nogoods/scp/inf.cc`, nogood `{x = 1, y ≥ 2, z ≠ 3}`):
  ```
  a 1 i[z][eq3] 1 ~i[x][eq1] 1 ~i[y][eq2] 1 ~i[z][ge0] 1 i[z][ge4] >= 1;
  ```
  `z = 3` is the conclusion; `x = 1` and `y = 2` are the reason's fixed
  variables (the clause needs only `y ≥ 2`), and `z`'s own bounds are in it too.
- **Hint** — none (no `hints::` type).
- **Offline reconstructibility** — `offline`: an unhinted RUP of the assertion
  succeeds against the clause's OPB row (fixed form) or learned line (rule 3),
  both in the baseline context, as for `NegativeTable` ([`table.md`](table.md))
  and the logical family's clauses.
- **Proof size** — one line per inference, `O(k + runs)` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No mutation lane exists for this rule.

### Rule: violated

- **Infers** — a contradiction, when every literal of a nogood is entailed.
- **Fires when** — the initialiser, at install; the scan or refined path when
  both watches are entailed and no literal is left that is not
  (`nogoods.cc:186-187`, `:333-335`). It needs every literal entailed before
  the propagator next runs: one decision entailing two literals on one
  variable, or two literals on different variables entailed by other
  propagators in the same round (`Equals{x, z}`, `Equals{y, z}` and the nogood
  `{x = 1, y = 1}`, branching on `z` first, violates the nogood in the `z = 1`
  branch on both paths; its line is below;
  `tmp/fd-nogoods/factcheck/doc/viol/viol.cc`).
- **Strength** — as rule 1.
- **Algorithm** — as rule 1; the failing search for a replacement is `O(k)`.
- **Why it is true** — the forbidden conjunction holds.
- **Proof technique** — `RUP`, as rule 1: the row is falsified outright.
- **Reason** — as rule 1.
- **Assertion** — `¬reason`, since this is an explicit `contradiction()`. At
  `Inferences` (`con.cc`, nogood `{x ≥ 1, x < 3, y = 0}`, `y` branched first):
  ```
  a 1 ~i[x][eq1] 1 ~i[y][eq0] >= 1;
  ```
  and from the two-variable probe above, `a 1 ~i[x][eq1] 1 ~i[y][eq1] >= 1;`.
- **Hint** — none.
- **Offline reconstructibility** — `offline`, as rule 1.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: learned-nogood

- **Infers** — the clause `∨_{d ∈ P ∪ {s}} ¬d` at `Top`, for a frame on a path
  abandoned at a restart cutoff, its kept positive decisions `P`, and a sibling
  decision `s` it had fully refuted. The same nogood goes into the store.
- **Fires when** — the restart unwind, at every frame with a refuted sibling,
  deepest first (`solve.cc:245-275`); never on a normal backtrack.
- **Strength** — n/a: a derived clause, not a propagation.
- **Algorithm** — one line per refuted sibling: `O(|P| + 1)` literals each. The
  number per restart is bounded by the abandoned path's total sibling count.
- **Why it is true** — `s`'s subtree under the full path was refuted, so
  `¬(path ∧ s)` holds. Each decision dropped from the path is `¬f` for a first
  sibling `f` that an ancestor frame on the same path had already refuted, so
  the ancestor's kept decisions imply `¬f`. By induction from the root, `P`
  implies every dropped decision, so `P ∧ s` implies `path ∧ s`, which is
  refuted (Lecoutre et al.'s argument). What the subtree is refuted against
  depends on the mode. A decision run stops at its first solution, so nothing
  has been excluded when a nogood is learned, and it follows from the model.
  Under enumeration a subtree counts as refuted once it is fully explored, its
  solutions reported: the nogood holds in the model with the solutions reported
  so far excluded, and need not hold in the model itself. Under optimisation it
  holds in the model with the objective below the incumbent when it is learned,
  a bound that only tightens. The search posts no blocking clause, so the store
  is what keeps a later pass out of an explored subtree, and under enumeration
  what stops a solution being reported twice (examples under [Next
  steps](#next-steps), item 7).
- **Proof technique** — `RUP`, against everything live at that moment: the
  sibling's own backtrack clause and the ancestors' backtrack clauses, still at
  their levels because the unwind is deep first, re-derive the dropped negative
  decisions, and the sibling's backtrack clause then conflicts. **No published
  procedure**; the thesis's backtracking justifications (§3.3.2) are the
  unreduced, non-restart case. Preconditions: emitted before this frame's
  `forget_proof_level`, and the root's level 1 kept across restarts
  (`solve.cc:279-288`), without which later passes' backtracks are not RUP.
  Always `rup`, even at `Inferences` and `Backtracking`, where the backtrack
  clauses it uses are themselves asserted.
- **Reason** — none; the clause is the conclusion.
- **Assertion** — never asserted.
- **Hint** — none.
- **Offline reconstructibility** — n/a: never asserted. It is a plain RUP line
  in the proof, which a reconstructor keeps as it is.
- **Proof size** — one line, `|P| + 1` literals, plus a `core id` when promoted.
  On `qap --restarts=1 8`: 145 lines, 574 literals, at most 7 in one.
- **Gaps** — `None.`
- **Tightness** — **shown**, by three mutations of `emit_learned_nogood` in a
  scratch build of `86caad24` (`tmp/fd-nogoods/nogoods/mut/`, the random
  differential below at seed 6, 20 instances, every restarting run, `Off`).
  That build, `src-rootfix`, also carries the root-seeding fix of #1390, on by
  default, and environment-switched probes that were off, so
  its optimisation runs search differently from the audit build's:
  - *drop the first decision from the line* (the store keeps the full nogood):
    VeriPB refuses 64 of 108 enumeration runs, 256 of 594 optimisation runs and
    10 of 42 find-one runs, every one at a RUP step. The others learned no
    nogood with two or more decisions, or one whose first decision was
    re-derivable;
  - *emit it at `ProofLevel::Current`* (deleted at the restart's forget): 61 of
    108 enumeration runs refused (56 at a checked deletion, 5 at RUP), 70 of 594
    optimisation runs, 1 of 42 find-one runs;
  - *never move it to core*: 56 of 108 enumeration runs refused, each at a
    checked deletion, and none of the optimisation or find-one runs, which never
    put anything in core at a search level;
  - control, unmutated, same build: 744 of 744 verify.

  So the reduction, the `Top` level and the core promotion are each load-bearing
  on these fixtures; that does not make every corruption detectable.

## Evidence

### Tests

- **`nogoods_constraint`** (`nogoods_test`, `run_test_only.bash`): ten
  hand-picked fixed-nogood instances (equalities, the diagonal, a cascade, a
  unit order literal, mixed operators, `≠` literals, a root contradiction,
  entailment by a bound that overshoots the literal), each with and without an
  `AutoTable` pseudo-root presolver (#1106), on both paths, against a
  brute-force oracle and a per-node unit-propagation check; with proofs, 40
  VeriPB runs. Then a scan-versus-refined differential on recursions and
  solutions over the hand-picked instances and 300 random ones (two to four
  variables, one to six nogoods of one to four literals, values just outside
  the domains), under `in_order` with `smallest_in` and `split_smallest_first`.
  Seeded (`--seed=N`). Not `solve_for_tests_checking_gac`, rightly: the
  propagator is not GAC on the conjunction.
- **`solve_test`**: restart cases for unsatisfiability with d-way, binary,
  bound-split and reject-interval branching, optimisation, enumeration
  (six solutions, each reported once), root propagation kept across restarts,
  and two scan-versus-refined differentials, both satisfaction problems
  (`solve_test.cc:122-465`). VeriPB runs in each proving case.
- **Other families' suites that run the learned store under restarts**:
  `logical_test`'s clause sets, with and without every solution blocked, under
  `luby(1)` (`logical_test.cc:380-413`); `disjunctive_2d_test`'s shared-origin
  case under `luby(50)` (`disjunctive_2d_test.cc:500-503`), whose strict proof
  carries 744 learned-nogood lines (counted by the fact-check); and
  `difference_test`'s randomised restart stress
  (`difference_constraints_test.cc:1125-1187`). None of them checks the store as
  such; they exercise it.
- **`restarts_test`**: the Luby sequence.
- **`scp_reader_test`**: one `nogoods` enumeration and one round trip.
- **`large_domain_audit_test`**: the one `Clean` row, quoted from the source;
  this audit did not complete a run of the lane (stopped after 33 minutes).

**Runtime caps.** `nogoods_test` uses `solve_for_tests_with_callbacks`, so the
suite's default caps apply, and they **do not fire**: the output with
`GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500` is identical to the
uncapped run, and every proof concludes `COMPLETE ENUMERATION` (36) or
`UNSATISFIABLE` (4) (`nogoods_test --seed=1`, audit build). That is
`nogoods_test`'s oracle runs; its scan-versus-refined differential calls
`solve_with` directly (`nogoods_test.cc:286`). `solve_test`, `restarts_test`,
`scp_reader_test` and `large_domain_audit_test` read no caps, and the other
families' restart solves call `solve_with` directly, so the caps never touch a
restart run. Reported results are from the audit build at `86caad24`,
run directly from scratch directories.

**What the tests do not cover**, and what this audit ran instead:

- **The scan-versus-refined differential under optimisation, under dom/wdeg,
  or under a degree-reading brancher on a posted store.** Both diverge (#1390
  and #1392).
- **Holey initial domains, views and constants in the fixed form.** The
  strength sweep above covers them.
- **The proof at any assertion level but `Off`**, and with value-list
  variables. Below.
- **Long restart runs.** The fact-check counted 744 learned-nogood lines in one
  `disjunctive_2d_test` proof; the other suites were not counted. Nothing in the
  suite is known to approach the tens of thousands of nogoods of a long
  benchmark run, which is where the cost is (below).
- **A store grown other than at a restart**, which fails (#1393).

**The end-to-end differential** (`tmp/fd-nogoods/nogoods/e2e/e2e.cc`): random
CSPs of three to seven variables over intervals or holey value lists, with
`NotEquals` over offset and negated views, `LessThanEqual` and `NegativeTable`
constraints; seven branchers (`in_order` with `smallest_first` and
`smallest_in`, `dom` with `split_smallest_first`, `random` with `random_out` and
`reject_random_interval`, `dom_wdeg` with `smallest_in`, `dom_then_deg` with
`largest_first`); Luby scales 1, 2 and 4; refined and scan. Against brute
force: the solution set, one callback per solution, `Stats::solutions`,
completion, the optimum. Seeds 1 to 4, 60 instances each, enumeration,
optimisation and find-one, intervals and value lists: **60,480 runs with a
restart schedule, 17,581 of which restarted, no mismatch**. That is the
evidence for "enumeration with restarts reports each solution exactly once".
The fact-check's own harness (`tmp/fd-nogoods/factcheck/doc/harn/`: five to
eight variables, other constraints and branchers, Luby 1 and 3) agrees over
172,800 runs, 39,291 of them restarting.

**Proofs at every assertion level** (`tmp/fd-nogoods/nogoods/proofs/`, the same
harness at seed 5, 30 instances, every second restarting run re-run with a
proof (the harness's counter steps twice per unproved run); VeriPB 3.0.2,
`--force-checked-deletion`). The harness reads only the words of the `s` line,
not its counts or bounds; the fact-check's harness compares the whole line with
brute force, at two other seeds, and agrees at every level but `Links`
(below; `tmp/fd-nogoods/factcheck/doc/harn/prf/`).

| Level | Interval variables | Value-list variables |
|---|---|---|
| `Off` | 665 of 665 `VERIFIED` | 520 of 520 `VERIFIED` |
| `Definitions` | 665 of 665 `UNDER ASSERTIONS` | 520 of 520 |
| `Links` | 74 of 665; the other 591 fail at a `solx` or `soli` step (#1210) | 520 of 520 on this fixture |
| `Inferences` | 665 of 665 `UNDER ASSERTIONS` | 520 of 520 |
| `Backtracking` | 665 of 665 `UNDER ASSERTIONS` | 520 of 520 |

The `Links` failure is generic: the same probe without restarts fails at its
first `solx` (`tmp/fd-nogoods/nogoods/links/links.cc`). Value lists do not
avoid it as such: every failure is at a solution line over a range-declared
variable. In the fact-check's harness, whose optimisation objective is
range-declared, 285 of 304 value-list runs pass at `Links` and the other 19
fail at their first `soli`, before any learned nogood; 0 of its 661 interval
runs pass, where 74 of 665 do here. Larger runs, all `Off`
unless said: `qap --restarts=1 8` (91 restarts, 145 learned) `VERIFIED BOUNDS`,
and `UNDER ASSERTIONS` at `Definitions`, `Inferences` and `Backtracking`;
`langford --restarts=1` 7 and 8 complete enumerations `VERIFIED` (52 and 300
solutions), 8 also at `Inferences`; `langford --restarts=10 11`, 35,584
solutions, `VERIFIED COMPLETE ENUMERATION` in 1,615 s
(`tmp/fd-nogoods/nogoods/bigproofs/`). Fixed nogoods with views, constants, an
empty nogood and two literals on one variable verify too (`scpview.cc`). There
is no cake chain to run.

### Benchmarks and examples

- **In the repository:** every example and MiniCP benchmark with
  `--restarts` (above). None posts a fixed `Nogoods`.
- **For CPU:** `tsp --restarts=N`, with a node limit so the work is fixed
  (`tmp/fd-nogoods/nogoods/cpu/tspn.cc`, a copy of `minicp_benchmarks/tsp`
  that stops after `GCS_PROBE_NODE_LIMIT` trace calls). It is optimisation, so
  the refined and scan trees differ (#1390); compare paths on the
  `src-rootfix` build, where they do not.
- **For proof verification:** `qap --restarts=1 8` (26 s at `Off`) and
  `langford --restarts=1 8` (6 s). `langford --restarts=10 11` writes 733 MB and
  takes 27 minutes to check.
- **Never uncapped:** any `--restarts=0` (#1391).

### CPU performance

*Release build of `86caad24` (GCC 15.2.0, `-O3 -march=native`), the audit
build and a scratch build of the same commit (`src-rootfix`, below);
fataepyc-08, pinned with `taskset`, `GLIBC_TUNABLES` fixing the malloc
thresholds; one run each; proofs off; 2026-10-22. Time is `Stats::solve_time`,
and `instructions:u` is from `perf stat` over the whole process. The
`src-rootfix` rows' binary carries the root-seeding fix of #1390
and switch-guarded probes, all off; the undo figures come from a later binary
of the same build with the undo-direction switch.*

The benchmark is the 17-city `tsp` with its default brancher (`dom`,
`smallest_in`), stopped after 1,000,000 trace calls, about 2.0 million
recursions, so every row does roughly the same amount of search
(`tmp/fd-nogoods/nogoods/cpu/tspn.cc`, `fixedwork.sh`). It is optimisation, so
on the audit build the refined and scan trees differ (#1390); the
`src-rootfix` build, which carries the fix of #1390, gives both paths the same
tree, and its rows are the same-tree comparison.

| Build | `--restarts` | Restarts | Learned | Refined | Refined `instr:u` | Scan | Scan `instr:u` |
|---|---|---|---|---|---|---|---|
| audit | none | 0 | 0 | 13.2 s | 68.5 G | — | — |
| audit | 10000 | 43 | 1,074 / 1,106 | 13.95 s | 72.6 G | 81.2 s | 473.1 G |
| audit | 1000 | 254 | 4,663 / 4,698 | 17.4 s | 93.0 G | 393.2 s | 1,950.9 G |
| audit | 300 | 765 | 11,283 | 26.4 s | 152.1 G | stopped at 600 s, 1.67 M recursions | 2,929.8 G |
| audit | 100 | 2,045 | 23,747 | 87.8 s | 543.9 G | stopped at 600 s, 1.14 M recursions | 2,826.4 G |
| `src-rootfix` | 10000 | 43 | 1,106 | 14.2 s | 73.3 G | 80.1 s | 473.1 G |
| `src-rootfix` | 1000 | 254 | 4,698 | 17.0 s | 91.2 G | 393.5 s | 1,950.9 G |

("Learned" gives refined / scan where they differ.)

- **The scan path is far slower**: on one tree, 5.6
  times the refined path's time at 1,106 nogoods and 23 times at 4,698, since it
  visits every clause on every wake of any variable. It is the oracle, and
  nothing else should use it.
- **The refined path's per-node cost still grows with the store**: 6.6 times
  the no-restart time at 23,747 nogoods. A profile of `tsp --restarts=100
  --timeout 40` (audit build, `perf record -F 999 -g`) puts 59.4% of samples in
  the `on_backtrack` callback of `Propagators::propagate`, which undoes
  refined-watch edits by searching the variable's watch list from the front for
  each watch it removes (`propagators.cc:1074-1092`), 6.0% in the firing loop,
  5.7% in `literal_is_entailed` and 3.1% in this family's propagator. That is
  hotspot context; the saving is the next measurement.
- **Searching from the back halves it at `--restarts=100`** (#1394): same
  binary, same tree, the direction behind a switch in the
  scratch build: 72.1 s and 449.9 G instructions against 35.2 s and 194.3 G
  (24,043 nogoods). At `--restarts=300` the gain is smaller, 26.9 s and 155.4 G
  against 21.2 s and 112.4 G (11,356 nogoods). Run on another core while the
  scan rows ran; the fact-check's re-run agrees on instructions to four figures.
- `refined-triggers.md`'s table (`tsp --restarts=10000`, 190.6 s scan against
  58.4 s refined against a 55.6 s floor, 2026-07, to the end of the search) is
  a different series on an older tree and should not be mixed with these.
- **What this does not exercise:** fixed stores, long clauses, `≠` and range
  literals, and dom/wdeg. No comparison with Gecode, Choco or ACE was made
  (#868). Gecode records nogoods from restarts after Lecoutre et al. too (see
  [Prior art](#prior-art)), and Lee, Schulte and Zhu's comparison of nogood
  propagators ran in Gecode 4.3.2; comparing with it would need Gecode's
  brancher and restart schedule matched to this search's, which was not
  attempted.

### Proof performance

*Audit build of `86caad24`, fataepyc-08, 2026-10-22, VeriPB 3.0.2 with
`--force-checked-deletion`, one run each.*

| Instance | Level | Lines | Bytes | Learned lines | This family's `a` lines | VeriPB |
|---|---|---|---|---|---|---|
| `qap --restarts=1 8` | `Off` | 382,526 | 52.0 MB | 145 | — | 26.3 s |
| `qap --restarts=1 8` | `Inferences` | 37,410 | 5.8 MB | 145 | 367 of 35,507 | 0.31 s |
| `langford --restarts=1 8` | `Off` | 105,020 | 6.2 MB | 458 | — | 6.1 s |
| `langford --restarts=1 8` | `Inferences` | 69,876 | 7.6 MB | 458 | not attributed | 0.51 s |
| `langford --restarts=10 11` | `Off` | 11,471,680 | 733 MB | 11,594 | — | 1,615 s |

**This family's own share is small.** The learned lines are 145 of 382,526 on
`qap 8` (0.04%) and 11,594 of 11.5 million on Langford 11 (0.1%), each a few
literals. The propagator's inferences are 367 of `qap 8`'s 35,507 assertions
at `Inferences` (1.0%; the same run without restarts has no unannotated
assertion, so the 367 are this family's); at `Off` they are `rup` lines
indistinguishable by
form from other constraints' and were not separated. The rest is the other
constraints, the backtracking and the shared literal layer, as in any proof.
How many learned lines a restart run writes depends on how often it restarts,
not on the store's propagation: it is one per refuted sibling on each
abandoned path.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is a RUP at `Off`, every learned clause is a RUP at
every level, and the propagator is the same with proofs on or off. Assertions
carry no hint, which is a reconstructibility matter, not a gap. A range literal
in a posted nogood throws rather than going unlogged (#310); in a learned one it
is logged.

### Known limitations

Restart use:

- **Optimisation with restarts propagates learned nogoods late** on the
  refined path, which is the learned store's default: those learned in a pass
  that improved the incumbent stay unarmed until a later root that leaves the
  objective bound unchanged (#1390). The answers are right.
- **A restart scale of 0 hangs**, through the own `--timeout` of XCSP3, the
  examples and the MiniCP benchmarks (and through SIGTERM on XCSP3, the one
  front end that handles it; `fzn-glasgow` treats 0 as off), even on an
  instance whose root propagation alone would refute it, since the root never
  propagates (#1391).
- **Store conflicts do not inform dom/wdeg** on the refined path, and the
  refined and scan paths branch differently under it (#1392). The scope fix
  removes that cause; the paths still charge some failures to different
  constraints, which dom/wdeg reads (see [Propagator
  inventory](#propagator-inventory)).
- **The store grows without bound**: no deletion (under enumeration it has
  conditions of its own, [Next steps](#next-steps), item 7) and no
  minimisation (the reduction is Lecoutre et al.'s first one only), so a long
  restart run slows with it; `tsp --restarts=100` runs at about a sixth of the
  node rate of the same search without restarts, most of it in the engine's
  watch undo (see [CPU performance](#cpu-performance); #1394).
- **Two literals on one variable** are propagated as atoms, so
  `{x ≥ 3, x < 6}` removes nothing until search or other propagation entails
  one of them. Learned nogoods have such pairs too (bound-split branching keeps
  `x < v` at one frame and `x < w` deeper).
- **No hint** on any assertion; restart proofs carry this family's unhinted
  assertions.

Anything else, which would need work first:

- **A nogood added to a store during search** is enforced only at the next
  root propagation on the refined path, and is not in the proof on either path,
  so the scan path's proof is rejected (#1393).
- **A posted store under the default brancher** can give a different tree on
  the refined path than on the scan path, since the refined one adds nothing to
  degree (#1392).
- **A range literal in a posted nogood throws** with proofs on (#310, and
  `s_expr()`), and **a view** makes the written `.scp` unreadable by our own
  reader (generic).
- **No thread safety**: `clone()` shares the store, which has no
  synchronisation.

### Next steps

1. **Fix the optimisation catch-up** (#1390). Small: at depth 0, do
   not push the objective bound onto `guesses`, so the root runs every
   propagator, the objective's included; that is a superset of what #418 wakes,
   and #418 predates the restart loop, so it restores the root behaviour #418
   changed by accident. Tested in a scratch build only by counts: refined then
   equals scan on every `qap` size tried and every non-dom/wdeg pair of the
   random differential. Needs the suite and a timing check.
2. **Reject or neutralise a scale of 0** (#1391), and read the abort
   flag in the restart driver loop. Trivial.
3. **Declare the refined propagator's scope** (#1392):
   `scope_only = trigger_vars`, as #506 intended. One line. It does not make
   the two paths one search under dom/wdeg, since they charge some failures to
   different constraints (`langford --branch dom-wdeg --restarts=1 8`: 3,055
   and 3,114 recursions refined without and with it, 2,928 scan; see
   [Propagator inventory](#propagator-inventory)). The test for it is
   solutions, verifying proofs and the domains at each branch callback under
   replayed decisions, not equal node counts. Whether a store conflict should
   weight every variable or only the failing clause's is a heuristic question
   to settle with it.
4. **Make the refined-watch undo cheap** (#1394, the engine's).
   Searching the watch list from the back in `on_backtrack` halves
   `tsp --restarts=100`'s time on the same tree, and saves about a fifth at
   `--restarts=300` (above); a one-line change in `propagators.cc`, with no
   change to state or proof, not yet run against the suite. The other clients
   of the watch index (`NegativeTable`, the long-clause `Or`, the slack-watched
   `LinearInequality` of #507) were not measured.
5. **Make the public surface match the intent** (#1393): move the
   growable constructor and `NogoodStore` into `innards` (only `solve.cc` and
   `Nogoods::clone()` use the constructor), or support mid-search additions
   properly. Small for the first; which of the two is Ciaran's call.
6. **A hint naming the clause**, for the external justifier: the fixed form's
   row, or the learned line. It would make the RUP cheaper to check, not more
   reconstructible; whether it pays waits for the external justifier's design.
7. **Store management**, if restart runs get long: deletion of learned nogoods
   (with a proof `del`), Lecoutre et al.'s minimisation, or Lee, Schulte and
   Zhu's increasing-nogood propagator, whose subscription set Gecode's
   `NoGoodsProp` also has ([Prior art](#prior-art)). Each is a design choice
   with a search-shape cost to measure, not a fix. Deletion has two conditions
   under enumeration, one from the search and one from the proof (see [Rule:
   learned-nogood](#rule-learned-nogood), *Why it is true*). Measured on the
   example below and with the end-to-end differential's harness (seeds 1 and 2,
   30 instances each, intervals and value lists), in a scratch build of
   `86caad24` that forgets nogoods by class
   (`tmp/fd-nogoods/codex/c1-deletion/`, fataepyc-08, 2026-10-22):
   - **Search.** At each restart the store has to keep, for each solution
     reported so far, a nogood that forbids it, or a later pass can report it
     again. Forgetting, in the store only, every nogood learned at a frame
     whose subtree held a solution re-reported solutions in 630 of the 746
     restarting enumeration runs, each with the right solution set and too
     high a count; forgetting only those learned at the root, in 394.
     Forgetting every other nogood, in the store and with a `del` of its line,
     changed no answer, and the proofs of all 746 verify at `Off`.
   - **Proof.** A line the store still propagates cannot safely be deleted,
     since a later inference can cite it. A line moved to core can be deleted
     only when the core that is left implies it, and checked deletion consults
     core alone.
   - **They are separate.** A deletion that checks can still drop an exclusion
     the search needs: VeriPB then refuses the proof only at the repeated
     solution, and with proofs off nothing reports it.

   Under optimisation and in a decision run no learned line is moved to core,
   and under optimisation the objective bound is imposed at every node
   (`solve.cc:100-112`): forgetting every nogood, with a `del` of each line,
   gave the right optimum or verdict in all 3,441 and 212 restarting runs, and
   every proof verifies at `Off`.

   The example: `a ∈ 1..4`, `b, c, d ∈ 1..3`, all six `≠`, and `e ∈ 0..1`; `e`
   first with `smallest_in`, then `variable_order::random(p, 1234)` with
   `value_order::random_out(5678)`; `luby(1)`. On the audit build it reports 12
   solutions, each once, in 39 recursions, 4 restarts and 5 learned nogoods, and
   its `Off` proof verifies. With a `del` inserted after a learned line:
   `{e = 0, a ≠ 2}`, learned once the first pass has reported the six solutions
   with `e = 0`, and moved to core, is refused by checked deletion; the third
   pass's root unit `{d ≠ 2}` deletes, since a core backtrack clause with the
   same literal is live at the kept root level, yet forgetting it in the store
   re-reports a solution in the next pass, and VeriPB refuses that repeat;
   `{e = 0, d ≠ 3}`, not in core, forbids four reported solutions, and deletes
   only when the store forgets it too. Minimising `3a + 2b + c − d + 5e` under
   the same brancher, `{e = 0, b ≠ 1}` is learned after the solution of
   objective 14 with `b = 2`, which it forbids: it holds only below that
   incumbent.
8. **An audit-lane row for the learned store**, and one for a `≠` literal over a
   holey wide variable on the fixed form. Small.
9. **Correct the stale text** listed under [Developer
   commentary](#developer-commentary).

## Prior art

- **Nogood recording from restarts.** Lecoutre, Sais, Tabary and Vidal,
  *Nogood Recording from Restarts*, IJCAI 2007, pp. 131–136, record nogoods
  from the last branch of the search tree at each restart cutoff, and introduce
  the **reduced nld-nogoods** this store holds: the positive decisions above a
  negative decision, plus the corresponding positive one; the number recorded
  per restart is bounded by the branch's length, and (as Lee, Schulte and Zhu
  describe it) they are propagated by watched literals. The journal version,
  *Recording and Minimizing Nogoods from Restarts* (JSAT 1(3–4), 2007,
  pp. 147–167), adds minimisation, which is not implemented here.
  `restarts-nogoods-weighting.md` cites the IJCAI paper.
- **Increasing nogoods.** Lee, Schulte and Zhu, *Increasing Nogoods in
  Restart-Based Search*, AAAI 2016, show that the reduced nld-nogoods of one
  restart are "increasing", so they can be propagated together by the
  propagator for increasing nogoods from the authors' earlier work, rather than
  one clause at a time. They add a lightweight filtering that still enforces
  GAC on each nogood while subscribing to fewer decisions, and an approximate
  nogood minimisation; the two together trade a little pruning for speed. Not
  implemented; it is the published alternative to the store's per-clause
  propagation. Their experiments (Gecode 4.3.2) also record that, with the
  nogoods' own weight left out, two nogood propagators of equal pruning gave
  different dom/wdeg trees on several instances, which they put down to the
  order filtering runs in when more than one constraint can fail, while
  dom/ddeg gave identical trees; the two paths here do the same (under
  [Propagator inventory](#propagator-inventory)).
- **Nogoods from restarts in Gecode.** Gecode has recorded nogoods at restarts
  since release 4.2.0 (dated 2013-07-19 in its `changelog.in`), off unless a
  search sets `nogoods_limit` above zero (the driver's `-nogoods` option, with
  `-nogoods-limit`, the depth limit, defaulting to 128). *Modeling and
  Programming with Gecode* (Schulte, Tack and Lagerkvist), §9.6 in the edition
  for Gecode 6.2.0, says
  they follow Lecoutre et al.'s JSAT paper with a different implementation,
  that a nogood literal may be any constraint, and that choices may have any
  arity. In Gecode 6.3.0 (tag `release-6.3.0`, commit `a658ba49`), the integer
  branchers' literals are `x = v`, `x ≤ v` and `x ≥ v` (`x > v` becomes
  `x ≥ v + 1`), and the set branchers' are inclusion and exclusion; these
  branchers give a binary choice's second alternative no literal, since it
  negates the first, which is the reduced nld-nogoods' drop of negative
  decisions. Each literal subscribes on the matching event (assignment for `=`,
  bounds for `≤` and `≥`) and reports itself subsumed by entailment: the
  literal `x ≥ 10` is subsumed once `x.min() >= 10`, so a lower bound of 12
  subsumes it (`GqNGL`, `gecode/int/branch/ngl.hpp:122-149`). One
  `Search::NoGoodsProp` per restart holds that restart's path as a list and
  subscribes to the first two path literals not yet entailed and the refuted
  alternatives between them, advancing along the path as path literals become
  entailed; on each wake it re-tests every literal it subscribes to
  (`gecode/search/nogoods.hpp:49-70`, `nogoods.cpp:99-193`). That is the
  subscription set Lee, Schulte and Zhu's Lemma 3 gives for their LightFilter.
  It drops satisfied nogoods from its list, and the list is restored by
  Gecode's copying and recomputation, not by a trail.
- **Two watched literals.** Moskewicz, Madigan, Zhao, Zhang and Malik, *Chaff:
  Engineering an Efficient SAT Solver*, DAC 2001. Gent, Jefferson and Miguel,
  *Watched Literals for Constraint Propagation in Minion*, CP 2006 (LNCS 4204,
  pp. 182–197), bring watches to CP propagators. In their terms (§2) a
  *dynamic* trigger is one the constraint may move, add or delete when it
  fires, and a *watched* one is dynamic and also stable on backtracking, so it
  needs no restoration; they note that removing a watch when the constraint
  prunes its value is correct for a dynamic trigger but not for a watched one.
  Lee, Schulte and Zhu draw the same line, calling the restored kind dynamic
  subscriptions. This family's refined watches are of the restored kind: the
  engine trails every watch edit, which is what lets the unit case leave a
  fired watch consumed, and the undo is what costs the time under
  [CPU performance](#cpu-performance).
- **What the refined path chose, against these.** One propagator for the whole
  store, every restart's nogoods in it, and the restart unwind records every
  refuted sibling on the abandoned path, with no depth limit
  (`solve.cc:245-275`); each clause is watched on two literals of its own (one
  once it is unit at first sight), not structured on the path; literals `=`,
  `≠`, `≥`, `<`, `∈` and `∉` over variables, views and constants, where a
  learned `x ≠ v` or `x ∉ I` comes from a kept first sibling. Each watch is the
  engine's, armed on one literal with the clause's index as its payload: on a
  change to the variable, the engine tests the literal's entailment, gated by
  the operator's event mask (`propagators.cc:343-370`, `:1008-1027`), and
  delivers the payload, so the propagator visits only the clauses that fired.
  Watch edits and the clauses' watched positions are trailed and undone on
  backtrack (`:1072-1098`), and a satisfied clause keeps its watches. This audit
  claims none of it as new; it compared against Gecode's source, Gent, Jefferson
  and Miguel, and Lee, Schulte and Zhu only.
- **Proof logging.** McIlree's thesis (§3.3.2) gives the backtracking
  justification, `∑ ¬d_i ≥ 1` over the path's decisions, after Gocht, McCreesh
  and Nordström, *An Auditable Constraint Programming Solver*, CP 2022 (LIPIcs
  235, 25:1–25:18). Neither covers restarts. What is ours: deriving each
  *reduced* nld-nogood by RUP during the restart unwind, while the ancestors'
  backtrack clauses still supply the dropped negative decisions; keeping the
  root's propagation level across passes; and promoting learned clauses to core
  so that the abandoned levels' solution-blocking clauses can be deleted by a
  checked deletion. No published account of certified restart-nogood learning
  was found; the search was not exhaustive.

## Further reading

- [`restarts-nogoods-weighting.md`](../restarts-nogoods-weighting.md): the
  restart loop and its unwind signal, `RestartSchedule`, the weighting seam and
  schemes, reduced-nld extraction and the proof lifecycle (keeping level 1, why
  the reduced clauses are RUP, why enumeration needs no blocking nogoods). Read
  it with the stale points under [Developer commentary](#developer-commentary).
- [`refined-triggers.md`](../refined-triggers.md): the engine's per-literal
  watches, the two-watched-literal mapping used here, the `AutoTable` pitfall
  (#1106), and the 2026-07 measurements that motivated it.
- [`solution-clause-deletion.md`](../solution-clause-deletion.md), "Restarts":
  why learned nogoods are moved to core.
- [`logical.md`](logical.md) and [`table.md`](table.md): the two other
  watched-clause implementations.

## Developer commentary

**Stale text found by this audit** (none edited here; lines at `86caad24`):

- `nogoods.hh:74-79`, `:95-102` and `nogoods.cc:131-133`: the learned store
  "stays coarse until ... stage C-2" (#335); it has been refined since the
  commit that wrote them.
- `nogoods.hh:20-24`: "initialises a newly added nogood's watches lazily on its
  next fire" is the scan path's behaviour; the refined path does so only at a
  root propagation.
- `nogoods.hh:53`, and `restarts-nogoods-weighting.md:163` and `:168`: the
  literals are listed as `=` / `≠` / `≥` / `≤`; the fourth operator is `<` (and
  the two range operators are missing).
- `nogoods.cc:370-374`: "A nogood may hold x == v, which a hole in x
  falsifies"; holes matter through `x ≠ v` and `x ∉ I` literals.
  `optional-interior-pruning.md:52-54` repeats the `x == v` reason, and
  `:301-307` says a nogood holds the negations of the path's decisions and that
  `smallest_in`'s right branch puts `x == v` in one; it holds the kept decisions,
  and that right branch is the dropped negative decision.
- `restarts.hh:23-26`: restarts with all-solution enumeration are "rejected at
  runtime (gcs::solve_with throws UnimplementedException)";
  `difference_constraints_test.cc:1132-1134` says the same. `solve.hh:133-134`
  says restarts are "Sound only for finding one solution or for optimising".
  Both are stale: enumeration with restarts is supported, and `solve.cc` throws
  nothing. `fzn_glasgow.cc:371-373`'s help and `minizinc/glasgow.msc.in:10`'s
  flag text (and the generated `.msc` files) say "find-one / optimisation only".
- `restarts.hh:18-20` ("eventually exceed any tree's size") and
  `restarts-nogoods-weighting.md:67-69` ("Completeness holds because the cutoff
  grows without bound"): not at scale 0 (#1391).
- `solve.cc:45-47`: "`RestartCutoffHit` is unused here and is produced once the
  restart loop lands"; it is produced and used.
- `solve_test.cc:338-341` and `constraints.md:419-422`: "a refined-watch literal
  puts its variable in the propagator's scope" holds for `Triggers::refined`,
  not for `ctx.watch`; `solve_test`'s differential agrees because the learned
  store's degree shift is uniform.
- `restarts-nogoods-weighting.md`: the code map's
  `gcs/constraints/nogoods.{hh,cc}`
  and `gcs/constraints/nogoods_test.cc` are now under `nogoods/`; entailment is
  read by `State::literal_is_entailed`, not `test_literal` (#895); and the driver
  loop calls `on_restart()` on every observer in `conflict_observers()`. Its
  reject-interval paragraph (`:241-249`) is stale as a whole: the generator
  exists (`value_order::reject_random_interval`, tested in `solve_test.cc:226`),
  PR #303 merged on 2026-06-16, and a learned `x ∉ I` reaches the proof; the
  "not-a-plain-condition guard" is now `solve.cc:266-270`, which skips only
  proof-scaffolding literals.
- `refined-triggers.md:18`, `:229` and `:481` cite `gcs/constraints/nogoods.cc`,
  now under `nogoods/`. `:233-236` says the scan path is "used by the
  growable-store constructor only when `GCS_LEARNED_NOGOODS_SCAN` is set";
  that constructor defaults to scan (`nogoods.hh:103`), and it is `solve_with`
  that picks refined. `:245-247`: catch-up at "`propagate(nullopt)`, depth 0,
  which the restart loop re-enters once per pass"; under optimisation the root
  is seeded by the objective bound instead (#1390).
- `restarts-nogoods-weighting.md` and `refined-triggers.md`: "semantics-preserving
  (identical tree, nogoods and proof)". For the learned store, satisfaction and
  enumeration give the same tree and the same learned nogoods on both paths under
  every brancher tried except dom/wdeg, but not the same proof: on
  `langford --restarts=1 --prove 7` both paths take 527 recursions and learn the
  same 109 nogoods, and the proofs are 26,705 and 26,661 lines, the inference
  lines differing with the propagation order. Optimisation differs in the tree
  too (#1390 and #1392). The `tsp --restarts=10000`
  table in `refined-triggers.md` is from 2026-07 and was not re-measured as
  such; the figures under [CPU performance](#cpu-performance) are a different
  series.
