# `parity_system_gathering`: gather posted XORs and Boolean equalities into GF(2) systems

> **Maturity** experimental, opt-in: off unless added; reached from the C++
> API only, including a `.scp` read back with `read_scp`; no front end and no
> example adds it · **Audited** 2026-10-20 at `86caad24` · **Open issues**
> filed by this audit: #1381, a `.scp`'s `not_equals`, or any `ReifiedEquals`
> whose `neq` flag disagrees with its condition, is lifted with the wrong
> polarity, and the solve returns wrong solutions; #1380, the pass is
> quadratic in time and memory in the size of the XOR structure. Commented on
> #1193: a gathered system's proof fails the cake chain whenever a `ParityOdd`
> donor has an equality-type literal (`v = c`, `v ≠ c`) over a `{0, 1}`
> variable, which is #1193's root cause in one more place; and on #1374,
> asking to broaden it to every presolver, which takes in this one's `.scp`
> switch. Already open
> and touching this presolver: #983 (no front end reaches it, and
> three-argument `bool_xor` donors are skipped), #1309 (installing many
> propagators under one constraint id is quadratic), #310 (a range literal
> throws with proofs on), #649 (implied equivalences have nowhere to live),
> #1210 and #1330 (assertion levels above `Off`), and #868 (cross-solver).
> Tracked under #871.

`ParitySystemGathering` scans a posted `Problem` for XOR-shaped constraints. It
reads every `ParityOdd`, and every unconditional `Equals` or `NotEquals` whose
operands lie within `{0, 1}` when it runs. It canonicalises their literals into
GF(2) atoms, splits the rows into connected components by shared atom, and
installs one Gauss-Jordan system propagator, plus a root initialiser, over each
component of two or more rows. By default it then retires the gathered donors'
own propagators. Nothing is written to the OPB. The initialiser derives each
donor's slack form inside the proof, from rows the donor already emitted. The
system propagator, its initialiser's derivation, their proof rules, their state
and their hole sensitivity are documented in
[`parity.md`](../constraints/parity.md), which owns them whichever entry point
installs them. This document owns detection, the rewrite catalogue, what the
pass costs, and what it does to the rest of the model. The long design note is
[`parity-system.md`](../parity-system.md). This document audits the presolver
against the presolver variant of the
[template](../constraints/TEMPLATE.md#the-presolver-variant).

Five things to know before touching it.

- **It is invisible by design, so the counters are the only evidence.** It adds
  no OPB content and, outside #1381's shape, changes no solution set. A
  version that gathered nothing
  would pass every solution, OPB and VeriPB check in the tree. The header and
  the test file both say so. See [Evidence that it fired](#evidence-that-it-fired).
- **It decides a Boolean donor's polarity from the wrong field, and that gives
  wrong answers.** The row's parity comes from `enforces_equality()`, which is
  `! _neq`, a description-only flag. What the constraint means is decided by
  its condition. `read_scp` builds every `not_equals` as `(MustNotHold, neq =
  false)`, so a `.scp` written by `fzn-glasgow` and read back with the presolver
  added gives 4 solutions where Gecode and the model give 2. With proofs on,
  VeriPB rejects the proof. With proofs off nothing notices. See #1381 and
  [lift-boolean-equality-row](#rewrite-lift-boolean-equality-row).
- **No front end reaches it** (#983). Through a local switch in `fzn-glasgow`,
  which is on no branch, it gathers 111 rows into one system on
  `parity-learning` and 3,048 rows into 568 systems on `speck-optimisation`'s
  `hard_0`.
  On `parity-learning` the node count is the same either way (1,523,353), and
  the solve takes 4.2 times as long: 224.0 s against 53.3 s. That cost is the
  installed machinery's ([`parity.md`](../constraints/parity.md), CPU
  performance).
- **Its own pass is quadratic.** It builds a dense bit matrix over every
  candidate row, and recounts every atom for every component. On 32,000
  two-row components, setup to the first search node takes 6.7 s and 1.4 GB,
  against 0.13 s and 85 MB without the presolver (#1380). Most of that is the
  pass; the engine adds its own quadratic term through #1309.
- **Its proofs are not chain-portable for equality-type literals over Boolean
  variables.** The header calls
  in-proof slack rows "the chain-portable option". Against the OPB
  `cake_pb_cp` re-derives from the `.scp`, the derivation fails for any
  `ParityOdd` donor with an equality-type literal (`v = 0`, `v = 1`, `v ≠ 0`,
  `v ≠ 1`) over a `{0, 1}` variable, which is what `array_bool_xor` posts.
  The two encoders spell those atoms differently (ours the bit, cake's
  `eq0`/`eq1`), and the derivation cancels by spelling. That is #1193's root
  cause, met in one more place (commented on #1193). Ordering literals
  (`v ≥ 1`, `v < 1`) pass. Against the solver's own OPB, every `AssertionLevel::Off` proof in this
  audit verifies outside #1381's shape.

## What it is

### Semantics

`ParitySystemGathering{stats}` is a `Presolver`. `Problem::add_presolver`
clones it, and `solve_with` runs it after `create_propagators`, after the proof
model is finalised, and **after the root initialisers have run**
(`solve.cc:373–378`). Then it runs the initialisers that it installed
(`:391`), and only after the last presolver does it call
`choose_optional_interior_pruning()` (`:407`). `run` never returns `false`, so
the presolver never refutes a model itself. A contradiction it makes visible
is found later, by the installed machinery.

The rows it gathers each state "an odd number of these literals hold":

- a `ParityOdd(lits)` is the row `lits`;
- an `Equals(x, y)` with both operands within `{0, 1}` is the even 2-XOR
  `[x ≠ 0] ⊕ [y ≠ 0] = 0`, written odd as `{x ≠ 0, y = 0}`;
- a `NotEquals(x, y)` with both operands within `{0, 1}` is the odd 2-XOR
  `{x ≠ 0, y ≠ 0}`.

Over GF(2), the conjunction of the gathered rows of one component is the
system the installed propagator eliminates over. That propagator is
[`parity.md`](../constraints/parity.md)'s, rules 5 and 6.

Degenerate shapes, each measured (`h1-harness`, below):

- **No donors**: `gathered nothing`, nothing installed.
- **One donor, or a component of one row**: left to its own propagator, and
  counted in `skipped_alone_in_component`. Not retired.
- **An empty `ParityOdd`**: counted in `skipped_empty_row`, and left to its
  own propagator, which refutes it at the root.
- **A row whose atoms all cancel** (`ParityOdd{x, x}`, `Equals{x, x}`,
  `NotEquals{x, x}`): no atoms, so alone by construction, and left to its
  donor. `Equals{x, x}` is then trivially true (2 solutions over a Boolean
  `x`), `NotEquals{x, x}` is refuted in 1 recursion, and `ParityOdd{x, x}`
  alone is refuted only by search, in 3 recursions, because `ParityOdd` treats
  the two copies as independent. (`ParityOdd{x, x}` is the in-tree
  `all_cancel` fixture; the harness has `Equals{x, x}` and `NotEquals{x, x}`;
  the solo counts are the fact-check's probe.)
- **Constants and fixed variables**: a `TrueLiteral` or `FalseLiteral` folds
  into the row's parity. A literal over a constant operand, such as `1 = 0` in
  `Equals{x, 1}`, stays as a column of its own, fixed at the root, and is
  counted in `atoms` (`const_operand` reports 5 atoms for 3 variables). That
  column is **shared by every row that mentions the same constant**, so rows
  with no variable in common become one component: see
  [Detection](#detection-and-its-failure-modes), item 7.

### Concrete constraints and frontend coverage

This is the entry-point table, with one row because there is one class:

| Entry point | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `ParitySystemGathering` (presolver) | `frontend gap (#983)` | `frontend gap (#983)` | `frontend gap (#983)`¹ | `frontend gap (#1374)`² | C++ API only; no example adds it |

1. `python/gcspy.cc` has no presolver plumbing at all, so CPMpy, which drives
   gcs through it, cannot reach this.
2. A `.scp` is a model and a presolver is a solve option, so this is a gap in
   `glasgow_scp_solver`, which takes no presolver flag. #1374 asks for a
   `DifferenceLogic` switch there, and its fix (two options, their stats blocks,
   one `add_presolver`) would not cover this presolver: that needs its own
   option. #983 is where the vocabulary for presolver switches is being decided,
   but its table has no `.scp` column and it does not mention
   `glasgow_scp_solver`, so a comment on #1374 asks for that issue to be
   broadened to every presolver, and this one is cited there. The C++ API can
   read a
   `.scp` with `read_scp` and add the presolver. That route is live, and it is
   the one where #1381's wrong answers appear.

What each front end posts, for when one of them gets a switch:

| Front end | XOR-shaped input | Posted as | Gathered? |
|---|---|---|---|
| MiniZinc | `array_bool_xor` | `ParityOdd` over the array (`fzn_glasgow.cc:827–830`) | yes |
| | `bool_not`, `int_ne` | `NotEquals` (`:771–775`) | yes, over `{0, 1}` operands |
| | `bool_eq`, `int_eq`, `bool2int` | `Equals` (`:606–610`) | yes, over `{0, 1}` operands |
| | two-term `int_lin_eq` / `int_lin_ne` with unit coefficients | `Equals` / `NotEquals`, possibly over an offset view (`:690–712`) | only if both operands' bounds are within `{0, 1}` |
| | two-argument `bool_xor` | `NotEquals` (`:864–872`) | yes, but neither MiniZinc version emits it: `flatzinc_builtins.mzn` declares only the three-argument form. A top-level `a xor b` flattens to `bool_not`, and an explicit `constraint bool_xor(a, b)` to `bool_xor(a, b, true)`, which is posted as `EqualsIff{a, b, 1 ≠ 1}` and skipped as reified (Detection, item 2) |
| | three-argument `bool_xor`, `bool_eq_reif`, `int_eq_reif`, `int_ne_reif` | `EqualsIff` (`:611–616`, `:776–781`, `:864–870`) | no: `skipped_reified` (#983's comment of 2026-09-21) |
| XCSP3 | top-level `xor(...)` | `ParityOdd` (`xcsp_glasgow_constraint_solver.cc:1832–1838`) | yes |
| | top-level `eq`, `ne`, `iff` | `Equals` / `NotEquals` (`:1743–1760`, `:1851–1858`) | yes, over `{0, 1}` operands |
| | a condition `(eq, …)` / `(ne, …)` | `Equals` / `NotEquals` (`:1242`, `:1245`) | yes, over `{0, 1}` operands |
| | any other top-level intension | `Equals{r, 1}` over its reified 0/1 result (`:1863`) | yes, and every such row shares the constant atom `1 = 0`, so they all join one component (Detection, item 7) |
| | `not(...)` inside an expression | `a + r = 1` as a `LinearEquality` (`:1444–1448`) | no: a linear equality is not read |
| | `xor` inside an expression | `ParityOdd` over the arguments and an auxiliary `not_r`, with `r + not_r = 1` as a `LinearEquality` (`:1588–1602`) | the `ParityOdd` row, yes. The link `r ⊕ not_r = 1` is a linear equality, which the scan does not read, so `r` is never joined to the row |
| `gcspy` | `post_xor` | `ParityOdd` | n/a, no presolver plumbing |
| `.scp` | `parity` | `ParityOdd` | yes |
| | `equals` / `not_equals` | `ReifiedEquals{x, y, MustHold or MustNotHold, false}` (`scp_reader.cc:263`, `:480`) | yes, and **a `not_equals` with the wrong polarity** (#1381) |

Through the local switch (see [Detection](#detection-and-its-failure-modes)),
both MiniZinc 2.9.7 and 2.10.1 deliver the same donors to the scan on the two
corpus models with XOR structure.

### Options

**`keeping_donor_propagators(bool = true)`**, default off: leave the gathered
donors' own propagators running, instead of retiring them. It exists so that a
test can check that the system subsumes the donors (the
[retire-gathered-donors](#rewrite-retire-gathered-donors) tripwire), and it
does not change the OPB or what is gathered. Donors in a component that got no
propagator are never retired, however it is set. `parity.md` (Options)
describes it as comparing trees node for node. What the test compares is
solution counts and recursion counts.

The default differs from `DifferenceLogic`'s on purpose. Its
`disabling_lifted_donors()` ships off. The header gives the reason: a donor
row with one literal left becomes a unit row of the reduced system, so the
system infers whatever the donor would have.

There is no `with_consistency()`, and neither `consistency::Auto` nor
`consistency::Dynamic` applies. What the installed propagator achieves is
`parity.md`'s, and what gathering adds is under
[install-component-system](#rewrite-install-component-system).

**Defaults, and why.** It is off, like every presolver, and #983's measurement
says it should stay opt-in when a front end gets a switch: on the one corpus
model where parity dominates, it prunes nothing and costs four times as much.

### Variable kinds and views

- **`ParityOdd` donors**: any literal over any `IntegerVariableID`, as
  `ParityOdd` accepts. Views and constants included. Literals are canonicalised
  syntactically by `canonical_atom` (`gf2_system.cc:79–91`): `≠` to `=`, `<` to
  `≥`, `∉` to `∈`, with the negation moved to the row's parity. Two spellings
  of one fact, such as `x ≥ 1` and `x ≠ 0` over `{0, 1}`, or a view and its
  variable, therefore get separate columns ([Can it weaken the
  model?](#can-it-weaken-the-model)). A range literal works with proofs off
  and throws with proofs on, from model writing, before the presolver runs
  (#310; checked here with `ParityOdd{in_range(x, 1, 3), y}`).
- **Boolean donors**: both operands may be variables, views or constants, as
  long as their bounds **in the state the presolver sees** lie within `[0, 1]`
  (`within_a_bit`, `parity_system_gathering.cc:159–168`). The header says
  "declared domain", but the code reads `initial_state.bounds`, and the root
  initialisers have already run by then. So `x ∈ −3..1` narrowed to `0..1` by
  `Abs`'s root initialiser is gathered (`narrowed_abs_*` fixtures), and so is
  `1 − y` over `y ∈ {0, 1}`. A negated view `−y` has bounds `−1..0` and is
  skipped. A domain narrowed by root **propagation**, or during search, is
  never seen: only the root initialisers run before the presolver. With
  `x ∈ 0..3` and `x ≤ v`, `v ∈ {0, 1}`, an `Equals{x, z}` is counted as wide
  (`p2-order`, and the fact-check's probe). The literals of a
  Boolean row are `x ≠ 0` and `y = 0` or `y ≠ 0` over the operands as given,
  so a view operand gets its own column, distinct from its variable's.

### Reification

`None.` for the presolver: it takes only `reif::MustHold` and
`reif::MustNotHold` donors. `If`, `NotIf` and `Iff` donors are counted in
`skipped_reified` (`:148–157`). For `If` and `NotIf` that is right, since a
row that might not be there is not a parity row. An `Iff` over `{0, 1}`
operands is a 3-XOR, `r ⊕ [x ≠ 0] ⊕ [y ≠ 0] = 1`, and could be gathered
(#983's comment of 2026-09-21). From MiniZinc, every three-argument `bool_xor`
arrives that way: 21 of `parity-learning`'s donors and 1,536 of
`speck-optimisation`'s `hard_0`.

### Relation to other families

- **Into this presolver.** `ParityOdd` and `ReifiedEquals`, both found by the
  class `Problem` stores (`each_constraint_of_type<ParityOdd>()` and
  `<ReifiedEquals>()`). `constraint_enumeration_test.cc` holds down both
  enumerations.
- **What it installs.** Per component, one propagator and one initialiser
  through `install_parity_system_propagator` (`gf2_system.cc:187–336`), under
  `CurrentlyUnnamedConstraint` (`"parity_system"` is the type its empty-row
  note would carry, a path the presolver never takes). They are
  [`parity.md`](../constraints/parity.md)'s machinery: the system propagator
  (rules 5 and 6) and the slack-row initialiser.
- **Shared code.**
  - `find_parity_chain` (`parity_chain.{hh,cc}`): this presolver is its only
    caller.
  - `derive_parity_slack_rows` (`parity_chain.{hh,cc}`), with `ParitySystem`:
    it is called only from the initialiser `install_parity_system_propagator`
    installs, whose callers are `ParitySystem` and this presolver.
  - `build_gf2_system` and `canonical_atom`, with that propagator.
  - `ReifiedEquals`' accessors (`left_variable`, `right_variable`,
    `reification_condition`, `enforces_equality`), which exist for this
    presolver. Outside the tests, it is the only caller of
    `enforces_equality()`, and that accessor is the cause of #1381.
  - `Propagators::disable_propagators_for_constraints`
    (`propagators.cc:864–884`), with `DifferenceLogic`, as
    [`difference_logic.md`](difference_logic.md) records.
- **Other presolvers, and order.** It adds nothing to the `Problem`, so a later
  presolver's scan sees the same constraints either way. It reads the state's
  bounds after every earlier presolver and its initialisers have run, so an
  earlier presolver that narrows an operand to `{0, 1}` at the root would
  change what it gathers. `AutoTable` cannot: it backtracks the epoch its
  subproblem search opened and installs no initialiser, so it leaves the
  domains as it found them (`auto_table.cc:124`, `:137`).
  **`DifferenceLogic` can.** Its installed initialiser fixes conditions
  ([`difference_logic.md`](difference_logic.md)), and a condition can be a
  bound literal on one of this presolver's operands. With `x ∈ 0..3`,
  `a, b ∈ 0..5`, `LessThanEqual{a, b}`, `LessThanIf{b, a, x ≥ 2}`,
  `NotEquals{x, z}` and `ParityOdd{z, w}`, `DifferenceLogic` fixes `x ≤ 1` at
  the root. Added first, it leaves `x` within `{0, 1}`, and this presolver
  gathers 2 rows into one system. Added second, this presolver sees `x` wide
  and gathers nothing. Both orders give the same 42 solutions in 55
  recursions, and both proofs verify at `Off` (`p12-dlnarrow/dlnarrow.cc`,
  the final fact-check's probe, re-run here). So the order changes what is
  gathered; here it did not change the answer. Where nothing is narrowed, the
  order changes nothing: with `x ∈ 0..3` bounded above by a `{0, 1}` variable, through
  `x ≤ y ≤ v` for `DifferenceLogic` (two edges, a propagator installed) and
  through `x ≤ v` for an `AutoTable` over `{x, v}`, run before and after this
  presolver, `x` was still wide when it ran, either way, and stats, solutions,
  recursions and proof verdicts (`Off`, `Inferences`) were identical in both
  orders (`p2-order`). No other presolver reads `ReifiedEquals` or `ParityOdd`.
  The scheduling presolvers' initialisers pin makespan bounds, which could in
  principle narrow a Boolean donor's operand; none was measured.
- **Running it twice** (adding it twice) gathers the same rows again, installs a
  second system over each component, and retires nothing new, since the donors
  are already retired. The proof verifies, because the fresh flags are distinct
  even though their stems repeat. Nothing stops it, and nothing tests it.
- **Reached only through a decomposition?** No. The donors are posted
  directly, by the API and by every front end.

## The proof model

### OPB encoding

None. The presolver writes nothing to the OPB. The `.opb` was byte-identical
with and without it on every size probe here (`p4-size`: `n` = 2, 3, 5, 10,
20 and 50 for both the chain and the Boolean shape, 12 cases). The donors'
encodings are [`parity.md`](../constraints/parity.md)'s accumulator chain for
`ParityOdd`, and [`equals.md`](../constraints/equals.md)'s `le`/`ge` rows
(`Equals`) and `gt`/`lt` rows on a `b[id][ne]` selector (`NotEquals`).

### Labels

It writes no labels. It reads each `ParityOdd` donor's chain by its published
names: `ConstraintProofModelData<ParityOdd>::chain_naming()`, through
`find_parity_chain` (`parity_chain.cc:102–140`), which asks the tracker for
`0ge`, `0le`, `acc`, the four `k_{0,1}_{0,1}` clauses per literal and the
`x[id][k]` flags, all or nothing. These are cake's names. Every `ParityOdd`
emits its chain unconditionally when proofs are on (`parity.cc:70–73`), and a
labelled row is always registered: the chain rows go through
`add_labelled_constraint(id, role, …)`, which claims the label and emits the
row unconditionally (`proof_model.cc:292–298`). So the lookup fails only for a
`ParityOdd` that
was never written to the OPB. That would be one posted into the `Problem`
after `create_propagators`, by a presolver, and no presolver in the tree does
that. A Boolean donor's rows are not cited by name: its two slack rows are
RUP.

### Cake conformity

There are no rows to conform. No SCP chain case runs the presolver, and none
can, because the chain solves with `glasgow_scp_solver`, which has no presolver
switch (#1374, which a comment asks to broaden to every presolver). The
chain's steps 2 to
4 (`verified_encodings/run_scp_chain.bash`) were run by hand on presolved proofs
here (`c1-cake`):

- **Boolean donors only** (`bool_only`, `bool_only_unsat`): all three steps
  pass, and the core verifies.
- **Every `ParityOdd` donor with an equality-type literal over a `{0, 1}`
  variable fails** (`v ≠ 0`, `v = 0`, `v = 1`, `v ≠ 1`), at the `qed` of the
  first `red ... : subproof` whose literal is such an atom (13 fixtures, among
  them two rows, a cycle, constant and negated literals, a fixed variable and
  an empty row). The solver's OPB writes `x ≠ 0` over a `{0, 1}` variable as
  `i[x][b0]`, and cake writes `~i[x][eq0]`. The subproof's `pol` adds the
  labelled step clauses and divides by two, so it needs the literal spelled
  as the `red` line spells it. That is #1193's root cause, which #1193 records
  for `GlobalCardinality` and `Among`; this case is commented there.
- **Ordering literals over `{0, 1}` pass** (`v ≥ 1`, `v < 1`; both encoders
  write `i[v][ge1]`), and so do **`ParityOdd` donors over wider variables**
  (`0..2`, with `≠ 0`, `≥ 1` and `≥ 2` literals). Core verified for each.
- The same models without the presolver pass all three steps.

So the in-proof derivation is chain-portable in its labels and not in its
literals. `parity-system.md` ("The constraint") says that the chain lane covers
the presolver's donors. That is true of their OPB rows. It is not true of a
presolved proof. A hand-written restatement step, three `rup` lines in the
tracker's spelling cited by the subproof instead of the labels, verified against
both OPBs for the derivation's first step (the fact-check's `fixtest.pbp`, a
truncated proof, `VERIFIED NO CONCLUSION` against each; re-run here), so the fix
looks local to the derivation.

### Proof-time state

**At the root, from the pass: nothing.** The pass emits no line, no comment and
no marker.

**At the root, from each installed initialiser** (`InitialiserPriority::
SimpleDefinition`, run by `solve_with` straight after this presolver,
`gf2_system.cc:207–215`): per gathered row, its two slack rows `Σ l = 1 + 2B`
at `ProofLevel::Top`, which every later inference of the system cites by line
number from a shared vector. The derivation is `parity.md`'s (Proof-time
state) and `parity-system.md`'s §2. Measured here at the first node
(`p4-size`):

- **A `ParityOdd` donor over `n` literals**: exactly `10n + 2` proof-file lines,
  that is two `red` steps per literal, the second with a five-`pol` subproof,
  then two telescoping `pol`s. Of these, `2n + 2` stay at `Top`. Two rows of
  `n = 2, 3, 5, 10, 20, 50` added `20n + 4` lines: 44 to 1,004 lines, 1,864 to
  46,134 bytes.
- **A Boolean donor**: exactly two `rup` lines at `Top`, `l₁ + l₂ ≥ 1` and
  `−l₁ − l₂ ≥ −1` (100 lines for 50 `NotEquals`).
- **Nothing is deleted.** `parity-system.md` argues that the `red` steps
  could be (#666's tax applies to what stays).

The fresh flags are proof-only, named `f[<index>][pgather<donor id>_y<k>]`.
Each is determined on a solution by `y_k = (a_{k−1} + l_k + a_k) / 2`
(`parity.md`).

**At every assertion level.** The initialiser emits the same scaffolding at
`Definitions`, `Links`, `Inferences` and `Backtracking` as at `Off`, fully
justified: `red`, `pol` and `rup` lines, no `a`. At those levels no inference
cites it, because the system's inferences are asserted, or, at `Backtracking`,
omitted.

**During search.** The installed propagator's proofs are `parity.md`'s: per
inference one `pol` at `Temporary` over the slack rows of the donors in the
derived row's origin, then a RUP. At `Definitions`, `Links` and `Inferences`
each inference is one `a` line carrying `parity:((constraint_id unnamed))`,
for example at `Inferences`:

```
a 1 i[x][b0] 1 i[y][b0] >= 1::parity:((constraint_id unnamed));
```

That hint names no constraint, so a reconstructor does not know which donors
were gathered. [`parity.md`](../constraints/parity.md) rule 5 gives the
`search` procedure that does not need to: re-collect the eligible rows from the
`.scp`, which are a superset of what the scan read, and eliminate.
[Detection](#detection-and-its-failure-modes) below is what that procedure's
eligibility test has to match.

**Auxiliaries.** Only the `y_k` flags, introduced inside the proof. With proofs
off, the initialiser returns at once, and the shared vector of slack-row lines
stays empty and is never read.

**The assertion levels**, over the 30 harness fixtures, range-declared and
value-list-declared (`h1-harness`):

- `Off`: `s VERIFIED` on every fixture except the two whose donors #1381's
  polarity bug mis-lifts, which are rejected at every level.
- `Definitions`: `UNDER ASSERTIONS` on all the rest.
- `Links`, `Inferences` and `Backtracking`: `UNDER ASSERTIONS`, except two
  shapes, both the #1210 / #1330 family and recorded here, not filed:
  - **A Boolean donor whose operand was narrowed into `{0, 1}` at the root**
    (`x ∈ −3..1` under `Abs`). With range declarations, VeriPB rejects one of
    the presolver's own slack-row `rup`s at `Links`, `Inferences` and
    `Backtracking`: for `NotEquals{x, y}` the second half,
    `rup -1 ~i[x][eq0] -1 i[y][b0] >= -1` (`pbp:56` at `Links`, `:48` and
    `:47` above), and for `Equals{x, y}` the first,
    `rup 1 ~i[x][eq0] 1 ~i[y][b0] >= 1` (`pbp:55`, `:47`, `:46`). `Abs`'s
    narrowing `x ≥ 0` is an asserted unit clause from `Definitions` up. At
    `Definitions` the proof still defines `i[x][ge0]` and `i[x][ge1]` over
    `x`'s bits by `red`, and verifies. From `Links` up those definitions are
    omitted, so the RUP cannot get from `x ≥ 0` and `x ≠ 0` to `x`'s bits. With
    value-list declarations only `Backtracking` rejects it, and only for
    `NotEquals` (`pbp:47`). This is the #1210 / #1330 family: scaffolding
    emitted at every level that needs definitions the tracker omits at `Links`
    and above.
  - **A range-declared variable wider than `{0, 1}`** (`wide_neq0`,
    `y ∈ −2..2`), at `Links`, at a solution line: #1210, with or without the
    presolver. `wide_two_atoms`, over `0..2`, passed at `Links`.
    (`parity_system_gathering_presolver_test` itself aborts at `Links` on
    `wide_domains` in its no-presolver arm, and passes at every other level.)

## The implementation

### Initialisation and global data

Four costs, kept apart as the template asks.

**1. The pass** (`parity_system_gathering.cc:95–246`):

1. Register the stats block, always (`:100`).
2. Walk every posted constraint twice, by `dynamic_cast`: once for `ParityOdd`,
   once for `ReifiedEquals`. With proofs on, each `ParityOdd` costs a chain
   lookup of `4n + 3` label lookups and `n + 1` flag lookups over its `n`
   literals.
3. **`build_gf2_system` over every candidate** (`:183–186`): one `map` lookup
   per literal for the columns, then per row an atom bitset `A` bits wide and an
   origin bitset `R` bits wide, for `R` candidates over `A` atoms. That is
   `Θ(R · (A + R))` bits, zero-filled, whatever the components turn out to be.
4. A union-find over atoms, and a `map` from component to rows.
5. Per component of at least two rows: install one propagator and one
   initialiser (cost 2 below), and **count the component's atoms by calling
   `find` on every atom in the model** (`:233–235`), so `Θ(components · A)`
   for the statistic alone.
6. One `disable_propagators_for_constraints` call, linear in the propagators.

Neither the time nor the memory depends on a domain or a value. Both are
quadratic in the size of the XOR structure (#1380). Measured at `86caad24`,
Release, fataepyc-09, core 60, boost off,
`GLIBC_TUNABLES=glibc.malloc.mmap_threshold=33554432:glibc.malloc.trim_threshold=4294967295`,
2026-10-20, three runs each (wall and `instructions:u` agreed to under 1%), on
`k` components of two `ParityOdd` rows (`x_i ⊕ y_i`, `y_i ⊕ z_i`), stopping at
the first search node (`p3-scale/scale.cc`):

| k | rows / atoms | no presolver | with it | max RSS (off / on) |
|---|---|---|---|---|
| 2,000 | 4,000 / 6,000 | 7 ms, 39.9 M instr | 44 ms, 361 M | 9 / 20 MB |
| 4,000 | 8,000 / 12,000 | 14 ms, 77.6 M | 139 ms, 1.26 G | 14 / 46 MB |
| 8,000 | 16,000 / 24,000 | 28 ms, 153 M | 484 ms, 4.68 G | 25 / 126 MB |
| 16,000 | 32,000 / 48,000 | 59 ms, 305 M | 1.76 s, 18.0 G | 45 / 406 MB |
| 32,000 | 64,000 / 96,000 | 126 ms, 608 M | 6.69 s, 70.5 G | 85 MB / 1.43 GB |

At `k = 16,000`, `perf` puts 58% of the samples in `run`'s own code and 15% in
`Propagators::install_returning_id`. The fact-check's `perf annotate` of `run`
puts nearly all of that 58% in one loop, the atom count's `find`, compare and
increment. The dense matrix shows mostly as memory: `build_gf2_system`,
`set_indices` and `first_set` are each under 2%.
A scratch patch that canonicalises sparsely and counts atoms in one pass
(`p3-scale/sparse-scan.patch`, on no branch; it passes the presolver's test)
takes 1.43 s and 175 MB at `k = 32,000`. There, 70% of the samples are in
`install_returning_id`. That is #1309's constraint-scope loop: every component's
propagator is installed under the one `CurrentlyUnnamedConstraint`, so the
union of their scopes grows with every install. The candidate's figures are
for scale, not a saving claimed for shipped code.

**2. The installed initialisers**, one per component, at the root, with proofs
only (they return at once with proofs off): the slack-row derivation above,
`10n + 2` lines per chain donor and 2 per Boolean donor. Its cost is linear in
the gathered rows' total length.

**3. The installed propagation during search** is `parity.md`'s: from scratch
every call, `O(rows² · (atoms + rows) / 64)` word operations per component. A
component built only from Boolean equalities gets a system too. The size gate
asks for two rows, not for a `ParityOdd`. `n − 1` `NotEquals` in a chain over
`n` Booleans, with no XOR in the model, took 25 ms to the first solution at
`n = 1,000` against 1.7 ms without the presolver, and 143 ms against 3.4 ms at
`n = 2,000` (`p3-scale`, same setup, one run each).

**4. Certificate generation** during search is per inference, as `parity.md`
says.

### Propagator inventory

The pass itself installs nothing that runs during search. These rows
summarise, for this presolver's configuration, what
[`parity.md`](../constraints/parity.md) documents:

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| system, `GaussJordan`, one per component | per literal of every gathered row, via `add_trigger_for` | derived: `on_change` for `=`, `≠` and range literals, `on_bounds` for `<` and `≥`, the donors' own | `parity.md` rules 5, 6 | a component of at least two gathered rows | not claimed (`parity.md`: is, when every atom is over a different variable; the claim would be ignored for aliasing anyway) | `DisableUntilBacktrack` when every atom was decided at the start of the call |
| slack-row initialiser, one per component | none (initialiser, `InitialiserPriority::SimpleDefinition`) | n/a | scaffolding for rules 5 and 6 | as above, proofs on | n/a | one shot |

The presolver never installs `parity.md`'s empty-row refutation, rule 4: it
skips empty rows before installing. The donors' own propagators, and their
idempotence and hole sensitivity, are `parity.md`'s (`ParityOdd`, rules 1–3)
and `equals.md`'s. They are permanently disabled by default
([retire-gathered-donors](#rewrite-retire-gathered-donors)).

### Mutable state and incrementality

The pass keeps no state. The stats block is shared with the clone that
`add_presolver` stores and is filled by assignment at the end (`:243`), so a
caller's handle reads what the last solve that ran the presolver did. A solve
on which it did not run (see [Evidence](#evidence-that-it-fired)) leaves the
previous values in place. The installed machinery keeps
none either (`parity.md`): each call copies the rows and eliminates from
scratch.

### Interior values and optional pruning

**What this presolver offers:** none. It installs no optional-interior-pruning
pair.

**What it observes.** Its pass runs before `choose_optional_interior_pruning()`
(`solve.cc:407`), so what it installs is counted. Nothing is added or lost, but
the observations move from one constraint to another:

- **The system's sensitivity is the donors'.** Its triggers are `add_trigger_for`
  over exactly the gathered rows' literals, which is what each `ParityOdd`
  donor registers. A `≠ c` or `= c` literal over a wide variable declares holes
  in it, as the donor did.
- **Retired donors stop counting.** The analysis skips permanently disabled
  propagators (`propagators.cc:1668–1671`), so with the default retirement the
  same variables are observed by the system instead. With
  `keeping_donor_propagators()` they are observed by both.
- **Boolean donors' operands have no interior.** Their bounds are within
  `[0, 1]` when they are gathered, so whatever the operands' triggers say, no
  hole exists to observe.
- **One caveat, today vacuous.** The analysis keys observers by constraint
  index, and every presolver-installed propagator shares
  `CurrentlyUnnamedConstraint`'s index. A pair installed under that id would
  not see the system as an observer "other than" itself. No presolver installs
  a pair: only `Element` does, under its own id.

The pass reads no domain except the two bounds of each Boolean donor's
operands.

### Robustness and limits

- **Unbounded domains and the integer range.** The pass does no arithmetic:
  bit sets, parity and two bound comparisons against 0 and 1. `ParityOdd`
  refuses an unbounded literal value at construction (`require_bounded`), and a
  wide Boolean-donor operand is simply skipped.
- **Negative values and zero.** A `ParityOdd` literal `v ≠ 0` reads a negative
  value as true, as the donor does (`wide_neq0`, `y ∈ −2..2`). A Boolean
  donor's operand must have a lower bound of at least 0.
- **Degenerate shapes**: see [Semantics](#semantics). Every one was run in
  both declaration styles, with proofs at every level (`h1-harness`).
- **Overflow.** None in the pass. The proof's `pol` coefficients are 1, 2 and
  the division by 2.
- **Large models.** The pass is quadratic in rows and atoms (cost 1 above,
  #1380), and the install adds #1309's quadratic term in the gathered
  variables.

### Interval efficiency

1. **Propagation side (the pass).** `Fine at any width`. The only `State`
   reads are the two bounds of each Boolean donor's operands
   (`initial_state.bounds`). There is no per-value iterator anywhere in
   `parity_system_gathering.cc`. The scan's costs are in donors, literals,
   rows and atoms, quadratic in the last two (#1380). A domain's width never
   enters.
2. **Reason side.** The pass gives no reasons. The installed propagator's
   reasons are one literal per decided atom of the derived row's support, in
   atoms (`parity.md`).
3. **Proof side.** The scaffolding is per literal of each gathered row: `10n
   + 2` lines per chain donor, 2 per Boolean donor. Never per value. The
   donors' chain rows name each literal once, whatever its variable's
   width. There is no width gate, since nothing is chosen by width.
4. **Audit lane.** No row in `gcs/large_domain_audit_test.cc` posts the
   presolver. The parity family's one row there is `ParityOdd`,
   `NoWidePosition`, over `{0, 1}` variables. What no test varies, through this
   entry point: a gathered row over a wide variable, which the harness here
   reached (`wide_neq0`, `holey`, `wide_two_atoms`) and the in-tree test reaches
   only in `wide_domains`; a gathered system of more than six variables in the
   unit tests; a view or a constant operand.

## Rewrite catalogue

These facts hold for every entry:

- The presolver adds nothing to the OPB.
- The pass itself emits no proof line. The installed initialiser emits the
  slack rows. The installed propagator certifies each inference by
  [`parity.md`](../constraints/parity.md)'s rules 5 and 6, against those rows.
- Nothing the presolver route writes is an assertion at `AssertionLevel::Off`.

### Rewrite: lift-parity-odd-row

- **Pattern.** A posted `ParityOdd` with at least one literal. With proofs on,
  `find_parity_chain` must also recover its whole chain (`:111–131`).
  Otherwise it is counted in `skipped_empty_row` or `skipped_uncitable_chain`.
  The latter cannot fire on any constraint posted before solving (see
  [Labels](#labels)).
- **Posts.** A candidate row over the donor's literals, as posted, with its chain
  as its slack source and `pgather<id>_` as its flag stem. Whether it reaches a
  system is decided by
  [install-component-system](#rewrite-install-component-system).
- **Derived mode.** Yes. No OPB row.
- **Why it is true.** The row is the donor's own statement, unchanged.
  Canonicalising a literal to its positive atom with a flip of the right-hand
  side is `¬p = p ⊕ 1`, and a repeated atom cancels because `p ⊕ p = 0`. So
  the canonical row is equivalent to the donor over every assignment.
- **Proof technique.** Of the lift: none. Of its slack rows, in the installed
  initialiser: `redundance` twice per literal, introducing `y_k` by Thm 2.4. The
  second `red` discharges its one real goal by a five-step `pol` subproof that
  divides three times, `parity-system.md`'s §2. Then two telescoping `pol`s,
  each the sum of the per-step rows and the chain's pins. This is ours: Gocht
  and Nordström's §4.4 recovers the same rows from a CNF by enumeration
  (`parity.md`, Prior art). Preconditions: the four step clauses and three
  pins of a chain over exactly these literals, in the order posted, and each
  literal spelled in the proof as the clause spells it (the case commented on
  #1193 is where that fails).
- **Neutral?** For propagation, yes: a single XOR's unit propagation is subsumed
  by the system's ([retire-gathered-donors](#rewrite-retire-gathered-donors)).
  It is stronger over a repeated literal, which the system cancels and the donor
  does not (`parity.md`, Semantics). That holds only once the row is in a
  system. Alone, it stays with the donor's non-GAC propagator.
- **Offline reconstructibility.** Nothing to reconstruct for the lift. The
  slack rows are definitions a reconstructor can introduce itself, by the same
  derivation from the chain, which is fixed by the rule and cites the chain by
  label: `offline`. The installed rules' verdicts are `parity.md`'s, `search`
  for a gathered system (rule 5).
- **Proof size.** `10n + 2` file lines at the root for a donor of `n` literals,
  `2n + 2` of them at `Top`, measured exactly at `n` = 2 to 50. Per later
  inference, two slack-row terms per donor in the origin (`parity.md`).
- **Gaps.** None against the solver's OPB. Against cake's, the derivation
  fails for a literal over a `{0, 1}` variable (#1193).
- **Tightness.** No committed lane: the presolver has no mutation hooks.
  `parity-system.md` records seven ad hoc mutations of the derivation and the
  fold, not re-run here. Two of them survive, telescoping with `a_0 ≥ 1` and
  dropping the `a_n ≤ 0` pin, because the result only weakens the row by a
  pinned term. The two detection failures the test file's header names, a
  chain naming that stops resolving and an enumeration that matches nothing,
  would show in its exact counts. Neither was injected here.

### Rewrite: lift-boolean-equality-row

- **Pattern.** A posted `ReifiedEquals` whose condition is `reif::MustHold` or
  `reif::MustNotHold`, both operands with bounds within `[0, 1]` in the state
  at presolve time (`:147–177`). Otherwise it is counted in `skipped_reified`,
  which is checked first, or in `skipped_wide_operands`.
- **Posts.** The two-literal row `{x ≠ 0, y = 0}` when `enforces_equality()`,
  otherwise `{x ≠ 0, y ≠ 0}`, with `ParitySlackFormIsRUP` as its slack source.
  `boolean_rows_offered` counts it.
- **Derived mode.** Yes.
- **Why it is true**, for the derived classes. Over `{0, 1}`, `x = y` says
  `[x ≠ 0] = [y ≠ 0]`, an even 2-XOR, and `x ≠ y` says they differ, an odd
  one. **It is not true when `_neq` disagrees with the condition.** The constraint's
  meaning is its condition: `MustHold` is `x = y` and `MustNotHold` is `x ≠ y`
  (`equals.cc:404–418`, the propagators, and `constraint_type()`). `_neq` only
  describes it (`equals.cc:386–392`, #865). `enforces_equality()` returns
  `!_neq`. `Equals` is `(MustHold, false)` and `NotEquals` is `(MustNotHold,
  true)`, so both agree. But the public constructor's default builds
  `(MustNotHold, false)`, and so does `read_scp` for every `not_equals`
  (`scp_reader.cc:263`, `:480`). Such a donor is lifted as an equality.
  `gcs/constraints/equals/equals.hh:62–66` says that only one of the two
  spellings is constructible. Both are (#1381).
- **Proof technique.** Of the lift: none. Of its slack rows: `RUP`, twice.
  Negating either half fixes both operands. For an `Equals` donor, that
  falsifies its `le` or `ge` row, JP 3.2. For a `NotEquals` donor, it falsifies
  both halves of its selector pair, JP 3.1. Preconditions: the operands are
  within `{0, 1}` in the proof so far (the declared domain, or a unit clause the
  narrowing initialiser wrote), and the donor's rows say what the lifted
  polarity says. Neither precondition is checked at lift time.
- **Neutral?** For propagation, yes, as lift-parity-odd-row. Its value is the
  atoms it shares: in `bool_bridge_unsat` two XOR rows conflict only through an
  equality, and the system refutes at the root (1 recursion against 3).
- **Offline reconstructibility.** The two slack rows are RUP and stated in
  full: `offline`. The installed rules: `parity.md`'s.
- **Proof size.** Two `rup` lines at `Top` per donor, measured.
- **Gaps.** None for the derived classes. For a mis-polarised donor, the first
  slack `rup` is rejected, at every level (`pbp:24` in the reproducer). Above
  `Definitions`, for a range-declared operand narrowed at the root, the `rup`
  can fail because definitions are omitted (the #1210 / #1330 family; see
  Proof-time state).
- **Tightness.** No lane. The in-tree `bool_equals` fixture is the one the test
  file says would catch a backwards negation, by solution-set mismatch. It
  should, for the derived classes, but nothing was injected to show it. Nothing
  builds the other two shapes.

### Rewrite: install-component-system

- **Pattern.** After canonicalising every candidate together, a connected
  component of the atoms-share-a-row relation that holds at least two
  candidate rows (`:188–227`). Rows with no atoms all fall into one group,
  which the gate always refuses. The group is keyed `nullopt`, and the gate
  checks for that as well as counting members. Refused rows are counted in
  `skipped_alone_in_component`.
- **Posts.** `install_parity_system_propagator(propagators,
  CurrentlyUnnamedConstraint{}, "parity_system", rows)`: one system
  propagator, and one slack-row initialiser, per component.
  `components_installed`, `rows_gathered` and `atoms` count them.
- **Derived mode.** Yes. Certified per inference.
- **Why it is true.** The system's rows are the donors' rows, so every GF(2)
  combination of them holds. The propagator infers only what such a combination
  forces (`parity.md` rule 5).
- **Strength.** `GAC` over the component's system on its PB relaxation, in
  which each canonical atom is a free 0/1 variable: `parity.md` rules 5 and 6.
  That is `GAC` on the conjunction of the gathered rows **when each variable
  contributes one atom**, and on those rows' variables only. Checked by brute
  force:
  - **The fuzz** (`f1-fuzz/fuzz.cc`): 1,062 random models in which every
    constraint was gathered and every atom was a distinct variable's `≠ 0`
    or a constant. Domains were `{0, 1}` or a range inside `−2..3`, declared as
    ranges and as value lists. The whole model was checked by
    `solve_for_tests_checking_gac`: no failure.
  - **The named fixtures** that pass: chains, cycles, negated and constant
    literals, a fixed variable, a holey and a wide variable, Boolean-only
    components.
  - **Shapes that are not `GAC`**, as named:
    - a variable with two atoms (`x = 1` and `x = 2`, `wide_two_atoms`);
    - two spellings of one fact (`x ≥ 1` and `x ≠ 0`, which misses a root
      refutation, `two_spellings`);
    - a view beside its own variable (`Equals{x, −y + 1}`, `eq_view`);
    - a row the gate leaves alone, which keeps its donor's strength:
      `ParityOdd{x, x, y}` alone is not `GAC`, although the system would be
      (`repeat_alone`);
    - every donor that is skipped: reified, wide.
- **Proof technique.** None at install: no line. Each later inference is
  certified by `parity.md` rules 5 and 6, one `pol` (Gocht and Nordström's
  §4.3 fold over the origin's slack rows) and a `RUP`.
- **Neutral?** No. It is a strength gain on the conjunction, which is the point:
  `camouflage` and `bool_bridge_unsat` are refuted in 1 recursion against 3. It
  is also not search-neutral under the default heuristic, because the installed
  propagator raises the degree of every variable in the component. See [Can it
  weaken the model?](#can-it-weaken-the-model).
- **Offline reconstructibility.** `parity.md` rule 5: `search` for a gathered
  system, with the procedure written out there.
- **Proof size.** The install adds no line itself. Its initialiser's lines are
  the two lift entries'.
- **Gaps.** None. There is no proof-only budget or decline. The one
  proofs-only skip, `skipped_uncitable_chain`, is unreachable for constraints
  posted before solving, so proofs on and off gather the same rows (the
  in-tree test asserts the counter is 0 in both arms). That they also search
  identically was checked directly (`p9-fixup/onoff.cc`): 200 random models of
  3 to 8 variables (Booleans and ranges inside `−2..3`; `ParityOdd`, `Equals`,
  `NotEquals`), 134 of which gathered something, gave identical solution
  sequences and recursion counts with proofs on and off, under the default
  heuristic.
- **Tightness.** Not shown by a lane. The strength differentials `camouflage`
  and `bool_bridge_unsat` are what catch a system that gathers and then infers
  nothing.

### Rewrite: retire-gathered-donors

- **Pattern.** At least one component was installed, and
  `keeping_donor_propagators()` was not set (`:238–239`). It covers the
  `ConstraintID` of every donor whose row is in an installed component, and
  never a donor that was skipped or left alone.
- **Posts.** Every propagator of those constraints is permanently disabled
  (`propagators.cc:864–884`). `donor_propagators_disabled` counts propagators,
  one per donor on every fixture and corpus model here (111 for 111 rows on
  `parity-learning`). The constraints keep their OPB rows, scopes, adjacency and
  degrees.
- **Derived mode.** Not applicable: nothing is posted.
- **Why it is true.** Disabling a propagator never loses a solution. For
  strength: a donor infers only when one of its literals is left undecided,
  and then forces it. At that point the system's reduced form contains that
  donor's row with one atom, or a sum of rows that forces the same atom, so
  the system infers it in the same call. A `ParityOdd` donor's `{x, x, y}` is
  weaker than the system's cancelled row, never stronger. A Boolean donor over
  `{0, 1}` prunes only to a fixed value, which is its row's unit propagation.
- **Proof technique.** None: no line.
- **Neutral?** Yes, and it is the presolver's tripwire. Degrees do not move,
  because both arms carry the system. So under the default heuristic, solutions
  and recursions must match with the donors kept and retired.
  - `parity_system_gathering_presolver` asserts that on four fixtures. At
    `86caad24` they give `chain` 2 solutions / 3 recursions / 14 against 5
    propagations, `camouflage` 0 / 1 / 4 against 1, `two_components`
    4 / 7 / 24 against 14, and `bool_bridge` 2 / 3 / 14 against 5.
  - The fuzz here asserts it over 9,600 random models (2,484 of which gathered
    something). All matched.
  - The harness compares it over its 30 named shapes. Recursions matched on
    all of them. Solutions matched on all but #1381's two shapes, where the
    kept arm finds none and the retired arm finds the wrong two.
- **Proof size.** It shrinks the proof by what the retired donors would have
  logged.
- **Gaps.** None.
- **Tightness.** Not applicable: there is no derivation. The tripwire's
  failure message, and the test's check that the retired arm retired something,
  are the guards.

## Detection and its failure modes

What the scan recognises was established directly, by the harness
(`h1-harness/harness.cc`, 30 shapes, each declared as ranges and as value
lists). Each shape ran under no presolver, donors retired and donors kept, and
with proofs at all five levels in the retired configuration. A fuzz added 9,600
random models (24 seeds), and a MiniZinc differential through the local switch
added 1,200 random models on each of 2.9.7 and 2.10.1.

**Gathered:**

- `ParityOdd` over variables, negated literals (`v = 0`), `v op c` literals,
  views, constants, `TrueLiteral` / `FalseLiteral`, repeated literals, a fixed
  variable, wide and holey domains;
- `Equals` and `NotEquals` over `{0, 1}` variables, constants, a view whose
  bounds are within `[0, 1]`, and an operand narrowed into `{0, 1}` by a root
  initialiser.

**Every solution count matched brute force**, except where #1381's polarity
bug applies. The scan fails as follows:

1. **A Boolean donor whose `_neq` disagrees with its condition** is gathered
   with the wrong polarity, and the solution set is wrong (#1381). From the
   `.scp`, every `not_equals`. Nothing counts this. The donor looks like any
   other `boolean_rows_offered`.
2. **Fully reified Boolean donors** (`Iff`): `skipped_reified`, together with
   `If` and `NotIf`. From MiniZinc, every three-argument `bool_xor` and every
   `bool_eq_reif` / `int_eq_reif` / `int_ne_reif` arrives this way. The counter
   lumps them with all reified equalities over any domains: on
   `speck-optimisation` `hard_0` it counts 6,576, of which 1,536 are reified
   XORs over Booleans and 5,040 `int_eq_reif`.

   **An `Iff` or `If` whose condition is a constant literal is not read as
   unconditional.** The scan tests the condition's kind, not its value
   (`:148–157`). From MiniZinc, an explicit `constraint bool_xor(a, b);`, or
   `forall(i)(bool_xor(a[i], a[i+1]))`, flattens on both 2.9.7 and 2.10.1 to
   `bool_xor(a, b, true)`, and `fzn-glasgow` posts that as
   `EqualsIff{a, b, 1 ≠ 1}` (`fzn_glasgow.cc:867–869`): a plain `a ≠ b`.
   Through the local switch, three such rows over four Booleans gave
   `gathered nothing` with `skipped_reified` 3 (`p10-boolxor/bx.mzn`). `DifferenceLogic` does the same
   for `Iff`, though it lifts an `If` whatever its condition
   ([`difference_logic.md`](difference_logic.md)): two `LessThanEqualIff` or two
   `LinearLessThanEqualIff` donors under the constant condition `1 = 1` lift
   nothing and count `skipped_reified` 2, where the unconditional spellings lift
   2 edges (`p10-boolxor/dl.cc`). The scheduling presolvers' makespan-link scan
   asks for `reif::MustHold` (`makespan_links.cc:27`, `:83`); that was read, not
   run.
3. **Wide operands**: `skipped_wide_operands`. Right for equality over wide
   domains, which is not a parity. It also takes Booleans hidden behind a view
   whose bounds leave `[0, 1]` (`NotEquals{x, −y}`), and operands narrowed into
   `{0, 1}` only by root propagation or during search.
4. **Rows alone in their component**: `skipped_alone_in_component`. This
   includes a row whose atoms all cancel. The counter cannot tell that from a
   real singleton.
5. **Shapes never looked at, with no counter at all**, so that nothing says
   they were seen:
   - XOR posted as a `LinearEquality` (`r + not_r = 1` from XCSP3's nested
     `xor`; `x + y = 1` over Booleans), as `Table` or `SmartTable`, as `Or` /
     `And`, as `Count` or a linear sum modulo 2;
   - `ParitySystem` itself, which installs its own system;
   - any `ParityOdd` a constraint installs as a child rather than posting.
6. **Atoms are matched by syntax.** Two spellings of one literal, or a view and
   its variable, are separate columns. The rows are still gathered, but into a
   weaker system, or into separate components where one would do.
7. **A constant operand is one shared column, so it joins unrelated rows.** A
   literal over a `ConstantIntegerVariableID` is an atom like any other, and
   every row that mentions the same constant literal shares it. Measured
   (`p9-fixup/cj.cc`, four Booleans): `ParityOdd{a, b}` and `ParityOdd{c, d}`
   give `gathered nothing` (2 alone); `ParityOdd{a, b, 0}` and
   `ParityOdd{c, d, 0}` give `2 rows gathered over 5 atoms into 1 system`,
   with both donors retired; the same with `FalseLiteral` in place of the
   constant gives `gathered nothing`; `Equals{a, 1}` and `Equals{b, 1}` give one
   system of 2 rows over 3 atoms. Solutions are unchanged and every proof
   verifies. But a fixed column informs nothing, which is the header's own
   reason for splitting components ("rows sharing no atom cannot inform each
   other"), so the system costs a propagator and per-call elimination for no
   strength. The shapes that post it: MiniZinc `array_bool_xor` with constant
   entries (each `parity-learning` row has 6 to 17 variables among 23 entries,
   the rest `false`; those rows are one component anyway), and XCSP3's
   `Equals{r, 1}` for every top-level intension, which would join all of a
   model's top-level intensions over `{0, 1}` results into one component.
   Unfiled; see [Next steps](#next-steps).

`skipped_empty_row` and `skipped_uncitable_chain` are refusals, not misses.
An empty row is its donor's to refute. An uncitable chain would make the proof
invalid, and that bucket stays at 0 for anything posted before solving.

**The counters account for every enumerated donor.** Each `ParityOdd` and each
`ReifiedEquals` is in `rows_gathered`, `skipped_alone_in_component`, or exactly
one `skipped_*` bucket, as the header promises. A model built from an
unrecognised class gets `gathered nothing`, the same answer as a model with no
XOR structure.

**On real models, through the local switch.** The switch is five lines in a
scratch copy of `fzn_glasgow.cc` that add the presolver. It is on no branch.
At `86caad24`, with both MiniZinc 2.9.7 and 2.10.1, the counters were identical:

| Instance | FlatZinc input | Gathered | Atoms | Components | Boolean offered | Alone | Reified |
|---|---|---|---|---|---|---|---|
| `parity-learning` `44_22_5.2` | 44 `array_bool_xor`, 44 `bool_not`, 44 `bool2int`, 21 three-argument `bool_xor` | 111 | 134 | 1 | 88 | 21 | 21 |
| `parity-learning` `52_26_6.3` | the same shape | 136 | 163 | 1 | 104 | 20 | 20 |
| `speck-optimisation` `easy_1` | 32 `array_bool_xor`, 62 `bool_not`, 138 `bool2int`, 96 three-argument `bool_xor`, 300 `int_eq_reif` | 186 | 264 | 46 | 200 | 46 | 396 |
| `speck-optimisation` `hard_0` | 512 `array_bool_xor`, 1,016 `bool_not`, 2,088 `bool2int`, 1,536 three-argument `bool_xor`, 5,040 `int_eq_reif` | 3,048 | 4,128 | 568 | 3,104 | 568 | 6,576 |

`cryptanalysis` 2016 (`step1_aes.mzn`, `kb128_n5_obj11`), the other XOR family
`parity-system.md` names, failed to flatten under both versions, and was not
pursued.

**The MiniZinc differential** (`d1-mzn/gen_and_diff.py`): random Boolean models
built from `xorall`, `xor`, `= not`, `=`, `<-> (… xor …)`, `bool2int` sums and
clauses. `fzn-glasgow -a`, with and without the switch, was compared against
Gecode 6.3.0 `-a`, with the statuses `==========`, `=====UNSATISFIABLE=====`,
`=====ERROR=====` and `=====UNKNOWN=====` classified and completeness compared.
8 seeds of 150 models on each of 2.9.7 and 2.10.1 gave 2,400 runs and 2,400
agreements. 700 models per version gathered something, 2,052 rows in all.
None of these models reaches #1381, because `fzn-glasgow` posts the derived
classes.

## Evidence that it fired

The `ParitySystemGatheringStats` block is registered on every run, before
anything is decided (`:100`), and filled at the end. Its ten entries are
`rows_gathered`, `atoms`, `components_installed`, `donor_propagators_disabled`,
`skipped_empty_row`, `skipped_uncitable_chain`, `skipped_alone_in_component`,
`boolean_rows_offered`, `skipped_reified` and `skipped_wide_operands`.

| Report | Form |
|---|---|
| C++ API | the shared block's fields, or `Stats`' `operator<<`, which prints each block's summary |
| `fzn-glasgow -s` (local switch only) | `%%%mzn-stat: paritySystemGatheringRowsGathered=…`, one line per entry, rendered generically |

The summary line separates the cases:

- `parity_system_gathering: gathered nothing`: it ran and found nothing to
  install;
- `… N rows gathered over A atoms into C system(s), with B rows offered by a
  Boolean equality, retiring D donor propagators`: it ran and installed;
- **no `parity_system_gathering` line at all**: it did not run. It was never
  added; or root initialisation failed, so no presolver ran (`p5-evidence`:
  `Abs{v, v − 2}` gives no block); or an earlier presolver returned `false`,
  or the initialisers an earlier presolver installed failed, so no later one
  ran (`solve.cc:378–393`; the fact-check's probe, an `AutoTable` over an
  unsatisfiable scope added first, gives no block).

That three-way split holds for the printed `Stats` only. **A caller's own block
cannot tell the third case from the first.** `ParitySystemGatheringStats` has
no `ran` field, unlike `AutoTableStats`, and its summary says `gathered nothing`
whenever `rows_gathered` is 0 (`parity_system_gathering.cc:255–256`). A block
handed to a solve on which the presolver did not run keeps its old values,
which for a fresh block means `gathered nothing`. Re-run here
(`p11-noblock/noblock.cc`, the cross-document check's probe): with an
`AutoTable` over three pairwise-`≠` Booleans added first, the solve's `Stats`
print has no `parity_system_gathering` line, and the caller's block says
`gathered nothing`. In the other order the presolver gathers 5 rows. Whether
the solve's `Stats` lists the block is what tells the two apart.

The counter that tells "gathered" from "found nothing" is `rows_gathered`, with
`components_installed`. `boolean_rows_offered` is broken out because the
Boolean path can regress on its own while the `ParityOdd` path keeps the
presolver looking busy. The proof has no marker. Its only signs are the
`pgather…` flags in the root scaffolding and, above `Off`, `parity` assertions
naming no constraint. The presolver reports no `StatsNote`, so nothing is said
while it runs.

Expected values on named instances at `86caad24`. The in-tree fixtures' proofs
verify at `Off`; no proof of the `parity-learning` row was checked:

| Instance | Expected counters |
|---|---|
| `parity_system_gathering_presolver_test` `bool_bridge` | 3 rows over 4 atoms into 1 system, 1 Boolean offered, 3 donor propagators retired |
| the same file's `two_components` | 4 rows, 6 atoms, 2 components |
| `empty_row` | 2 rows, 3 atoms, 1 component, `skipped_empty_row` 1 |
| `bool_reified` | 0 rows, `skipped_alone_in_component` 1, `skipped_reified` 1 |
| `parity-learning` `44_22_5.2`, local switch | as in the table above: 111 rows, 134 atoms, 1 component, 88 Boolean offered, 111 retired |

## Can it weaken the model?

**Lose solutions: yes, through #1381, and otherwise no.** Nothing reaches the
OPB. A Boolean donor lifted with the polarity its condition gives states
exactly the donor's constraint over `{0, 1}`, and a `ParityOdd` row is its
donor's row. The installed machinery derives only GF(2) consequences of those
rows, and VeriPB checks each one. The solution sets were checked against an
independent oracle four ways:

- **The in-tree test's equivalence lanes**: 12 fixtures, three configurations,
  with and without proofs.
- **The harness**: 30 shapes, range and list declarations, three
  configurations. Brute-force-identical except the two shapes #1381 covers.
- **The fuzz**: 9,600 random models, three configurations, against brute force.
  No mismatch. 590 `Off` proofs, on the gathered models whose index is a
  multiple of four, all `s VERIFIED`. The generator does not build the
  off-diagonal `ReifiedEquals`.
- **The MiniZinc differential through the local switch**: 2,400 runs, no
  disagreement in sets, status or completeness.

#1381's shape loses and invents solutions: `ReifiedEquals{x, y,
reif::MustNotHold{}}` with `ParityOdd{x, z}` enumerates `(0,0,1)` and `(1,1,0)`
where the model has `(0,1,1)` and `(1,0,0)`. With the donors kept, it
enumerates nothing. With proofs on, VeriPB rejects the first slack row, so no
proof certifies the wrong answer.

**Lose propagation strength: no.** It only adds propagators, and it retires
only donors that a component's system subsumes. The tripwire checks that over
the four in-tree fixtures, the harness's 30 shapes and the fuzz's 9,600 models.
Rows it does not gather keep their donors. There is no proof-only budget, and
no decline that depends on proofs. `skipped_uncitable_chain`, the one
proofs-only skip, cannot fire on a constraint posted before solving.

**It is not search-neutral under the default heuristic.** Each installed system
raises the degree of every variable in its component by one
(`propagators.cc:772–775`), and `dom_then_deg` breaks ties by degree. Over the
fuzz, the recursion count with the presolver differed from without it on 159 of
9,600 models: 157 fewer, which is the system's strength, and 2 more, which is
the heuristic. One of the two (`p7-degree/deg2.cc`, five Booleans, an
`EqualsIf`, an `EqualsIff` and two `ParityOdd`s over views and `TrueLiteral`)
finds the same 4 solutions in 7 recursions without the presolver and in 15 with
it, and in 7 both ways under in-order branching (`deg3.cc`). All its variables
are Booleans, so `dom` ties and degree decides. The other (fuzz seed 6, model
40) is also 9 both ways in order, per the fact-check; it has a `{0, 2, 5}`
variable, so domain size may contribute there. The tripwire is unaffected, since
both of its arms carry the system. On `parity-learning`, the node count was the
same with and without (1,523,353), with the same failures, peak depth and
printed optimum: that model's search annotation (`bool_search` over
`parity_bits`, input order) fixes the branching, so degree plays no part.

**The wrong line, soundly derived.** There is no `ia` pin. The telescoping
`pol`s that produce each chain donor's slack rows emit whatever their sum is,
and nothing states the row they are meant to produce. What ties them to the
intended rows is:

- **The chain lookup.** `find_parity_chain` builds every name through the
  donor's published `ParityChainNaming`, all or nothing, and asks for exactly
  as many steps as the donor has literals.
- **The closing step.** Every inference that uses a slack row ends in a RUP of
  the inferred literal or the contradiction. A wrong row fails there, at the
  first use, not at the root. If a component's row is never used, nothing ever
  checks it.
- **A Boolean donor's rows are stated.** `rup l₁ + l₂ ≥ 1` checks the row it
  states, so a mis-polarised donor is rejected at the root (#1381). That is
  the one place where VeriPB catches the presolver's mistake, rather than a
  later one's.

`parity-system.md`'s two surviving mutations are the evidence that the chain
derivation has slack. One telescopes with `a_0 ≥ 1` and the other drops the
`a_n ≤ 0` pin, and both still verify, because the rows they produce are weaker
than intended by a term the OPB pins. An `ia` restating each slack row after
its telescoping `pol` would be a pin, and should reject both at the root.
That was not tried here. A lift that is too *weak*, gathering nothing, is
invisible to every proof. Only the counts, the equivalence lanes and the
strength differentials catch it.

## Evidence

### Tests

- **`parity_system_gathering_presolver`** (`parity_system_gathering_test.cc`),
  run with `run_test_only.bash`:
  - **Equivalence**: 12 fixtures, each in three configurations (no presolver,
    donors kept, donors retired), with proofs off and on. Solution sets are
    compared against an independent oracle. Every stats field is checked
    exactly, except `donor_propagators_disabled`, which is checked for being
    non-zero when retiring and zero when kept. VeriPB runs whenever it is on the
    `PATH`: 36 proofs verified at `--seed=1`, `86caad24`. The enumeration uses
    plain `solve_for_tests`, so the gathered system's per-node strength is not
    checked.
  - **Tripwire**: four fixtures, kept against retired, solution and recursion
    counts under the default heuristic, proofs off.
  - **Strength**: `camouflage` and `bool_bridge_unsat`, no presolver against
    retired, recursions strictly fewer, proofs off.
- **`constraint_enumeration_test`**: both typed enumerations, and the two
  derived-class shapes of `ReifiedEquals` (`:295–311`).
- **No front-end lane**, since no front end reaches it.

**Runtime caps.** No lane sets or clears one. With the default caps passed in
the environment (`GCS_TEST_MAX_SOLUTIONS=300`, `GCS_TEST_MAX_RECURSIONS=1500`),
the binary printed no truncation: the largest fixture has 7 solutions. So the
capped run checks completeness here. The tripwire and strength cases call
`solve_with` directly, outside the caps. The results above came from running
the binary directly with no caps set, at `--seed=1`.

**Seeding.** The equivalence lanes branch randomly from the announced seed and
are reproducible with `--seed=N`. The tripwire and strength lanes use the
default heuristic.

**The assertion levels.** The test passes with `GCS_ASSERTION_LEVEL` at `Off`,
`Definitions`, `Inferences` and `Backtracking`. At `Links` it aborts on
`wide_domains` in its no-presolver arm (#1210), before reaching the later
fixtures.

**What the tests do not cover:**

- **A Boolean donor whose `_neq` disagrees with its condition**, and any
  `.scp` read back (#1381). That is the one wrong answer this audit found.
- **Any per-node consistency check.** The equivalence runs use plain
  enumeration.
- **Views, constants and root-narrowed operands** as Boolean donors; a
  `ParityOdd` donor with `TrueLiteral`, a view or a fixed variable.
- **The cake chain** on a presolved proof (no lane can run the presolver),
  which fails for equality-type literals over `{0, 1}` in `ParityOdd` donors
  (#1193).
- **Scale.** Every fixture has at most six variables; the quadratic pass
  (#1380) is invisible to it.
- **Running it twice, or with another presolver.**
- **A mutation lane.** There are no mutation hooks.
- **`skipped_uncitable_chain` non-zero.** It is asserted 0 everywhere and
  cannot be provoked. The comment at `:236–238` says it is "Only ever non-zero
  with proofs off", which inverts the header (`.hh:80–86`): it can only be
  non-zero with proofs on.

### Benchmarks and examples

- **In-repo**: no example adds the presolver.
- **Corpus**: `parity-learning` 2012 and `speck-optimisation` 2023 are the
  MiniZinc Challenge models with `array_bool_xor` (`parity.md`, Benchmarks).
  Both are reachable only through a local switch.
- **For the pass's own cost**: the synthetic `pairs` probe above, which isolates
  it. No corpus model is large enough to show it, although `speck-optimisation`
  `hard_0`'s 568 components are the shape.
- **For the installed machinery**: `parity-learning` `44_22_5.2` to its proved
  optimum, about 4 minutes with the presolver. For proofs, cap it, as
  `parity.md` does.

### CPU performance

At `86caad24`, Release, fataepyc-09, core 100, boost off, the `GLIBC_TUNABLES`
above, 2026-10-20, one run each, through the local switch (the same presolver
code as `main`):

**`parity-learning` 2012 (`44_22_5.2`), to the proved optimum, MiniZinc 2.9.7:**

| | nodes | propagations | wall | `instructions:u` |
|---|---|---|---|---|
| `ParityOdd` per row | 1,523,353 | 75,347,953 | 53.3 s | 284 G |
| gathered: 111 rows, 1 system, 111 donors retired | 1,523,353 | 9,749,762 | 224.0 s | 1,678 G |

The same node count either way, and the same optimal solution printed. The
factor is 4.2 in wall time and 5.9 in instructions. Why gathering prunes nothing
on this model is `parity.md`'s analysis (CPU performance). Where the time goes
was not profiled there or here; parity.md names the from-scratch elimination and
the row copies as the obvious candidates. It measured 57.2 s against 227.9 s at
`f28fdef8` on an instrumented build. Those figures are from another commit and
build, and should not be mixed with these.

What this does **not** exercise: the pass's own cost (milliseconds here), any
component split (one component), and #1381 (`fzn-glasgow` posts derived
classes).

### Proof performance

The presolver's own contribution is the root scaffolding: `10n + 2` lines per
chain donor of `n` literals, `2n + 2` of them at `Top`, and 2 lines per Boolean
donor, measured exactly ([Proof-time state](#proof-time-state)). A `ParityOdd`
donor's `n` counts every literal it was posted with, constants included: each of
`parity-learning`'s `array_bool_xor` rows has 23, of which 6 to 17 are
variables. The scaffolding was not measured on a corpus model, and neither was a
capped proof of a whole solve: an uncapped `--prove` run of `44_22_5.2` with the
presolver wrote 10 GB in two minutes, and was stopped. Everything per inference
is `parity.md`'s. The share of the proof's assertions that carry
`parity:((constraint_id unnamed))` was not measured at scale.

## Status, gaps, and next steps

### Proof-logging gaps

- **#1381**: a mis-polarised Boolean donor's slack row is rejected, at every
  assertion level. The proof never certifies the wrong answer, but the solve
  produces one.
- **#1193's cause**: against cake's OPB, a `ParityOdd` donor with an
  equality-type literal over a `{0, 1}` variable has an underivable slack row.
  Against the solver's own OPB, every `Off` proof outside #1381's shape
  verifies.
- **Above `Off`**, recorded and not filed, all the #1210 / #1330 family:
  - the Boolean slack `rup` over a root-narrowed, range-declared operand is
    rejected at `Links`, `Inferences` and `Backtracking`;
  - with value-list declarations, the same shape's `NotEquals` is rejected at
    `Backtracking` (`pbp:47`);
  - a range-declared variable wider than `{0, 1}` (`wide_neq0`) is rejected at
    `Links`, at a solution line, with or without the presolver (#1210).
- Strength does not change with proofs: there is no budget, and the one
  proofs-only skip cannot fire.

### Known limitations

- **No front end can turn it on** (#983), and `glasgow_scp_solver` cannot
  either: #1374 asked for a `DifferenceLogic` switch there, and a comment
  now asks for every presolver (#983 is the general design question).
- **Wrong solutions through `read_scp`**, or a directly constructed
  `ReifiedEquals` whose `neq` disagrees with its condition (#1381).
- **Three-argument `bool_xor`, and every reified Boolean equality, is
  skipped**, though an `Iff` over `{0, 1}` is a 3-XOR (#983).
- **Quadratic in the XOR structure's size** (#1380, #1309), and the pass
  cannot be stopped: `Presolver::run` takes no abort flag (`presolver.hh:32`;
  `solve.cc:378` passes none), so an abort flag, and so any `--timeout`, does
  not reach it (#816).
  6.69 s at 32,000 two-row components is spent before any limit is checked.
- **Not chain-portable for equality-type literals over `{0, 1}` variables**
  (#1193).
- **A shared constant joins unrelated rows** into one system, which costs and
  buys nothing (Detection, item 7).
- **Atoms are syntactic**: two spellings of one literal, or a view and its
  variable, weaken the system.
- **Boolean-only components are gathered too**, and pay the system's
  per-call cost for what odd-cycle detection buys.
- **On the one corpus model where parity dominates, gathering prunes nothing
  and costs four times as much** (`parity.md`).
- **It changes the search under `dom_then_deg`**, through degree, even where
  it prunes nothing.

### Next steps

Ranked by what they buy for what they cost.

1. **Fix the polarity (#1381).** Take a Boolean row's parity from the
   condition, `MustHold` or `MustNotHold`, not from `_neq`. Correct
   `equals/equals.hh`'s claim that only one spelling is constructible, and add a
   fixture for each off-diagonal shape and one through `read_scp`. A few lines,
   and it closes the only wrong answer found.
2. **Make the pass linear (#1380).** Sparse canonicalisation for the
   grouping, and one pass for the atom counts. The scratch patch passes the
   test, and on 32,000 components cuts setup to the first node from 6.7 s and
   1.4 GB to 1.4 s and 175 MB; of the remaining 1.4 s, about 72% is
   `install_returning_id` (#1309) and under 2% is the pass.
3. **Make the slack derivation chain-portable (#1193)**: either
   #1193's "make the encodings agree", or restate each step clause by RUP in
   the tracker's spelling before the subproof cites it (verified by hand for
   one step). Add a by-hand chain case; a lane needs a `.scp` presolver switch
   (#1374).
4. **Read a constant-condition `Iff` or `If` as what it is** (Detection,
   item 2): evaluate a reification condition over a constant before choosing
   the bucket, so that `EqualsIff{a, b, 1 ≠ 1}`, an explicit MiniZinc
   `bool_xor(a, b)`, is lifted as `a ≠ b`. `DifferenceLogic` has the same
   gap for `Iff`. Unfiled.
5. **Ignore constant atoms when splitting components** (Detection, item 7):
   union only over non-constant atoms, so that a shared constant does not
   join unrelated rows into one system. No strength is lost, since a fixed
   column informs nothing. Unfiled.
6. **Pin each chain slack row with an `ia`** after its telescoping `pol`, so
   that a wrong chain fails at the root rather than at its first use. Two
   lines per row. It should reject the two mutations `parity-system.md`
   records as surviving. Not tried.
7. **#983's decision**, with this audit's measurements: keep any front-end flag
   opt-in. Gathering `Iff` Boolean donors as 3-XORs (#983's comment) and
   asking a component to contain a `ParityOdd` are both design calls for that
   issue, not defects.
8. **Fix the test comment** at `parity_system_gathering_test.cc:236–238`,
   which inverts when `skipped_uncitable_chain` can be non-zero.

## Prior art

**Gaussian elimination over GF(2) during search** is SAT's. Soos, Nohl and
Castelluccia added native XOR clauses and Gaussian elimination to MiniSat in
CryptoMiniSat (*Extending SAT Solvers to Cryptographic Problems*, SAT 2009, LNCS
5584). Soos (*Enhanced Gaussian Elimination in DPLL-based SAT Solvers*, POS-10)
splits the XOR matrix into independent matrices, the idea behind this
presolver's component split. Han and Jiang integrate Gauss-Jordan elimination
with CDCL in the style of the simplex method (*When Boolean Satisfiability Meets
Gaussian Elimination in a Simplex Way*, CAV 2012). Soos and Meel's BIRD (AAAI
2019) and Soos, Gocht and Meel (*Tinted, Detached, and Lazy CNF-XOR Solving*,
CAV 2020) are the current CNF-XOR line. Those solvers recover XORs from CNF
clauses. Here the XORs are posted constraints, so detection is a class scan.
Treating a binary XOR as an equivalence is routine in that SAT machinery, so
reading `Equals` / `NotEquals` as 2-XORs is not new in technique; what is this
solver's is only that it reads them from CP constraint classes.

**In CP**, Rouquette and Solnon's `abstractXOR` (CP 2020) is a global
constraint over the XOR systems of differential cryptanalysis models.
`parity-system.md` and #647 survey the rest. No CP solver this audit knows of
gathers posted XORs into a system automatically.

**Certification.** Gocht and Nordström (*Certifying Parity Reasoning Efficiently
Using Pseudo-Boolean Proofs*, AAAI 2021; extended version arXiv:2209.12185) give
the slack form and the one-`pol` fold the installed machinery uses. Earlier,
Philipp and Rebola-Pardo (*DRAT Proofs for XOR Reasoning*, JELIA 2016) produced
DRAT for XOR reasoning, and Bryant and Soos (*Combining CDCL, Gauss-Jordan
Elimination, and Proof Generation*, POS 2022; arXiv:2304.04292, 2023, by Soos
and Bryant, as *Proof Generation for CDCL Solvers Using Gauss-Jordan
Elimination*) produce clausal
proofs for CryptoMiniSat's elimination through BDDs. McIlree's thesis cites
Gocht and Nordström as background and does not treat parity. What is this
solver's, and `parity.md`'s, is deriving the slack form from the accumulator
chain `cake_pb_cp` defines, in a linear number of steps. What is this
presolver's is doing that for constraints it did not post, by citing their
published row names, and the case commented on #1193 shows that this is not
yet portable to cake's encoding.

## Further reading

- [`parity.md`](../constraints/parity.md): the installed machinery, `ParityOdd`
  and `ParitySystem`. Its rule 5 gives the `search` reconstruction procedure for
  a gathered system's assertions, which depends on this document's
  eligibility rules.
- [`parity-system.md`](../parity-system.md): the long design note. Its "The
  presolver" half covers the two donor families, components, why donors are
  retired by default, the tripwire and strength tables, and the API the
  presolver needed. §2 derives the slack rows from the chain, and "What
  mutation testing says" has the seven mutations.
- [`difference_logic.md`](difference_logic.md): the other presolver that
  retires donors, and the template this one was built to.
- [`equals.md`](../constraints/equals.md): the Boolean donors' encoding and
  propagators.
