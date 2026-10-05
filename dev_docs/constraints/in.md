# `In`: a variable takes one of the listed values, or the value of one of the listed variables

> **Maturity** production ·
> **Audited** 2026-09-30 at `c9ceea25` ·
> **Open issues** none filed by this audit yet; see [Next steps](#next-steps)
> for what it would file. Already open and touching this family: #833 (the
> large-domain policy), #868 (cross-solver comparisons; this document gives a
> whole-solve comparison by hand, not the identical-tree one #868 asks for).
> Tracked under #871.

`In(var, vars, vals)` says that `var` equals one of the constants in `vals` or
one of the variables in `vars`. One class and one propagator. The encoding is
`cake_pb_cp`'s: an at-least-one row over an equality literal per constant and a
reified "equal to `var`" flag per variable. The propagator has two branches.
With no variable candidates it removes whatever the constant set does not
allow. With them, it removes `var`'s unsupported values and, when exactly one
candidate is left that could equal `var`, prunes that candidate to `var`'s
domain. Both branches take their differences as intervals, never value by
value (#874).

Four things to know before touching it.

- **It is generalised arc consistent, on distinct variables.** Root brute
  force over 18,000 random instances with holes, views and constants finds no
  missing pruning, and the unit test checks GAC at every node. Gecode's
  `member` never prunes a candidate once posted, so it is weaker. On an
  enumeration where that makes no difference (the same solutions and no
  failures in either solver, under different branching schemes), GCS takes
  3.3 to 3.7 times Gecode's time.
- **Every listed domain is an `In`.** `Problem::create_integer_variable` over a
  vector of values posts one to carve out the holes, whether or not the list
  has any. That covers the C++ API and XCSP3's listed domains; Python's
  `post_in` posts the same constants-only `In` directly. This has three
  consequences:
  - Carving `K` holes costs Θ(K²) at the root, in the state layer's linear
    interval scans: 12.1 s for 10⁵ values.
  - After its first call the posted `In` can never infer anything again, but
    it stays live at `O(K)` per wake. On an enumeration of the variable that is
    half the solve time.
  - Its `on_change` trigger declares the variable's holes as observed, which
    keeps every other constraint's optional interior pruning on that variable
    switched on.

  Tested fixes for all three are in [Next steps](#next-steps).
- **A candidate that aliases `var`, or another candidate, weakens it.** The
  results stay sound, and every proof checked verifies. But:
  - `In{x, {y, y}}` never prunes `y`.
  - `In{x, {x + 1}}` is unsatisfiable but takes W/2 calls to fail.
  - `In{x, {−x}}` is not even `bounds(Z)`.
- **Variable candidates arrive from MiniZinc's `member`, the `.scp` reader and
  `gcspy`'s `post_in_vars`.** XCSP3's index-free `element`, which is exactly
  this constraint, is rejected as unsupported. MiniZinc's `set_in` and its holey
  domains are decomposed into other constraints, and so is XCSP3's intension
  `in`.

## What it is

### Semantics

`In(var, vars, vals)` holds exactly when `var = c` for some `c ∈ vals`, or
`var = V` for some `V ∈ vars`. The two lists are a union. The other two
constructors, `In(var, vars)` and `In(var, vals)`, leave one list empty.

- **Both lists empty:** unsatisfiable. `prepare()` notes it
  (`in.cc:100–106`), the OPB row degenerates to `0 ≥ 1`, and the propagator is
  replaced by an initial contradiction (`in.cc:145–149`).
- **Constants among `vars`:** a `ConstantIntegerVariableID` among the variable
  candidates is moved into `vals` in `prepare()` (`in.cc:90–95`). A variable
  whose domain happens to be a single value is not folded, because the
  `.scp` still names it and `cake_pb_cp` gives it a flag triple (see [Cake
  conformity](#cake-conformity)).
- **Duplicate constants** are removed (`in.cc:97–98`). Duplicate *variables*
  are kept, and so are candidates that are views of `var`. See
  [Robustness](#robustness-and-limits).
- **`var` a constant** is accepted. `In{2, {x0, x1, x2}}` over `1..4`
  enumerates its 37 solutions with a verifying proof
  (`tmp/fd-small/in/probes/inconstvar.cc`).
- **`var` among its own candidates** (`In{x, {x}}`) is always true. The
  propagator runs and finds nothing. The test covers it.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `In`, constants only | `set_in`: `decompose`[^setin]; the empty set: ✓ | a listed domain: ✓[^xdom]; intension `in`: `decompose`[^xin] | ?[^gcspy] | ✓ `in` | also every `create_integer_variable(vector)` |
| `In`, with variable candidates | ✓ `glasgow_member_int`, `glasgow_member_bool`[^member] | `frontend gap`[^xelem] | ?[^gcspy] | ✓ `in` | |
| a reified form | `decompose`: the standard library's `int_eq_reif` and `bool_clause_reif`[^reif] | n/a | — | — | no class exists |

[^setin]: `fzn_glasgow.cc:771–788`. A non-empty `set_in` posts two linear
    bounds and one `Or{var < l, var ≥ u}` per gap; the empty set posts
    `In{var, {}}`, which the hand-written JSON test `minizinc-emptysetin`
    exercises. A holey *domain* in FlatZinc is decomposed the same way, one
    `Or` per gap (`fzn_glasgow.cc:474–488`). Flattening `var 1..9: y;
    constraint y in {1, 3, 5};` gives no constraint at all on 2.9.7 or 2.10.1:
    the domain becomes `[[1,1],[3,3],[5,5]]`, and so a gap `Or` each.

[^xdom]: `buildVariableInteger(id, vals)` (`xcsp_glasgow_constraint_solver.cc:161`)
    keeps the value list, and the variable is created over it
    (`:1076`), which posts `In`. `xcsp/tests/sum_not_equals.xml` has one, `0 3`.

[^xin]: `in(x, {…})` and `notin` in an intension go to a unary `Table` and
    `NegativeTable` (`xcsp_glasgow_constraint_solver.cc:1805–1820`), not here.

[^member]: `fzn_member_int.mzn` and `fzn_member_bool.mzn` call the builtins,
    and `fzn_glasgow.cc:1156–1159` posts `In{var, vars}`. A `par` array
    arrives as a `glasgow_member_int` over an array of constants
    (`member([1, 3, 5, 3], y)` flattens that way on both versions), which
    `prepare()` folds into `vals`. Flattened on 2.9.7 and 2.10.1, and solved
    with `-a` against Gecode on both: `member` over a `var` array (148
    solutions), over a `par` array (3), over bools (14), over a mixed array of
    variables and constants (496), and reified (320) all agree
    (`tmp/fd-small/in/mzn/`).

[^reif]: `b <-> member(x, y)` flattens to three `int_eq_reif` and a
    `bool_clause_reif`, and `b -> member(x, y)` adds a `bool_clause`, on both
    versions.

[^xelem]: XCSP3's `<element>` with a `<list>` and a `<value>` but no `<index>`
    means "the value is in the list". The frontend overrides neither of the
    parser's callbacks for it, `buildConstraintElement(id, list, int)` and
    `buildConstraintElement(id, list, XVariable *)`. So the parser's defaults
    throw, and the solver prints `s UNSUPPORTED` with `Element value constraint
    is not yet supported` or `Element variable constraint is not yet supported`
    (`tmp/fd-small/in/xcsp/`). Both map directly onto `In`. See [Next
    steps](#next-steps).

[^gcspy]: `gcspy` binds `post_in` (constants) and `post_in_vars` (variables)
    (`python/gcspy.cc:526–545`), which post `In` directly. It binds only the
    bounds form of `create_integer_variable`, so Python has no listed domains.
    Whether CPMpy's GCS interface calls them was not checked.

Positions carry no meaning here, and no value is an index, so an array
indexed from something other than 1 cannot be mistranslated the way #987's
were.

### Options

`None.` There is no consistency tag and no algorithm switch.

### Variable kinds and views

`var` and every candidate may be a plain variable, a constant or a view of
either sign. The propagator is the same for all of them. It reads domains
through `State`, which resolves views.

**The proof handles views too.** A view gets its own bit-sum proof variable
with channel rows ([`view-proof-logging.md`](../view-proof-logging.md)). The
flag rows and the range literals are stated over that variable, which is what
#904 made possible and #874 relied on. So a range conclusion or reason literal
about a view names a literal that exists, and the bound lemmas cross the flag's
equality on whichever encoding each operand resolves to (the comment at
`in.cc:165–174`). The evidence:
- `in_test`'s `view_mixed` lane wraps every position, `var` and the three
  candidates.
- 300 random instances with `±1` views on distinct variables all verify (see
  [Tests](#tests)).
- So do 300 with views over repeated variables.

### Reification

`None.` MiniZinc's reified `member` is the standard library's decomposition
(the frontend table). No front end needs a class.

### Relation to other families

- **Decomposes into it:**
  - every `Problem::create_integer_variable(vector)` (`problem.cc:125`), so
    every listed domain from the C++ API and XCSP3;
  - MiniZinc's `member`, and `gcspy`'s `post_in` and `post_in_vars`.
- **Child constraints:** none. (`GlobalCardinality` used to post child `In`s
  for its closed form; 76c8eeab replaced them with rows of its own.)
- **Shares code:**
  - `justify_not_in_range_across_equality` (`innards/justify_not_in_range`)
    with `all_equal`, `equals` and `min_max` (`element` has its own). `In` is
    the one caller that passes the `under` guard on both lemmas; see
    [`large-domains.md`](../large-domains.md) around line 202.
  - The `IntervalSet` primitives (`each_interval_minus`, `erase_range`) and
    `State::domains_intersect`, which everyone uses.
- **Presolvers:** none reads or writes it.
- **The same unary membership is stated three ways**, one per front end:
  - `In` for a listed C++ or XCSP3 domain, and Python's `post_in`;
  - a unary `Table` for XCSP3's intension `in`;
  - two linear bounds and an `Or` per gap for MiniZinc's `set_in` and holey
    FlatZinc domains.

  They have three different encodings and three different propagators. This
  document covers only the first. Whether they should converge is not settled
  here: `In` over constants and the unary `Table` both reach GAC; the `Or`
  decomposition does too, one gap at a time.

## The proof model

### OPB encoding

For `var`, the constants `c ∈ vals` (after folding and de-duplication) and
the variable candidates `V_0 … V_{k−1}`:

```
for i in 0 .. k-1:
    x[id][i][ge]  ⇔  V_i − var ≥ 0          (fully reified)
    x[id][i][le]  ⇔  V_i − var ≤ 0          (fully reified)
    x[id][i][eq]  ⇔  ge + le ≥ 2            (fully reified)
@c[id][al1]:   Σ_{c ∈ vals} [var = c]  +  Σ_i x[id][i][eq]  ≥ 1
```

`define_proof_model()` at `in.cc:111–141`. A constant whose `[var = c]` is
literally false is dropped from the sum, and one that is literally true is
folded into the degree. Both happen only when `var` is itself a constant. A
constant outside `var`'s bounds is kept, as `cake_pb_cp` keeps it.

**It is definitional.** The flags are extension variables and the one row says
what the constraint means. The constraint writes `6k + 1` rows of its own: six
reification rows per flag triple and the sum (`in_two_vars_sat` has 13). The
sum has `|vals| + k` terms. Each constant also needs the literal layer's shared
rows defining `[var = c]`, up to six, whatever the width. Nothing is
proportional to a domain's width.

### Labels

`@c[id][al1]` names the at-least-one row, and `x[id][i][ge|le|eq]` with
`[r]`/`[f]` name the reification rows, all as `cake_pb_cp` names them. No rule
cites a row by label, since every step is a RUP. The flag *names* are what
matters to a reconstructor: the scaffolding lines name `x[id][i][eq]` for
candidate `i`. `i` counts only the non-constant candidates, in the order
posted.

### Cake conformity

`cake_pb_cp`'s `in` is an equality-literal grid, then its count helper
(`cencode_count_aux`, which is also what `Count` was conformed to in #354),
then the `al1` row. (The comment at `in.cc:120–121` calls it literally the
count helper, which overstates it: the count helper is only the middle part.)
Our flags were conformed to it in c347b153. The seven chain cases:
- `in_const_sat`, `in_two_vars_sat`, `in_two_vars_unsat`, `in_mixed_sat` and
  `in_fixed_var_sat` are `strict`.
- `in_var_sat` and `in_unsat` are `none`, for the #358 boundary-literal
  residue: every `in` row matches, but a materialised boundary order literal
  carries coefficient 1 where cake's carries 0.

All seven pass the full workflow-2 chain at `c9ceea25`
(`tmp/fd-small/in/chain/`). In `in_var_sat`, `(0 W)`, cake indexes `W` as
`x[_1][0]`. It counts only variables, which is what our fold relies on.

Checked beyond the suite, on 120 random models (`tmp/fd-small/in/chain/rnd/`,
30 each of distinct and repeated variables, with and without views):
- **Every model without a view** verifies through the whole chain: all 60
  from the plain modes, and 16 from the view modes where the generator
  happened to draw no view.
- **opbdiff `strict` differs in two benign ways.**
  - The #358 boundary literals: 42 differing rows, all `i[…][ge…]`.
  - **Duplicate constants.** `prepare()` removes a duplicate, and `cake_pb_cp`
    keeps it, so a constant listed twice (or listed and also a constant
    candidate) appears once in our `al1` and twice in cake's. That is 9
    differing rows, every one of them an `al1`. It is semantically equivalent
    for a `≥ 1` row.
- **A constant `var`**, as in `(in (x[0] x[1] x[2]) 2)`, chain-verifies too.
  But the flags' reification rows differ from cake's in their big-M: 8 on
  `x[_1][i][ge][f]` where cake has 6, and 7 on `x[_1][i][le][r]` where cake has
  5 (`tmp/fd-small/in/chain/cvx.*`); which halves differ depends on the
  constant. With constants in the list there is a second divergence, found by
  the fact-check: cake writes trivial rows for the constant's own literals
  (`@n[2][ge9][f]` and the like), where we drop literally false constants and
  fold literally true ones into the degree. All of these
  are equivalent row for row (the fact-check checked them exhaustively over
  0/1 assignments), and the chains verify. No suite case posts a constant
  `var`.
- **A view anywhere in the model can't go through the chain at all.** The
  `.scp` writer spells a view as a list, `(_1 + -1)`, and the reader's
  `resolve_variable` (`scp_reader.cc:141`) accepts only atoms. The solver
  therefore rejects its own `.scp` at step 1, with `S-expression error:
  expected an atom, found a list`. That hit 44 of the 60 view models. This is
  the reader's limitation, not `In`'s.

### Proof-time state

- **At the root:** nothing of this family's beyond the OPB. The flags are in
  the model, not introduced in the proof. (With a view candidate, the view
  layer's own preamble cites the flag rows by label.) They are fully reified
  over bit sums, so a complete assignment of the bits determines each of them
  by unit propagation, as `solx` needs.
- **Lazily:** each rule's bound lemmas and scaffolding lines are written at
  `ProofLevel::Temporary` and deleted straight after the conclusion. A step-1
  range removal over two candidates ends with `del range -7 -1`. Nothing a
  later step needs is deleted.
- **What a reconstructor needs to find:** the flags, by the names above, and
  the range and order literals, which the shared literal layer introduces the
  first time a reason or lemma names them.
- **Proof-only vectors:** `_selectors` holds the `eq` flags and is filled only
  in `define_proof_model()`. With proofs off it stays empty. The justification
  lambdas that index it run only with a logger, so nothing dangles.

## The implementation

### Initialisation and global data

`prepare()` folds constant candidates into `vals`, sorts and de-duplicates
`vals`, and flags the empty case. `install_propagators()` builds `vals` once as
an `IntervalSet` (`in.cc:161–163`). There is no initialiser.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| the `In` propagator, constants only | `on_change` on `var` | derived: `var`, **an overstatement**; see below | 1 | always, when there are constants and no variable candidates | not claimed; one call is a fixpoint | only when `var` is fixed |
| the `In` propagator, with variable candidates | `on_change` on `var` and every candidate | derived: all of them | 2, 3, 4, 5 | always, when there is a variable candidate | not claimed; one call is a fixpoint on distinct variables, and not with aliasing | only when `var` is fixed to a permitted constant |
| the initial contradiction | — | nothing | 6 | both lists empty | — | — |

**The constants-only branch declares a sensitivity it does not have.** What it
infers is `dom(var)` minus the permitted set. A hole can only shrink that, so
from any domains no hole ever gives it a new inference. After its first call it
cannot infer anything at all. Its `on_change` trigger nevertheless derives
"holes in `var` affect me". Every variable created from a vector, holey or not
(Dubois' `0 1` lists are contiguous), therefore reports itself as observed, and
`consistency::Auto` elsewhere cannot switch off an interior pruning on it.
Measured (`tmp/fd-small/in/probes/inholes.cc`, an `ElementConstantArray` under
`Auto` whose result feeds only a linear inequality):
- declared as an interval, `switched 1 of 1 optional interior prunings off`;
- declared over a vector of values, `kept, because holes in what it prunes
  affect _1 (_2)`, where `_1` is the `In`.

Declaring an empty `Triggers::holes_affect_propagation` for this branch gives
`switched 1 of 1` on the vector form too. [Next steps](#next-steps) has it.

**Idempotence.** Neither branch claims it. With variable candidates, on
distinct variables, one call is a fixpoint:
- step 1 leaves every value of `var` supported;
- step 3 then trims the single supporting candidate to `dom(var)`, which
  leaves `var` untouched.

Measured: 10,000 random root instances over interval domains, never a second
effectful call (`probes/inidem.cc`, seeds 1 and 2). With aliasing it is not
one: `In{x, {x + 1}}` takes W/2 calls ([Robustness](#robustness-and-limits)).
A claim would be safe anyway, since the propagator machinery ignores claims
when positions alias.

**Self-disabling.** `DisableUntilBacktrack` when `var` is fixed to a value in
`vals` (`in.cc:431–433`). The constants-only branch could disable after its
first call whatever `var` is, since by then every value left is permitted and
none can come back. It does not, and that costs `O(|vals| + intervals)` per
wake for nothing; see [Interval efficiency](#interval-efficiency).

### Mutable state and incrementality

`None.` Nothing persists between calls but the permitted `IntervalSet`, built
once. Every call copies `var`'s domain, and in the variable branch each
candidate's too.

### Interior values and optional pruning

**Offers.** `None.` Rules 1 to 5 remove interior values, but the family
installs no optional pair.

**Observes.** Holes in `var` and in every candidate affect the variable
branch: support is a question about values, and `domains_intersect` is too.
The derived declaration is right there. The constants-only branch declares
holes in `var` that affect nothing, as above. This is the one place where
this family's answer is wrong in the direction that costs other families
something. It is never unsound, and it is common: every listed domain is
involved.

### Robustness and limits

**Unbounded domains.** Fine on distinct variables, at any width; see
[Interval efficiency](#interval-efficiency). A variable over the widest
supported range, `−2⁶¹ .. 2⁶¹ − 1`, against constants at both ends and 0
solves with and without proofs (`probes/inovf.cc wide`). So does a candidate
`y + 2⁶¹` against `x ∈ 0..10`, whose proof verifies as unsatisfiable
(`viewfar`).

**Negative values and zero.** Tested: `in_test` has `[−3, 3]` against
`{−2, 0, 2}`, and candidates over `[−2, 2]`. Its random sweep reaches `−3`.

**Degenerate shapes.**
- *Empty lists, a singleton `var`, and `var` among its own candidates* are
  covered by the test, per #254. A constant `var` is not: the test's
  `create_integer_variable_or_constant` always returns a variable
  (`constraints_test_utils.hh:1210–1214`).
- ***A repeated candidate blocks the single-support rule.*** Step 3 fires only
  when exactly one candidate intersects `dom(var)`, and the scan
  (`in.cc:306–316`) counts positions, not variables. `In{x, {y, y}}` with
  `x ∈ 1..2` and `y ∈ 1..10⁶` leaves `y` at all 10⁶ values, where only 1 and 2
  have support: not `bounds(Z)` (`probes/inwide.cc dupsrc`). Gecode's `member`
  removes duplicates at post (`x.unique()`).
- ***A candidate that is a view of `var`*** is taken at face value: its domain
  counts as support.
  - `In{x, {x + 1}}` is unsatisfiable. Each call removes one value at each end
    of `x`, and the propagator is woken again by its own change. That is W/2
    calls on a domain of width W: 50,001 propagations at 10⁵, and 500,001
    (0.36 s, one run) at 10⁶ (`inwide selfplus`). The same shape as
    `increasing`'s #1144.
  - `In{x, {−x}}` over `±10⁶` has one solution, `x = 0`, and the root leaves
    all 2,000,001 values (`inwide selfneg`). Not `bounds(Z)`.
  - A guard build of `c9ceea25` (`tmp/fd-table/build-guard`) runs
    `In{x, {x + 1}}` at W = 2·10⁵ to its 100,001 propagations without
    tripping. No single call walks anything.
  - The results are sound, and every proof checked verifies (see
    [Tests](#tests)).
- *Brute force over aliasing.* The root probe (`probes/incheck.cc`, 3,000
  instances per mode and seed, seeds 1 to 3) draws the terms from a pool
  smaller than the number of positions.
  - Plain repeats: GAC fails on 34, 45 and 41 instances, and `bounds(Z)` on
    17, 25 and 22. Every printed failure has a repeated candidate.
  - With `±1` views and offsets: GAC fails on 732, 716 and 724 instances, and
    `bounds(Z)` on 586, 567 and 579. 72, 70 and 68 unsatisfiable instances are
    not failed at the root.
  - No instance is unsound.

**Overflow.** No arithmetic in `in.cc` can overflow. The `IntervalSet` merges
add and subtract one at interval ends, but only at ends inside a domain.
Proofs are the exception: a constant too near either end of the 64-bit range
throws with proofs on, while the same models solve with proofs off.
- **With `var ∈ 0..10`** (bisected, `probes/inovf.cc val=…`):
  - `2⁶³ − 1` throws `IntegerOverflow` (`9223372036854775807 + 1`) in
    `need_direct_encoding_for` (`names_and_ids_tracker.cc:1084`), which
    defines `[var = c]` through `var ≥ c + 1`. `2⁶³ − 2` is fine.
  - Everything from `−2⁶³` to `−2⁶³ + 16` throws. The messages are
    `IntegerOverflow` (`--9223372036854775808`, `-15 + -9223372036854775807`,
    and, at `−2⁶³ + 1`, `9223372036854775807 + 1`) or a `ProofError` that the
    reification constant of a half-reified row is the most negative `Integer`.
    They come from `need_gevar`'s `−v` and `−v + 1`
    (`names_and_ids_tracker.cc:1213–1214`), or from `reification_shape`'s
    addition and its `ProofError` (`:2894`, `:2902`), as the fact-checks
    traced with gdb.
  - `−2⁶³ + 17` is fine, and so are the three far constants checked, `2⁶²`,
    `2⁶³ − 2⁶¹` and `−(2⁶³ − 2⁶¹) − 1`, which verify.
- **The unsafe band grows with `var`'s encoding**, as the fact-checks found by
  bisecting further (`tmp/fd-small/factcheck/in/ovfsearch.py`). The first safe
  constants are:

  | `var` | lowest safe | highest safe |
  |---|---|---|
  | `0..10` | `−2⁶³ + 17` | `2⁶³ − 2` |
  | `0..1000` | `−2⁶³ + 1025` | `2⁶³ − 2` |
  | `0..10⁶` | `−2⁶³ + 1,048,577` | `2⁶³ − 2` |
  | `−10..0` | `−2⁶³ + 17` | `2⁶³ − 1 − 17` |
  | `±2⁴⁰` | about `−2⁶³ + 2.2·10¹²` | about `2⁶³ − 1 − 2.2·10¹²` |
  | `−2⁶¹ .. 2⁶¹ − 1` | `−2⁶³ + 2⁶¹ + 1` | `2⁶³ − 1 − (2⁶¹ + 1)` |

  Roughly, a constant within about `2^b` of `−2⁶³` throws, where `b` is the
  number of magnitude bits in `var`'s encoding, not its width: 4 for `0..10`,
  and 10 for `1000..1010`, whose band is 1025 wide. At the top only `2⁶³ − 1`
  throws, unless `var` can be negative, when the band there is the same size
  (`−1000..−990` has 1025 at both ends). The widest `var` throws for any
  constant beyond about `±6.9·10¹⁸`. (Re-bisected in
  `tmp/fd-small/factcheck2/in/`.)

Only a model that lists a constant far outside `var`'s own range, near the
64-bit limits, can meet this. `Table`'s far entries hit the same band (#1117).

### Interval efficiency

**Fine at any width.** No site walks values. What the work is proportional to
instead is the number of **intervals**, and there two things are not linear.

1. **The propagation side.**
   - *Constants-only step 1* (`in.cc:205–207`): `each_interval_minus` of
     `dom(var)` against the permitted set, a merge, `O(intervals(var) +
     |vals|)`.
   - *Variable step 1* (`in.cc:225–234`) builds the union by erasing each
     permitted interval and each candidate's intervals from a copy of
     `dom(var)`. `erase_range` scans from the front, and dropping a covered
     interval shifts the vector (`interval_set.hh:314–352`). The copy is not
     fixed in size: an erase inside an interval splits it, inserting into the
     vector, so the copy can gain an interval per erase, and later erases
     rescan the pieces. With `E` erases (the permitted set's intervals plus
     `Σ intervals(V_i)`) over a copy that starts with `I₀ = intervals(var)`,
     the copy never exceeds `I₀ + E` intervals. The scans are then
     `O(E · (I₀ + E))` steps, and each interval dropped (at most `I₀ + E`) or
     split off (at most `E`) shifts up to `I₀ + E` entries, so one call's
     union is `O((I₀ + E)²)`: quadratic in interval counts, both ways round.
     - *Many erases over one interval.* With `var = 0..3K` and one candidate
       over `{0, 3, 6, …, 3K}`, the first and last of the `K + 1` erases trim
       and the other `K − 1` split, so the copy ends with `K` intervals; the
       scans take 5,051, 20,101 and 80,201 loop iterations at `K` = 100, 200
       and 400 (`tmp/fd-codex-1005/small/probes/cmpcount.cc`, a verbatim copy
       of `erase_range`). Each split inserts at the end here, so nothing
       shifts.
     - *One erase over many intervals.* A single `erase_range` covering a copy
       of `I₀` singletons drops each with a vector erase that shifts the tail:
       0.034, 0.138 and 0.560 s at `I₀` = 1, 2 and 4·10⁴
       (`tmp/fd-codex-1005/small/factcheck/dropall.cc`). In `In{x, {y, z}}`
       with `x` over 30,000 even values and `y`, `z` over an interval covering
       them, `E = 2`, of which only `y`'s erase runs: it empties the copy, so
       `z`'s is skipped (`in.cc:229–230`). `perf` puts 36% of a 1.73 s root
       in `erase_range`, which here is that shift (`indrop.cc`).

     Copying the candidates' domains, and applying the removals through the
     state layer's own front-to-back scan (#1160), come on top.
   - *Step 1 stops early*: it stops copying candidates once nothing is left
     unsupported (`in.cc:229–230`).
   - *Step 2* uses `State::domains_intersect` per candidate
     (`in.cc:307–316`), a merge that stops at the first common value. But
     `const_supports` (`in.cc:319`) is an `any_of` over every constant calling
     `in_domain`, whose `contains` scans `dom(var)`'s intervals from the front:
     `O(|vals| · intervals(var))` per call at worst. It runs in the
     constants-only branch too, where nothing uses it.
   - *Step 3* (`in.cc:400`) is `each_interval_minus` of the candidate against
     `dom(var)`.
   - There is no `each_value`, `for_each_value` or value loop anywhere in
     `in.cc`.
2. **The reason side.**
   - Step 1: one literal per candidate per run, `not_in_range(V, lo, hi)`,
     guarded on `want_reasons()` (`in.cc:237–244`).
   - Step 3: a `generic_reason(var)`, which is per run of `dom(var)`, plus one
     `not_in_range` per other candidate per interval of `dom(var)`, guarded
     (`in.cc:350–361`).
   - Finding the runs is a walk over intervals in both cases, never over
     values (#874 fixed the per-value spelling of step 3's reason and
     scaffolding).
3. **The proof side.** Every line is per run or per interval. The form is
   picked by a **width test**: a run of one value takes the `≠` path, since
   `not_in_range` would canonicalise to the same literal and its lemmas would
   be pure cost (`in.cc:273–278`); anything wider takes the range form. It is
   never picked by the kind of a variable.
4. **The audit lane.** Three rows, all `Clean`:
   - `In`: one variable over the wide range against `{1, 2, 3}`;
   - `In/vars`: two singleton variable candidates at the ends;
   - `In/vars-single-support`: step 3.

   The `"Large domain proof sizes"` case uses `In{x, {1, 2}}` over width 10⁴ to
   confine every variable, so each of its rows also shows that a
   constants-only proof does not grow with width. **The rows do not vary**
   holes, the number of intervals, views, repeated or aliased candidates, or
   `vals` sizes. The two costs this audit found are both interval counts,
   which a guard counting values walked per call cannot see. The fact-check
   showed it with a guard build of `c9ceea25` at a limit low enough to mean
   something (`GCS_LARGE_DOMAIN_GUARD_LIMIT=1000`; the default 10⁵ is above
   every size here): `carve` and `vars` do not trip. `enumodd` does, but in the
   default brancher's `each_value_generator`, not in `In`.

**Intervals, measured.** Release build of `c9ceea25`, fataepyc-10,
`taskset -c 25`, fixed `GLIBC_TUNABLES`, proofs off, 2026-09-30
(`probes/inwide.cc`). Each shape runs to the root and stops. The variables are
over the `K` odd values `1..2K−1`, so every domain has `K` intervals. Times are
single runs unless marked as medians.

| Shape | K = 10³ | K = 10⁴ | K = 3·10⁴ | K = 10⁵ |
|---|---|---|---|---|
| `carve`: one variable created over the `K` values | 1.5 ms | 0.123 s (median of 3) | 1.09 s (median of 3) | 12.1 s (median of 3) |
| `vars`: three such variables, `In{x, {y, z}}` | 4.9 ms | 0.437 s | 3.98 s | — |
| `varsvals`: two, `In{x, {y}, the K values}` | 3.5 ms | 0.318 s | 2.84 s | — |

- **`carve` is the state layer, not `In`'s own code.** Profiled, 99% of it is
  `State::change_state_for_not_in_range`. `contains_any_of` and `erase_range`
  each scan the domain's intervals from the front (`state.cc:250–252`), once
  per gap, so `K` gaps cost Θ(K²). `In`'s own merge is linear.
  - With both scans starting at a binary search, `carve` takes 2.1 ms, 6.1 ms
    and 21 ms at 10⁴, 3·10⁴ and 10⁵ (medians of 3). The patch is
    `probes/interval_set_bsearch.patch`.
  - Every other constraint's `not_in_range` on a many-interval domain pays
    the same per-call scan.
- **`vars` and `varsvals` are then `In`'s own step 1.** With the binary search
  in place they still take 0.074 s and 0.653 s (`vars`) and 0.073 s and
  0.642 s (`varsvals`) at 10⁴ and 3·10⁴, for the whole root, which runs the
  variable-candidate `In` twice. The fact-check timed the calls: about
  0.32 s each at 3·10⁴. Profiled, that is `erase_range`'s vector shifts
  inside step 1's union. A merge would make it linear.
- **Per call, in search.** Enumerating one variable over the `K` odd values
  (`enumodd`) takes 0.428 s at 10⁴ and 3.83 s at 3·10⁴ (median of 3). The
  same enumeration over the interval `1..K` takes 0.017 s at 3·10⁴.
  - About half of `enumodd` is the constants-only `In`, woken at every node:
    `const_supports`' `in_domain` calls, the propagator body and
    `each_interval_minus`, 49% by `perf`.
  - Disabling that branch after its first call gives 30,002 → 1
    propagations, and 0.219 s and 1.92 s (medians of 3). The patch is
    `probes/in_self_disable.patch`.
  - The rest is the search's own `O(K)` work per node on a many-interval
    domain.
- **The same, on a real benchmark shape.** The `all_equal` audit's
  enumeration (`tmp/fd-small/all_equal/bench/ae_gcs.cc allequal 5 5 40 1`)
  declares its variables over value lists. It makes 2,087,886 propagations,
  1,620,040 of them calls of these `In`s, 25 effectful. Against the patched
  library (the self-disable, the empty hole declaration and the binary search)
  it makes 467,871, with the same solutions and recursions. Timed by the
  fact-check, uninstrumented, it goes from 1.21 s to 0.88 s, 27% less, and
  the `In` changes alone give all of it. The same benchmark with its holes
  carved by `NotEquals` instead takes 0.92 s, so the fixed `In` is slightly
  faster than avoiding it. (This audit's own timings of that comparison ran
  with `GCS_PROPAGATOR_STATS=time` on, which inflates the unpatched side, and
  are not quoted.)
- **And on a real instance.** XCSP3's `Dubois-015` (in the local collection)
  declares 45 variables over the list `0 1`, so it posts 45 `In`s that can
  never prune. They are called 262,179 times, never effectfully. With the
  three patches, propagations go from 655,413 to 393,279 and the reported
  solve time from 0.289 s to 0.259 s, 10% (medians of 5, `taskset -c 25`,
  fixed `GLIBC_TUNABLES`).

How much this matters in the corpora in hand:
- The MiniZinc Challenge's `member` shapes have arrays of 1 to 9, and
  FlatZinc domains never reach `In`.
- The local XCSP3 collection (`/cluster/ciaran/claude/xcsp-instances`) has
  6,178 files. The fact-check counted 1,672 that declare listed domains, each
  of which posts an `In`. 79 list more than five values: all 69 `Rlfap`
  (up to 44) and all 10 `Mario` (up to 99). (This audit's first count, 44 of a
  400-file sample with at most five values, was wrong, and no seed was
  recorded for it.) At those sizes the Θ(K²) carve is negligible, but the idle
  `In` and its hole declaration are on every one.

So the carve and step 1's union are next steps, not emergencies, though a
model that lists 10⁵ values takes 12 s before search starts. The idle `In` is
cheap to fix and costs something on real instances today.

## Inference catalogue

Six rules. A conflict is not a seventh: it arises when a removal empties a
domain, and the tracker asserts the attempted literal with its reason, exactly
as for a successful one.

Facts shared by every rule:

- **No published justification procedure covers `In`.** The derivations are
  ours, and **Why it is true** carries the argument. The pieces are standard:
  - Theorem 2.8, for a value crossing a flag's equality;
  - Theorem 2.9, for a bound crossing it;
  - Theorem 2.6, for stating everything under a reason and a flag.

  The shape of rules 3 and 5 is JP 3.10's, a per-candidate line and then a
  conclusion against the disjunction, with the at-least-one row in place of
  the element's index domain. See
  [`justification-techniques.md`](../justification-techniques.md).
- **Two wire forms.** `hints::In`, `(constraint_id <id>)`, is used by rules 1,
  3, 5 and 6. `hints::InNotInRange`, `(constraint_id <id>) (subhint
  not_in_range)`, is used by rules 2 and 4. Neither carries a payload.
  Measured at `Definitions` on the benchmark below (`k = 4`, `D = 8`, `var`
  branched first): 4,802 `In` annotations, 4,116 of them `not_in_range`.
- **Which direction a rule runs is read off the asserted literal's
  variable:** `var` for rules 1 to 3, a candidate for rules 4 and 5. Whether
  `In` has variable candidates at all is in the `.scp`. So the plain `in` hint
  covers three derivations, and a reconstructor tells them apart from the
  baseline context, not from the hint.
- **The justifications read no `state`** except one. Rule 4's and rule 5's
  scaffolding asks `state.has_single_value(var)` (`in.cc:373`) to skip the
  per-interval lines, which are redundant when `var` is fixed: the reason's
  `var = w` then gives `¬sel_j` directly. The reason is built from the same
  call's state, so the two agree. It is still a read of `state` inside a
  justification, which the template asks to avoid.

### Rule: constants-filter

- **Infers** — `var ∉ [lo, hi]` for each maximal run of `dom(var)` outside
  `vals`.
- **Fires when** — the propagator has no variable candidates; on every change
  to `var`, though it can only ever infer something on its first call.
- **Strength** — `GAC`. It is a unary constraint, and this is its domain
  intersection.
- **Algorithm** — `each_interval_minus` of `dom(var)` against `vals`, one merge,
  `O(intervals(var) + |vals|)`; one conclusion per run (`in.cc:185–208`).
- **Why it is true** — no value in the run is permitted, and there is no
  variable candidate.
- **Proof technique** — `RUP`. Under `var ∈ [lo, hi]` the order literals
  bound `var` inside the run, so every `[var = c]` in `@c[id][al1]` is false
  by Theorem 3.3's complete propagation within one variable, and the row is
  violated.
- **Reason** — `NoReason`: none is needed, since the row alone refutes the
  run.
- **Assertion** — `¬[var ∈ lo..hi]`, e.g. `a 1 ~i[s0][in4_7] >= 1`. A width-one
  run is `¬[var = v]` (the range literal canonicalises to it).
- **Hint** — `hints::In`: `originator`, the `ConstraintID`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per run, whatever the width. `K` runs for a
  variable created over `K` scattered values.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: unsupported-run

- **Infers** — `var ∉ [lo, hi]` for a run of two or more values of `dom(var)`
  that no permitted constant and no candidate's domain holds.
- **Fires when** — the propagator has a variable candidate; step 1, any change
  to `var` or a candidate.
- **Strength** — `GAC` on distinct variables, together with rules 3 to 5.
  - *The argument.* At the fixpoint every value `a` of `var` is a constant or
    in some candidate's domain; set that candidate to `a` and the rest
    anywhere.
  - Every value `b` of a candidate `V` is supported when some other source
    (a constant or another candidate) can meet `var`: put `var` there, and
    `V = b`.
  - When nothing else can, rules 4 and 5 have made `dom(V) = dom(var)`, and
    `var = V = b` is a solution.
  - Holes do not break any of this.
  - *The evidence.* Root brute force over 3,000 instances per seed and mode,
    seeds 1 to 3 (`probes/incheck.cc`). The instances have holes, zero to
    three candidates, zero to two constants, a constant candidate half the
    time, and in `dviews` random `±1` views and offsets on distinct variables.
    There are no GAC failures and no unsatisfiable instance left unfailed.
    `in_test` checks GAC at every node, on interval and holey domains.
  - On repeated or aliased variables it is not even `bounds(Z)`: see
    [Robustness](#robustness-and-limits).
- **Algorithm** — the union of `vals` and every candidate's domain, erased from
  a copy of `dom(var)`, then one conclusion per remaining run
  (`in.cc:225–271`). `O((I₀ + E)²)` for the union as written, scans and
  vector shifts together, with `E` the permitted set's intervals plus the
  candidates' and `I₀` the intervals of `dom(var)`; see [Interval
  efficiency](#interval-efficiency).
- **Why it is true** — if `var` were in the run it would equal a constant, and
  none is there, or a candidate, and each candidate is outside the run.
- **Proof technique** — `RUP sequence`: per candidate `V_j`,
  1. two bound lemmas, `var ≥ lo → V_j ≥ lo` and `V_j ≥ hi + 1 → var ≥ hi + 1`,
     each guarded by `¬sel_j`;
  2. the line `¬sel_j ∨ ¬[var ∈ lo..hi] ∨ [V_j ∈ lo..hi]`;

  then the conclusion by RUP against `@c[id][al1]`.
  - *The lemmas.* Each is Theorem 2.9 across one of the flag's halves
    (`V_j − var ≥ 0` or `≤ 0`, so `B = 0`), with the guard and the reason
    assumed by Theorem 2.6. That is `justify_not_in_range_across_equality`
    with `under`.
  - *Why the lemmas.* The range literal asserts only order atoms, so without
    them the conclusion cannot cross the flag's equality.
  - *When they are load-bearing.* Only when the candidate is missing the run
    through a **hole**. A run outside a candidate's declared bounds crosses
    without help ([`large-domains.md`](../large-domains.md), around line 213).
- **Reason** — `not_in_range(V_j, lo, hi)` for every candidate, one literal per
  candidate per run, guarded on `want_reasons()`. Minimal: each literal is
  what rules its candidate out.
- **Assertion** — `¬[var ∈ lo..hi] ∨ ⋁_j [V_j ∈ lo..hi]`. Measured at
  `Inferences`:
  ```
  a 1 ~i[x][in4_7] 1 i[s0][in4_7] 1 i[s1][in4_7] >= 1::in:((constraint_id _3) (subhint not_in_range));
  ```
- **Hint** — `hints::InNotInRange`: `originator`; the subhint names the
  two-lemma shape.
- **Offline reconstructibility** — `hinted`.
  - The lemmas are fixed by the run's endpoints and the flags' names, and the
    subhint says to build them, as `equals`' range rule does.
  - At `Inferences` they are absent from the proof, which is why the annotation
    has to carry the distinction.
- **Proof size** — `3k + 1` lines for `k` candidates, plus one `del range`,
  per run. That is per run and per candidate, never per value. Measured on a
  root probe with `k = 2` (`probes/inrule.cc step1range`): six candidate
  lines, the conclusion, and `del range -7 -1`.
- **Gaps** — `None.`
- **Tightness** — shown by hand in #874, not by a lane.
  - Dropping the two lemmas is *rejected* on `in_test`'s three hole rows.
  - It is *accepted* on the 37 contiguous proving rows
    ([`large-domains.md`](../large-domains.md), around line 213).

### Rule: unsupported-value

- **Infers** — `var ≠ v` for a run of one value of `dom(var)` that nothing
  supports.
- **Fires when** — as rule 2, for a width-one run.
- **Strength** — as rule 2.
- **Algorithm** — as rule 2; a width test picks the form (`in.cc:273–297`).
- **Why it is true** — as rule 2, for a single value.
- **Proof technique** — `RUP sequence`: per selector `¬sel_j ∨ var ≠ v` under
  the reason, then the conclusion by RUP against `@c[id][al1]`.
  - Each selector line is Theorem 2.8: under `var = v` and `sel_j`, the flag's
    two halves fix `V_j`'s bits to `v`, against the reason's `V_j ≠ v`.
  - The shape is JP 3.10's.
- **Reason** — `V_j ≠ v` for every candidate. Minimal.
- **Assertion** — `var ≠ v ∨ ⋁_j V_j = v`, e.g.
  `a 1 ~i[x][eq5] 1 i[s0][eq5] 1 i[s1][eq5] >= 1::in:((constraint_id _3));`.
- **Hint** — `hints::In`: `originator`.
- **Offline reconstructibility** — `offline`. The per-selector lines are fixed
  by the literal and the flags.
- **Proof size** — `k + 1` lines.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: single-support-run

- **Infers** — `V ∉ [lo, hi]` for each run of two or more values of
  `dom(V) \ dom(var)`, where `V` is the only candidate still meeting
  `dom(var)` and no constant is in `dom(var)`.
- **Fires when** — step 3, after steps 1 and 2 of the same call.
- **Strength** — `GAC` on distinct variables, with rules 2, 3 and 5; see rule 2.
  Gecode's `member` has no counterpart: see [Prior art](#prior-art).
- **Algorithm** — `each_interval_minus` of `dom(V)` against `dom(var)`
  (`in.cc:400–418`).
- **Why it is true** — every other source is unavailable. No constant is in
  `dom(var)`, and every other candidate misses `dom(var)`. So the constraint
  forces `var = V`, and `V` cannot take a value `var` does not have.
- **Proof technique** — `RUP sequence`. First, for every other candidate `V_j`
  and every interval `[a, b]` of `dom(var)`:
  - the two guarded bound lemmas, when `a < b`;
  - the line `¬sel_j ∨ ¬[var ∈ a..b] ∨ [V_j ∈ a..b]`.

  Then comes `¬sel_j`, which is the collapse of Theorem 3.2: `var`'s interval
  memberships, all ruled out under `sel_j`, empty `dom(var)` against the
  reason's bounds and holes. After that, the conclusion's own two lemmas cross
  `V = var` unguarded, since `@c[id][al1]` now forces `V`'s selector. The
  conclusion is last, by RUP. `in.cc:368–398` and `:409–415`.
- **Reason** — the same for every run:
  - `generic_reason(var)`: `var`'s bounds and one literal per hole;
  - `not_in_range(V_j, a, b)` for every other candidate and every interval of
    `dom(var)`;
  - `not_in_range(var, lo, hi)` for the run itself.

  It is guarded on `want_reasons()` and is per interval, never per value.
  **Not minimal.** The last literal is always implied by the generic reason,
  since the run lies outside `dom(var)`. When the run is a hole of `var` it is
  the very same literal: the step-3 probe's assertion names `i[x][in3_5]`
  twice.
- **Assertion** — e.g.
  ```
  a 1 ~i[s0][in3_5] 1 ~i[x][ge0] 1 i[x][ge9] 1 i[x][in3_5] 1 i[s1][in0_2] 1 i[s1][in6_8] 1 i[x][in3_5] >= 1::in:((constraint_id _2) (subhint not_in_range));
  ```
- **Hint** — `hints::InNotInRange`: `originator`.
- **Offline reconstructibility** — `hinted`, as rule 2. The supporting
  candidate is the one the asserted literal is about, and `dom(var)`'s
  intervals are in the reason.
- **Proof size** — `(k − 1)(I + 2·I_w + 1) + 3` lines per run, for `k`
  candidates, where `dom(var)` has `I` intervals of which `I_w` are wider than
  one value. When `var` is fixed the per-interval lines are skipped, so it is
  `(k − 1) + 3` (4 at `k = 2`, found by the fact-check). Plus the shared
  layer's definitions for any range literal named for the first time. That is
  10 lines on the probe with `k = 2`, `I = I_w = 2` (`probes/inrule.cc
  step3range`). Before #874 this was per value of `dom(var)`; the survey read
  7,048 → 70,048 across a decade of width. The audit row now reads 93 steps,
  flat ([`large-domains.md`](../large-domains.md), around line 1232).
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: single-support-value

- **Infers** — `V ≠ v` for a width-one run of `dom(V) \ dom(var)`, under the
  same condition as rule 4.
- **Fires when** — as rule 4.
- **Strength** — as rule 4.
- **Algorithm** — as rule 4 (`in.cc:420–425`).
- **Why it is true** — as rule 4.
- **Proof technique** — `RUP sequence`: the same ruling-out of the other
  selectors as rule 4, then the conclusion by RUP. Once `sel_V` is forced,
  Theorem 2.8 carries `var ≠ v` (from the reason's description of `dom(var)`)
  across the equality. No bound lemmas are needed for a single value.
- **Reason** — as rule 4, without the run literal.
- **Assertion** — e.g.
  `a 1 ~i[s0][eq3] 1 ~i[x][ge0] 1 i[x][ge7] 1 i[x][eq3] 1 i[s1][in0_2] 1 i[s1][in4_6] >= 1::in:((constraint_id _2));`.
- **Hint** — `hints::In`: `originator`.
- **Offline reconstructibility** — `offline`. Everything the walk needs is in
  the reason.
- **Proof size** — `(k − 1)(I + 2·I_w + 1) + 1` lines, or `(k − 1) + 1` when
  `var` is fixed.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: no-candidates

- **Infers** — a contradiction, at the root.
- **Fires when** — both lists were empty after `prepare()`; an initial
  contradiction replaces the propagator.
- **Strength** — `GAC` (the constraint is unsatisfiable).
- **Algorithm** — none.
- **Why it is true** — no value can satisfy a membership in the empty set.
- **Proof technique** — `RUP`: `@c[id][al1]` is `0 ≥ 1`.
- **Reason** — none.
- **Assertion** — `a >= 1::in:((constraint_id _1));`, i.e. `0 ≥ 1`.
- **Hint** — `hints::In`: `originator`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

- **`in_test`** (`in_constraint`, plus `in_constraint_view_mixed`), 60 cases
  per proof setting:
  - constants only (alternating, even, all, single, all outside, some outside,
    negative, duplicates);
  - constant candidates;
  - mixed;
  - variable candidates (overlapping, singletons, a single supporter, disjoint,
    a forced gap, negatives);
  - four rows added by #874 that reach the range forms;
  - self-reference;
  - the four empty-list overloads of #254;
  - fixed-variable tautologies and contradictions;
  - three **hole rows** (`run_all_holes_tests`), the only ones where the bound
    lemmas are load-bearing;
  - five random instances of each of the four shapes.

  They run under `solve_for_tests_checking_gac`, or under
  `solve_for_tests_checking_consistency` with GAC on `var` and the candidates.
  So every value left at every node is checked against the solution set. With
  proofs, VeriPB runs when it is on the path. Seeded.
- **`scp_chain_in_*`:** the seven cases under [Cake
  conformity](#cake-conformity).
- **MiniZinc:**
  - `membertest.mzn` (`member` over three `var 1..4`) against the reference
    solver;
  - `minizinc-emptysetin`, hand-written JSON FlatZinc for `set_in` with the
    empty set.
  - `setinreif` and `disjointdomain` do not reach this family (the frontend
    table).
- **XCSP3:** `sum_not_equals.xml`'s listed domain `0 3` posts three `In`s,
  incidentally.
- **Audit lane:** the three rows under [Interval
  efficiency](#interval-efficiency).

**Runtime caps.** No lane sets or clears one, and the default caps **never
fire** here. Both lanes run 120 cases (60 without proofs, 60 with), none
truncated (`GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500 in_test
--seed=1`, and the same with `--view-position=mixed`, at `c9ceea25`). So the
capped and uncapped runs check the same thing.

**Beyond the suite, for this audit** (`tmp/fd-small/in/probes/`):
- **The root brute force.** 36,000 instances: four modes, three seeds, 3,000
  each.
- **Proofs.** 300 random instances per mode, the same generator with proofs,
  enumerating every solution: all 1,200 verify at `Off`. At `Definitions`,
  `Links` and `Inferences`, 100 per mode with views (`dviews` and
  `aliasviews`) all give `s UNDER ASSERTIONS`, except four `aliasviews`
  instances at `Definitions` with no `In` inference, which give `s VERIFIED`.
- **The cake chain** on 120 of those models.

**Tightness:** no mutation lane. #874's hand-run lemma removal is recorded
under rule 2.

**What the tests do not cover.**

- **Repeated or aliased candidates.** No row repeats a candidate or makes one
  a view of `var` other than `var` itself. So the lost `bounds(Z)` and the
  W/2 failure are invisible to the suite.
- **Many intervals.** Every domain in the suite has a handful of values, so
  the Θ(K²) carve, step 1's quadratic union and the per-wake cost never show.
- **A constant `var`**, which XCSP3's index-free `element` would post: no row
  and no chain case.
- **Duplicate constants in the chain**, the one `al1` divergence from cake.
- **Extreme 64-bit constants with proofs.**
- **Real instances:** none ported.

### Benchmarks and examples

- **In the repository:** no example or benchmark posts it for its own sake. The
  circuit tests use `In` to shape domains, and so do the examples
  `circuit_small` (which posts `In`) and `rostering` (listed domains). An
  earlier microbenchmark, `tmp/in-bench/bench.cc`, lives outside the tree.
- **Corpus:** 2,809 `glasgow_member_int` posts in 7 of the 285 flattened
  MiniZinc Challenge models: `code-generator` 2019, 2020 and 2023 (333, 2,115
  and 329), and `elitserien` 2014, 2016, 2018 and 2023 (8 each). Arrays are 1
  to 9 long, with up to four constants.
  - The `elitserien` JSON in that corpus predates #997 and no longer parses,
    so it was flattened again with the current library.
  - **The family is never a meaningful share of a solve** (60 s limit,
    `GCS_PROPAGATOR_STATS=time`). The call counts come from runs cut off by the
    limit, so they vary between runs: the fact-check's re-runs gave 330,221 for
    `code-generator` 2020 and 600,678 for `handball11`.
    - `code-generator` 2020: 315,171 calls and 0.26 s of 60 s;
    - `code-generator` 2019 and 2023: 1,625 and 1,703 calls, about 1 ms;
    - `elitserien` 2014 `handball11`, 2018 `handball1` and 2023 `handball10`:
      550,467, 488,618 and 156,799 calls, 0.40, 0.36 and 0.11 s.
  - The corpus's listed domains are all FlatZinc, which does not use `In`.
- **For CPU:** the enumeration below, branching on the candidates first, on
  which neither solver fails and both enumerate the same solutions. The trees
  are not the same: the branching schemes differ (below).
- **For proof verification:** the same enumeration branching on `var` first,
  which reaches all five rules, at `k = 4` and `D` from 6 to 8.

### CPU performance

*Release build of `c9ceea25` (GCC 15.2.0); probes built `-O3
-march=native`. Gecode 6.3.0, built locally. fataepyc-10, pinned with
`taskset -c 25`, `GLIBC_TUNABLES` fixing the malloc thresholds. Median of five
runs; wall time of the whole solve, proofs off; 2026-09-30.*

`var` and `k` candidates over `1..D`, one `In`, every solution enumerated. In
the `mixed` rows, `1` and `D` are also permitted constants.
- *Candidates first* branches the candidates, then `var`, in order, smallest
  value first. When the candidates are fixed, both solvers restrict `var` to
  exactly their values, so the two searches have the same solutions and no
  failures.
- *`var` first* reaches the single-support rule, which Gecode does not have.

The node counts differ throughout, because GCS gives a variable one child per
value where Gecode's `INT_VAL_MIN` branches in two. The drivers are
`tmp/fd-small/in/bench/in_gcs.cc` and `in_gecode.cc`.

| Order | Shape | k | D | Solutions | GCS | Gecode `member` | Ratio |
|---|---|---|---|---|---|---|---|
| candidates first | variables | 6 | 8 | 1,155,960 | 1.800 s | 0.489 s | 3.7 |
| candidates first | mixed | 6 | 8 | 1,391,258 | 2.057 s | 0.583 s | 3.5 |
| candidates first | variables | 5 | 12 | 1,053,372 | 1.668 s | 0.452 s | 3.7 |
| `var` first | variables | 6 | 8 | 1,155,960 | 1.435 s | 0.642 s | 2.2 |
| `var` first | mixed | 6 | 8 | 1,391,258 | 1.491 s | 0.648 s | 2.3 |

| Order | Shape | k | D | GCS recursions | GCS propagations | GCS failures | Gecode nodes | Gecode propagations | Gecode failures |
|---|---|---|---|---|---|---|---|---|---|
| candidates first | variables | 6 | 8 | 1,455,545 | 1,717,689 | 0 | 2,311,919 | 1,282,031 | 0 |
| candidates first | mixed | 6 | 8 | 1,690,851 | 1,952,275 | 0 | 2,782,515 | 1,382,705 | 0 |
| candidates first | variables | 5 | 12 | 1,324,813 | 1,573,645 | 0 | 2,106,743 | 1,247,446 | 0 |
| `var` first | variables | 6 | 8 | 1,321,097 | 1,455,553 | 0 | 3,488,409 | 1,508,330 | 588,245 |
| `var` first | mixed | 6 | 8 | 1,590,009 | 1,091,667 | 0 | 3,690,093 | 1,173,834 | 453,789 |

- **Candidates first, GCS takes 3.5 to 3.7 times Gecode's time** for the
  whole enumeration here, and 3.3 to 3.6 in the fact-check's re-run
  (`tmp/fd-small/factcheck/in/bench/cpu.txt`, with every count identical to
  the first run). The two searches have the same solutions and no failures,
  but not the same tree: GCS's one child per value against Gecode's binary
  branching gives 1,455,545 recursions against 2,311,919 nodes on the first
  row, with different intermediate domains and propagation work. This is a
  whole-solve comparison on a benchmark with no failures, so it measures the
  search loop as much as the propagator. By `perf`, the `In` propagator is
  about half of GCS's time on the first row; `copy_of_values` alone is 11%.
- **Branching on `var` first, GCS searches no failures and Gecode 588,245.**
  Gecode's `member` restricts `var` to the union of the candidates and drops
  candidates that cannot meet it, but after posting never prunes a candidate.
  GCS's single support rule does, and the ratio falls to 2.2.
- **What the benchmark does not exercise:** holes, views, aliasing, wide
  domains and many intervals. At `D ≤ 12` every domain is a single interval
  until search splits it. The constants-only branch is exercised only as the
  `mixed` shape's constants.

### Proof performance

*Same build and machine. `in_gcs <shape> 3|4 6|8 p <level>`, enumerating every
solution. VeriPB 3.0.2 with `--force-checked-deletion`, single runs; the
`k = 4, D = 8` times were repeated twice and reproduced within 0.05 s.*

| Order | k | D | Solutions | Lines, `Off` | Bytes, `Off` | VeriPB, `Off` | Lines, `Definitions` | `In` annotations (range / value) | VeriPB, `Definitions` | VeriPB, `Inferences` |
|---|---|---|---|---|---|---|---|---|---|---|
| candidates first | 3 | 6 | 546 | 9,628 | 469 KB | 0.15 s | 6,426 | 430 (212 / 218) | 0.10 s | 0.03 s |
| `var` first | 3 | 6 | 546 | 6,224 | 239 KB | 0.07 s | 4,977 | 250 (200 / 50) | 0.06 s | 0.03 s |
| `var` first, mixed | 3 | 6 | 796 | 7,824 | 266 KB | 0.09 s | 6,827 | 200 (150 / 50) | 0.08 s | 0.04 s |
| `var` first | 4 | 6 | 4,026 | 40,686 | 1.74 MB | 0.54 s | 33,189 | 1,250 (1,000 / 250) | 0.44 s | 0.32 s |
| `var` first | 4 | 8 | 13,560 | 137,708 | 6.17 MB | 2.55 s | 108,215 | 4,802 (4,116 / 686) | 2.00 s | 4.94 s |

**Own versus shared.** At `Definitions` each of the family's inferences is one
`a` line in place of its derivation. So `Off − Definitions + annotations`
counts the lines the family's derivations write. It also counts the few
shared range-literal definitions a derivation causes, which are written only
when a justification runs. That is 1,497, 8,747 and 34,295 lines on the three
`var`-first rows without constants, 24%, 21% and 25% of the proof.
- The rest is the enumeration's own backtracking, `solx` and the shared
  literal layer.
- The share holds as `D` grows from 6 to 8, and the derivations grow with the
  candidate count, as the per-rule sizes say.

**Assertion levels.** At `Off` every proof verifies. At `Definitions` and
`Inferences` VeriPB accepts each with `s UNDER ASSERTIONS`, not `VERIFIED`, so
only `Off` checks the family.
- *`Inferences` is slower to check.* At `k = 4, D = 8` it takes 4.9 s against
  2.5 s at `Off`, though it is shorter.
- *`Links` fails on this benchmark at its first `solx`* (lines 35 to 76,
  depending on the row). VeriPB reports `The propagated assignment does not
  satisfy the constraint with ID …` (35 to 50, by row), an equality-literal
  definition
  (`red … ~i[x[k]][eq1]`). The mechanism, worked out by the fact-check: at
  `Links`, an order literal introduced in the proof gets only
  `::initial_bound:` and `::bound_link:` assertions, with no definition over
  the bits. So propagating the `solx` bits cannot fix, say, `ge2`, and the
  `eq1` definition is left unsatisfied. It is the literal layer's, not this
  family's, and it is the failure the other family documents record.
- *Declaring the variables over value lists avoids it.* The 200 random probe
  proofs pass `Links`, because the carving `In`'s `al1` row puts those order
  literals' definitions in the OPB. The fact-check's direct test: the benchmark
  with its variables declared over the vector `1..D`
  (`tmp/fd-small/factcheck/in/bench/in_gcs_vec.cc`) passes `Links` on all five
  rows.
- *Which assertions are the family's.* Of the `Inferences` assertions, 430 of
  1,775 carry this family's hint on the first row, and 4,802 of 33,859 on the
  last. The rest are the search's own.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified at `Off`, and the propagator is the same
with proofs on or off. One limitation in the proof model: a constant near a
64-bit limit (within about `2^b` of `−2⁶³`, or of `2⁶³ − 1` when `var` can be
negative, where `b` is `var`'s magnitude bits; `2⁶³ − 1` itself always) throws with proofs on only
([Robustness](#robustness-and-limits)).

### Known limitations

- **Declaring a variable over a long list of values is quadratic in the list.**
  10⁵ values take 12 s before search starts, in the state layer's interval
  scans. Every other constraint's range removal on such a domain pays the same
  per-call scan.
- **A variable declared over a list of values keeps an `In` live for the whole
  search.** It can never infer anything after the root, but it runs at every
  change, `O(|vals| + intervals)` each time: half the time of an enumeration
  of that variable. It also marks the variable's holes as observed, so other
  constraints' `consistency::Auto` cannot drop their interior pruning on it.
- **With variable candidates and many-interval domains, each call is quadratic
  in interval counts.**
- **Repeating a candidate, or listing a view of `var` among the candidates,
  loses propagation.** `In{x, {y, y}}` never prunes `y`; `In{x, {−x}}` keeps
  the whole of `x`; and `In{x, {x + 1}}` takes time proportional to `x`'s
  width to fail.
- **XCSP3's index-free `element`**, which means exactly this constraint, is
  rejected as unsupported.
- **A constant near a 64-bit limit** (within about `2^b` of `−2⁶³`, or of
  `2⁶³ − 1` when `var` can be negative; `2⁶³ − 1` itself always) aborts a proof-logged run; with the
  widest `var`, that is any constant beyond about `±6.9·10¹⁸`.

### Next steps

1. **Binary-search the interval scans in `State::change_state_for_not_in_range`
   (`IntervalSet::erase_range` and `contains_any_of`).**
   - *What it buys.* Carving 10⁵ values goes from 12.1 s to 0.021 s, and every
     range removal on a many-interval domain gets cheaper.
   - *What was tried.* A `lower_bound` start in both
     (`probes/interval_set_bsearch.patch`) gave the `carve` figures above. With
     it and the two `In` changes of step 2 applied together, the full suite
     passes, 962 of 962 (`ctest -j6`, default caps;
     `tmp/fd-small/in/NOTES.md`).
   - *Cost.* Small, but it is a shared primitive, and it wants a benchmark
     across families as well as the suite. Filed as #1160.
2. **Stop the constants-only `In` after its first call, and have it declare no
   hole sensitivity.**
   - *The change.* Return `DisableUntilBacktrack` at the end of that branch
     (every value left is permitted and none can return), and set
     `Triggers::holes_affect_propagation` to an empty list for it.
   - *Tested together* (`probes/in_fixes.patch`). `enumodd` goes from 30,002
     propagations to 1, and from 3.83 s to 1.92 s at 3·10⁴. The `Element`
     probe's optional pruning is switched off on the vector-declared result.
     The `all_equal` benchmark above loses 1.62 million propagations and 27%
     of its time (the fact-check's timing), and `Dubois-015` 262,134
     propagations and 10% (with step 1's patch too). `in_test --seed=1`
     passes, and so does the full suite with step 1's patch as well.
   - *Cost.* Three lines of code; the analysis in
     [`optional-interior-pruning.md`](../optional-interior-pruning.md) needs a
     sentence. Filed as #1161.
3. **Build step 1's union by merging, not by repeated `erase_range`.**
   - *The change.* A k-way merge of `vals` and the candidates' intervals,
     followed by one `each_interval_minus`, makes the call linear in interval
     counts.
   - *Separately,* compute `const_supports` only when step 3 could use it, by
     a merge, not an `any_of` over every constant.
   - *Cost.* Small. It buys about 0.32 s per call at 3·10⁴ intervals, on a
     shape no model in hand has. Filed as #1162.
4. **Handle repeated and aliased candidates.**
   - *De-duplicating identical candidates* in the propagator would restore
     `bounds(Z)` and GAC on the plain-repeat shape.
   - *For a candidate `a·u + b'` over `var`'s own `u`:*
     - with the same sign, it is `var` itself (always true) when `b' = b`, and
       can never equal `var` otherwise;
     - with the opposite sign, it can equal `var` only at `(b + b')/2`.

     The propagator could treat each accordingly.
   - *The catch.* The encoding must not change: `cake_pb_cp` gives every
     listed variable a flag triple, and the flag indices must agree. So this
     is propagation-side only, and the justification then has to rule the
     dropped selectors out.
   - *What it buys.* It fixes the repeated-candidate shape and the
     candidates that are views of `var`, and turns the W/2 failure into an
     immediate one. **It does not restore `bounds(Z)` in general**:
     candidates that alias each other through different views stay weak.
     `In{x, {y, y + 1}}` with `x ∈ 1..2` and `y ∈ 0..10` leaves `y ∈ 0..10` at
     the root, though 10 has no support (`tmp/fd-small/factcheck/in/myalias2.cc`). It
     needs a wide-domain audit row, the same as #1144.
   - *Status.* Not tried. Filed as #1163.
5. **Map XCSP3's index-free `element` onto `In`.**
   - Override the two `buildConstraintElement(id, list, value)` callbacks:
     `In{value, list}` and `In{constant, list}`.
   - That is not the whole job, the fact-check found:
     - an integer list with a variable value throws inside the parser itself
       (`XCSP3Manager.cc:955–957`);
     - the `<condition>` form goes to a third callback,
       `(list, XVariable *index = NULL, startIndex, XCondition &)`, which the
       frontend does not override;
     - a mixed list such as `x[0] 7 x[1]` passes an `XInteger` entry, which a
       plain `need_variables` rejects.
   - The constant-`var` shape verifies (`probes/inconstvar.cc`). It then wants
     a chain case, which opbdiff will not pass `strict` until the big-M
     difference above is resolved.
   - Small. Filed as #1164.
6. **Claim idempotence** on distinct variables, which holds. Trivial; not worth
   an issue on its own.
7. **Drop the run literal from step 3's reason**, which the generic reason
   always implies. It would then need spelling out in the justification, so
   it is cosmetic at best.

Not worth an issue: the extreme-constant overflow. It needs a model listing a
constant near a 64-bit limit (within about `2^b` of `−2⁶³`, or of `2⁶³ − 1`
when `var` can be negative; `2⁶³ − 1` itself always), far outside `var`'s own range, and the fix belongs
to the literal layer (`need_direct_encoding_for`, `need_gevar` and the
reification renderer), not here. `Table`'s far entries hit the same band
(#1117); a comment there would do.

## Prior art

Membership in a set of variables is `member` in the Global Constraint Catalogue.
Membership in a set of constants is just a unary domain restriction.
- **Gecode's `member(home, x, y)`** (`gecode/int/member/prop.hpp`, 6.3.0) is
  documented as domain consistent. At post it removes duplicates, and if only
  one view is left it posts plain domain equality instead, which does prune
  that view. Otherwise it folds fixed views into a value set, restricts `y` to
  the union, and eliminates views that cannot meet `y`. After posting it never
  prunes a remaining `x_i`, so the
  single-support rule here is stronger than it (588,245 failures against none,
  above).
- **Proof logging:** we know of no published certification of `member`. The
  encoding is `cake_pb_cp`'s, built around its count helper. The derivations
  here, including the guarded bound lemmas that carry a range across a
  selected equality, are ours.

## Further reading

- [`large-domains.md`](../large-domains.md), for #874 and its predecessor:
  - around line 112, the constants branch's rewrite, byte-identical before and
    after;
  - around line 124, the variable branch's three sites;
  - around line 202, why both lemmas carry the selector;
  - around line 213, when the lemmas are load-bearing;
  - around line 858, why `In` is worth more than its own audit row;
  - around line 1232, the proof-size survey that found step 3's per-value
    scaffolding.
- [`range_literals_spec.md`](../range_literals_spec.md): the range-literal
  layer every range rule here rests on. §6 and item 3 of §9 record that
  `In`'s per-value root pruning was once the hidden per-value literal factory,
  and that initial-domain gaps are root-derived in the proof, not stated in
  the OPB, pending the CakePB decision recorded there.
- [`optional-interior-pruning.md`](../optional-interior-pruning.md): what the
  *Holes affect* column feeds, and why an overstated sensitivity costs other
  families rather than this one.
- [`justification-techniques.md`](../justification-techniques.md): Theorems
  2.6, 2.8, 2.9 and 3.2, and JP 3.10, whose shape rules 3 and 5 follow.
