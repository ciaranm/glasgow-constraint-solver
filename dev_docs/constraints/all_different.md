# `AllDifferent`: no two variables take the same value

> **Maturity** production ·
> **Audited** 2026-09-21 at `6b220c79`; its six fixes merged 2026-09-22, all in
> `main` by `1d7dcf28`, and this document updated to describe them ·
> **Open issues** `None.` of the six this audit filed, each closed by its pull
> request: #987 → #997, #988 → #1004, #989 → #1002, #990 → #1001, #991 → #1000,
> #992 → #999.
> Two more wrong answers turned up while fixing them and are fixed in the same
> pull requests. Filed since: #1006 (MiniZinc differential tests over the shapes
> a front end gets wrong), whose pilot on this family's globals merged as #1011
> and fixed two more `arg_sort` bugs, one of them #1010; and #1008 (the
> single-value reason cache sized by the span of variable IDs, not the scope),
> fixed by #1020. On 2026-09-25 #1088 changed code here for `Inverse`'s sake
> only; this family's own `.opb` and `.pbp` are byte-identical either side of
> it (`f28fdef8` against `61112ed0`) on a GAC, BC and VC enumeration probe.
> The shared-helper table records the change, and the note on `Inverse`'s
> root at-most-one initialiser records #1089, which made it lazy. Already open
> and touching this family: #522 (SCC incrementality), #944 (Hall proofs cost
> values × vars²), #833 (the large-domain policy; the GAC arm is a
> `KnownTrip`), #868 (cross-solver). Tracked under #871.

Four posted classes over three propagation algorithms: `AllDifferent` with a
choice of generalised arc consistency, bounds consistency or value consistency,
`AllDifferentExcept` and its `ExceptZero` spelling, and `SymmetricAllDifferent`.
They share one OPB encoding — a half-reified pair of strict inequalities per pair
of variables — and one proof argument, the Hall set, in two shapes: over the
value graph for the generalised arc consistent propagator, and over an interval
of values for the bounds consistent one.

Three things to know before touching it. First, the justification is the
textbook one, **JP 3.16 and 3.17** of McIlree's thesis, and its cost is not the
Hall argument but the at-most-one it sums: one per value, built from a pairwise
clause per pair of variables, so a Hall proof over `k` values costs `k · C(n, 2)`
lines. On a pigeonhole that is cubic in `n` against a quadratic shared literal
layer, and it overtakes the literal layer at about `n = 19`. Second, this
directory's propagators are **not only this family's**: `Inverse` and `ArgSort`
run the generalised arc consistent propagator, and `Circuit` and `SubCircuit` run
the value consistent one and the clique encoding, so a change here is a change
there. Third, `AllDifferent` has a bounds consistent arm but that arm **cannot**
be paired with the generalised arc consistent one as an optional-interior-pruning
`consistency::Auto`, and the reason is the most useful thing this family has to
say about the #902 mechanism: see [Interior values and optional
pruning](#interior-values-and-optional-pruning).

**The audit's most serious finding was not in this directory.** MiniZinc's
`symmetric_all_different` reached `SymmetricAllDifferent` with its start
hard-coded to 1, so on any array whose index set did not start at 1 it enforced
a different constraint — wrong solutions, or a wrong `UNSATISFIABLE`. Sweeping
the MiniZinc library for the same shape found two more, `inverse` and
`arg_sort`, in other families (#987). And the wrong `UNSATISFIABLE` **verified**,
all the way through `cake_pb_cp`, because the mistranslation happened before the
`.scp` was written. See [Known limitations](#known-limitations).

**What the fixes changed.** Every finding the audit filed is fixed, all six
merged by `1d7dcf28`, and the document describes the code as they leave it; a
figure taken at `6b220c79` says so.

| Issue | Pull request | What it changed here |
|---|---|---|
| #987 | #997 | the three MiniZinc globals pass the model's index set, behind `circuit`'s empty-array guard, with a non-1-based differential test each. **And `Inverse` numbered `x`'s values from `x_start` rather than `y_start`**, in the value set it hands this family's propagator and in its root at-most-ones, so two arrays starting at different indices failed at the root: a wrong `UNSATISFIABLE` that XCSP3's two-list `channel` could already reach |
| #992 | #999 | the value consistent arm wakes `on_instantiated` and declares no hole sensitivity. **And it ignored every variable fixed at post time**, whose values it therefore never removed: at `VC`, `AllDifferent{x, y}` with `y = 3` accepted `x = 3`. The arm gains the enumeration lane it never had, which the old code fails at its first row with a constant |
| #991 | #1000 | the Hall search runs only when a proof or reasons want it, in all five constraints that run the propagator |
| #990 | #1001 | `SymmetricAllDifferent`'s dead root initialiser is deleted |
| #989 | #1002 | XCSP3's `allDifferent` with `except` posts `AllDifferentExcept` |
| #988 | #1004 | a repeated `AllDifferentExcept` variable is forced a run at a time, by RUP alone, and is no longer walked for the value set — which, not the forcing loop, was most of the measured cost |
| #1008 | #1020 | the single-value reason cache is sized by the scope, not by the span of its variable IDs; filed after the audit, while reviewing this document. No search tree or proof changes |

The sections that moved are the frontend table, the [propagator
inventory](#propagator-inventory), [Interior values and optional
pruning](#interior-values-and-optional-pruning), [Interval
efficiency](#interval-efficiency), rules 1, 2, 4 and 8, the tests, and
everything under [Status, gaps, and next steps](#status-gaps-and-next-steps).
#1020 moved [Mutable state](#mutable-state-and-incrementality), rule 4's
reason and the tests. The rule catalogue's arguments for rules 1 to 7 and 9
were not re-derived, and the main performance tables are still `6b220c79`'s.

## What it is

### Semantics

- **`AllDifferent(vars)`**: every pair of variables takes distinct values.
- **`AllDifferentExcept(vars, excluded)`**: every pair of variables takes
  distinct values, except that any variable taking a value in `excluded` is
  unconstrained by this constraint. An empty `excluded` is `AllDifferent`.
- **`AllDifferentExceptZero(vars)`**: exactly `AllDifferentExcept(vars, {0})`, a
  constructor rather than a separate implementation.
- **`SymmetricAllDifferent(vars, start = 0)`**: the variables form an
  involution over `[start, start + n)`: each `x[i]` lies in that range, they are
  pairwise distinct, and `x[x[i] − start] = i + start`. The range restriction is
  part of the constraint, not a precondition — `prepare()` narrows every domain
  to it and writes the two bounds into the OPB as model rows.

The degenerate cases, where the frontends and the tests disagree most often:

- **Empty, or one variable**: trivially satisfied. `AllDifferent` has tests for
  both (`run_alldiff_collection_test`, `empty` and `single_var`).
- **All constants**: a tautology if they are distinct and a root contradiction
  if two are equal, both tested (#254).
- **The same variable handle twice** is a legal post and not an exception, and
  what it means differs by class. For `AllDifferent` and `SymmetricAllDifferent`
  it is unsatisfiable (`x ≠ x`), and `install_propagators` installs only a
  root contradiction. For `AllDifferentExcept` it **forces the variable into
  `excluded`**, by an initialiser that removes the runs of other values between
  the excluded ones — and if `excluded` is empty, it is unsatisfiable too.
- **Two views of one variable** (`x` and `x + 1`, or `x` and `−x`) are not a
  repeated handle, so `prepare()` does not divert them: they reach the
  propagator, which treats the positions as independent. This is the one shape
  where the order the deletion batches run in is visible to VeriPB (see rule 3),
  and since #1013 `run_alldiff_aliased_views_test` covers it.
- **An excluded value no variable can take** is dropped from the propagator's
  graph but kept in the encoding: `cake_pb_cp` encodes every listed exception
  value, and dropping one changes the rows' unit-propagation strength, which the
  aliased-pair case turned into a chain-verification failure (#480).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `AllDifferent` | ✓ `fzn_all_different_int` | ✓ `allDifferent`; `decompose` for `allDifferent` as a matrix[^matrix]; `unsupported` over expressions[^xexpr] | ?[^cpmpy] | ✓ `all_different` | the level is not selectable from either frontend[^level] |
| `AllDifferentExcept` | ✓ `fzn_alldifferent_except` | ✓ `allDifferent` with `except`[^xexcept] | ? | ✓ `all_different_except` | |
| `AllDifferentExceptZero` | ✓ via `fzn_alldifferent_except`[^zero] | as above | ? | ✓ as `all_different_except` | |
| `SymmetricAllDifferent` | ✓ `fzn_symmetric_all_different`, passing the index set's start[^sym] | `n/a` | ? | ✓ `symmetric_all_different` | wrong for a non-1-based index set until #997 |

[^matrix]: `buildConstraintAlldifferentMatrix` posts one `AllDifferent` per row
    and one per column. `allDifferent-list` — lists pairwise distinct *as
    tuples* — is a different constraint and is `unsupported`; the retiring
    support matrix already says so.

[^xexpr]: The XCSP3 parser's default `buildConstraintAlldifferent` over a
    vector of expression trees throws "not yet supported", and the binding does
    not override it.

[^cpmpy]: `gcspy` exposes `post_alldifferent`, which posts `AllDifferent` at
    its default level; whether the CPMpy side reaches it was not checked, as
    for every family so far. Neither `AllDifferentExcept` nor
    `SymmetricAllDifferent` has a `gcspy` binding.

[^level]: Both frontends post `AllDifferent` at its default, generalised arc
    consistency. The level is selectable from the C++ API and from the
    examples: `--all-different gac|bc|vc|not-equals` in `ortho_latin`, `sudoku`
    and `magic_square`, `gac|bc` in `golomb` and `langford`, and
    `gac|vc|not-equals` in `seat_moving`. `not-equals` there is the clique
    decomposition, which is [`equals`](equals.md)'s family, not this one.

[^xexcept]: The parser's default `buildConstraintAlldifferentExcept` throws
    "AllDiff constraint with exception is not yet supported", and until #1002
    the binding did not override it, although `AllDifferentExcept` takes exactly
    that constraint's arguments. It now posts `AllDifferentExcept` over the list
    and the excepted values. `xcsp/tests/all_different_except` and
    `all_different_except_values` are cached from ACE, at 73 and 44 solutions.

[^zero]: MiniZinc's `alldifferent_except_0` is defined in the standard library
    as `alldifferent_except(vs, {0})`, which reaches `fzn_alldifferent_except`,
    so a model gets `AllDifferentExcept{vars, {0}}` and never the
    `AllDifferentExceptZero` class. Checked on the flattened model of
    `minizinc/tests/alldifferentexceptzero.mzn`: its one constraint is
    `glasgow_all_different_except_int`.

[^sym]: Until #997, `fzn_symmetric_all_different(x) =
    glasgow_symmetric_all_different(x)`, and `fzn_glasgow.cc` posted
    `SymmetricAllDifferent{vars, 1_i}`. The start was hard-coded, and the
    flattened call carries no index set: FlatZinc arrays are 1-based, so by the
    time the builtin runs the information is gone. The standard library's own
    default is `inverse(x, x)`, which respects the index set. Diffing solution
    sets against MiniZinc's default solver at `6b220c79`:

    | index set | domain | Glasgow | default | in common |
    |---|---|---|---|---|
    | `1..4` | `1..4` | 10 | 10 | 10 |
    | `0..3` | `0..3` | **0** (`UNSATISFIABLE`) | 10 | 0 |
    | `0..3` | `0..4` | 10 | 10 | **0** |
    | `2..5` | `1..6` | 10 | 10 | **0** |
    | `0..3` | `-1..5` | 10 | 10 | **0** |

    The fix is in the front end, as model rewrites always are here: the
    redefinition passes `min(index_set(x))` as a second argument, behind the
    `if length(x) = 0` guard `fzn_circuit.mzn` uses, and `fzn_glasgow.cc` reads
    it. Every row above now agrees with the default solver, and so does an
    index set starting at −2 — checked against a hand-written standard-library
    decomposition instead, since Gecode's native `inverse` errors on a negative
    offset. `minizinc/tests/symmetricalldifferentoffset.mzn`, over `array[0..3]`
    and `array[2..5]`, fails on the old front end; the 1-based
    `symmetricalldifferent.mzn`, the only test before it, never could. See
    [Known limitations](#known-limitations) for what the proof did with it.

### Options

**`AllDifferent::with_consistency(AllDifferentConsistency)`**, where
`AllDifferentConsistency` is `std::variant<consistency::GAC, consistency::BC,
consistency::VC>` — those three and nothing else, so asking for `Tabulated`,
`Dynamic` or `Auto` is a compile-time error. The default is `GAC`, for every
posted class that has the setter. `AllDifferentExcept` and
`SymmetricAllDifferent` have no setter. `AllDifferentExcept` is always
generalised arc consistent. `SymmetricAllDifferent` always runs the same
generalised arc consistent all-different component plus a symmetric channelling
pass, and that conjunction is **weaker** than generalised arc consistency on the
symmetric all-different, which needs non-bipartite matching; see
[symmetric-channel](#rule-symmetric-channel).

| Tag | Installs | Strength |
|---|---|---|
| `consistency::GAC` (default) | the matching-and-SCC propagator, staged behind a value consistent pass on big enough constraints | `GAC` |
| `consistency::BC` | the Hall interval propagator (López-Ortiz, Quimper, Tromp and van Beek) | `bounds(Z)` |
| `consistency::VC` | the value consistent propagator, the same code GAC stages in front of itself | `partial`: removes a fixed variable's value from every other variable, and nothing else |

It selects **propagation strength only and never changes the OPB encoding**.
Measured rather than asserted: on `ortho_latin --all 5` the three levels write
byte-identical `.opb` files. That is also why the `.scp` does not record it —
the chain always rebuilds the default — and the consequence worth knowing is
that **neither the `BC` nor the `VC` arm's proofs ever go through
`cake_pb_cp`**. Their encoding is the one the chain checks; their derivations are
checked by VeriPB only.

**No `consistency::Auto` and no `consistency::Dynamic`: two separate facts.**
The first is a disproved guarantee. The existing `BC`/`GAC` pair cannot be an
optional-interior-pruning pair, the mechanism `Element`'s `Auto` uses, because
bounds consistency is not the generalised arc consistent propagator with the
interior removals switched off: GAC's own holes stay made and later move bounds
BC cannot. [Interior values and optional
pruning](#interior-values-and-optional-pruning) writes that out. So there is no
`Auto` that promises `GAC`'s search.

The second is a design choice nobody has made, and the first fact does not
settle it. Neither tag has to promise `GAC`'s search: `consistency::Dynamic` is
defined as `GAC` where the `GAC` algorithm is cheap on the current domains and
something weaker otherwise, and `consistency::Auto` is a policy that may fall
back on something cheaper. A cost-based policy of either kind would be a
deliberate weakening, and #970's figures are what it would have to trade
against — trees ×1.23 on `magic_square`, ×1.27 on `langford`, ×3.1 on
`ortho_latin`. That is why `BC` is opt-in. It is not a proof that no such
policy could pay, and none is proposed here.

**Two internal thresholds that are not options**, recorded because they change
the propagation counts and the proof shape without changing the search:

- **Staging** (`min_var_val_pairs_for_staged_gac = 256`). When `vars × values ≥
  256`, the generalised arc consistent propagator runs the value consistent pass
  first and defers the matching whenever that pass made a removal. The per-node
  fixpoint is unchanged, so the tree is too; the counts and the order of
  inferences are not. Measured at the time: 1.36× faster at 22 × 33
  (`langford --size=11`), about 2% slower at 10 × 10 (a quasigroup instance).
- **The dense value table** (`min_vals_for_domain_sweep = 24`, and a span of at
  most `64 · values + 1024` slots). Above it, edges are built by sweeping each
  domain and mapping values through a table, rather than probing every value
  with `in_domain`. Same edges, same order.

### Variable kinds and views

Every position is an `IntegerVariableID`, so plain variables, constants and views
are all accepted.

**Constants** are left out of every Hall variable list (`is_constant_variable`),
in both the generalised arc consistent and the bounds consistent arms. That is
correct and deliberate: a constant has no at-least-one of its own to contribute,
and its value is already accounted for by the at-most-ones, which name every
variable. #108 was the crash that happened when they were not left out, and two
fixed rows in `all_different_test.cc` pin it.

**Views** are handled by the proof with no detour. The clique rows are written
over whatever the positions are; an at-least-one for a registered view is stated
over the view's own encoded variable, which is where its atoms live since #904;
and an unregistered view falls back to the per-value at-least-one over the
underlying variable, which is correct and is the one place a view costs more.
The view sweep exercises six positions for `AllDifferent` in the default, `bc`
and (since #999) `vc` lanes, four for `AllDifferentExcept` — whose repeated
variable has a negated and two offset views of its own since #1004 — and
**none** for `SymmetricAllDifferent`, which has no view lane at all.

### Reification

`None.` No class in the family is reified or half-reified. MiniZinc's
`all_different_reif` and friends fall through to the standard library's
decompositions. Nothing in the frontends or the examples asks for one, and a
reified generalised arc consistent all-different is a different algorithm
rather than a wrapper, so this is not a gap worth filing.

### Relation to other families

**Decomposes into this family.** XCSP3's `allDifferent` over a matrix, as one
`AllDifferent` per row and column. MiniZinc's `alldifferent_except_0` via the
standard library, as above.

**Posts as children.** Nothing. `SymmetricAllDifferent::prepare` narrows its
variables' bounds with `define_bound`, which writes an OPB row and installs an
initialiser but posts no constraint.

**Shares code with, and this is the widest coupling in the arc so far.** Four
other families run code from this directory, and a change to it is a change to
them:

| Helper | Also used by |
|---|---|
| `propagate_gac_all_different` | `Inverse`, `ArgSort`; since #1088 it can also report the values every matching takes (an optional out-parameter, `nullptr` for every caller but `Inverse`'s injection form) |
| `justify_all_different_hall_set_needs_value` (since #1088, beside `justify_all_different_hall_set_or_violator` in `justify.cc`) | `Inverse` only: the Hall-set sum without the needed value's own at-most-one |
| `propagate_non_gac_alldifferent` (the value consistent pass) | `Circuit` (both algorithms), `SubCircuit` |
| `define_clique_not_equals_encoding` | `Circuit`, `SubCircuit` |

The idempotence claims are deliberately **not** in the shared helpers: the value
consistent propagator's comment says so, because `Circuit` wraps the same helper
in propagators that do more work in the same run and must not claim. The
triggers are not in the helpers either, which is why #999 could change
`AllDifferent`'s value consistent trigger without touching any other family.

**A caller has to hand `propagate_gac_all_different` the values its variables
take**, and `Inverse` did not: it passed `x`'s own indices where `x`'s values
are `y`'s indices, which coincide only when both arrays start at the same
index. Nothing in `Inverse`'s tests used different starts, and no front end
passed them except XCSP3's two-list `channel`. Fixed in #997, and
`inverse_test` now runs every case again over shifted index sets.

**Presolvers.** None rewrites this family or into it. `AutoTable` and
`DifferenceLogic` post `AllDifferent` in their tests only.

**The disequality clique** is the model-level alternative, and it is
[`equals`](equals.md)'s family rather than this one's. The two write different
OPBs — the clique's `NotEquals` pairs are named for `not_equals` — so they are
two models of one fact, not two strategies for one model. The examples'
`--all-different not-equals` arm is the clique.

**Not a candidate merge, and one correction to the family list.** The list
describes this document as "GAC and VC variants, `AllDifferentExcept`,
`ExceptZero`". It also covers the BC arm, which landed after the list was
written (#970), and `SymmetricAllDifferent`, which lives in this directory,
shares the encoding and the generalised arc consistent propagator, and has no
other home. `GlobalCardinality` generalises `AllDifferent` mathematically but
shares no code with it and has its own Hall reasoning, so it stays in the
counting family.

## The proof model

### OPB encoding

**`AllDifferent`**, and the clique half of `SymmetricAllDifferent` — Encoding
Procedure 3.9 of the thesis, one selector and two half-reified strict
inequalities per pair:

```
for each i < j:
    x[id][i_j]                                        (a flag in the OPB)
    @c[id][<i>lt<j>]:   ¬x[id][i_j]  ⇒  vars[i] − vars[j] ≤ −1
    @c[id][<i>gt<j>]:    x[id][i_j]  ⇒  vars[j] − vars[i] ≤ −1
```

**Definitional**: the rows say that each pair differs, which is what the
constraint means, and nothing more. `n(n − 1)` rows and `n(n − 1)/2` flags, each
row over the two variables' bits and the flag, so the encoding is **quadratic in
the number of variables and logarithmic in domain width** — it never names a
value. As written, on `ortho_latin`:

```
@c[_51][0lt1] -1 i[_1][b0] -2 i[_1][b1] -4 i[_1][b2] 1 i[_4][b0] 2 i[_4][b1] 4 i[_4][b2] 8 x[_51][0_1] >= 1;
```

**`AllDifferentExcept`** replaces the selector's guard with a conjunction: each
half is reified on the selector *and*, for every excluded value `s`, both
`vars[i] ≠ s` and `vars[j] ≠ s`. Still definitional, and still `n(n − 1)` rows,
but each carries `2|excluded|` more literals, and those are **equality**
literals, which is what keeps it off the strict chain. Three differences from
`AllDifferent`'s encoding that a reader of the OPB will trip on: the selector is
an unnamed `create_proof_flag("notequals_except")` rather than `x[id][i_j]`; its
polarity is the other way round (true means `vars[i] < vars[j]`); and the rows
are unlabelled. Encoded from the **original** excluded list, not the pruned one
the propagator uses (#480).

**`SymmetricAllDifferent`** is three parts: up to two bound rows per variable
from `define_bound` (only where the declared domain is wider than
`[start, start + n)`), two channelling clauses per pair `i < j` —
`x_i ≠ j + start ∨ x_j = i + start` and its mirror — and the clique above.
Definitional as the constraint is stated, with one caveat worth recording: the
clique is **implied** by the channelling and the range (two variables sharing a
value `j` would both force `x_j`), so the model states a consequence. It is the
consequence the Hall justifications cite, which is why it is there.

### Labels

`AllDifferent`'s rows carry `@c[id][<i>lt<j>]` and `@c[id][<i>gt<j>]`, cake's own
names (#354), and **no rule cites them**. The justifications reach the rows by
unit propagation over the variables' literals, so the labels exist for
`opbdiff` to match against cake and for nothing else. `SymmetricAllDifferent`'s
clique rows carry the same labels under its own constraint id; its channelling
and bound rows, and every `AllDifferentExcept` row, are unlabelled.

### Cake conformity

| Class | Chain mode | Cases | Where it diverges |
|---|---|---|---|
| `AllDifferent` | `strict` | `all_different_sat` (three over `0..3`), `all_different_unsat` (four into three) | nowhere: byte-matches cake since #354 |
| `AllDifferentExcept` | `none` | `all_different_except_sat`, `all_different_except_unsat`, and since #1004 `all_different_except_duplicate` (two repeated variables) | the excluded-value literals are equality literals, which diverge from cake's eager variable encoding (#358) |
| `SymmetricAllDifferent` | `none` | `symmetric_all_different_sat`, `symmetric_all_different_unsat` | the bit/eq encoding's labels; the boundary pins cake's encoder needs are arranged as persistent proof lines |

Two things no case exercises. **The `BC` and `VC` arms never reach the chain**:
the `.scp` does not record a consistency level, so `cake_pb_cp` always rebuilds
the default. Their encoding is the one checked; their derivations are checked by
VeriPB alone. And **no case is wider than four variables or has a hole**, so the
chain has never seen a Hall justification over a holey domain — which is the
only kind whose reason states runs.

### Proof-time state

- **At the root, nothing** for `AllDifferent` and `AllDifferentExcept`.
  `SymmetricAllDifferent` infers its range at the root (the `define_bound`
  initialisers, under the `InitialBound` hint). It also had an initialiser
  meant to emit every value's at-most-one at the root, dead since it was added
  and deleted by #1001; see [Proof-logging gaps](#proof-logging-gaps).
- **Lazily, per value: an at-most-one**, the first time a Hall argument needs
  that value. `C(n, 2)` pairwise `rup` clauses at `ProofLevel::Temporary`,
  folded into one cardinality line by `recover_am1_from_pairs` at
  **`ProofLevel::Top`** — so the clauses are deleted and the fold survives for
  the rest of the proof. The line number is cached in a
  `map<Integer, ProofLine>` the propagator owns, and it spans **all** of the
  constraint's variables, not only the Hall set, so one line serves every later
  Hall set that mentions the value.
- **Lazily, per variable: an at-least-one**, owned by the names-and-IDs tracker
  and cached there. It names the values the justification singles out, and
  covers the rest of the definition range either one term per value or, above
  100 values of definition range, one range literal per run (#939's width
  gate).
- **Per inference: one `pol`** summing the Hall variables' at-least-ones and the
  Hall values' at-most-ones, at `ProofLevel::Current`, then the conclusion by
  RUP.
- **Naming.** None of this is named. The at-most-ones and at-least-ones are
  found by line number, so an external tool rebuilds them rather than locating
  them: the at-most-one for a value is determined by the constraint's variable
  list and the value, and the at-least-one by the variable and the values it
  singles out. The Hall set itself is **not on the wire** — the hint is
  `(constraint_id) (subhint hall)` — but it does not need to be, because the
  reason names exactly the Hall variables and states their domains, from which
  the Hall values follow.
- **In the OPB versus in the proof.** The selectors are in the OPB. There are no
  proof-only auxiliaries. Each selector is determined by unit propagation on a
  solution — true exactly when `vars[i] > vars[j]` — as `solx` requires.
- **Proof-only data that dangles with proofs off**: the at-most-one map, which
  simply stays empty, and the `hall` hint's two raw pointers into it and into the
  variable list. Both are constraint-owned and outlive the search, which the
  hint's comment relies on for replay at backtrack time.

## The implementation

### Initialisation and global data

**`AllDifferent::prepare`** sorts the variables, which is how it finds a
duplicated handle, and then does level-specific work:

- **`GAC`** builds the *compressed value set* — the union of the initial
  domains, in first-seen order, which fixes each value's index in the
  propagator's graph. That walks every initial domain a value at a time, so it
  is `O(Σ |D|)`, and it is the family's install-time cost proportional to
  domain size. Until e45b8e1a it was worse than that: membership was a linear
  scan of what had been collected so far, so `O(values × distinct values)` —
  three variables over `0..10⁵` spent 6.6 s here and `0..10⁶` did not finish.
  It is a `std::set` now, and still walks every value, which is what keeps the
  arm a `KnownTrip`. It also takes the staging decision, which needs the set's
  size.
- **`VC`**, and **`GAC` when staged**, register a backtrackable list of the
  variables whose values the value consistent pass has not yet pushed through
  the clique: every variable at the start, a fixed one included. Until #999 a
  variable already fixed here was left out, and since a variable leaves the list
  only once its value has been removed from the others, that value never was —
  at `VC`, a wrong answer; see rule 4. Skipped otherwise, because an unused
  constraint state is still saved and restored at every node.
- **`BC`** does nothing at install beyond the sort.

**`AllDifferentExcept::prepare`** additionally prunes the excluded list to values
some variable can take (an `in_domain` probe per variable per excluded value),
finds the runs of duplicated variables, and builds the compressed value set
without the excluded values — the same walk, with a linear `find` in the excluded
list per value, which is `O(Σ |D| · |excluded|)` and harmless because the
excluded list is the model's and not domain-sized. Since #1004 the walk skips a
repeated variable altogether: its initialiser puts it inside the excluded set
before anything propagates, so none of its other values can be matched, and
walking a wide one was most of what #988 measured.

**`SymmetricAllDifferent::prepare`** detects duplicates and calls `define_bound`
twice per variable, which writes the range into the OPB and installs a root
initialiser to infer it. Its value set is `[start, start + n)` by construction,
so it builds nothing proportional to a domain.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| generalised arc consistent, maybe staged | `on_change` every variable | derived: **every variable** | 1, 2, 3, and 4 as stage 1 | `AllDifferent` at `GAC` | claims | no |
| bounds consistent | `on_bounds` every variable | derived: **nothing** | 5, 6 | `AllDifferent` at `BC` | claims | no |
| value consistent | `on_instantiated` every variable | derived: **nothing** | 4 | `AllDifferent` at `VC` | claims | no |
| except | `on_change` every variable | derived: **every variable** | 1, 2, 3 | `AllDifferentExcept` | never claims | no |
| symmetric | `on_change` every variable | derived: **every variable** | 1, 2, 3, 9 | `SymmetricAllDifferent` | never claims | no |
| duplicate contradiction, initialiser | — | nothing | 7 | a repeated handle in `AllDifferent` at any level, in `SymmetricAllDifferent`, or in `AllDifferentExcept` with nothing excluded | n/a | one shot |
| duplicate forcing, initialiser | — | nothing | 8 | a repeated handle in `AllDifferentExcept` with something excluded | n/a | one shot |
| range, initialisers | — | nothing | — | `SymmetricAllDifferent` over a domain wider than its range | n/a | one shot |

**The generalised arc consistent propagator claims idempotence, and the argument
survives staging.** One call prunes to the closure — what survives is exactly the
union of maximum matchings — and stage 1 cannot break the claim, because the
closure has already removed every value a newly fixed variable would push through
the clique. A staged call that deferred returns `Enable` *without* the claim, on
purpose, so the removals it made requeue it at the round boundary; deferral only
happens when stage 1 strictly shrank a domain, so the matching cannot be starved.
The two `AllDifferentExcept` and `SymmetricAllDifferent` wrappers of the same
propagator make no claim, and nobody has asked whether they could: the except
propagator's phantom vertices and the symmetric one's channelling pass would each
need their own argument.

**The bounds consistent propagator claims idempotence** because it loops until a
sweep writes every bound exactly where it put it. One lower pass and one upper
pass reach the fixpoint of the bounds they read, so it re-sweeps only when a
written bound *snapped past a hole* — #970's main speed-up, checked against a
brute-force oracle on 100,000 instances.

**The value consistent propagator wakes on instantiation only** (#999). It reads
nothing but `optional_single_value`, and until #999 it was registered
`on_change`, because it shared the `triggers` object the generalised arc
consistent arm builds. That cost twice. Every interior removal on any of its
variables woke it to scan its unassigned list and find nothing, which is what
#819 found for `NotEquals`. And because hole sensitivity is *derived* from the
triggers, it declared that holes in every variable affected it, which they
cannot, since removing a value from strictly between the bounds never fixes a
variable; so an `AllDifferent` at `VC` kept another constraint's optional
pruning alive for nothing. It now builds its own `Triggers`. The staged
generalised arc consistent propagator runs the same pass as its first stage and
keeps `on_change`, since its second stage reads the interiors.

The same tree under the example's own brancher, which reads only domains and
degree, with 23% fewer calls; see [CPU performance](#cpu-performance). **Under
dom-wdeg the tree changes**: 626 to 560 nodes on `ortho_latin --all 5`, the same
eighteen solutions. A wake that fixes nothing infers nothing, so the per-node
fixpoint is unchanged; what moves is the order propagators run in, and so which
one detects a failure and is weighted for it.

**Self-disabling.** None. The duplicate initialisers are one-shot by nature.

### Mutable state and incrementality

**Backtrackable**: the unassigned list, a flat `vector` so that the per-node copy
is one allocation and a `memcpy`. Order is not significant, and removals
swap-and-pop.

**Not backtrackable, and deliberately so**: the generalised arc consistent
propagator's *scratch* — every buffer it uses, `clear()`ed rather than
reallocated, so capacity ratchets up to the biggest wake and stays (#522, #523).
Most importantly **the matching**, kept across wakes and even across backtracks
(#526). That is sound without restoring anything, because any set of matched
pairs whose edges still exist is a valid partial matching whatever search state
it came from: `build_matching` revalidates each pair against the current edges,
drops the stale ones, and repairs by augmenting paths. The deletions are the
edges in no maximum matching, which does not depend on which maximum matching was
found, so the search is unchanged; the proof's shape can differ. Also kept: the
value-index lookup table, built once, since the value set is fixed.

**The single-value reason cache** is not backtrackable either, and never changes
once built: one prebuilt `ExactSingleValue` per plain variable in the scope,
built at install time and held by the value consistent propagator and by staged
GAC's first stage. It is found by a binary search over the scope's sorted
variable IDs, paid once per newly fixed variable, which the pass then checks
against every unassigned variable anyway. It is sized by the scope. Until #1020
it was a table indexed by variable ID across the span of the scope's IDs (#1008),
which over the columns of a row-major `n × n` Latin square is `n³` reasons: 194
MB at `n = 100`, with proofs off, before any search. #1020 changes no search tree
and no proof: the `.opb` and `.pbp` for `sudoku-sixteen` are byte-identical
before and after it, at both `GAC` and `VC`.

**Recomputed per call, and what maintaining it would buy.** The strongly
connected components, every wake, into reused buffers — **#522's remaining
item**. Keeping the decomposition across the search and reprocessing only the
component a deletion touches is the textbook incremental form; the persistent
matching is its prerequisite and is done. Contracting matched pairs to run
Tarjan over variables only would renumber the components and so change the
proof's shape, which is why #526 left it for this. Either change has to run the
deletion batches in an order that puts each component after every component it
reaches: rules 2 and 3 both depend on it, and #1013 checks it. Tarjan's exact
numbering is not needed, only that property. The bounds consistent
propagator re-sorts every call, but by insertion sort from the previous call's
order, which is nearly sorted already.

### Interior values and optional pruning

**Offers.** `None.`, and this family is the clearest case in the arc of **why
a bounds consistent arm is not automatically a fallback**. It has both arms, a
`consistency::BC` that reads only bounds and a `consistency::GAC` that also
removes interior values, and it looks exactly like `Element`'s pair. It cannot
be paired, and #970 established why by measurement before
[optional-interior-pruning.md](../optional-interior-pruning.md) had a name for it.

The pair's **first promise** is that the two members differ only in the
targets' interiors: wherever the fallback has nothing left to do, the pruning
could remove nothing but interior values. For `AllDifferent` that holds on
hole-free domains — bounds(Z) consistency leaves exactly the bounds generalised
arc consistency would — and fails the moment a domain has a hole, because arc
consistency can use a hole to close a Hall set:

```
x ∈ {1, 3},  y ∈ {1, 3},  z ∈ {1, 2, 3}
GAC:  {x, y} is a Hall set on {1, 3}, so z = 2    — z's bounds move from [1, 3] to [2, 2]
BC:   [1, 3] holds three variables and three values, so nothing moves
```

That is a **bound**, which anything can observe, so the promise is broken. And
it is broken even in a model where nothing else ever makes a hole, which is the
part that is easy to miss: **the holes arc consistency makes itself stay
made**, and later in the search they move bounds that bounds consistency cannot.
So the analysis cannot rescue it either — there is no model property to check
that would make the switch safe, short of the constraint never having pruned an
interior value, which is the thing being decided.

*Measured elsewhere, #970's own figures, not to be put beside this document's.*
Over whole searches, `BC`'s trees against `GAC`'s: ×1.23 nodes on
`magic_square`, ×1.27 on `langford`, ×3.1 on `ortho_latin` — reproduced here at
×3.12, see [CPU performance](#cpu-performance) — and generated Sudoku puzzles of
16, 25 and 36 that `GAC` solves at the root and `BC`, `VC` and the disequality
clique time out on in 53 of 54 runs. Only on Golomb rulers, where nothing but
the all-different makes a hole and the search branches smallest-first on
variables it does not constrain, do the two arms agree on the shape of the
search: the same recursions at every size measured, and at `n = 9` and
`n = 10` also the same solutions in the same order, failures and depth. They
still differ in propagator calls (see [CPU performance](#cpu-performance)).
That is the shape under which the pair's promise would hold, and it is rare
enough that an opt-in tag is the right answer.

The contrast with `Element` is exact and worth stating as such. Over a
**constant** array, `Element`'s range at a fixpoint *is* the union's range: a
hole in the result can move the result's own bound, but the range propagator
re-runs after a bound snaps past a hole and gets there too. What it cannot see
is a hole in *another* variable — which is why a variable-array `Element` is not
paired, since a hole in an entry moves the result's bound. `AllDifferent` is
that second case everywhere: a Hall set's support is shared between variables,
so a hole in `x` moves `z`'s bound. **A pair is legal only if no variable's
holes can move another variable's bounds under the pruning**; holes feeding
back into a target's own bounds are fine, because a fallback that re-runs after
snapping sees those too.

**Observes.** The generalised arc consistent, except and symmetric propagators
are genuinely hole-sensitive on every variable — a hole in any of them can
change the matching — so an `AllDifferent` at its default keeps alive any
optional pruning whose target it constrains. That is the expected answer for a
domain consistent global, and correct.

The bounds consistent and value consistent arms are hole-transparent, derived
from `on_bounds` and `on_instantiated` and right: they read nothing else. So
**an `AllDifferent` at `BC` or `VC` over an `Element`'s result lets that element
drop to `BC` too**, which is where the two families' options compose.
`element_auto_test` pins the verdict at each level: the pruning is kept for
`GAC` and switched off for `BC` and `VC`.

The value consistent arm was the finding. Until #999 its triggers
**overstated** its hole sensitivity — derived as every variable, truly none — so
an `AllDifferent` at `VC` kept other constraints' prunings on when nothing here
could observe them. Over-reporting is never unsound; it costs time elsewhere,
in a pruning kept on that could have been switched off. #902's own audit left
overstated declarations alone on purpose, with the one exception of the
slack-watched linear inequality, since long sums are what an element result
tends to feed. This one came free with fixing the wakes.

### Robustness and limits

**Unbounded domains.** Only the generalised arc consistent propagator needs an
explicit value set, at install: `BC` reads bounds and `VC` reads fixed values.
The except class's forcing initialiser walked a repeated variable's domain until
#1004 and no longer does. So an unbounded domain is a width question; see
[Interval efficiency](#interval-efficiency).

**Negative values and zero.** Fine, and covered: the random data in
`all_different_test.cc` is drawn from `[-10, 10]`, in every position, in both
lanes. Zero is special only to `AllDifferentExcept`, and only by the model's
choice; `ExceptZero` is a constructor.

**Degenerate shapes.** All covered by tests, and listed under
[Semantics](#semantics): empty, one variable, all constants distinct, two equal
constants, and a repeated handle at every level (`run_alldiff_dup_test` runs all
three levels over three shapes). **What is not tested is a repeated handle
reaching the propagator** — it never does, since `prepare` diverts it — so the
duplicate tests say nothing about any propagator's behaviour. Two views of one
variable do reach it, and since #1013 `run_alldiff_aliased_views_test` is the
one case that posts them. Until #999 the
`vc` one was the *only* place `consistency::VC` appeared in the family's test
file, which is how the arm's fixed-at-post bug went unseen. See
[Tests](#tests).

**Overflow.** The value-index arithmetic is `(val − min).as_index()` over a span
the dense table has already bounded, and the bounds consistent propagator's
`s.bounds[nb] + 2_i` and `ub + 1_i` go through `Integer`'s checked operators,
which throw `IntegerOverflow` rather than wrap. `SymmetricAllDifferent`'s
`start + Integer(n) − 1_i` likewise. Not separately probed; the mechanism is the
one `equals` verified UBSan-clean.

### Interval efficiency

**Three arms, three different answers, and one hidden site.** The bounds
consistent and value consistent arms are fine at any width. The generalised arc
consistent arm is per value by the nature of the algorithm, has a weaker arm to
fall back on, and is correctly a `KnownTrip`. And `AllDifferentExcept` had a
per-value loop the audit lane never reached, which since #1004 goes a run at a
time and is a `Clean` row.

**1. The propagation side.**

- **Generalised arc consistency is genuinely per value**, and that is not a bug
  to fix: Régin's algorithm wants a vertex per value. Each wake builds the value
  graph's edges either by sweeping every domain (`for_each_value_immutable`,
  above 24 values) or by probing every compressed value with `in_domain`, and
  keeps a `vars × values` bitmap. Install builds the compressed value set by
  walking every initial domain. So this is the hazard large-domains.md calls
  **H1c plus H2** — a genuine per-value scan and an install-time precompute —
  and the policy's answer is the weaker arm, which exists twice over.
- **Bounds consistency is width-independent.** It reads `bounds()` and nothing
  else, sorts `n` intervals, and sweeps them with union-find. Nothing is
  proportional to a domain.
- **Value consistency is width-independent.** It reads `optional_single_value`
  and walks the unassigned list.
- **`AllDifferentExcept`'s duplicate forcing was per value, and it was the one
  hidden site** (#988). For a variable posted twice it removed every value not
  in `excluded`, one `infer(x != v)` at a time, over `each_value_immutable`:
  large-domains.md's **H1a**, a per-value spelling of "the domain minus a small
  given set". Since #1004 it takes `each_interval_minus` against the excluded
  values and makes one `infer_not_in_range` per run.

  **The forcing loop was not most of the cost, though.** Fixed on its own, it
  moved the measurement below from 7.99 s to 7.29 s at width 10⁷, with memory
  unchanged: `prepare()` was walking the repeated variable's domain as well, to
  build the generalised arc consistent value set, and #1004 stops that too (see
  [Initialisation](#initialisation-and-global-data)). Measured through
  `glasgow_scp_solver --all` on `all_different_except (X X Y) (0)`, `X` over
  `0..w`, `Y` over `0..3`, proofs off, one core, fataepyc-09:

  | width | before #1004 | after |
  |---|---|---|
  | 10³ | 0.00 s, 4.7 MB | 0.04 s, 4.7 MB |
  | 10⁶ | 0.69 s, 137 MB | 0.00 s, 4.7 MB |
  | 10⁷ | 8.03 s, 1.33 GB | 0.00 s, 4.7 MB |
  | 10⁹ | not run: linear, about 130 GB | 0.00 s, 4.7 MB |

  Four solutions, `X = 0`, at every width. The audit's own run of the "before"
  column, on the other socket, measured 0.71 s and 8.02 s at 10⁶ and 10⁷.
- **`SymmetricAllDifferent`'s channelling pass** walks each variable's domain,
  but `prepare` has narrowed every domain to `[start, start + n)`, so the walk is
  bounded by `n`.

**2. The reason side.**

- **Hall reasons are lazy and per run.** Both generalised arc consistent shapes
  hand back a `LazyReasonOver` the Hall variables' `generic_reason`, materialised
  only if something reads it; `generic_reason` states each variable's bounds and
  holes, and since #935 finds the holes by reading the domain's intervals rather
  than testing every value. So the output and the work are both per run.
- **The Hall *search* is guarded since #1000.** `prove_deletion_using_sccs`
  walks a strongly connected component to find the Hall set,
  `prove_matching_is_too_small` grows a violator along alternating paths, and
  both build the hint's two vectors. Until #1000 they did so on every wake that
  deleted or failed, with proofs off too, for a hint and a reason nothing read.
  Now both run only when `logger || want_reasons()`, as the bounds consistent
  arm (#970) always did, and otherwise the inference goes in bare. That was
  never a width cost — the walk is over the value graph, which is already per
  value — but it was the pattern #864 and #907 found in `equals` and
  `comparison`: work for a proof, paid with proofs off. Measured under [CPU
  performance](#cpu-performance).
- **Bounds consistent reasons** are two bound literals per Hall variable plus one,
  built only when `logger || want_reasons()` for a bound push. The contradiction
  path is guarded on `logger` alone. The two are equivalent today — only the
  proof-logging tracker materialises reasons — but not by the contract
  `want_reasons()` states, which anticipates conflict-directed search wanting
  reasons without a logger. A one-word inconsistency, not filed.
- **One-literal reasons built unconditionally**: the symmetric channelling
  pass's `x_v ≠ i`. Cheap, and on a constraint nothing benchmarks. The
  trivial-SCC deletion's `m == d` was one too, until #1000 moved it behind the
  same guard as the Hall search.

**3. The proof side.**

- **Every per-value proof loop in the Hall justifications is bounded by the
  number of variables, not by any width**, and the argument is worth writing down
  because the loops look alarming. A Hall set has exactly as many values as
  variables and a violator fewer, so the at-most-ones — one per Hall value — are
  at most `n`. The bounds consistent form's two `for (v = lo; v <= hi; ++v)`
  loops walk a Hall interval, which by definition holds at least as many
  variables as values, and each Hall variable's bounds, which lie inside it. So
  both are at most `n` long however wide the domains are.
- **What they cost is cubic in `n`**, and that is #944: each at-most-one is
  built from `C(n, 2)` pairwise clauses. See [Proof
  performance](#proof-performance) for the measurement.
- **The at-least-ones sit behind #939's width gate**: above 100 values of
  *definition* range, a cover — the values the justification singles out as
  their own atoms, the rest as one range literal per run — and below it, one term
  per value, which is cheaper there. `AllDifferent/confined` in the proof-size
  lane pins the wide side at **132 lines, flat** from 10³ to 10⁵.
- **Each caller names only the values its variable can still take**, not the
  whole Hall set, so the residue is exactly the complement of the domain and the
  reason discharges it by construction.
- **The except duplicate forcing's proof was per value too, and per run it
  needs nothing at all** (#1004). Per value it was two `rup` lemmas and the
  conclusion for every value removed, plus the eleven lines defining each
  value's equality atom: exactly `14w + 78` lines on the instance above,
  14,078 at 10³ and 140,078 at 10⁴, and 0.61 s and **90.2 s** of VeriPB. The
  audit asked whether the two lemmas would carry over to a range literal, since
  a range literal names order atoms and the duplicate rows are written over
  equality atoms. They are not needed: with `x` inside a run, unit propagation
  falsifies every excluded value's equality atom down the chain of `x`'s order
  atoms, and the pair's two rows then force the selector both ways, so each run
  is RUP from the rows alone. The whole proof of that instance is now **91
  lines at every width up to 10⁹**, verifying in about 20 ms.
- **No form here is chosen by the kind of a variable.** The one fork on kind is
  the at-least-one for an *unregistered* view, which falls back to per value over
  the underlying variable because the singled-out values would otherwise need
  mapping through the view to be named — a representation constraint rather than
  a cost choice.

**4. Where the family stands in the audit lane.**

| Row | Outcome | What it reaches |
|---|---|---|
| `AllDifferent` | `KnownTrip` | the install-time value set, which walks `0..10⁹` |
| `AllDifferent/BC` | `Clean` | the sweep; four identical wide domains, so no Hall interval |
| `AllDifferent/VC` | `Clean` | the unassigned scan |
| `AllDifferentExcept` | `KnownTrip` | the same value set, with the excluded values filtered |
| `AllDifferentExcept/duplicate` | `Clean` | the forcing, over a wide repeated variable with a narrow partner; trips before #1004 |
| `SymmetricAllDifferent` | `NoWidePosition` | nothing: the range is `n` values |

And two rows in `TEST_CASE("Large domain proof sizes")`, which runs in the
ordinary suite. `AllDifferent/confined`, three variables confined to two values
inside `0..10⁴`, 132 lines; it cannot be checked at 10⁹ — not because of the
proof, but because the generalised arc consistent setup still wants a vertex per
value, which is the `KnownTrip` above. And since #1004
`AllDifferentExcept/duplicate`, a repeated variable over `0..10⁴` forced into
`{5}`, 124 lines against 140,108 before.

The `AllDifferent` row's comment was stale — it blamed "a linear find per
value", which e45b8e1a replaced with a set — and #1004 corrects it. The row
still trips, and correctly, on the walk itself.

**Which axes those rows do not vary**, and here the gaps are real:

- **A repeated handle is reached since #1004**, by
  `AllDifferentExcept/duplicate`. Before it no row posted one, so the forcing
  loop — the one width-proportional site in the family that was not by design —
  was reached by no row, although, iterating through `each_value_immutable`,
  it was counted and would have tripped at once.
- **No bounds consistent row reaches a Hall interval.** Four identical wide
  domains contain no interval holding more variables than values, so neither the
  push nor its justification runs. The justification is bounded by `n` by the
  argument above, so this is a gap in the evidence rather than a suspected
  hazard.
- **No row is holey, and none wraps a variable in a view.** For the `KnownTrip`
  arms that adds nothing, and for the two clean arms there is no fork on
  representation to reach — bounds and fixed values read the same through a
  view.
- **The proof-size lane has no `BC` or `VC` row**, so the bounds consistent
  arm's at-least-ones over a wide definition range are pinned by nothing.

## Inference catalogue

Nine rules. Three belong to the generalised arc consistent propagator, which
`AllDifferent` at `GAC`, `AllDifferentExcept` and `SymmetricAllDifferent` all
run; one is the value consistent pass, which is `VC`'s whole propagator and the
staged `GAC`'s first stage; two are the bounds consistent arm's; two handle a
repeated variable; and one is `SymmetricAllDifferent`'s channelling.

Five facts hold across them and are not repeated in each entry.

**What licenses them.** The Hall set rules are the thesis's own: **JP 3.16
(All-Different infeasibility)** and **JP 3.17 (All-Different propagation)**,
which sum an at-least-one per Hall variable (RUP by **Theorem 3.2**) and an
at-most-one per Hall value (recovered from pairwise clauses by **Theorem 2.3**),
with **Lemma 3.6** saying why a strongly connected component of the residual
graph yields a Hall set, and **Lemmas 2.1 and 2.2** licensing the saturation
that turns the sum into the conclusion. The single-value removals are **JP 3.1
(Not-Equals)** against one pair's rows, whose shape is exactly Encoding
Procedure 3.2's. The bounds consistent rules, the duplicate forcing and the
channelling are ours.

**How we depart from JP 3.16 and 3.17**, which an external justifier has to
know, because each changes what it can find in the proof:

- **The at-most-ones span every variable of the constraint, not just the Hall
  set**, and are emitted once per value at `ProofLevel::Top` and reused by every
  later Hall set that mentions that value. The thesis builds one over the Hall
  set per justification. The extra terms are what JP 3.17 needs anyway — the
  deleted literals appear in them — and for a violator they are harmless, since
  they only make the summed left-hand side more negative.
- **The at-least-ones are not RUPs under the reason.** They are the
  names-and-IDs tracker's cached, unconditional statements that a variable takes
  one of its values, naming the values the justification singles out and
  covering the rest of the definition range; the reason discharges that residue
  at the final RUP instead.
- **The reason is each Hall variable's own domain** — its bounds and holes, via
  `generic_reason` — rather than the thesis's `R`, which is built from the Hall
  values' overall range and the holes inside it.

**The wire inventory is a closed list of four forms.**

| Wire form | Hint type | Means | Rules |
|---|---|---|---|
| `all_different:((constraint_id N))` | `hints::AllDifferent` | one RUP | 3, 4, 7, 9 |
| `all_different:((constraint_id N) (subhint hall))` | `hints::AllDifferentHall` | a Hall set or violator over the value graph | 1, 2 |
| `all_different:((constraint_id N) (subhint hall_interval))` | `hints::AllDifferentHallInterval` | a Hall interval or violator over bounds | 5, 6 |
| `all_different_except:((constraint_id N))` | `hints::AllDifferentExcept` | one RUP | 7, 8 |

**The hint's name does not identify the class**, and a justifier dispatching on
it alone will be wrong. `propagate_gac_all_different` builds its own hints, so
every Hall set and forced value from an `AllDifferentExcept` or a
`SymmetricAllDifferent` — and from `Inverse` and `ArgSort`, which run the same
code — arrives as `all_different`. Only the two duplicate paths carry
`all_different_except`, which makes the `hints::AllDifferentExcept` comment's
claim that "its name lets the justifier dispatch on the right family" true of
those two and no others. What does identify the class is the constraint id,
through the `.scp`, and that is what an external tool should key on — the
`AllDifferentExcept` encoding in particular differs, and the Hall reason carries
a `v ≠ s` per excluded value.

**The Hall justifications read `state`.** `justify_all_different_hall_set_or_violator`
asks `state.in_domain` which Hall values each variable can still take, and the
interval form asks `state.bounds`. That is the invariant #870 removed from
`equals` and described as holding "everywhere else", and it does not hold here.
It is **safe today**: at `AssertionLevel::Off`, `infer_all` snapshots the reason
and emits the steps in one go, before any literal in the batch is applied, so
the two reads see the same domains; at every other level no steps are emitted at
all. It would stop being safe under a hints-only mode that re-emitted
justifications later, and the fix is the one #885 made — read the reason, which
states every Hall variable's domain already. Not filed; recorded here and in
[Next steps](#next-steps).

### Rule: hall-violator

- **Infers** — a contradiction.
- **Fires when** — the generalised arc consistent propagator's maximum matching
  leaves a variable uncovered. Runs under `AllDifferent` at `GAC`, in
  `AllDifferentExcept` and in `SymmetricAllDifferent`.
- **Strength** — `GAC`: this is the closure detecting infeasibility.
- **Algorithm** — the matching is kept across wakes and repaired, greedily and
  then by breadth-first augmenting paths, so a wake that leaves most of it
  intact costs little. When a proof or reasons are wanted, a violator is then
  grown from the first uncovered variable along alternating paths
  (`prove_matching_is_too_small`), adding each value's matched variable until
  the neighbourhood closes; otherwise, since #1000, the contradiction goes in
  bare. `O(edges)` per step of that growth, and edges are `(variable, value)`
  pairs, so all of it is in **values**. Régin (1994) for the matching; Hall
  (1935) for the argument.
- **Why it is true** — Hall's marriage theorem: a set of variables whose domains
  together hold fewer values than there are variables cannot take distinct
  values.
- **Proof technique** — `pol`, then `RUP`, by **JP 3.16**, with the
  departures listed above. The `pol` sums one at-least-one per Hall variable and
  one at-most-one per Hall value; after the reason restricts it, the left-hand
  side cancels to nothing and the right-hand side is `|W| − |N(W)| ≥ 1`.
  Preconditions: the encoding is Encoding Procedure 3.9's, so that every
  pairwise at-most-one clause is JP 3.1 against one pair; and the matching is a
  maximum one, or the uncovered variable would not be in a violator.
- **Reason** — `generic_reason` over the Hall variables that are not constants,
  plus `v ≠ s` for each Hall variable and each excluded value `s` under
  `AllDifferentExcept`. A `LazyReasonOver`, materialised only if read. Minimal
  for the violator found, which is not necessarily the smallest one — it is
  whichever one the alternating paths from the first uncovered variable reach.
- **Assertion** — the negated reason as a clause, with no conclusion literal.
- **Hint** — `hints::AllDifferentHall`: `hall_vars`
  (`vector<IntegerVariableID>`, the violator), `hall_vals` (`vector<Integer>`,
  its neighbourhood), `all_vars` (`const vector<IntegerVariableID> *`, the
  scope, which the at-most-ones span) and `value_am1_constraint_numbers`
  (`map<Integer, ProofLine> *`, the at-most-one cache). None of it reaches the
  wire.
- **Offline reconstructibility** — `hinted`. The Hall variables are exactly the
  variables the reason names, the Hall values are the union of their domains as
  the reason states them, and the scope comes from the constraint id through the
  `.scp`. Nothing solver-side is needed.
- **Proof size** — per inference, one `pol` and one RUP, plus whatever has not
  been emitted before: an at-least-one per Hall variable (cached per variable,
  or per variable and cover) and an at-most-one per Hall value, at `C(n, 2)`
  pairwise clauses and a fold each (cached per value). So the first violator over
  `k` values costs about `k · C(n, 2)` lines and later ones reuse them — **cubic
  in `n` in the worst case**, never in any width. Measured under [Proof
  performance](#proof-performance).
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No mutation lane exists for this family.

### Rule: hall-set-deletion

- **Infers** — `x ≠ d` for every edge in no maximum matching, batched by the
  strongly connected component its value lies in.
- **Fires when** — the matching covers every variable, and some edge is neither
  matched, nor inside one component, nor on an alternating path from an
  unmatched value; and the Hall set behind it has a variable that is not a
  constant. Same propagators as rule 1.
- **Strength** — `GAC`.
- **Algorithm** — Régin's: the components of the residual graph by an iterative
  Tarjan, rebuilt **every wake** (#522's remaining item), plus a sweep from the
  unmatched values that is skipped outright when there are exactly as many
  values as variables. Then, per component with deletions and only when a proof
  or reasons are wanted, a walk inside it from one deleted value
  (`prove_deletion_using_sccs`) to collect the Hall set, by Lemma 3.6; otherwise,
  since #1000, the batch goes in bare. `O(variables + edges)`, in values.
- **Why it is true** — a Hall set uses every value in its neighbourhood, so no
  variable outside it can take one.
- **Proof technique** — `pol`, then `RUP` per deleted literal, by **JP
  3.17**, with the departures above. One `pol` per component serves every
  deletion in it: `infer_all` with `ThenRUP::Yes` emits the steps once under a
  temporary level and RUPs each literal inside it.
- **Reason** — as rule 1, over the Hall set; pinned once for the whole batch.
  **It is only sufficient because the batches run sinks first.** The Hall set
  is the component's own variables and values, and the reason is their domains
  read from the state, so it describes a Hall set only once every edge from the
  component into a downstream component has been deleted, by an earlier batch.
  No views are needed for that to matter: reversing the loop breaks `langford`,
  `ortho_latin-5` and the three `sudoku` lanes, and `all_different_test`'s
  default lane and its view lane with them. Stating the Hall condition in the
  reason instead — `x ≠ w` for every non-Hall value still in a Hall variable's
  domain — makes the order irrelevant when no two positions are views of one
  variable (measured on a throwaway branch: every family lane verifies reversed
  and shuffled), but not when two are; see rule 3.
- **Assertion** — `x ≠ d ∨ ¬reason`, one per deleted literal.
- **Hint** — `hints::AllDifferentHall`, as rule 1.
- **Offline reconstructibility** — `hinted`, as rule 1. Each assertion carries its
  own reason, so each deletion can be rebuilt alone; the batching is an
  optimisation of the proof, not something a justifier has to reproduce.
- **Proof size** — one `pol` per component, one RUP per deletion, and the first
  use of any at-least-one or at-most-one.
- **Gaps** — `None.` Until #1000 the Hall set was collected, and the hint's
  vectors and the reason built, on every wake that deleted, with proofs **off**
  too; see [CPU performance](#cpu-performance).
- **Tightness** — `Not shown.`

### Rule: forced-value-deletion

- **Infers** — `x ≠ d`, where `d`'s component in the residual graph is `d`
  alone.
- **Fires when** — as rule 2, but the walk from `d` finds no variable in its own
  component, because `d`'s matched variable `m` has no path back to it. There is
  then no Hall set to sum, and the value is simply taken. This is also the path
  a constant in the scope takes, which #108 made reachable.
- **Strength** — `GAC`.
- **Algorithm** — as rule 2, then an `O(1)` look-up of `d`'s matched variable.
- **Why it is true** — `m` is fixed to `d`, and two variables of the scope cannot
  share a value.
- **Proof technique** — `RUP`, by **JP 3.1**, against the pair `(m, x)`,
  licensed by **Theorem 2.8**.
- **Reason** — `{m == d}`, one literal, built only when a proof or reasons are
  wanted (since #1000, as rule 2).

  **Why that literal is true when the inference is made is an ordering
  argument.** `m` is not necessarily fixed when the wake starts: it can have
  other values, each in a component downstream of `d`'s. Every edge from `m` to
  one of those is deleted too, in an earlier batch, because Tarjan numbers
  components in the order it completes them — sinks first — and the deletion
  loop takes them in that order. So by the time `d`'s batch runs, `m` has lost
  every other value and the reason holds. Since #1013 the code says so at the
  loop, and `prove_deletion_using_sccs` throws if `m` is not already fixed to
  `d`; with the loop reversed, an ordinary unaliased case of
  `all_different_test --seed=12345` trips it.

  **The order matters to the proof, not only to the reason, once two positions
  are views of one variable.** Without that, this rule on its own survives a
  reversed order (rule 2, as written, does not): `x ≠ d ∨ m ≠ d` is RUP
  whenever it is written, every batch's line is written
  before anything needs it, and unit propagation reaches `m = d` through the
  other batches' lines. With it, one batch's deletion can entail a later batch's
  literal, and the tracker does not log an inference that is already entailed.
  Out of order, a line is written whose reason only its own inference makes
  true, and the batch that would have supported it is skipped. In
  `AllDifferent(1 − u, −1 − u, e)` with `u ∈ {3, 5}` and `e = −2`, sinks first
  logs `e = −2 → u ≠ 3` and skips `u = 5 → u ≠ 3` as entailed; reversed, it
  logs the second, skips the first, and VeriPB rejects the proof. That instance
  is `run_alldiff_aliased_views_test`. Sinks first is safe even here, because
  every reason already holds, through lines written earlier, when its own line
  is written. So #522's incremental components and #526's contraction idea,
  which both renumber, have to keep each component after everything it
  reaches. A reason that is not yet entailed would also defeat trail-ordered
  nogood learning, which needs every reason literal on the trail before its
  consequence.
- **Assertion** — `x ≠ d ∨ ¬(m = d)`.
- **Hint** — `hints::AllDifferent`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: value-consistency

- **Infers** — `y ≠ v` for every other variable `y` not yet fixed, once some
  variable is fixed to `v`; and a contradiction when two newly fixed variables
  share a value, which surfaces as the same inference on a variable that is
  already fixed.
- **Fires when** — a variable in the backtrackable unassigned list is found
  fixed. The whole of `AllDifferent` at `VC`, and the first stage of the staged
  generalised arc consistent propagator, which defers the matching whenever this
  stage removed something. Registered `on_instantiated` at `VC` since #999; see
  [Propagator inventory](#propagator-inventory). The list starts with every
  variable, a fixed one included. Until #999 a variable fixed at post time was
  left out, so its value was never removed from the others, and at `VC` the
  arm accepted assignments that are not solutions: `{x, z, y}` with `x, z ∈
  {3, 4}` and `y = 3` has none and got two. With a proof, VeriPB rejects the
  first of them as conflicting with a constraint; a run without one returned
  them.
- **Strength** — `partial`: a fixed variable's value is removed from every other
  variable, and nothing else.
- **Algorithm** — collect the newly fixed variables by swap-and-pop from the
  unassigned list, then a worklist that cascades through variables this fixes.
  `O(n)` per fixed variable. The non-throwing `infer_not_equal_or_stop`, because
  this propagator fails about once per node in circuit-style models and the
  throw was a large per-node cost.
- **Why it is true** — two variables that must differ cannot both be `v`.
- **Proof technique** — `RUP`, by **JP 3.1 (Not-Equals)**, `rup x=v ∧ y=v ⇒ 0 ≥
  1` against the pair's two rows, licensed by **Theorem 2.8**. The precondition
  is that the pair is encoded as Encoding Procedure 3.2 is, which the clique's
  rows are.
- **Reason** — `{x == v}`, one literal. For a plain variable it is prebuilt once,
  as a deferred `ExactSingleValue` that materialises to whatever `x` is fixed to,
  found by binary search over the scope's variable IDs (see [Mutable
  state](#mutable-state-and-incrementality)), and handed back by reference; a
  view or constant builds it inline, guarded on `want_reasons()`. Minimal.
- **Assertion** — `y ≠ v ∨ ¬(x = v)`.
- **Hint** — `hints::AllDifferent`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` Since #999 `all_different_test vc` proves every
  instance and checks value consistency at every node; before it, the only
  proving lane anywhere was the `seat_moving-vc` example. See [Tests](#tests).

### Rule: hall-interval-bound

- **Infers** — `x ≥ b`, or `x ≤ b`, where `[lo, b − 1]`, or `[b + 1, hi]`, is a
  Hall interval containing the bound being moved.
- **Fires when** — any variable's bounds change. `AllDifferent` at `BC` only.
- **Strength** — `bounds(Z)`: every bound has a support among the other
  variables' bounds, holes ignored — which is what the algorithm promises and
  all it promises.
- **Algorithm** — López-Ortiz, Quimper, Tromp and van Beek (IJCAI 2003): sort
  the variables by their bounds, and sweep them with union-find over the sorted
  distinct bounds, lower bounds in one pass and upper in a mirrored second. Those
  two passes reach the fixpoint of the bounds they read, so it re-sweeps only
  when a written bound snapped past a hole. The published `O(n log n)` is the
  cost of the sort; the sweeps after it are the cheap part. **This
  implementation's sort does not meet that bound.** It is an insertion sort
  from the previous call's order, for each of the two orders, with no fallback.
  That costs `O(n + inversions)`: close to linear while the saved order is still
  nearly sorted, which is the common case it was chosen for, but `Θ(n²)` in the
  worst case. The first call reaches that when the bounds are reversed against
  scope order, and a backtrack can leave the saved order far from sorted again.
  So a call is `O(n²)` in the worst case. No per-value step either way. Only
  when a proof or reasons are wanted, the narrowest interval behind each moved
  bound is then found afresh against the current state, `O(n²)`.
- **Why it is true** — a Hall interval holds at least as many variables with
  their bounds inside it as it has values, so between them they take every value
  in it; any other variable whose bound lies inside must move past it.
- **Proof technique** — `pol`, then `RUP`. **Ours**, with no published
  procedure: it is JP 3.16 and 3.17's summing argument with the Hall
  neighbourhood replaced by the interval `[lo, hi]`. Each Hall variable's
  at-least-one names **every** value between its bounds, holes included, so that
  the reason need state only bounds — which is all a bounds consistent propagator
  knows — and the holes cost nothing, because they lie inside `[lo, hi]` where
  the at-most-ones cancel them. The moved variable's current bound **on the side
  being moved** goes into the reason, so that RUP can walk it past every value
  the interval takes: for `x ≥ b` that is `x ≥ lb(x)`, which confines `x` to the
  interval once `x ≥ b` is negated. With `x, y ∈ [1, 2]` and `z ∈ [1, 4]`, the
  assertion for `z ≥ 3` carries the old `z ≥ 1`, not `z ≤ 4`.
- **Reason** — each Hall variable's two bound literals, and the moved variable's
  current bound on the side being moved. Built only when `logger ||
  want_reasons()`, and otherwise `NoReason{}` with `NoJustificationNeeded{}`.
- **Assertion** — `x ≥ b ∨ ¬reason`, or the mirror.
- **Hint** — `hints::AllDifferentHallInterval`: `lo`, `hi` (`Integer`, the
  interval). Not on the wire.
- **Offline reconstructibility** — `hinted`. `hi` is `b − 1` from the
  conclusion, the Hall variables are those whose bounds the reason states, and
  the argument goes through over the interval from the least of their lower
  bounds, which a justifier can compute; the subhint is what tells it to build
  this shape rather than rule 2's.
- **Proof size** — one `pol` and one RUP, plus an at-most-one per value of the
  interval and an at-least-one per Hall variable. Both loops are at most `n`
  long, since the interval holds at least as many variables as values. The
  at-least-ones name a variable's own bounds, which change between firings, so
  above #939's width gate each distinct cover costs a fresh line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` `bc_all_different_test` checks the propagation
  against a brute-force oracle at the root on thousands of small random
  instances, which pins the *strength* and not the derivation.

### Rule: hall-interval-violator

- **Infers** — a contradiction: some interval holds more variables than values.
- **Fires when** — either sweep fails.
- **Strength** — `bounds(Z)`.
- **Algorithm** — the failed sort and sweep, as rule 5: `O(n²)` in the worst
  case, for the same insertion sort. Then, with a logger, a
  violating interval found by trying every pair of a lower and an upper bound and
  counting the variables inside: `O(n³)`, and only when proving.
- **Why it is true** — pigeonhole over the interval.
- **Proof technique** — as rule 5, ours.
- **Reason** — the violator's variables' bounds. Guarded on `logger` rather than
  `want_reasons()` — equivalent today, since only the proof-logging tracker
  materialises reasons, but not what the tracker's contract asks for.
- **Assertion** — the negated reason, with no conclusion literal.
- **Hint** — `hints::AllDifferentHallInterval`, over the violator.
- **Offline reconstructibility** — `hinted`, as rule 5.
- **Proof size** — as rule 5.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: duplicate-contradiction

- **Infers** — a contradiction, at the root.
- **Fires when** — the scope repeats a variable handle: `AllDifferent` at any
  level, `SymmetricAllDifferent`, or `AllDifferentExcept` with nothing excluded.
  Installed by `install_clique_duplicate_contradiction_initialiser` in place of
  every propagator.
- **Strength** — n/a; it decides the constraint.
- **Algorithm** — a sort and an adjacent search in `prepare`, `O(n log n)`.
- **Why it is true** — a variable cannot differ from itself.
- **Proof technique** — `RUP`, directly on the encoding, needing no procedure:
  the pair `(x, x)`'s two rows each read `0 ≤ −1` under their guard, so they
  collapse to the unit clauses `selector` and `¬selector`.
- **Reason** — none.
- **Assertion** — `0 ≥ 1`.
- **Hint** — `hints::AllDifferent`, or `hints::AllDifferentExcept` for the except
  class. The diagnostic comes from `constraint_type()`, not from the hint, so a
  `SymmetricAllDifferent` justified with the all-different hint still reports
  itself correctly.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: duplicate-forcing

- **Infers** — `x ∉ [lo, hi]`, at the root, for every maximal run `[lo, hi]` of
  a repeated variable `x`'s domain that holds no excluded value.
- **Fires when** — an initialiser, for `AllDifferentExcept` with a repeated handle
  and something excluded. Afterwards the propagator sees the variable once, and
  since #1004 the variable contributes nothing to the propagator's value set.
- **Strength** — n/a; it forces `x` into the excluded set, which is exact.
- **Algorithm** — `each_interval_minus` of `x`'s domain against the excluded
  values, and one `infer_not_in_range` per run: `O(runs)`, however wide `x` is.
  Per value, with a linear search of the excluded list for each, until #1004;
  see [Interval efficiency](#interval-efficiency).
- **Why it is true** — `x` must differ from itself unless it takes an excluded
  value.
- **Proof technique** — `RUP`, directly on the encoding, needing no procedure
  and no lemma. Under their guards the pair `(x, x)`'s two rows read `0 ≤ −1`,
  so they collapse to `selector ∨ ⋁ [x = s]` and `¬selector ∨ ⋁ [x = s]` over
  the excluded values `s`. With `x` inside the run each `[x = s]` is false by
  unit propagation, down the chain of `x`'s order atoms from the run's bound on
  whichever side `s` lies — no excluded value is inside a run — and the two rows
  then force the selector both ways. As written into a proof, for `x` over
  `-3..0` with `-1` excluded:
  ```
  rup 1 ~i[_1][in-3_-2] >= 1;
  rup 1 ~i[_1][eq0] >= 1;
  ```
  Per value, until #1004, each conclusion followed two lemmas on the selector,
  `x ≠ v ∨ selector` and `x ≠ v ∨ ¬selector`; the range form turned out to need
  neither. Checked with proofs on holes (an excluded value in a hole between two
  runs, one outside the bounds, one in no domain at all), on negated and offset
  views, and through the full `cake_pb_cp` chain.
- **Reason** — none; it is a root inference.
- **Assertion** — `x ∉ [lo, hi]`.
- **Hint** — `hints::AllDifferentExcept`, carrying only the constraint id. The
  encoding helper no longer hands back the pair's selector, which only the
  lemmas used.
- **Offline reconstructibility** — `offline`. RUP finds the rows without naming
  them, so the selector being an unnamed flag on unlabelled rows no longer
  matters.
- **Proof size** — one line per run, plus the literal layer's lines defining
  the range literal. On `(X X Y) except (0)`, the whole proof is 91 lines at
  every width up to 10⁹; per value it was `14w + 78`.
- **Gaps** — `None.`
- **Tightness** — `Not shown`, and there is little to corrupt: the conclusion is
  the only step. What is pinned is the width, by an audit-lane row and a
  proof-size row that both fail on the per-value code.

### Rule: symmetric-channel

- **Infers** — `x_i ≠ v`, when `i + start` is no longer in the domain of
  `x_{v − start}`.
- **Fires when** — every wake of `SymmetricAllDifferent`'s propagator, as a
  single pass before the generalised arc consistent one.
- **Strength** — `partial` for the conjunction: arc consistency on the
  all-different plus this channelling, which is strictly weaker than Régin's
  (1999) generalised arc consistency on the symmetric all-different, which needs
  non-bipartite matching.
- **Algorithm** — for every variable and every value in its domain, one
  `in_domain`. `O(n²)`, since every domain lies inside `[start, start + n)`.
- **Why it is true** — if `x_i = v` then `x_{v − start} = i + start`.
- **Proof technique** — `RUP`, on the channelling clause `x_i ≠ v ∨ x_{v − start}
  = i + start`, which the reason falsifies half of. Plain clausal unit
  propagation; no procedure needed. Ours in the sense that the thesis has no
  symmetric all-different, not in any sense that needs an argument.
- **Reason** — `{x_{v − start} ≠ i + start}`, built unconditionally.
- **Assertion** — `x_i ≠ v ∨ x_{v − start} = i + start`.
- **Hint** — `hints::AllDifferent`, so it arrives looking like rule 4; the
  reason's literal is a disequality rather than an equality, which is what tells
  them apart.
- **Offline reconstructibility** — `offline`: the channelling row is unlabelled,
  but RUP finds it without naming it.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` Uses the throwing `infer` rather than the
  non-throwing form every other propagator here has moved to.

## Evidence

### Tests

Five binaries, and a family whose coverage is uneven in an instructive way.

- **`all_different_test`**, run as three lanes — `all_different_constraint` at
  the default, `all_different_constraint_bc`, and since #999
  `all_different_constraint_vc` — each with a mixed view lane, and the full
  per-position view sweep behind `GCS_ENABLE_VIEW_WRAP_SWEEP`. Six variables per
  instance: seven fixed rows, including #108's two constant-in-a-Hall-set
  crashes and #254's all-constant cases, and forty seeded random rows over
  `[-10, 10]`, and since #1013 one case whose scope holds two views of one
  variable, `run_alldiff_aliased_views_test`, which fails if the deletion
  batches run out of order (checked by mutation). **Per-node consistency is
  asserted**:
  `solve_for_tests_checking_gac` at the default,
  `solve_for_tests_checking_consistency` with `CheckConsistency::BC` on every
  variable in the `bc` lane, and in the `vc` lane a check at every node that no
  fixed variable's value is left in another domain, which is the whole of what
  value consistency promises. **VeriPB really runs**, on every instance, when it
  is installed. Seeded and reproducible with `--seed=N`. Capped by default; see
  below.
- **`all_different_except_test`**, one lane and a mixed view lane over four
  positions; per-node GAC asserted; duplicate cases that exercise the forcing
  initialiser at test widths, and since #1004 six more over a repeated variable
  with holes or as a view: an excluded value in a hole between two runs, one
  outside the bounds, one in no domain, and negated and offset views.
- **`symmetric_all_different_test`**, one lane, no view lane. Small fixed cases
  up to four variables, with GAC asserted only on the cases where the
  constraint is GAC — it is not, in general, since the channelling is weaker
  than Régin's symmetric algorithm — and plain enumeration on the rest.
- **`bc_all_different_test`**, a Catch2 test of the bounds consistent propagator
  against a brute-force reference at the root, on thousands of small random
  instances: it checks that the arm reaches **exactly** bounds(Z) consistency,
  which pins the strength rather than the proof.
- **`vc_all_different_test`**, since #1020, a Catch2 test of the single-value
  reason cache alone, over a scope whose IDs are 10,000 apart and which holds a
  view and a constant. A lookup that misses is invisible to every solver-level
  test, because the propagator then builds an equivalent reason inline, and the
  cache's size is a memory cost no correctness test sees. So both are checked
  directly.
- **Runtime caps: the defaults fire on every `all_different_test` lane.** No
  lane sets or clears a cap of its own, so under a default `ctest` every lane
  runs with the suite-wide caps (300 solutions and 1,500 search nodes per
  solve; see [`building.md`](../building.md)), and a truncated solve checks
  soundness and a partial proof only. Over three unseeded runs at `d3f3f1aa`
  (2026-09-22) they truncated between 126 and 144 solves on each of the six
  `all_different_constraint*` lanes, and none on `all_different_except_test`'s
  two or `symmetric_all_different_test`'s one. So this family's default local
  run checks noticeably less than its uncapped one. The two Ubuntu CI lanes
  build with the caps off, so every pull request gets the complete check, and
  all ten lanes of the four binaries it then had pass uncapped locally at
  `d3f3f1aa` (`cmake --preset release -DGCS_TEST_CAP_DEFAULTS=OFF`, then
  `ctest -R '^(all_different|symmetric_all_different|bc_all_different)'`).
- **Seven `.scp` chain cases**, listed under [Cake
  conformity](#cake-conformity); #1004's `all_different_except_duplicate` is the
  first to repeat a variable. **Four MiniZinc differential tests**
  (`alldifferentexcept`, `alldifferentexceptzero`, `symmetricalldifferent`, and
  since #997 `symmetricalldifferentoffset`, the only non-1-based one) and three
  XCSP3 ones (`all_different_matrix`, and since #1002 `all_different_except` and
  `all_different_except_values`). Plain `all_different` has no MiniZinc test of
  its own, being reached by a great many models.
- **`element_auto_test`** checks each level's hole-sensitivity verdict, from the
  side of an `Element` whose result only an `AllDifferent` observes (#999).
- **Examples with proving lanes that reach the family**: `seat_moving` under its
  default, under `--all-different vc` and under `not-equals` (the last reaching
  only its `AllDifferentExcept`), `sudoku` and `sudoku-sixteen`, `ortho_latin-5`
  (which runs `--all-different gac`), `langford`, and `hitori`, which with
  `seat_moving` is where `AllDifferentExcept` is posted by a realistic model.
  `magic_square-3` runs its default, the disequality clique, and so exercises
  `equals` rather than this family.
- **Six audit-lane rows and two proof-size rows**, under [Interval
  efficiency](#interval-efficiency).
- **Rule 3's reason, checked on every trivial-component deletion to be
  entailed already when the batch runs.** Added for this audit as a local
  assertion; #1013 commits it as a check that throws. It held on all
  **76,541** such deletions across
  `all_different_test` (15,222), `all_different_except_test` (200),
  `symmetric_all_different_test` (50), `inverse_test` (94), `arg_sort_test`
  (142), `langford` at 8 and 11 (326 and 56,568), `sudoku` (911) and
  `ortho_latin --all 5` (3,028), with the branch counted as well as checked so
  that "held" does not mean "never ran".

**What the tests do not cover**, and this is the section's point:

- **The value consistent arm had no enumeration test and no strength
  assertion**, until #999 added the `vc` lane. It failed at its first data row
  with a constant, on a wrong answer no other lane could see: the arm ignored
  variables fixed at post time (rule 4).
- **The staged path is never reached by the family's own tests** (#1023), and
  that follows from arithmetic rather than from reading. Every variable is a
  constant or a range of at most six values, so a scope holds at most 36
  distinct values: `6 × 36 = 216`, under the staging threshold of 256. So the
  per-node GAC assertion has only ever checked the unstaged propagator. The
  dense-table sweep, at 24 or more values, is within that bound; whether any
  seed reaches it was not checked. The staged one's claim
  — "the per-node fixpoint is therefore still exactly the GAC closure" — is
  argued in a comment and exercised by examples, which check solutions and
  proofs but not consistency.
- **There was no non-1-based `symmetric_all_different`**, which is the whole of
  why the MiniZinc bug survived; #997 added one. Every global's MiniZinc tests
  are thin on the shapes a front end gets wrong — index sets, empty arrays,
  repeated variables — and Gecode, the harness's reference, is itself wrong or
  errors on some of them: that is #1006. For this family's globals it is now
  done: #1011 added nine MiniZinc shape lanes over `all_different`,
  `alldifferent_except` and its `_0` spelling, `symmetric_all_different`,
  `inverse` and `arg_sort`, compared against the standard library's
  decompositions (`-G std`) where native Gecode is wrong, and mutation-checked
  against eleven front-end breakages. `all_different` itself had no lane before.
  They found two `arg_sort` bugs, both outside this family's classes: two
  `ArgSort`s in one problem shared proof names (#1010), and a reified
  `arg_sort` did not flatten.
- **There was no wide repeated handle in `AllDifferentExcept`**, so the forcing
  loop's width cost was visible only to a probe written for this audit. Since
  #1004 an audit-lane row and a proof-size row see it.
- **The `BC` and `VC` arms never reach `cake_pb_cp`**, since the `.scp` does not
  record a level.
- **No mutation lane.** Per the template's policy that is an ordinary state. If
  one is ever wanted, rule 1 or 2 is the place: dropping one Hall value's
  at-most-one from the `pol` is the obvious corruption, and it would say whether
  the reason alone can close the residue.

### Benchmarks and examples

Every example that takes `--all-different` exercises this family, and most offer
the disequality clique as a fourth arm: `ortho_latin`, `sudoku`, `magic_square`
(in `minicp_benchmarks`, whose default strength must not change because it
reproduces MiniCP's search tree), `langford`, `golomb`, `seat_moving`. `qap` and
`tsp` post an `AllDifferent` over the permutation, and `hitori` and `seat_moving`
post `AllDifferentExcept`. Nothing in the tree posts `SymmetricAllDifferent`.

**For CPU benchmarking, `ortho_latin --all 6 --all-different gac`.** It is a
complete refutation — there are no orthogonal Latin squares of order six — so the
tree is fixed and nothing depends on solution order, and under
`GCS_PROPAGATOR_STATS=time` this family takes **49% of propagation time and 46%
of calls**, the most family-dominated instance found. It is also `equals`'
benchmark under `--all-different not-equals`, which makes the two families
directly comparable on one model. `langford` is `element`'s instead (42–45% of
time there), and `sudoku`'s sixteen-by-sixteen puzzle solves at the root. For an
identical-tree comparison of `GAC` against `BC`, `golomb`: nothing else there
makes a hole, and the search branches smallest-first on variables the
all-different does not constrain.

**For proof benchmarking, `ortho_latin --all 5 --all-different gac`**, again
`equals`' instance under the other arm: 405 nodes, eighteen solutions, 5.9 s to
verify fully justified on this machine. And the `.scp` pigeonholes of [Proof
performance](#proof-performance), which isolate the family's own cost.

**Never run uncapped**: `ortho_latin --all 7`, which was not attempted; at 6 the
arms take 63–167 s. A proving run of `AllDifferentExcept` with a wide repeated
handle used to belong here too — 90 s of VeriPB at width 10⁴ — and since #1004
is 91 lines at any width.

### CPU performance

*Measured 2026-09-21 at `6b220c79` (built from the family-document branch, whose
code is identical), Release + `GCS_WERROR=ON`, g++ 15.2.0, on fataepyc-09: AMD
EPYC 7643, boost off (a flat 2.3 GHz), otherwise idle,
`numactl --cpunodebind=0 --membind=0 taskset -c 4 setarch -R`. Min of three;
every arm's three runs agreed to within 0.7%. Not comparable with the other
family documents' tables, which were taken on a boosted Ryzen 9 9950X3D.*

`ortho_latin --all 6`, one row per `--all-different` arm:

| Arm | Time | Recursions | Propagator calls | Effectful | Contradicting |
|---|---|---|---|---|---|
| `gac` | 73.08 s | 864,835 | 29,006,249 | 16,784,765 | 441,766 |
| `bc` | 167.10 s | 2,697,942 | 104,875,744 | 63,968,408 | 1,788,086 |
| `vc` | **62.78 s** | 1,283,966 | 37,681,972 | 21,660,421 | 651,341 |
| `not-equals` | 64.03 s | 1,339,912 | 77,784,903 | 47,304,809 | 679,314 |

Four different search trees, so the times answer "which arm is fastest on this
model" and nothing about per-call cost. Three things they do say:

- **`BC` searches 3.12× the nodes `GAC` does**, which reproduces #970's ×3.1 on a
  different machine and is the whole of why `BC` is opt-in: it is faster per
  call and loses 2.3× overall.
- **`VC` is the fastest arm here despite 1.48× the nodes**, and the disequality
  clique, which reaches the same fixpoint through one propagator per pair of
  variables, is within 2% of it with 1.55×. On this model the matching does not pay for
  itself; that is a statement about `ortho_latin`, where most of the work is the
  other constraints', and not about the algorithm.
- **The clique and `VC` search nearly the same tree** — 1,339,912 against
  1,283,966 nodes — but not the same one, since `VC` removes a fixed value from
  every variable in one wake where the clique does it pairwise, which changes the
  order the other constraints see things in.

**Two A/B measurements for this audit's findings**, both from one experimental
binary at `6b220c79` in which an environment variable of the same length in both
arms selects the behaviour, so code layout is identical; interleaved, three
rounds, same machine and pinning. The experimental binary is not the one in the
table above and its baselines differ from it by about 1%, so compare within
these rows only.

*The value consistent trigger* (#992, fixed by #999), `--all-different vc`:

| Trigger | Time, min of three | Range | Recursions | Propagator calls | Instructions |
|---|---|---|---|---|---|
| `on_change` (before #999) | 63.38 s | 63.38–63.70 s | 1,283,966 | 37,681,972 | 340.6 G |
| `on_instantiated` | **61.82 s** | 61.82–62.07 s | 1,283,966 | **28,989,095** | 333.9 G |

**The same tree with 23.1% fewer propagator calls**, 2.0% fewer instructions,
and 2.5% faster, the two ranges not overlapping. Instructions from `perf stat`,
three interleaved pairs, stable to 0.03%; cycles in the same runs moved by
−0.8%, −2.5% and −2.7%, so a single cycle count would have understated it. Every call removed is a wake on an interior removal that
found nothing, which is what #819 measured for `NotEquals`; the saving in time is
small because on this model most of the work is the other constraints'.

*The Hall-search guard* (#991, fixed by #1000), `--all-different gac`, skipping
`prove_deletion_using_sccs` and `prove_matching_is_too_small` when
`! logger && ! want_reasons()`:

| Hall search | Time, min of three | Range | Recursions | Propagator calls | Instructions |
|---|---|---|---|---|---|
| unguarded (before #1000) | 73.89 s | 73.89–74.07 s | 864,835 | 29,006,249 | 382.5 G |
| guarded | **72.06 s** | 72.06–72.27 s | 864,835 | 29,006,249 | 376.4 G |

**2.5% faster with every count identical**, 1.6% fewer instructions (one
`perf stat` pair; cycles −2.7%), the ranges again not overlapping.
Small, and deliberately not overstated: the family is 49% of this benchmark's
propagation time, so the guard is worth about 5% of the family's own cost here.
It was worth doing because it is free, because the bounds consistent arm
already did it, and because it applies unchanged to `Inverse` and `ArgSort`,
which run the same code.

**The same two, measured on the fixes themselves**, since an experiment is not
the change that ships. Same machine, boost off, pinned with `taskset -c 24`
alone rather than the main table's `numactl` and `setarch`; three interleaved
rounds, min of three. Each pair is the pull request's parent against its tip, so
code layout differs between them and the counts are the firmer evidence:

| Fix | Arm | Before | After | Recursions | Propagator calls | Instructions |
|---|---|---|---|---|---|---|
| #999 | `vc` | 63.59 s (63.59–64.16) | **62.03 s** (62.03–62.58) | 1,283,966 both | 37,681,972 → **28,989,095** | not taken |
| #1000 | `gac` | 73.68 s (73.68–73.90) | **71.97 s** (71.97–72.19) | 864,835 both | 29,006,249 both | 381.8 G → **375.7 G** |

Both reproduce the experiment, the ranges again not overlapping. #999's parent
is its own first commit, the fixed-at-post fix, which changes nothing on this
model: every count at size 5 is identical to `main`'s at `5397a50b`, because
no `ortho_latin` scope holds a variable fixed when it is posted.

**Same-search comparison of `GAC` and `BC`, on Golomb rulers**, the one shape
where #970 found the trees agree. Same build as the main table, on one core of
the other socket (`numactl --cpunodebind=1 --membind=1 taskset -c 60`), min of
three:

| `n` | Arm | Time | Range | Recursions | Propagator calls |
|---|---|---|---|---|---|
| 10 | `gac` | 2.51 s | 2.51–2.51 s | 92,093 | 2,560,811 |
| 10 | `bc` | **1.43 s** | 1.43–1.47 s | 92,093 | 3,083,338 |
| 11 | `gac` | 56.16 s | 56.16–56.23 s | 1,666,426 | 52,141,766 |
| 11 | `bc` | **31.49 s** | 31.49–31.72 s | 1,666,426 | 68,670,724 |

The same recursion counts, and `BC` **1.75× and 1.78× faster**. What was
compared is counts, not a node-by-node trace. Re-checked at `61112ed0` for
this document, at `n = 9` and `n = 10`: the two arms print the same ten
solutions in the same order, with the same recursions (13,104 and 92,093),
failures (13,070 and 92,053) and maximum depth (8 and 9). `BC` makes *more*
propagator calls, 20% and 32% more at `n = 10` and `n = 11`, each far cheaper,
since the matching and its components are gone. This is the whole case for having the arm, and it is
narrow: a model where nothing else makes holes and the search never reads an
interior.

*Measured elsewhere — #970's own figures, at n = 12 on another sitting, not to be
put beside the table above:* 29.2 µs per call for `GAC` against 5.85 µs for `BC`,
1.64× faster overall on what #970 reports as an identical tree.

**What this benchmark does not exercise.** Read off the proof's assertions (see
[Proof performance](#proof-performance)): of the nine rules, `ortho_latin`
reaches rules 1–4 under `gac` and 5–6 under `bc`. Nothing here posts
`AllDifferentExcept` or `SymmetricAllDifferent`, and no constraint repeats a
variable, so rules 7–9 are never reached. A per-inference cost quoted from this
benchmark is an average over rules 1–4 or 5–6 only.

**Cross-solver comparison: `Not measured.`** #868's harness exists and has been
pointed at `equals` only. This family is the best target the arc has had:
every solver has a GAC all-different, most have a bounds consistent one, and a
MiniZinc model hands each solver the same global rather than a decomposition, so
the "which model is defensible" question that dominated #868 does not arise.

### Proof performance

*Same build and machine as [CPU performance](#cpu-performance); proofs written
and verified on one core of the same socket, VeriPB 3.0.2, min of three.*

**The four arms on one model.** `ortho_latin --all 5`, eighteen solutions,
fully justified (`AssertionLevel::Off`):

| Arm | Recursions | `.pbp` | VeriPB | Verdict |
|---|---|---|---|---|
| `gac` | 405 | 5.74 MB | 5.91 s | `VERIFIED COMPLETE ENUMERATION OF 18 SOLUTIONS` |
| `bc` | 820 | 9.16 MB | 8.68 s | likewise |
| `vc` | 615 | 5.82 MB | 5.61 s | likewise |
| `not-equals` | 607 | 5.99 MB | 5.73 s | likewise |

The `gac`, `bc` and `vc` arms write **byte-identical** `.opb` files (423,961
bytes), which is the claim that the level is a propagation choice checked rather
than asserted. The clique's is different (435,170 bytes), being a different
model.

The table is `6b220c79`'s, and one fix moves one row. #999 changes when the `vc`
arm runs, and so the order its inferences reach the proof in: the `.opb` stays
byte-identical, and the proof goes from 130,921 lines to 130,154, both `VERIFIED
COMPLETE ENUMERATION OF 18 SOLUTIONS`. #1000 moves nothing, since its guard
cannot fire with a logger: all 592 proof artefacts of the five constraints'
tests that run the propagator are byte-identical at a pinned seed.

`gac` proves the smallest tree in about the same proof as the cheaper arms: its
Hall justifications are bigger per inference than a single disequality, and it
makes fewer inferences. `bc` is the outlier in both directions — twice the tree
and 1.6× the proof, because every bound it moves costs a Hall interval argument
where `vc` would have removed one value with one line.

*Measured elsewhere:* `equals`' own table gives 1.83 s to verify the clique's
proof of this instance, on the Ryzen. The 5.73 s here is the same proof on a
slower, unboosted machine, and the two should not be compared.

**Assertion levels**, for `gac`:

| Assertion level | `.pbp` | Assertions | VeriPB | Verdict |
|---|---|---|---|---|
| `Off` | 5.74 MB | 0 | 5.91 s | `VERIFIED COMPLETE ENUMERATION` |
| `Links` | 3.28 MB | — | — | — |
| `Inferences` | 2.98 MB | 24,759 | 0.10 s | `UNDER ASSERTIONS` |

Of the 24,759 assertions at `Inferences`, **11,887 (48%) carry the
`all_different` hint** — 10,765 bare and 1,122 with the `hall` subhint. The rest
are the model's arithmetic (`modulus` 6,281, `linear_equality` 3,203, `divide`
2,951) and its symmetry breaking (`equals` 14). None carries `hall_interval`, as
expected at this level, and none `all_different_except`.

The bare ones are rules 3 and 4, which the wire cannot tell apart and should not
need to: both are one RUP against one pair. This instance's 25-variable
constraint over all cells is big enough to be staged (`25 × 25 = 625 ≥ 256`), so
it runs rule 4 as its first stage; the twenty five-variable rows and columns are
not, so their bare assertions are rule 3.

**The family's own cost, measured.** The template asks for own-versus-shared as
a function of what the cost is proportional to. For this family that is the
number of variables, and a pigeonhole isolates it: `n` variables over `n − 1`
values, one `all_different` in an `.scp`, `glasgow_scp_solver --prove`, refuted
at the root by one Hall violator over every value.

| `n` | proof lines | pairwise at-most-one clauses | predicted `(n − 1)·C(n, 2)` | literal layer | everything else | VeriPB |
|---|---|---|---|---|---|---|
| 4 | 204 | 18 | 18 | 136 | 50 | < 0.01 s |
| 8 | 946 | 196 | 196 | 560 | 190 | < 0.01 s |
| 16 | 4,830 | 1,800 | 1,800 | 2,272 | 758 | 0.05 s |
| 32 | 27,574 | 15,376 | 15,376 | 9,152 | 3,046 | 0.65 s |

The pairwise clauses match the prediction exactly, and the literal layer — the
`red` and `core` lines defining each variable's order and equality atoms — is
exactly `n(9n − 2)`. So on a pigeonhole **the family's own proof is
`(n − 1)²n/2` lines against a shared layer of about `9n²`**, and the family
overtakes the layer it sits on at about `n = 19`. Everything else — the folds,
the at-least-ones, the one `pol` and the conclusion — is about `3n²`.

That is #944's measurement from the other side. #944 held the Hall set at two
intervals and grew the values inside them; this holds it at one interval and
grows the variables. Both land on the pairwise at-most-one: `C(n, 2)` clauses per
value, folded by Theorem 2.3. #944 proposes one cardinality constraint per
interval, `Σ [x_i ∈ I] ≤ |I|`, in its place, and is careful to say what is not
yet known — an interval literal has no arithmetic link to the values inside it
except through its covering, so deriving that bound still has to touch every
value in the interval, and whether it can do so without a clique fold per value
is the open question. This table does not answer it. What it does say is that on
a pigeonhole the answer decides nearly the whole of the family's own proof, which
is the case for finding out.

## Status, gaps, and next steps

### Proof-logging gaps

**Nothing is left unjustified, and no rule is weakened when proofs are
enabled.** There is no `a`-oracle use and no unlogged inference, and no
propagator changes strength with a logger attached: the bounds consistent arm
changes only *whether it looks for* the interval behind a bound, never whether
it moves the bound.

**One piece of dead proof code, now deleted** (#990, #1001).
`SymmetricAllDifferent` installed an initialiser meant to emit every value's
at-most-one at the root, and opened it with `if (! logger ||
logger->get_assertion_level() >= AssertionLevel::Off) return;`. `Off` is 0, the
lowest level, so the test was always true and the initialiser had returned
immediately since it was added in 4a433958 (2026-06-19). Proofs verified
regardless, because the Hall justification emits the at-most-ones lazily on
first use, the way `AllDifferent` always has. It was **deleted, not repaired**:
a repair writes `n · C(n, 2)` root lines that the lazy path makes unnecessary —
12% more proof lines even on the family's own small test instances, all still
verifying — and the deletion leaves every one of those tests' 64 proof
artefacts byte-identical, which is the check that it really never ran.

`Inverse` had the same initialiser, and there it was **live** (`> Off`), so it
paid the root cost this one avoids. That was filed as #1049, and #1089 deleted
it the same way: `Inverse` now builds each value's at-most-one on first use.

**One invariant exception, safe today.** The Hall justifications read `state`
rather than the reason; see the catalogue's preamble.

**The cost gap ran the other way, as in `equals` and `comparison`, and is
closed**: until #1000 the generalised arc consistent propagator did proof-shaped
work — finding the Hall set, building the hint — with proofs off. See [CPU
performance](#cpu-performance).

### Known limitations

**MiniZinc's `symmetric_all_different`, `inverse` and `arg_sort` gave wrong
answers on arrays not indexed from 1** (#987, fixed by #997). The first is this
family's; the other two were found by sweeping the MiniZinc library for the same
shape, and are recorded here because the fix is one pattern for all three. Each
passed its arrays to a builtin that carries no index set, and `fzn_glasgow.cc`
posted the propagator with its offset fixed at 1. At `6b220c79`:

| model | Glasgow | MiniZinc's default |
|---|---|---|
| `symmetric_all_different(x)`, `x : array[0..3] of var 0..3` | `UNSATISFIABLE` | 10 solutions |
| `inverse(f, g)`, both `array[0..2] of var 0..2` | `UNSATISFIABLE` | 6 solutions |
| `arg_sort(x, p)`, `x : array[0..2] of var 0..3` | `UNSATISFIABLE` | 64 solutions |

and where Glasgow did return solutions on a shifted array, none of them was a
solution of the model. **The wrong `UNSATISFIABLE` verified** — through VeriPB,
and through the full `cake_pb_cp` chain, re-deriving the OPB from the `.scp`,
elaborating to a core and re-checking it — because the `.scp` records the
constraint Glasgow posted, `(_1 symmetric_all_different (...) 1)`, and the chain
certifies that. Nothing was wrong with any proof. The chain starts at the
`.scp`, and a front end that posts the wrong constraint is upstream of
everything it can check. That is the most useful sentence this audit has for
the paper.

The fix copies `circuit` and `subcircuit`, which already passed
`min(index_set(x))` to their builtins, empty-array guard included; `inverse`
passes both arrays' starts, and also says `false` for arrays of different
lengths, as the standard library's decomposition does, rather than reaching
`Inverse` and failing as an invalid problem. And letting two different starts
through exposed a second wrong answer, in `Inverse` itself: see [Relation to
other families](#relation-to-other-families). There the proof does catch it:
VeriPB rejects the wrong `UNSATISFIABLE` at a RUP step, so it was a wrong answer
only for runs without a proof.

**`AllDifferent` at `VC` ignored variables fixed at post time**, fixed by #999
and found by it rather than by the audit: see rule 4. Like `Inverse`'s, a proof
catches the wrong solutions and a run without one returns them.

**`AllDifferentExcept` forced a repeated variable into the excluded set one value
at a time**, linear in the variable's width in time, memory and proof (#988).
Since #1004 it is a run at a time and flat in all three; see [Interval
efficiency](#interval-efficiency).

**Generalised arc consistency wants a vertex per value**, so an `AllDifferent`
over genuinely wide domains at its default is the audit lane's `KnownTrip`, and
both frontends post the default. The policy's answer is the bounds consistent or
value consistent arm, and nothing selects either automatically — correctly, for
the reason under [Interior values and optional
pruning](#interior-values-and-optional-pruning). A model with wide domains has
to ask.

**Hall proofs are cubic in the number of variables** (#944), and on a
pigeonhole overtake the shared literal layer at about `n = 19`.

**The strongly connected components are recomputed on every wake** (#522's
remaining item).

**`SymmetricAllDifferent` is not generalised arc consistent on the
conjunction**, being the bipartite algorithm plus channelling rather than
Régin's non-bipartite one. Its tests assert GAC only where it happens to hold.

**XCSP3's `allDifferent` over expressions is unsupported.** With `except` it
is supported since #1002 (#989); over expressions each one would need a
variable first, which is a different size of job.

**The hint's name does not say which class sent it**; see the catalogue's
preamble.

### Next steps

Ranked. The audit's six filed findings are all fixed — #997, #999, #1000,
#1001, #1002 and #1004 — and so they are gone from this list. What is left is
evidence, and the family's standing work.

1. **Test the path nothing tests.** An instance with at least 43 distinct values
   over six variables, so that the per-node GAC assertion reaches the staged
   path and the dense-table sweep, which today it never does. The other half of
   this item as the audit wrote it, a `vc` lane, is done (#999), and found a
   wrong answer on its first run; that is the argument for this half. #1023,
   filed from #1020's work, proposes a per-constraint staging threshold so the
   existing instances can be run staged; cheap.
2. **#1006 — MiniZinc differential tests over the shapes front ends get
   wrong.** #987 was invisible to every check but one, and this family's globals
   were the natural pilot. The pilot is done (#1011); what is left of #1006 is
   the other families.
3. **#1013 writes the sinks-first order down and checks it.** The
   comment at the batch loop covers rule 2 as well, which depends on the order
   too; `prove_deletion_using_sccs` throws if rule 3's reason does not already
   hold; and `run_alldiff_aliased_views_test` fails if the order is reversed,
   because with aliased views the order decides which lines are logged at all.
4. **#522 — incremental strongly connected components.** The remaining
   propagation work in the generalised arc consistent arm. It has to keep each
   component's batch after every component it reaches; any such order will do.
5. **#944 — Hall proofs over intervals.** The measurement under [Proof
   performance](#proof-performance) says how much of the family's own proof the
   answer decides; #944 says why the answer is not known yet.
6. **#868 — the cross-solver comparison.** This is the best family in the arc to
   point it at.

**Not to do, having been considered.**

*An optional-interior-pruning `consistency::Auto` for `AllDifferent`.* The
pair's first promise fails, and fails without any other constraint's help; see
[Interior values and optional
pruning](#interior-values-and-optional-pruning). #970 considered and measured
it, and this audit agrees. A cost-based `Auto` or `Dynamic` that deliberately
weakens propagation is a different question, which nobody has proposed and
this audit does not settle; see [Options](#options).

*Repairing `SymmetricAllDifferent`'s dead initialiser.* See [Proof-logging
gaps](#proof-logging-gaps): deleting it was the fix (#1001).

*Reading the reason instead of `state` in the Hall justifications, now.* Right in
principle, as #885 was for `equals`, and harmless to leave while every
justification is emitted synchronously with its reason. Worth doing alongside
anything that makes justification replay asynchronous, and not before.

## Prior art

- **Hall, "On Representatives of Subsets" (1935)**, for the argument every rule
  but two rests on.
- **Régin, "A Filtering Algorithm for Constraints of Difference in CSPs" (AAAI
  1994)**: the generalised arc consistent propagator, maximum matching plus
  strongly connected components of the residual graph. Ours is that algorithm,
  with a persistent matching repaired by augmenting paths (#526) and the
  unmatched-value sweep skipped for square constraints.
- **López-Ortiz, Quimper, Tromp and van Beek, "A Fast and Simple Algorithm for
  Bounds Consistency of the Alldifferent Constraint" (IJCAI 2003)**: the bounds
  consistent propagator, union-find over sorted bounds. Ours adds the re-sweep
  only when a written bound snapped past a hole, which is what makes it
  idempotent against a holey domain.
- **Régin, "The Symmetric Alldiff Constraint" (IJCAI 1999)**: the generalised arc
  consistent algorithm for `SymmetricAllDifferent`, via non-bipartite matching,
  which we do not implement; ours is the bipartite algorithm plus channelling.
- **Elffers, Gocht, McCreesh and Nordström, "Justifying All Differences Using
  Pseudo-Boolean Reasoning" (AAAI 2020)**: the first pseudo-Boolean justification
  of all-different, mostly by example, over sequences of guesses as reasons, on a
  different encoding. **McIlree's thesis, §3.4, JP 3.16 and 3.17**, restates it
  as procedures over Encoding Procedure 3.9 — the encoding we write — with
  correctness proofs; that is what rules 1 and 2 cite.

**What is ours, and so what a paper would have to argue rather than cite:** the
bounds consistent justification (rules 5 and 6), which we have found published
nowhere — the thesis certifies only the domain consistent algorithm; the three
departures from JP 3.16 and 3.17 listed in the catalogue's preamble, of which the
at-most-ones spanning the whole scope and cached at `Top` is the one that changes
proof size; `AllDifferentExcept`'s phantom vertices together with the excluded
values' disequalities in the Hall reason; and the duplicate forcing. None of them
is deep. The bounds consistent one is the one worth a paragraph, because naming
every value between a variable's bounds in its at-least-one, holes included, is
what lets a propagator that knows only bounds produce a reason that is only
bounds.

## Further reading

- [optional-interior-pruning.md](../optional-interior-pruning.md) — the
  mechanism this family is the counterexample for. Read its two promises beside
  [Interior values and optional pruning](#interior-values-and-optional-pruning).
- [large-domains.md](../large-domains.md) — the audit lane, the hazards H1a to
  H3, the proof-size lane, and two sections about this family specifically:
  "At-least-one constraints span the definition range (#939)", which is why the
  Hall proofs no longer grow with the declared width, and "AllDifferent's
  compressed value set was quadratic", which is e45b8e1a's measurement.
- [justification-techniques.md](../justification-techniques.md) — Theorems
  2.6–2.9 and the procedure table, which this audit extends with JP 3.16 and
  3.17 and with this family's two uses of JP 3.1.
- [propagator-performance.md](../propagator-performance.md) — the scratch-reuse
  and reason-guarding levers this family both uses and, in rule 2, does not.
- `gcs/innards/proofs/am1_from_pairs.hh` — `recover_am1_from_pairs`, the fold
  every Hall at-most-one goes through, and #805's account of the three
  hand-rolled folds it replaced.

## Developer commentary

**What fixing the audit taught**, which is about the next family's fixes more
than this one's.

- **A finding is a place to look harder, not only a thing to fix.** Two of the
  six fixes found a second wrong answer in the code the finding pointed at:
  `Inverse`'s value set, exposed the moment the MiniZinc fix let two different
  starts through, and the value consistent arm's unassigned list, exposed by the
  enumeration lane that fixing its trigger made worth writing. Fixing either
  finding as filed and stopping would have found neither.
- **Re-measure an issue's headline after its named fix.** #988 put 8 s and
  1.33 GB at width 10⁷ on the forcing loop. Fixing the loop alone moved the time
  by 9% and the memory not at all; the cost was `prepare()`'s value set, one
  function over. The audit's probe measured the right thing and attributed it to
  the wrong line.
- **The proof question an issue asks first can have a simpler answer than
  either option it offers.** #988 asked whether the per-value lemmas carry over
  to a range, or whether bound lemmas are needed instead. The range needs
  neither.

**The family's history is a performance arc, and it is worth knowing in order.**
#522 found the generalised arc consistent propagator rebuilding everything from
scratch on every wake — five adjacency lists of dozens of tiny allocations, a
`std::function` recursive Tarjan, a matching rebuilt greedily. #523 hoisted the
buffers into a reusable scratch, made Tarjan iterative and built edges by
sweeping domains; #524 staged the propagator behind the cheap value consistent
pass; #526 made the graph implicit, kept the matching across wakes and skipped
the unmatched sweep for square constraints. Together, 7.88 s to 3.93 s on
`langford --size=11`. e45b8e1a then removed a quadratic from the install-time
value set, and #970 added the bounds consistent arm. What is left of #522 is the
incremental SCC decomposition. Every one of those changes kept the search tree
and moved the proof's shape, which is why proof-line figures for this family
should always carry a commit.

**Two classes, one `prepare` idiom, two different reasons it is safe.**
`AllDifferent::prepare` does `_sanitised_vars = move(_vars)` on a `const`
member, which silently copies; `AllDifferentExcept::prepare` does the same on a
non-`const` one, which really moves, leaving `_vars` empty for `clone()` and
`s_expr()` to read. That is safe only because `Constraint::install` is
`&&`-qualified — a prepared object is consumed and never cloned or serialised
again, and the `.scp` is written from the unprepared originals the problem
keeps. Nothing is wrong. It is recorded because it is the shape of #865, where a
`clone()` did lose a member, and the next person to reach for `_vars` after
`prepare` in either class should know which of the two they are in.

