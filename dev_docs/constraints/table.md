# Table: `Table` and `NegativeTable`, and the extensional propagator behind them

> **Maturity** production ·
> **Audited** 2026-09-27 at `c9ceea25`; re-audited 2026-10-08 at `0a5b4ec6`
> for #1115 and #1117 ·
> **Open issues** filed from this audit: a wide domain is still walked value
> by value on three paths, one of them on every call (#1116), and
> `table::Auto` no longer picks the faster arm on Renault (#1118). **Fixed
> since the audit**: #1115 (overlapping tuples made the proof's solution
> lines fail), by #1202, and #1117 (extreme tuple values overflowed
> arithmetic or threw `IntegerOverflow` or a `ProofError`), by #1215; see
> [Re-audit, 2026-10-08](#re-audit-2026-10-08). Already open and touching
> this family: #503 (the engine, which is where the remaining gap to Gecode
> is), #364 (incrementality survey), #833 (large domains), #131 (a generic
> watched-clause propagator, which would subsume `NegativeTable`'s), #868
> (cross-solver). Tracked under #871.

### Re-audit, 2026-10-08

Two of the audit's issues have been fixed, and two fixes from elsewhere
touch this family. This pass brings the text into line with them at
`0a5b4ec6`.

| Issue | Fixed by | What changed here |
|---|---|---|
| #1115, overlapping tuples fail the solution line | #1202 | `Table`'s OPB gives each tuple a proof flag reified both ways and adds one labelled at-least-one, with no at-most-one and no two-tuple special case: cake's encoding. The summary loses its first bullet; [Semantics](#semantics), [Variable kinds](#variable-kinds-and-views), the `smart_table` merge note, [OPB encoding](#opb-encoding) (rewritten, with the old selector as history), [Labels](#labels), [Cake conformity](#cake-conformity), [Proof-time state](#proof-time-state), the catalogue's preamble and rule 2, [Tests](#tests), [Proof performance](#proof-performance), [Proof-logging gaps](#proof-logging-gaps), [Known limitations](#known-limitations), [Next steps](#next-steps) items 1, 3, 6 and 9, and [Prior art](#prior-art) |
| #1117, extreme tuple values | #1215, on #1214's range | a tuple value outside `S = −(2^60 − 1) .. 2^60 − 1` is refused with `IntegerOverflow` when the `Table` or `NegativeTable` is constructed, and #1214 refuses a declared domain or view offset outside `S`; [Semantics](#semantics), [Robustness and limits](#robustness-and-limits) (the overflow findings become history), [Interval efficiency](#interval-efficiency)'s widest domain, [Tests](#tests), the gaps, [Known limitations](#known-limitations) and [Next steps](#next-steps) item 8 |
| #1200, views registered after the rows that use them (not this audit's) | #1208 | a view that a `Table` row names gets its own bit vector, and its `=` literals are defined over it: [Variable kinds and views](#variable-kinds-and-views) |
| XCSP3 integers past `int` (no issue) | #1217 | the reader refuses a tuple value past `int`, and `2147483647`, its wildcard; the `<extension>` footnote and [Tests](#tests) |

#1266 (`Regular`'s ambiguous automata) changes nothing here.

**What was measured again**, at `0a5b4ec6` on fataepyc-10: the encoding's
shape and size (`opbsize.cc`), the degenerate shapes, the old overlap and
extreme-value repros and their in-range edges, the four chain cases under all
three `opbdiff` modes, the hand-built dependency sets of Next steps item 3,
the test caps, and the whole [Proof performance](#proof-performance) table,
with a same-sitting VeriPB control on the audit's OPB. Probes are under
`tmp/fd871-comments-1008/tables/probes/`; `raster_edge.cc` and `constpos.cc`
there come from the fact-check of this pass, and were re-run. **Not re-run**, and still at
`c9ceea25`: the CPU tables against Gecode and the forced arms, the corpus
shares, the [Interval efficiency](#interval-efficiency) timings and proof
sizes, the brute-force GAC checks, the second fact-check's 920-inference
hint campaign and the link-line counterexample. The propagator has not
changed since the audit: `extensional_utils.{hh,cc}` differ only in a
comment, and `table.cc` and `negative_table.cc` only in the constructors'
range checks and `Table::define_proof_model`. Every line citation holds at
`0a5b4ec6`: `table.cc`'s are updated, and the other files cited are
unchanged since the audit, or changed only below the lines cited.

Two constraints over an explicit list of tuples. `Table` requires the variables
to take one of them, and `NegativeTable` requires them to take none. `Table` is
generalised arc consistent, through one shared helper, `propagate_extensional`,
which also runs the tables that the `AutoTable` presolver builds and the tables
the tabulated arithmetic and linear constraints derive in the proof. This
document owns that helper, so it owns their propagation rules too.
`NegativeTable` is a different algorithm entirely: each forbidden tuple is a
clause, watched by two literals.

Three things to know before touching it.

- **The algorithm choice is invisible to every front end.** `table::Auto` is the
  default and the only setting MiniZinc, XCSP3 or `gcspy` can reach. It watches
  32 wakes and then switches to a compact table (bitsets) where the live set is
  big and dense enough. Against Gecode on the same tree, `Table`'s search is
  1.1–1.3× slower on Crossword, 2× on Dubois and 1.4–4.2× on the synthetic
  matrix. End to end it is ahead on most Renault and Kakuro instances, whose
  cost is posting, but 1.8× behind on the two small Renaults. #508's measurements
  put most of what remains in the engine (#503), not the table.
- **A wide domain is trimmed to the table's values once, at the root**, which is
  what keeps a `0..10^9` variable from costing its width. There are three ways
  round the trim.
  - It runs after the domain rasteriser, so a table of eight or more tuples,
    or any table under a forced `table::CompactTable`, still walks the whole
    of a variable's domain once, on a column the rasteriser accepts.
  - It runs only on the live-set path, so a forced `table::CompactTable`
    removes every out-of-range value separately, at about 34 proof lines each.
  - It never touches a column where any tuple has a wildcard. While a
    wildcard row there is live, the support scan walks the whole domain **on
    every call**, even with only two tuples and under the default algorithm.
    Once none is, the scan removes the unsupported values one at a time:
    33,942 proof lines at width 1,000.

  See [Interval efficiency](#interval-efficiency).
- **`NegativeTable` is not generalised arc consistent**, nor even `bounds(D)`
  on the constraint. It enforces each forbidden tuple's clause separately. `x, y ∈ {1, 2}` with `(1,1)` and `(1,2)`
  forbidden leaves `x = 1` in the domain at the root.

## What it is

### Semantics

- **`Table(vars, tuples)`** — `(vars[0], …, vars[k-1]) ∈ tuples`. A tuple entry
  is an `Integer` or, in `WildcardTuples`, a `Wildcard` matching any value.
  - Every tuple must have `k` entries, or `prepare()` throws
    `InvalidProblemDefinitionException{"table size mismatch"}`.
  - **No tuples** is unsatisfiable: `prepare()` notes it, the OPB gets `0 ≥ 1`,
    and an initial-contradiction initialiser fires with an important message on
    standard error ("A Table constraint was posted with no tuples, so the model
    is unsatisfiable before search starts").
  - **Arity 0** with one empty tuple is no constraint. With no tuples it is
    unsatisfiable, as above.
  - **Every tuple value must lie in `S`**, the solver's integer range
    `−(2^60 − 1) .. 2^60 − 1` ([`integer-ranges.md`](../integer-ranges.md)),
    wildcard tuples included. The constructor throws `IntegerOverflow`
    otherwise (`table.cc:53`, since #1215), before `prepare()` runs.
  - Tuple values outside a variable's domain are allowed and simply never
    match. Duplicate tuples and overlapping wildcard rows are allowed, solve
    correctly, and, since #1202, verify (see [OPB encoding](#opb-encoding)).
  - A variable may appear twice, directly or as a view. The tuples whose two
    positions disagree then never match. That works, but it is weaker than
    generalised arc consistency: see [Propagator inventory](#propagator-inventory).
- **`NegativeTable(vars, tuples)`** — for every tuple `t`, some `vars[i] ≠ t[i]`.
  A wildcard position never differs, so it can never satisfy the clause.
  - Every tuple must have `k` entries, or `prepare()` throws the same exception.
  - Every tuple value must lie in `S`, as for `Table` (`negative_table.cc:125`).
  - **No tuples** is no constraint.
  - **An all-wildcard tuple**, or **arity 0 with one empty tuple**, is
    unsatisfiable, and is detected at the root.
  - Duplicate forbidden tuples are harmless (tested).

All of these were probed with proofs on and VeriPB accepted every one
(`tmp/fd-table/probes/degen.cc`, 13 shapes). The length mismatch throws.
Re-run at `0a5b4ec6`, under #1202's encoding, with the same outcome
(`tmp/fd871-comments-1008/tables/probes/degen.cc`).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Table` | ✓ `fzn_table_int`, `fzn_table_bool`; `decompose` for the reified forms[^mznreif] | ✓ `<extension>` with `<supports>`, including `*` and shared tuples[^xext]; `in` inside an intension[^xin] | ? | ✓ `table` | always `table::Auto` |
| `NegativeTable` | `n/a`: MiniZinc has no negative table | ✓ `<extension>` with `<conflicts>`[^xext]; `notin` inside an intension[^xin] | ? | ✓ `negative_table` | |

[^mznreif]: `glasgow_table_int` / `glasgow_table_bool` post `Table` with the
    rows flattened, after checking the arity is non-zero and divides the array.
    GCS provides no reified table, so MiniZinc's standard library
    `fzn_table_int_reif` applies. It builds an extended table over the product
    of the variables' domain sizes, with the reification as one more column, and
    **refuses more than five variables** (an assertion in the library, not a
    solver error). The optional form `fzn_table_int_opt` is the library's
    element decomposition. MiniZinc 2.9.7 and 2.10.1 both keep duplicate rows
    in the flattened table.

[^xext]: `buildConstraintExtension` turns `*` into `Wildcard` and posts
    `Table` or `NegativeTable` over `SharedWildcardTuples`. The `extensionAs`
    callback reuses the previous constraint's tuple object, so a group of
    constraints over one relation shares one tuple list, and its support masks
    too (see [Initialisation](#initialisation-and-global-data)). The parser
    takes that callback for a `<group>` member only when its variables'
    domains equal the previous member's (`XCSP3Manager.cc:1415-1429` in the
    fetched parser). The unary form is the same with one column. Since #1202,
    `xcsp_extension_overlap` exercises supports, `*`, a `<group>` that takes
    `extensionAs`, an exact duplicate and the unary form; no lane posts
    `<conflicts>` (see [Tests](#tests)). Since #1217 the patched parser
    (`xcsp/xcsp3_parser_integer_overflow.patch`) refuses a tuple value that
    does not fit in an `int`, and `2147483647`, which it uses for `*`,
    rather than misreading either.

[^xin]: `in(x, set(…))` and `notin(x, set(…))` inside an `<intension>` post a
    unary `Table` or `NegativeTable` over the set.

`gcspy` binds `post_table` and `post_negative_table`, over `SimpleTuples`, with
no wildcards. `python_test.py`'s `test_table` exercises the first; that file
runs nowhere (#1078). Whether the CPMpy side reaches either binding was not
checked.

### Options

`NegativeTable` has none.

**`Table::with_algorithm(TableAlgorithm)`**, where `TableAlgorithm` is
`std::variant<table::Auto, table::LiveSet, table::CompactTable>`. Requesting
anything else is a compile-time error.

- `table::LiveSet` keeps the live tuples in a sparse set and re-tests each of
  them against the domains on every wake. It costs what is live, except on a
  column where some tuple has a wildcard, whose whole domain it scans on every
  call (see [Interval efficiency](#interval-efficiency)).
- `table::CompactTable` keeps them in a bitset, with a support mask per (column,
  value), and removes the tuples that used a value as the value goes. It costs
  what changed. It is forced from the first call.
- `table::Auto`, **the default**, runs the live set and watches. After 32 wakes
  it switches to the compact table if the mean live count over those wakes is
  at least 16 and at least one in 64 of the tuples, so that a bitset's words are
  worth scanning. A table of fewer than 64 tuples never gets the state that
  would let it switch. The thresholds and their measurements are in the
  comments on `ExtensionalCompactTable` (`extensional_utils.hh:237-273`), from
  #804. **Re-measured here, they no longer pick the better arm everywhere**:
  forced compact is 2.2× faster end to end on Renault, which `Auto` never
  switches on (see [Developer commentary](#developer-commentary)).

The compact table cannot run on a column holding a wildcard, on a column whose
values span more than 4,096 (64 words), or where the masks would exceed 16M
words for the tuple set. In any of those cases it falls back to the live set
for every constraint over that tuple set.

**The option never changes the OPB model or the search tree**: the three
algorithms write byte-identical `.opb` files, and every table test and
benchmark instance explores the same nodes under each. It **does change the
proof** when a domain extends past its column's range, which the header comment
on `TableAlgorithm` says it never does: see [Interval
efficiency](#interval-efficiency). No front end exposes the option. Only the
`tables` example (`--table`) and the benchmark driver do.

There is no `with_consistency`. `Table` is always generalised arc consistent;
`NegativeTable` always propagates each clause.

### Variable kinds and views

Both accept any `IntegerVariableID`: plain variables, constants and views. A
constant position works the way a fixed variable does. At the model level a
tuple entry a constant cannot take gives that tuple's flag a unit row
`¬flag ≥ 1` (`table.cc:199-200`), and a matching entry is left out of the
flag's rows. Both views and constants are tested
(`table_constraint_view_mixed`, `negative_table_constraint_view_mixed`, and,
since #1202, `run_constant_table_test`, `table_test.cc:191`, which posts a real
`ConstantIntegerVariableID` with a tuple it rules out).

**The proof handles views.** Every rule states literals on the positions as
posted. Since #1208, a view that a model row names gets a bit vector of its
own when the row is written, and its `=` literals are defined over that, with
two channel rows to the underlying variable: a `Table` over `x + 3` names
`p[0_view_of_x_plus_3][eq4]` and so on, each defined (rows labelled
`@po[0][eq4][r]` and `[f]`) over the view's `≥` literals, `p[…][ge4]` and
`p[…][ge5]`, which are defined in turn over its bits `p[0_view_of_x_plus_3][b…]`
(`tmp/fd871-comments-1008/tables/probes/enc.cc view`). The view lanes run
with proofs.

### Reification

`None.` There is no reified or half-reified `Table` or `NegativeTable`.
MiniZinc's reified table becomes an ordinary `Table` with an extra column,
built by its standard library. That is exponential in the arity, and it stops
at five variables ([Frontend coverage](#concrete-constraints-and-frontend-coverage)).
Nothing in the corpus asked for one.

### Relation to other families

- **Decomposes into this family:** MiniZinc's reified tables, and XCSP3's `in`
  and `notin` inside an intension.
- **Child constraints:** none.
- **Shares its code.** `propagate_extensional` (`extensional_utils.{hh,cc}`) is
  the propagator for three other callers, each with its own table:
  - the **`AutoTable` presolver**, which enumerates the solutions of its donor
    constraints over a scope and installs the extensional propagator over them,
    with no hint and no owning constraint (`auto_table.cc:110-173`);
  - **`install_tabulation`** (`innards/tabulation.hh:312-340`): the
    `consistency::Tabulated` arm of `Plus`, `Minus`, `Multiply`, `Divide`,
    `Modulus`, `Power` and `LinearEquality`, and for the arithmetic classes also
    `consistency::Auto` within a size budget (when and how is `arithmetic.md`'s
    business). Each derives its table in the proof and passes its own hint;
  - `Table` itself, with `hints::Table`.

  So a change to the helper is a change to all of them, and so is a change to
  `ExtensionalCompactTable`'s thresholds. The rules in this document's catalogue
  are theirs as well. Their table-building rules belong to `arithmetic.md` and
  `linear.md`, and the presolver's own pass to its document, not yet written.
- **`NegativeTable` shares a design, not code, with the refined nogood store**
  (`nogoods.cc`, `install_refined_nogoods`): two watches per clause, the watched
  positions packed into `watch_state`, and the set-up count kept in
  `watch_state` so that `AutoTable`'s throwaway root search cannot strand it
  (#1106, fixed for both by #1107). #131 proposes a generic watched-clause
  propagator, which would be the natural home for both.
- **Presolvers:** `AutoTable` installs this family's propagator. No presolver
  rewrites a posted `Table` or `NegativeTable`.
- **Reachability:** both classes are posted directly by the front ends. The
  propagator is exercised directly by all of them.

**The candidate merge with `smart_table` is settled: separate** (Ciaran,
2026-09-26). `SmartTable` does not use `extensional_utils`. Since #1202 both
encodings give each tuple one proof flag, reified both ways, under one
at-least-one; what differs is the entries. `SmartTable`'s are themselves
constraints (`<`, `≤`, `=`, `≠`, `>`, `≥`, set membership), each with a flag
of its own, where `Table`'s are equality literals. Its propagator is a different
algorithm. And it is reached only from the `.scp` reader and as the engine
underneath `LexSmartTable` and `AtMostOneSmartTable`. It has its own document.

## The proof model

### OPB encoding

**`Table`**, for tuples `t_0, …, t_{m-1}` over `vars` of arity `k`, with one
proof flag `f_j` per tuple, named `x[id][j]` (`table.cc:163-211`, since #1202):

```
  for each tuple j that no constant position rules out, with n_j the number of its entries
  [x_i = t_j[i]] that are not wildcards and not constant true:
    @x[id][j][r]   n_j·¬f_j + Σ_i [x_i = t_j[i]] ≥ n_j      f_j ⇒ tuple j matches
    @x[id][j][f]   f_j + Σ_i ¬[x_i = t_j[i]] ≥ 1            tuple j matches ⇒ f_j
  for a tuple with an entry a constant position cannot take:   ¬f_j ≥ 1
  @c[id][al1]      Σ_j f_j ≥ 1                               at least one tuple
  with no tuples at all:                                     0 ≥ 1
```

The `[f]` row is written in normalised form (`−Σ_i [x_i = t_j[i]] + f_j ≥
1 − n_j`). There is **no at-most-one**, and no special case for two tuples.
This is `cake_pb_cp`'s table encoding, with its flag names and labels. A
tuple whose entries are all wildcards or constant true has `n_j = 0`, so its
`[r]` row is the trivially true `1 ~f_j ≥ 0` (cake writes `0 ~f_j`) and its
`[f]` row the unit `f_j ≥ 1`. The encoding is **definitional**: the rows say
which tuples are allowed and nothing more, and every flag is determined by unit propagation on a
complete assignment, which is what the solution line needs. Its size is
`2m + 1` rows for the `m` tuples no constant position rules out, plus one
unit row per tuple one does, with at most `2(k + 1)` terms per such tuple in
the flag rows and `|T|` in the at-least-one, ruled-out flags included. A
tuple whose value lies outside a variable's domain can never match either,
but it gets both halves like any other. Measured at `0a5b4ec6` with arity 3 over `0..9`: 10,
100 and 1,000 tuples give 20, 200 and 2,000 flag rows plus the at-least-one,
with 80, 800 and 8,000 terms in the flag rows. The shared layer's `=` and `≥`
definitions come to 92, 126 and 126 rows, as at `c9ceea25`, because they are
bounded by arity × domain, not by the table
(`tmp/fd871-comments-1008/tables/probes/opbsize.cc`, a copy of the audit's
`tmp/fd-table/probes/opbsize.cc`). Nothing is proportional to a domain's
width.

**Before #1202** the encoding was a proof-only selector `s ∈ 0..m−1` in the
direct encoding, an exactly-one over its values, and one row per tuple saying
only `s = j ⇒ tuple j matches`: `|T| + 2` rows, and with exactly two tuples a
single selector bit with no selector rows. On a solution that two rows
matched, with three or more tuples, two selector literals were left
unassigned by unit propagation, and VeriPB rejected the solution line
(`solx`, or `soli` when optimising): #1115, found by this audit, with a
three-row duplicate, a three-row wildcard overlap and an XCSP3 wildcard
overlap as repros (`tmp/fd-table/probes/duptup.cc`,
`tmp/fd-table/factcheck/fc_*`, `star2.xml`). At `0a5b4ec6` the same three
shapes verify (`tmp/fd871-comments-1008/tables/probes/enc.cc dup|wild3`, and
`star2.xml` through `xcsp_glasgow_constraint_solver --prove`).

**This is the thesis's Encoding Procedure 3.10 without its exactly-one.** EP
3.10 reifies each tuple flag both ways, `t_j ⇔ Σ_i [x_i = τ_j[i]] ≥ n`, and
adds `Σ_j t_j = 1`. That is only satisfiable when no two tuples match one
assignment: the thesis's `τ` is a set, with no wildcards. With the reverse
halves present, an at-most-one would make an assignment two rows match
infeasible and lose solutions, which is why there is none. JP 3.3 and 3.4
use only the forward halves, `f_j ⇒ match`, so every propagation rule
certifies against them (see [What licenses rules 2–5](#inference-catalogue)).

**#1115 never affected the other tables:** `AutoTable`, whose tuples are distinct
full assignments with `red` lines reifying each selector value both ways
(`auto_table.cc:71-82`); the tabulated constraints, whose rows are disjoint
(`tabulation.cc:95-160`); and `NegativeTable`, which has no auxiliary and
verifies with duplicated or overlapping forbidden rows.

**`NegativeTable`**, one clause per forbidden tuple:

```
  for each tuple t:   Σ_{i : t[i] not a wildcard} [x_i ≠ t[i]] ≥ 1
```

This is **definitional**, with one row of at most `k` terms per tuple and no
auxiliary. An all-wildcard tuple is the empty clause.

### Labels

Since #1202, `Table` labels its flag rows `@x[id][j][r]` and `@x[id][j][f]`
and its at-least-one `@c[id][al1]`, cake's labels; the unit row of a tuple a
constant position rules out is unlabelled. `NegativeTable` labels nothing. No rule cites a row by
label. The `=` and `≥` literal definitions carry the shared layer's labels.

### Cake conformity

The `.scp` spellings are `table` and `negative_table`, with each tuple a list
whose entries are integers or `*`. The solver and `cake_pb_cp` agree on this
shape exactly.

**Since #1202 the table rows agree**, except an all-wildcard tuple's trivially
true `[r]` row (below).

- `Table`: cake gives each tuple a fully reified flag (`@x[_1][j][r]` and
  `[f]`) and one at-least-one (`@c[_1][al1]`), with no at-most-one, and so now
  does GCS, with the same names and labels. Before #1202 GCS had one
  direct-encoded selector with half-reified rows and an exactly-one,
  unlabelled.
- `NegativeTable`: the clauses are the same shape, and only the labels
  differ: cake labels clause `j` `@c[_1][<j>al1]`, and GCS leaves it
  unlabelled.

Four chain cases, all registered `none`: `scp_chain_table_sat`,
`scp_chain_table_unsat`, `scp_chain_negative_table_sat` and
`scp_chain_negative_table_unsat`. All four pass the full workflow-2 chain at
`0a5b4ec6`, run by hand with cake on the path
(`tmp/fd871-comments-1008/tables/probes/chain/`). Since #1202 the registration
comment in `verified_encodings/scp_cases/CMakeLists.txt` (lines 486-499) no
longer blames #358. It says the table rows have cake's shape and labels, and
that what still differs is how variables are written, plus that
all-wildcard row. Run with `aux` or
`strict`, each case fails `opbdiff` on one or two rows, all of them `≥`-literal
definitions for a value at or outside a variable's bounds, which GCS writes
with a 1 coefficient on the literal where cake writes 0
(`@i[A][ge0][r] 1 i[A][b0] 2 i[A][b1] 1 ~i[A][ge0] >= 0` against cake's
`0 ~i[A][ge0]` over `0..2`, and `@i[A][ge4][f]` in `table_unsat`). #1202's
body adds two causes that its 3,000-instance sweep found and these four cases
do not reach: an all-wildcard tuple's trivially true row (`1 ~x ≥ 0` against
cake's `0 ~x ≥ 0`), and a `{0, 1}` variable's `=` literals, which GCS writes
as its bit (#1193). So the cases stay `none`.

**Before #1202, the chain passed where GCS's own OPB failed.** A three-row
table with a duplicate row passed `run_scp_chain.bash`, since cake's encoding
already reified each tuple both ways, while the same proof against GCS's own
`.opb` was rejected at the first solution line. With the encodings now
agreeing on the table rows, that gap is closed.

### Proof-time state

- **`Table`: one proof flag per tuple**, `x[id][j]`, created in
  `define_proof_model` with no `State` (since #1202). **No proof line ever
  cites one**: every rule's RUP goes through the flags by unit propagation
  from the variables' literals. They are not in `preserved:`, and every flag
  is **determined by unit propagation on a solution**, through its `[r]` or
  `[f]` row or its unit row, however many rows the solution matches. Nothing
  is emitted at the root and nothing is deleted. Before #1202 this was one proof-only integer,
  `aux_table<id>`, whose `=` literals were left undetermined on a solution
  that two rows matched, in a table of three or more tuples (#1115).
- **`NegativeTable`:** none.
- **`AutoTable`'s table** has a `State` selector, whose identifier is reserved
  before the presolver's search and allocated after it. Its literals are
  introduced in the proof as the search finds each tuple, with two `red` lines
  per tuple (named `autotable`). **At any assertion level other than `Off`
  those lines are skipped**, so a hints-only proof holds no rows for its
  inferences at all. The tabulated constraints skip their in-proof table the
  same way (`arithmetic.md`, tabulate-relation).

## The implementation

### Initialisation and global data

**`Table::prepare`** (`table.cc:123-161`) does the following.

- It checks the tuple lengths and notes an empty table.
- It creates the live set: dense and position arrays of `|T|` entries, plus one
  backtracked `size_t` through `add_constraint_state`.
- Unless the algorithm is `LiveSet`, it creates the compact-table state. Under
  `Auto` that is `nullptr` below 64 tuples. The state is one more backtracked
  `size_t`, and it asks `Propagators::shared_derived_data` for the support masks
  keyed on the tuple object's address. A crossword's twenty constraints over one
  dictionary share one set of masks (`shared_tuples_test` checks that three
  constraints over one tuple set find one set of masks).

**The first propagator call, at the root,** does the rest.

- It lays out the per-column rasterisation, using each column's range of
  **table** values, up to 64 words; a column with a wildcard is excluded.
- It then trims every variable to what its column can supply (rules 2 and 3):
  two bound pushes for a rasterisable column, and one range removal per gap
  between the column's distinct values otherwise.
- It sizes the residue rows by the column's table range. They used to be
  sized by the variable, and three `0..10^9` columns asked for 12 GB (#833's
  work, per the code's comment).
- **This trim runs only on the live-set path, and after the rasteriser**, which
  is the root-width finding (#1116). It also skips any column where a tuple
  has a wildcard, live or not. `tuple_value_set` reads the whole tuple list,
  so a wildcard row that is already dead at the root still blocks the trim.

**`NegativeTable`** installs an initialiser that walks every tuple once, at the
default priority, looking for a tuple already violated or unit against the
initial domains. Its propagator's first run, also at the root, then arms two
watches per tuple.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| `Table` empty-table initialiser | initialiser | — | 1 | no tuples | n/a | one shot |
| `propagate_extensional` for `Table` | `on_change` on every position | derived, truthfully | 2–5 | at least one tuple | **claimed** (`EnableButIdempotent`); the engine ignores the claim when two positions share a variable | no |
| `propagate_extensional` for `AutoTable` | `on_change` on the presolver's scope | derived, truthfully | 2–5 | the presolver found at least one tuple | claimed, as above | no |
| `propagate_extensional` for a tabulated constraint | `on_change` on the enumerated variables | derived, truthfully | 2–5 | the tabulation initialiser built a table | claimed, as above | `DisableUntilBacktrack` if the table was empty |
| `NegativeTable` root detection | initialiser | — | 6, 7 | always | n/a | one shot |
| `NegativeTable` watched propagator | `scope_only` on every position, plus refined watches on `x_i = t[i]` armed at run time | derived as every position; **the truth is none** | 6, 7 | always, even with no tuples | not claimed, and not idempotent | no |

**Idempotence.** `propagate_extensional` claims it on both paths, and the claim
is argued in the code (`extensional_utils.cc:905-916`). A value survives only
if a live tuple matches it, and a live tuple's own entries are all still in
domain, so a re-run finds everything still supported. A repeated variable breaks
that: a tuple can be feasible position by position but not as an assignment.
The engine drops the claim whenever two positions share an underlying variable,
directly or through views. `table_test`'s lanes run with the claim checker on,
and so do the repeated-variable rows (`run_dup_table_test`).

`NegativeTable` returns `Enable`, correctly. A unit inference that leaves its
variable with one value makes that variable's `=` watches fire, which can make
another tuple unit on the next call.

**Strength with a repeated variable.** Pass 1 tests each position's entry
against its own domain, so `Table{x, x}` over `x ∈ {1, 2}` with the tuples
`(1, 2)` and `(2, 1)` keeps both values at the root, although the relation has
no solution: each value is supported at each position. Search then proves it
unsatisfiable (3 recursions; the proof verifies). With `(1, 2)` alone the
first call already fails. The first position removes 2, and the second then
finds 1 unsupported (1 recursion, 1 propagation; `tmp/fd-table/codex-r1/xx.cc`).
It gives the right answers and is
weaker than generalised arc consistency on the underlying variables. A
brute-force check (`tmp/fd-table/probes/gacbf.cc`, 3,000 random instances,
holey domains, views, wildcards, repeated variables) was run at every search
node. It found **no solution-set mismatch** under any algorithm. It found **no
non-GAC node on any instance with distinct variables**, and non-GAC nodes on 53
of the 1,866 instances with a repeated variable. Those tables have at most
eight tuples, so `Auto` never switches and is the live set, the rasteriser
barely runs, and the compact table is exercised only when forced. A second
run with up to 119 tuples (`gacbf_big.cc`, 1,500 instances, seed 7), which
makes the rasteriser run and the forced compact table work on tables above 64
tuples, found the same: no mismatch, and no non-GAC node with distinct
variables under any of the three settings. In that second run `Auto`
reached its 32-wake decision on 79 instances and switched to the compact
table on 18 of them, counted with a local print at the decision
(`tmp/fd-table/autoswitch/`, never committed); the result was the same on
those. `NegativeTable` had non-GAC nodes with distinct variables on 36 of
those 1,500 instances, and none in the smaller sample.

### Mutable state and incrementality

| State | Backtracked? | Why that is enough |
|---|---|---|
| live set (`ExtensionalLiveTuples`) | only its size | every deeper removal swaps within `[0, size)`, so restoring the size re-admits exactly the tuples dropped since. Order within the live region changes, which changes only which witness is found first |
| residual supports (`ExtensionalResidues`) | no | a stale residue is re-checked before use and re-sought if dead; a backtrack only makes more tuples live |
| rasterised domains (`ExtensionalDomainBitmaps`) | no | scratch, rebuilt at the top of every call that uses it |
| compact table: live words, their index, previous domains | through a propagator-owned undo trail and one backtracked trail mark | unwound lazily at the top of the next call. Nothing reads the arrays in between, so this is exact. Two constraint-state slots cost Dubois 14% before the limit moved onto the trail (#804) |
| support masks (`ExtensionalSupportMasks`) | no | read-only once built, and shared per tuple set |
| `NegativeTable` watch positions and set-up count | through the refined-watch `watch_state`, restored with the watches | the set-up count lives there because `AutoTable`'s throwaway root search would otherwise leave it saying "all armed" (#1106) |

The live-set path costs what is live per call, plus, on a column where some
tuple has a wildcard, a scan of that column's whole domain (see [Interval
efficiency](#interval-efficiency)). The compact path costs what
changed: for each column that lost values, it ORs the masks of whichever is
smaller, the removed values or the kept ones. The history of both, including
the measurements that chose them, is #508's project (#786, #795, #796, #799,
#804, #831, #832) and `propagator-performance.md`. That project concluded,
from measurements taken before #831/#832 and on fataepyc-10, that on every
benchmark instance but one, making the table propagator infinitely fast would
not close the gap to Gecode, and it put the remaining time in the engine
(#503).

### Interior values and optional pruning

**What this family offers:** `None.`

**What this family observes.**

- **`Table`: every hole in every position**, truthfully. It is generalised arc
  consistent, a hole can remove a tuple's support, and it wakes `on_change`.
- **`NegativeTable`, as declared: every position; in truth, none.** Its only
  question is whether `x_i = t[i]` is entailed, which only fixing `x_i` can
  make true. A hole can make a forbidden tuple's clause satisfied, but never
  unit. So no interior removal ever gives it an inference it could not already
  make. The declaration comes from `scope_only` plus the `=` watches, which the
  engine reads as hole-sensitive. That over-reports. It is safe, and it keeps a
  neighbouring `Element`'s interior pruning alive for nothing. Declaring
  `holes_affect_propagation = {}` would say the truth; nothing measured says it
  matters. See [Next steps](#next-steps).

### Robustness and limits

- **Unbounded domains.** A declared domain must lie in `S = −(2^60 − 1) ..
  2^60 − 1`, and so must a constant and a view's offset, so a position's
  values reach at most `±(2^61 − 2)` (#1214). A constant position of `±2^62`
  or `−2^63 + 1` is refused when the constant is made
  (`tmp/fd871-comments-1008/tables/probes/constpos.cc`, from the
  fact-check). A wide domain is handled by the root trim: once
  trimmed, every later walk on that column is bounded by the table. The trim
  never runs on a column where some tuple has a wildcard, so there the support
  scan stays proportional to the domain on every call. That and the other two
  exceptions are in [Interval efficiency](#interval-efficiency).
- **Tuple values must lie in `S`** (#1215). `Table` and `NegativeTable` call
  `innards::require_bounded` on every tuple value in their constructors,
  wildcard tuples included (`table.cc:53`, `negative_table.cc:125`), and throw
  `IntegerOverflow` for one outside `S`, before `prepare` or
  `define_proof_model` runs. An out-of-range value is refused, not dropped:
  it could match a view, and dropping it would hide the caller's mistake
  ([`integer-ranges.md`](../integer-ranges.md), "Do not narrow the rule by
  dropping inputs"). A view can still take values past `S`, but no tuple can
  name them. A value outside `S` from any front end or the C++ API is
  refused, at the latest by the constructor; XCSP3's patched parser refuses
  anything wider than an `int` first (#1217).

  With every input in range, `extensional_utils.cc`'s arithmetic, unchanged
  since the audit, cannot overflow: a column's span (`:617`) is at most
  `2 · (2^60 − 1)`, and the rasteriser's offset `value − base` (`:677`), a
  position's value less the column's least tuple value, is at most
  `3 · (2^60 − 1)` in magnitude. That is an argument from the bounds, not a
  sanitizer run. In-range edges verify: `integer_ranges_test` solves a `Table`
  whose rows name both ends of `S`, over two positions of three values at one
  end of `S`, each plain, negated or offset by an end of `S`, in six
  configurations, against brute force, with and without proofs
  (`integer_ranges_test.cc:324-336`, since #1214); and at `0a5b4ec6` a plain
  variable over all of `S` with a two-row column at either end, and views
  `x + (2^60 − 1)` and `−x − (2^60 − 1)` near their far reach against tuple
  values at the ends of `S`, all verify
  (`tmp/fd871-comments-1008/tables/probes/table_edges.cc`). So does the
  rasteriser's own shape: eight column values clustered at one end of `S`
  (span 7, so the column is rasterisable and `:677` runs), against
  `x ∈ 0..1000` (no solution) and against `x` within 1,000 of that end (eight
  solutions), at both ends, under the default algorithm and a forced
  `table::CompactTable` (`raster_edge.cc`, from the fact-check; all eight
  proofs verify). `table_edges.cc`'s `far8top` and `far8bot` shapes, a column
  spanning `0..6` and one end of `S`, are wider than 64 words, so the
  rasteriser skips that column (`extensional_utils.cc:617-620`).

  **Before #1214 and #1215** (#1117, at `c9ceea25`): variables were capped at
  `±2^61`, tuple values and view offsets were not capped at all, and
  arithmetic on differences between tuple values and domain values assumed
  they fit. A column spanning more than 2^63 overflowed the span computation
  (UBSan; a release build fell back and answered correctly), and a column far
  from a narrow domain overflowed the rasteriser's offset. With proofs on, a
  tuple entry about 2^63 from a plain variable's bound threw a `ProofError`
  or `IntegerOverflow` in `Table::define_proof_model`, not in the root trim
  where #1117's body put it. This audit also found a view `x + 2^62` and an
  entry `−2^63 + 1` throwing with proofs on, and a view `x − 2^62` throwing
  with proofs off, in pass 1 (`tmp/fd-table/codex-r1/extcrash.cc`). Every
  one of those inputs is now refused when the view or the `Table` is
  constructed (`table_edges.cc a|b|c`), and so is the `x + 2^62` control,
  `Table({x + 2^62}, {(2^62), (2^62 + 1)})`, which used to verify with two
  solutions (`tmp/fd-table/codex-r1/extview.cc`).
- **Negative values and zero.** Tested over `[-2, 2]` in both classes.
- **Degenerate shapes.** See [Semantics](#semantics): every shape probed
  verifies.
- **A repeated variable.** Correct, with the claim dropped and strength below
  GAC; see [Propagator inventory](#propagator-inventory).
- **Overflow elsewhere.** A flag row's coefficient is its count of literal
  terms, at most the arity, as an `Integer`. The rasteriser's offset is
  covered above.
- **Memory.** Support masks are capped at 16M words (128 MB) per tuple set.
  Above that, the compact table declines. The live set, residues and bitmaps are
  linear in the table, or in its column ranges up to 64 words a column.

### Interval efficiency

1. **Propagation.**
   - **The root trim** is width-free: bounds for a rasterisable column, and
     `each_interval_minus` against the column's distinct values otherwise. The
     second costs `|T| log |T|` to build.
   - **The support scan** (`for_each_value_mutable`, `extensional_utils.cc:864`)
     is a genuine per-value scan. It is how generalised arc consistency finds an
     unsupported value. Once the root trim has run it is bounded by the column's
     range (at most 4,096) or by its distinct values, **but not on a column
     where any tuple has a wildcard**. The trim skips such a column, and it has
     no residue row either, so every call visits every value of its domain and
     scans the live tuples for each one until one matches.
     - **While a wildcard row is live**, that row supports every value, so the
       walk finds nothing to remove and still visits the whole domain. With
       `x ∈ 0..W`, `y ∈ 0..1` and the two rows `(*, 0)` and `(1, 1)` under the
       default algorithm, a solve that stops at the root, after one
       propagation, takes 0.31 s at W = 10^8 and 3.06 s at 10^9.
     - **The walk recurs.** Ten such tables over `(x, y_i)`, with `Σ y_i ≥ 1`,
       branching on the `y_i` in order, give 2,045 recursions and 4,190
       propagations at every width. They take 0.10 s, 0.99 s and 9.6 s at
       W = 10^5, 10^6 and 10^7.
     - **Once no live row has a wildcard there**, the scan removes every
       unsupported value one at a time. A dead wildcard row still blocks the
       trim, because the trim reads the whole tuple list. The removals happen
       at the root when the row is already dead (`y ∈ 1..1` above). They happen
       again at every node where search kills the last live wildcard row, and
       backtracking undoes them.

     The timings are wall-clock time of the whole `solve_with` call
     (`steady_clock`), Release at `c9ceea25`, proofs off, fataepyc-10, pinned
     with `taskset -c 4` and `GLIBC_TUNABLES` (malloc's mmap and trim
     thresholds), median of three. The ten-table figures move by about 10%
     unpinned.
     A guard build trips on all three shapes at W = 2·10^5, in
     `for_each_value_mutable`, under all three algorithms. A one-row
     `{(1, 1)}` control neither trips nor grows under the default algorithm or
     a forced `LiveSet`. A forced `CompactTable` trips on it too, in the
     first path's rasteriser walk (`extensional_utils.cc:670`), which on the
     compact path runs on every call with no eight-tuple gate, before the
     compact dispatch at `:683` and before any trim. That is how one tuple
     reaches it. The per-value removals that follow are the second path. They
     empty the out-of-range values at the root, before the first solution, so
     only the root call walks the full domain
     (`tmp/fd-table/codex-r1/wild.cc`).
   - **The compact filter** (`:535`) walks the same values.
   - **The rasteriser** (`:670-681`, `for_each_value_immutable`) visits every
     value of each usable column's domain **whenever it runs**: on every
     compact-path call, and on live-set calls with eight or more live tuples.
     After the root trim that is bounded by the table. **At the root it runs
     before the trim**, so a table of eight or more tuples walks the whole of
     each domain once, on every column it accepts (no wildcard, table range
     at most 4,096 values). Release, 3 variables, 8 tuples: 0.39 s at width
     10^8 and 3.93 s at 10^9 (`probes/wide8.cc`). Over the widest legal
     domain, all of `S` (about ±1.15·10^18 since #1214; ±2^61 at the audit),
     that rate means it does not finish in any useful time, with or without
     proofs, whatever the tuple values.
     A guard build trips as soon as one call visits more than 100,000 values
     (at width 10^5 and above). A forced `table::CompactTable` never runs the
     trim at all.
   - **`NegativeTable`** never walks a domain: one `literal_is_entailed` per
     position per visited tuple.
2. **Reasons.** Both classes build `generic_reason` over the whole scope once,
   at install. It is materialised per run (#935) and only when something reads
   it. It is **not minimal**:
   - a `Table` range trim verifies with another variable's bound removed from
     its reason;
   - a `NegativeTable` unit verifies with the removed variable's own bounds
     removed.
3. **Proofs.** One RUP per removed value, and the root trims one per run. With
   a forced `table::CompactTable` over a domain wider than its column, the
   filter removes every out-of-range value separately. Each removal costs about
   34 proof lines, because its reason names a range literal and the
   range-literal layer re-derives an interval partition each time (at width
   10^3: 23,890 `red`, 20,892 `rup`, 5,990 `pol` and 47,768 `core` lines for
   about 3,000 removals). Bytes grow faster than lines, about quadratically
   in the width, because the partition steps list every `=` literal in the
   range (about 245 bytes a line at 10^3, 2.2 KB at 10^4):

   | width | lines | bytes |
   |---|---|---|
   | 10^2 | 9,758 | 557 KB |
   | 10^3 | 101,558 | 24.9 MB |
   | 10^4 | 1,019,558 | 2.27 GB |

   The live set writes 207 lines at every one of these widths. This is the only
   difference between the algorithms' proofs that this audit found. There is no
   width gate.
   The gap trim's per-run form was checked flat: 124 lines at widths 2·10^6 and
   10^9 (`probes/gap.cc`).

   **A column holding a dead wildcard costs the same under every algorithm.**
   Its unsupported values also go one at a time, at about 34 lines each the
   first time (see below), by the same range-literal mechanism. A wildcard
   column makes the compact table decline the whole table
   (`build_support_masks` returns false), and below 64 tuples `Auto` never
   builds compact state at all. So `Auto`, a forced `LiveSet` and a forced
   `CompactTable` write byte-identical proofs. The two-row table with
   `y ∈ 1..1` writes 3,342
   lines (187 KB) at W = 100 and 33,942 lines (8.3 MB) at W = 1,000. The
   one-row control writes 37 lines at both under the default algorithm. A
   forced `CompactTable` writes 3,340 and 33,940 lines on it, by the second
   path. The ten-table search writes 15,529
   lines (734 KB) at W = 100 and 54,229 lines (9.5 MB) at W = 1,000, across its
   1,023 solutions. Every one of these proofs verifies, as a complete
   enumeration.

   **The time recurs; the line cost mostly does not.** At W = 1,000 the
   ten-table search has ten removal episodes, one per table whose last live
   wildcard row dies. Each removes the 1,000 values 0 and 2..1000. An episode
   here is every removal whose reason names that table's `y_i`, spanning its
   first to its last removal line (`tmp/fd-table/codex-r1/episodes.py`).
   - **The first** spans 32,902 lines, 7,978 of them `red`: about 33 lines per
     value.
   - **Each of the other nine** is exactly 1,000 `rup` lines, one per value,
     with no `red`, so they introduce no new range-literal definitions.

   The whole proof has 8,004 `red` lines out of 54,229.
4. **The audit lane.** Three rows, `Table`, `Table/sparse` and `NegativeTable`,
   all pinned `Clean` and all still `Clean` on a guard build at `c9ceea25`. None
   in the proof-size case. **The axes they do not vary:**
   - the tuple count across `min_live` (all post two tuples, so the rasteriser
     never runs);
   - the algorithm (all default);
   - holes;
   - views;
   - wildcards (all post `SimpleTuples`);
   - the other callers of the helper.

   Moving either of the first two trips the guard (#1116), and so does a
   wildcard column over the wide domain, with two tuples and the default
   algorithm.

## Inference catalogue

Seven rules. Rules 1–5 are `propagate_extensional`'s and `Table`'s, and they
serve `AutoTable` and the tabulated constraints too; rules 6 and 7 are
`NegativeTable`'s.

**The wire inventory.**

| Wire form | Hint type | Who |
|---|---|---|
| `table:((constraint_id N))` | `hints::Table` | `Table` |
| `negative_table:((constraint_id N))` | `hints::NegativeTable` | `NegativeTable` |
| `linear_equality:…`, `plus:…`, `minus:…`, `multiply:…`, `divide:…`, `modulus:…`, `power:…` | the owner's | a tabulated constraint's table |
| empty | `NoHint` | `AutoTable`'s table, which has no owning constraint |

Each named hint carries `originator` (`ConstraintID`) and no subhint. So rules
2–5 arrive under eight different hint names, or none, depending on who posted
the table, and
a pivot keyed on hint name would split them. That is the same pattern `element`
has with `equals`.

**What licenses rules 2–5.** Each is McIlree's **Justification Procedure 3.3
(table propagation)** or **3.4 (table infeasibility)**. That is one RUP, under
the generic reason, against the tuple rows. Negating the conclusion falsifies
some entry of every tuple, which forces each tuple's flag false through its
forward half, `@x[id][j][r]`, and the at-least-one, `@c[id][al1]`, then
conflicts; a tuple that a constant position rules out has its flag false
outright. Since
#1202 this is the same for two tuples as for more. **Every tuple's forward
half is in that RUP's dependency set**, not only those of the tuples that use
the removed value, including any row with a wildcard at that position. A
tuple that uses the value is killed by another atom of the reason, and a
tuple that does not is killed by the negated conclusion itself. Both go
through the **literal layer**. That means the `=`, `≥` and
range-literal definitions and the order-ladder lines between them, including
those the proof itself has introduced, plus the **link lines** the logger
derives when it creates a range literal, such as `¬[y = v] ∨ [y ∈ a..b]`. The
links are themselves RUP from the definitions, but unit propagation over the
definitions only goes one way: `[y = v]` propagates to `[y ∈ a..b]`, while
`¬[y ∈ a..b]` does not propagate to `¬[y = v]`. So a reason that states a hole
as `¬[y ∈ a..b]` needs the links hinted. The `=` definitions
alone are not enough. The reverse halves, `[f]`, are never needed: one can
only set its flag true, and only once every entry is already true, when the
forward half has nothing new to give and, with no at-most-one, nothing
conflicts; and a flag is only made false by its forward half, which needs
an entry already false and so satisfies the reverse half, or by a unit row,
whose tuple has no reverse half. The bound rows were not needed in any
probe. See [Next steps](#next-steps), item
3, for which parts matter how often. The procedures are stated for EP 3.10's
fully reified encoding, and the argument uses only the `f_j ⇒ match`
direction.
For `AutoTable` and the tabulated constraints, the rows are the `red` lines
their builders emit instead of OPB rows. **Theorem 2.6** accounts for stating
each under a reason. **Theorem 3.3** (complete propagation
of implied atomic literals) is what lets a bound or a range be the conclusion
where JP 3.3 states one value.

### Rule: empty-table

(Rule 1.)

- **Infers** — a contradiction before search.
- **Fires when** — `Table` is posted with no tuples; its initial-contradiction
  initialiser.
- **Strength** — `GAC`: the empty relation has no support for anything, and
  this is detected before any variable is assigned.
- **Algorithm** — none: `prepare()` saw an empty list.
- **Why it is true** — no assignment is in the empty set.
- **Proof technique** — `RUP`, against the model's `0 ≥ 1` row.
- **Reason** — empty.
- **Assertion** — the empty clause, `a >= 1` with the hint.
- **Hint** — `hints::Table`, `originator`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: column-range-trim

(Rule 2.)

- **Infers** — `x ≥ lo` and `x < hi + 1`, where `[lo, hi]` is the range of
  values `x`'s column holds.
- **Fires when** — the first live-set call, at the root, for each column with
  no wildcard whose range fits 64 words. It does not run under a forced
  `table::CompactTable`.
- **Strength** — `partial`: a bound on each rasterisable column.
- **Algorithm** — two comparisons per column.
- **Why it is true** — a value outside the column's range is in no tuple.
- **Proof technique** — `RUP`, by JP 3.3 with a bound as the conclusion.
  Negating `x ≥ lo` makes every `[x = v]` with `v ≥ lo` false (Theorem 3.3), so
  every tuple's forward half forces its flag false.
- **Reason** — the generic reason over the scope. It is not minimal: only `x`'s
  own atoms are needed.
- **Assertion** — `[x ≥ lo] ∨ ¬R`, and `¬[x ≥ hi + 1] ∨ ¬R`.
- **Hint** — the caller's (see the wire inventory).
- **Offline reconstructibility** — depends on the caller.
  - `offline` for `Table`: the tuple rows are in the OPB.
  - `hinted` for a tabulated constraint, as `arithmetic.md`'s tabulate-relation
    says: its rows are skipped in a hints-only proof, and the hint's
    `originator` names the relation to rebuild them from.
  - **`search` for `AutoTable`**, whose rows are also absent and whose
    assertion carries no hint. A reconstructor has to re-enumerate the model's
    constraints over the variables the reason names, which is the presolver's
    own search, at the product of those domains.
- **Proof size** — one line per bound moved.
- **Gaps** — `None.`
- **Tightness** — a push one value too far (`v1 < 3` in place of `v1 < 4` in
  the `tables` example) is refused by VeriPB. Dropping another variable's bound
  from the reason still verifies.

### Rule: column-gap-trim

(Rule 3.)

- **Infers** — `x ∉ [a, b]` for each maximal run of `x`'s domain that its
  column does not hold.
- **Fires when** — the first live-set call, at the root, for each column with
  no wildcard whose range is **too wide** to rasterise.
- **Strength** — `partial`: every column value outside the table removed, on
  those columns.
- **Algorithm** — the column's distinct values as an interval set, then
  `each_interval_minus` against the domain. It costs `|T| log |T|` and one
  inference per gap, never width.
- **Why it is true** — as rule 2.
- **Proof technique** — `RUP`, as rule 2, with a range literal as the
  conclusion. It needs the range-literal layer's definitions (#904). A
  one-value gap is stated as `x ≠ v`.
- **Reason** — the generic reason.
- **Assertion** — `¬[x ∈ a..b] ∨ ¬R`.
- **Hint** — the caller's.
- **Offline reconstructibility** — as rule 2.
- **Proof size** — one line per gap. 124 lines in all for a four-tuple probe,
  at widths 2·10^6 and 10^9.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` **No test reaches this rule with proofs on**: the
  only other case that reaches it is the `Table/sparse` audit row, which writes
  no proof. The probe here verified.

### Rule: unsupported-value

(Rule 4.)

- **Infers** — `x ≠ v`.
- **Fires when** — any call, on either path, for a value no live tuple matches.
  Under a forced `table::CompactTable`, this is also how out-of-range values go
  at the root, one at a time. The same happens on a column where some tuple has
  a wildcard, under every algorithm, once no live row has a wildcard there. At
  the root, or at every node where search kills the last live wildcard row, it
  removes each value that no live row holds.
- **Strength** — `GAC`, with distinct variables (brute-forced).
- **Algorithm** — live set: pass 1 drops tuples with an entry out of domain,
  then each value's residue is checked and, if stale, the live tuples are
  scanned; `O(live × k)` per call plus a scan per value whose residue died.
  A column where some tuple has a wildcard has no residue row
  (`extensional_utils.cc:831-834`), so every value of its domain is scanned
  against the live tuples on every call.
  Compact: word-parallel filtering by the removed or kept values' masks, then
  one mask test per value against the live words.
- **Why it is true** — a value in no live tuple has no support: every tuple
  that uses it has some other entry out of domain.
- **Proof technique** — `RUP`, by **JP 3.3** exactly.
- **Reason** — the generic reason over the scope, per run. Not minimal: only
  the atoms that kill the tuples using `v` are needed.
- **Assertion** — `¬[x = v] ∨ ¬R`.
- **Hint** — the caller's.
- **Offline reconstructibility** — as rule 2.
- **Proof size** — one line per value. On the two matrix instances under
  [Proof performance](#proof-performance), 95–99% of the table's own
  assertions.
- **Gaps** — `None.`
- **Tightness** — removing a supported value instead (`v2 ≠ 2` for `v2 ≠ 1`
  under `v1 = 1`) is refused, and so is dropping the fixing literal from the
  reason. Both were run on the `tables` example, with an uncorrupted control
  (`tmp/fd-table/rules/`).

### Rule: no-live-tuple

(Rule 5.)

- **Infers** — a contradiction.
- **Fires when** — pass 1, or the compact update, leaves no live tuple.
- **Strength** — `partial`: the failure half of `GAC`. It prunes nothing; it
  detects that no tuple is left, on partial domains, not only on a full
  assignment. With distinct variables that is exactly when some variable has
  no support; with a repeated variable a tuple can stay live without being a
  real support, so the wipe-out is found later.
- **Algorithm** — as rule 4.
- **Why it is true** — no tuple matches the domains.
- **Proof technique** — `RUP`, by **JP 3.4**. **At `AssertionLevel::Off` it is
  not written at all**: the helper uses `NoJustificationNeeded` with no reason,
  which is how an emptied selector domain used to report, and the dom/wdeg
  conflict observer relies on that spelling. The following backtrack line's RUP
  re-derives it. At the assertion levels it is written explicitly.
- **Reason** — at the assertion levels, the generic reason. At `Off`, none.
- **Assertion** — `¬R`, from `contradiction_or_stop`, so it is the bare-reason
  form, not an attempted literal.
- **Hint** — the caller's.
- **Offline reconstructibility** — as rule 2.
- **Proof size** — one line, or none at `Off`.
- **Gaps** — `None.` The `Off` spelling leaves nothing unchecked.
- **Tightness** — `Not shown.`

### Rule: forbidden-tuple-unit

(Rule 6; `NegativeTable`.)

- **Infers** — `x_p ≠ t[p]`.
- **Fires when** — every other non-wildcard position of `t` is fixed to its
  entry. The root initialiser checks it, the arming run at the root checks it,
  and so does the watched propagator whenever a watch fires.
- **Strength** — `partial`: with distinct variables, GAC on each forbidden
  tuple's clause taken alone. That is weaker than GAC on the conjunction, and
  not even `bounds(D)` on the constraint: in the summary's counterexample,
  `x`'s lower bound, 1, has no support and stays. With a repeated variable not
  even the single clause is GAC: `NegativeTable{x, x}` forbidding `(1, 1)` over
  `x ∈ {1, 2}` keeps `x = 1` at the root (`tmp/fd-table/factcheck2/negdup.cc`).
- **Algorithm** — two watches per tuple, on positions not yet fixed to their
  entry. A firing moves the watch, or leaves one candidate. `O(k)` per visited
  tuple.
- **Why it is true** — the tuple is forbidden, and all its other entries hold.
- **Proof technique** — `RUP` against the tuple's clause. Ours; the thesis gives
  no negative table.
- **Reason** — the generic reason. Not minimal: only the other positions'
  equalities are needed.
- **Assertion** — `¬[x_p = t[p]] ∨ ¬R`.
- **Hint** — `hints::NegativeTable`, `originator`.
- **Offline reconstructibility** — `offline`: the clause is an OPB row.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — dropping the fixing literal from the reason is refused;
  dropping the removed variable's own bounds still verifies
  (`tmp/fd-table/probes/nmut_E_drop_the_equality.pbp`,
  `nmut_F_drop_own_bounds.pbp`, against `negcx.opb`).

### Rule: forbidden-tuple-conflict

(Rule 7; `NegativeTable`.)

- **Infers** — a contradiction.
- **Fires when** — every non-wildcard position of `t` is fixed to its entry,
  including an all-wildcard tuple at the root.
- **Strength** — `checker`.
- **Algorithm** — as rule 6.
- **Why it is true** — the forbidden tuple is the assignment.
- **Proof technique** — `RUP` against the tuple's clause.
- **Reason** — the generic reason.
- **Assertion** — `¬R`, from `contradiction()`.
- **Hint** — `hints::NegativeTable`, `originator`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

| Lane | What it covers |
|---|---|
| `table_constraint`, `table_constraint_view_mixed` (`table_test`) | hand-written two- and three-variable tables, empty tables, fixed variables (#254), negative values and wildcards, under **all three algorithms**, with **GAC checked at every node** (`solve_for_tests_checking_gac`). Since #1202 also two tables with duplicate rows and two whose wildcard rows overlap, each with solutions two rows match (`table_test.cc:274-277`, `:290-294`). In the bare lane only: `run_constant_table_test` (`:191`), a real constant position that rules out some tuples, with a duplicate row, since #1202, solutions only; random four-variable tables of 120 and 400 tuples over `0..7`, which the test's comment names as the only place `Auto` switches mid-search, so that the compact table is handed the live set and later re-seeded from scratch; and two repeated-variable shapes, solutions only |
| `negative_table_constraint`, `…_view_mixed` | hand-written tables, duplicates, all-forbidden, fixed variables, wildcards and repeated variables, **solutions only**, which is right, since it is not GAC |
| `table_shared_tuples_test` | tuple storage shared rather than copied, for both classes; one support-mask set for three compact tables over one tuple set; shared and unshared masks give the same 336 solutions |
| `tables`, `tables_live`, `tables_compact` | the example under each algorithm, verified. Its tables are under 64 tuples, so `Auto` never switches there |
| `table_layout-table`, `…-dzn` | the table-layout example posting one `Table` per cell, verified |
| `auto_table`, `table_layout-auto-table`, `skyscrapers-5-autotable`, `auto_table_presolver_test` | the presolver's tables. The three examples verify their proofs; the presolver test is a Catch2 unit test |
| `scp_chain_{,negative_}table_{sat,unsat}` | see [Cake conformity](#cake-conformity) |
| `minizinc-tableint`, `minizinc-tablebool` | the MiniZinc glue |
| `minizinc-tableintduplicates`, `minizinc-tableintduplicatesopt` | since #1202: duplicate rows that every solution matches twice, enumerated (`solx`) and optimised (`soli`), with proofs verified |
| `xcsp_extension_overlap` | since #1202, the first `<extension>` lane: overlapping wildcard supports and an exact duplicate in a `<group>` whose second member takes `extensionAs`, and a unary extension with a duplicate; solutions against ACE's, and the proof verified |
| `xcsp_range_tuple_past_int32`, `xcsp_range_tuple_int_max` | since #1217: a support past `int`, and `2147483647`, refused rather than misread |
| `integer_ranges` (`integer_ranges_test`) | since #1215: a `Table`, wildcard `Table` or `NegativeTable` tuple value one past either end of `S` is refused, and the ends are accepted (`integer_ranges_test.cc:162-164`); since #1214, a `Table` whose rows name both ends of `S`, over positions at one end of `S`, plain, negated or offset by an end of `S`, in six configurations, against brute force, with and without proofs (`:324-336`) |
| `large_domain_audit_test` rows `Table`, `Table/sparse`, `NegativeTable` | see [Interval efficiency](#interval-efficiency) |

VeriPB runs in the data-driven lanes when it is on the path. The lanes are
seeded (`--seed`), and the idempotence-claim checker is on in `table_test`'s.

**Runtime caps.** No lane sets or clears one. The default caps **fire on the
400-tuple random table**, in all six of its runs (three algorithms, with and
without proofs): 300 of 400 solutions checked for soundness only. They fire
nowhere in `negative_table_test`. Measured with `GCS_TEST_MAX_SOLUTIONS=300
GCS_TEST_MAX_RECURSIONS=1500 table_test --seed=1` at `c9ceea25`. The Ubuntu CI
lanes run uncapped. Re-run at `0a5b4ec6` with #1202's new rows: the caps
still fire on those six runs only.

**What the tests do not cover.**

- **XCSP3 `<conflicts>`.** `xcsp_extension_overlap` covers supports, `*`,
  `extensionAs` and duplicates, but no lane posts a `NegativeTable` from
  XCSP3 except the unary `notin` in `intension_reified.xml`. The table
  benchmark harness checks `.xml` solution counts, but outside the
  repository.
- **The rasteriser and the compact table at the ends of `S`.** The edge
  solves post five tuples under the default algorithm, so the rasteriser
  never runs on them. A rasterisable eight-tuple column at either end of `S`,
  under the default algorithm and a forced compact table, was probed by hand
  ([Robustness and limits](#robustness-and-limits)).
- **Rule 3 with proofs.**
- **A table of eight or more tuples, a forced compact table, or a column
  holding a wildcard, over a wide domain** (see the audit lane). Nothing
  either loses or restores the last live wildcard row during search over a
  wide domain.
- **`NegativeTable`'s strength**, deliberately: no consistency level is checked
  for it.
- **Mutation lanes:** none in the tree. The four refusals above were run by
  hand.
- **Whether `Auto` actually switches** in those random-table rows, capped or
  uncapped, was not checked here. There is no statistic for it: `Table` reports
  none, where `AutoTable` does (`compact_table`).

### Benchmarks and examples

- **In the repository:**
  - `examples/tables`, small; `examples/table_layout`, one table per cell,
    which also has an `AutoTable` and an `Element` variant of the same model;
  - `benchmarks/positive_table_random` and `benchmarks/negative_table_random`;
  - `examples/auto_table` and `examples/skyscrapers --autotable` for the
    presolver.
- **Outside it:** the `table-benchmarks` harness
  (`/cluster/ciaran/claude/table-benchmarks`). It holds a synthetic matrix of 18
  instances in two regimes, search-dominated and enumeration-dominated, plus
  real Crossword, Dubois, Kakuro and Renault instances converted from XCSP3.
  Its Gecode driver reads the same files, so its node counts are a check that
  the trees coincide.
- **In the MiniZinc Challenge corpus** (285 models, one instance each), 24
  models post `Table`. Seven of those were timed, and on four of them it is
  over half of the propagation time (see
  below). `spot5` 2022 posts 17,403.

**For CPU:** `proteindesign12` (table-bound), `opt-cryptanalysis`, `spot5`, and
the harness's Crossword and Dubois instances. **For proof verification:**
`srch_bin_d12_n30_s2` (490 nodes, 15 s to verify) and, as a smoke test,
`srch_func_k3_n24` (0.04 s at `c9ceea25`, 0.02 s at `0a5b4ec6`).
`srch_k5_d5_n12` takes about 250 s to verify (248.8 s at `c9ceea25`, 251.0 s
at `0a5b4ec6`), so it is the one to use for the
checker's cost. **Never run a forced `table::CompactTable` over a wide domain
with proofs on.**

### CPU performance

**Against Gecode 6.3.0 on the same tree.** `c9ceea25`, Release, fataepyc-09
(AMD EPYC 7643), 2026-09-27: a second run (19:31 onwards), after an earlier
one that may have overlapped other work. The two agree within 2% on every
row's **solve** times. Totals, which include posting, differ by more on a few
sub-millisecond rows (Kakuro-easy-001 1.0× then 0.5×, Kakuro-easy-008 0.3×
then 0.4×, souffleuse-pos − then 1.0×), ratios move by 0.1× on several matrix
rows, and post times differ by 2–8%. The harness pins to one core (`numactl`,
`taskset -c 4`, `setarch -R`). `GLIBC_TUNABLES` pinned malloc's mmap and trim
thresholds; `compare.py` does not set it, so it was exported in the calling
shell and inherited. Median of three launches. The real instances are solved
to the first solution, five times within each launch (`--inner-repeat 5`), and
the matrix enumerates all solutions. The invocations are recorded in
`tmp/fd-table/bench-commands.txt`. Both drivers post the same model with
static input order and smallest value first, and **every row's node and
solution counts agree** (the harness exits non-zero otherwise). `solve` is
GCS/Gecode search time and `total` includes posting; above 1 means GCS is
slower. `propagations` is GCS's, from a separate run of the same driver;
Gecode's is not comparable and not shown.

| instance | nodes | propagations | GCS solve | Gecode solve | solve | total |
|---|---|---|---|---|---|---|
| Crossword-words-vg-10-10 (relaxed) | 9,927 | 317,193 | 2.79 s | 2.53 s | 1.1× | 1.1× |
| Crossword-words-vg-10-12 (relaxed) | 1,088 | 37,956 | 0.376 s | 0.281 s | 1.3× | 1.3× |
| Dubois-018 | 1,572,863 | 7,602,204 | 4.06 s | 2.05 s | 2.0× | 2.0× |
| Renault-megane-pos | 28 | 429 | 0.0122 s | 0.0003 s | ~41× | **0.2×** |
| Renault-big-pos | 47 | 2,487 | 0.0324 s | 0.0025 s | 13× | **0.5×** |
| Renault-small-pos | 12 | 580 | 0.0006 s | 0.0001 s | ~6× | 1.8× |
| Kakuro-easy-003 | 1 | 110 | 0.0006 s | < 0.0001 s | — | **0.2×** |
| srch_bin_d20_n20_s1 | 26,570 | 1,906,820 | 1.38 s | 0.830 s | 1.7× | 1.7× |
| srch_k5_d5_n12 | 3,340 | 78,649 | 0.0884 s | 0.0506 s | 1.7× | 1.4× |
| srch_holey_d20_n25 | 2,726 | 289,543 | 0.201 s | 0.140 s | 1.4× | 1.4× |
| enum_func_k3_n20 | 1,830,556 | 6,216,134 | 5.19 s | 1.33 s | 3.9× | 3.9× |
| enum_bin_d2_n14 | 12,287 | 13,126 | 0.0113 s | 0.0027 s | 4.2× | 4.0× |
| enum_single_k10_t200k | 269,711 | 269,711 | 1.01 s | 0.305 s | 3.3× | 1.9× |

The full tables are `tmp/fd-table/bench-{real,matrix}-quiet.txt` and
`props-{real,matrix}.txt`.

- **Search time:** 1.1–1.3× Gecode's on Crossword, 2.0–2.1× on Dubois, and
  1.4–4.2× over the 18 matrix instances, worst in the enumeration regime
  (`nodes ≈ solutions`).
- **Renault is a different race.** Its searches are 9–47 nodes, and GCS's
  search time is 6–47× Gecode's on the eight instances where Gecode's time
  registers at all (souffleuse-pos reads 0.0000 s). Gecode prints to 0.1 ms,
  so its times carry ±0.05 ms: about ±2% on Renault-big and big-pos
  (2.5 ms), ±10% on master-pos (0.5 ms), ±17% on megane-pos (0.3 ms), and
  ±50% on the 0.1 ms rows (medium, medium-pos, small, small-pos). End to end,
  counting posting, GCS is **ahead on six of the nine Renault instances**
  (0.2–0.5×: big, big-pos, master-pos, medium, medium-pos, megane-pos), level
  on souffleuse-pos (1.0×), and **behind on small and small-pos (1.8×)**,
  whose tables are too small for Gecode's posting to matter. Gecode spends
  74–95 ms posting the big ones, which GCS posts in about 5 ms.
- **Kakuro** is one node each; GCS is 0.2–1.0× end to end, again on posting.

The comparison is fair on strength: both are GAC on every constraint of a
model that is only tables.

**Figures measured elsewhere, not to be mixed with the above:** the #508 project
measured the table propagator's share of each harness instance's solve time at
8–99.6%. By `1/(1 − share)`, it concluded that only one instance
(`srch_bin_d12_n25_s1`) could close the gap to Gecode through the table alone.
Those figures predate #831/#832 and were taken on fataepyc-10.

**On the corpus,** at 20 s caps with `GCS_PROPAGATOR_STATS=time`. Timed runs are
slower than untimed, so these are shares, not speeds. Seven of the 24
table-posting models, chosen for posting the most tables or for being
table-heavy; the other seventeen were not measured. `c9ceea25`, fataepyc-09,
2026-09-27, `tmp/fd-table/corpus/`.

| model | `Table` constraints | share of propagation time | share of calls | busiest besides |
|---|---|---|---|---|
| `proteindesign12` 2018 | 153 | **99.9%** of 16.8 s | 98.1% | — |
| `spot5` 2022 | 17,403 | **92.2%** of 4.6 s | 93.2% | `Equals` 4% |
| `opt-cryptanalysis` 2017 | 176 | **85.4%** of 14.2 s | 55.0% | `LinEquals` 11% |
| `spot5` 2015 | 10,475 | **80.6%** of 3.3 s | 73.6% | `Equals` 11% |
| `is` 2015 | 205 | 32.1% of 13.3 s | 17.8% | `Equals` 30%, `Element` 26% |
| `code-generator` 2020 | 2,412 | 4.0% of 9.8 s | 0.6% | `Disjunctive2d` 64% |
| `yumi-dynamic` 2024 | 1,381 | 0.5% of 19.5 s | 6.4% | `Cumulative` 50%, `ArrayMax` 48% |

On `spot5` 2022, propagation is only 4.6 s of the 20 s solve, so most of the
time there is outside any propagator.

**What these benchmarks exercise.** Rules 4 and 5, almost only. The harness's
domains are exactly its columns' values, so rules 2 and 3 never fire, and
neither does rule 1. `NegativeTable` is outside the harness by design (#508's
scope), and it was not benchmarked here.

**`Auto` against the forced arms:** see [Developer
commentary](#developer-commentary). In short, `Auto` beats the live set by up
to 4.7× and loses 2.2–2.3× to a forced compact table on Renault.

### Proof performance

Re-run at `0a5b4ec6`, fataepyc-10, 2026-10-08, after #1202's encoding
change. The XCSP3 renderings of three matrix instances, all solutions,
through `xcsp_glasgow_constraint_solver --prove`, with the assertion level set
by `GCS_ASSERTION_LEVEL`. Its own search order differs from the harness's,
so node counts are this front end's. `solve` is the solver's own `SOLVE TIME`
with proofs on, one run each. VeriPB 3.0.2 with `--force-checked-deletion`,
wall clock, pinned with `taskset -c 24` and `GLIBC_TUNABLES` (malloc's mmap
and trim thresholds), one run each
(`tmp/fd871-comments-1008/tables/probes/proofperf/`).

| instance | nodes | solve | level | lines | bytes | VeriPB |
|---|---|---|---|---|---|---|
| `srch_func_k3_n24` (UNSAT) | 3 | 0.037 s | `Off` | 980 | 43 KB | 0.02 s |
| | | 0.022 s | `Inferences` | 114 | 23 KB | 0.01 s |
| `srch_bin_d12_n30_s2` (UNSAT) | 490 | 0.19 s | `Off` | 42,435 | 3.2 MB | **15.4 s** |
| | | 0.20 s | `Inferences` | 27,596 | 3.4 MB | 0.12 s |
| `srch_k5_d5_n12` (1 solution) | 1,988 | 0.32 s | `Off` | 32,350 | 3.3 MB | **251.0 s** |
| | | 0.34 s | `Inferences` | 33,165 | 4.1 MB | 0.25 s |

**Every `.pbp` is byte-identical to the audit's** at `c9ceea25`
(`tmp/fd-table/proofperf/`), so the proof's lines, bytes and the counts below
are unchanged; #1202's flags are never cited, and on these instances not even
the later proof-only variables' numbering moved. What changed is the OPB:

| instance | OPB lines, `c9ceea25` | `0a5b4ec6` | OPB bytes, `c9ceea25` | `0a5b4ec6` |
|---|---|---|---|---|
| `srch_func_k3_n24` | 3,748 | 6,179 | 411,000 | 508,059 |
| `srch_bin_d12_n30_s2` | 19,245 | 36,209 | 2,163,947 | 2,559,463 |
| `srch_k5_d5_n12` | 35,305 | 70,221 | 5,482,234 | 7,853,284 |

These match #1202's own row counts. Checking the audit's OPB and proof again in
the same sitting, alternating with the new pair on the same core
(`control.sh`), VeriPB took 14.92 s and 72,556 KB on `srch_bin_d12_n30_s2`
against 15.37 s and 78,664 KB with the new OPB (+3% time, +8% peak memory),
and 238.2 s and 119,684 KB on `srch_k5_d5_n12` against 249.0 s and
146,340 KB (+5%, +22%). One run of each. The fact-check's two further
alternating pairs on `srch_bin_d12_n30_s2`, in another sitting, gave +4.7%
and +4.8% time and +8.6% and +8.5% memory
(`tmp/fd871-comments-1008/tables/factcheck/probes/pp/control_bin.txt`), so
the time cost there is 3–5%. #1202's body, on the same three
instances with three runs of the two slow ones, reports 2–3% more time and
6–18% more memory, and +6.5% time and +14% memory on `yumi-static` 2022.
At `c9ceea25`, on fataepyc-09, the table read 0.04, 0.02, 15.2, 0.10, 248.8
and 0.19 s for VeriPB, and 0.023, 0.021, 0.19, 0.20, 0.30 and 0.31 s for
`solve`.

**Checking dominates.** `srch_k5_d5_n12`'s fully justified proof takes about
800 times its solve to verify (251.0 s against 0.318 s), where the hints-only
proof is the same size but
checks in a quarter of a second. That is the family's largest cost for the
paper, and it is in the checker, not the proof's size. The likely reason is
that each RUP has to propagate through every tuple's rows in an arity-5
table, now both halves of each; VeriPB was not profiled to confirm it.
Every tuple's forward half is in each RUP's dependency set (see [What
licenses rules 2–5](#inference-catalogue)), so a hint naming only the tuples
that use the value is not enough. The levers are a `hinted RUP` over the whole
dependency set, or per-value support clauses derived once. See [Next
steps](#next-steps).

**What the `Inferences` proofs assert** (`tmp/fd-table/rules/classify.py`, on
the `c9ceea25` proofs, which the `0a5b4ec6` ones equal byte for byte):

| instance | `table` value removals | `table` contradictions | other `a` lines | `table` share of `a` lines |
|---|---|---|---|---|
| `srch_bin_d12_n30_s2` | 25,344 | 288 | 491 | 98.1% |
| `srch_k5_d5_n12` | 23,966 | 1,313 | 1,989 | 92.7% |

**Own against shared.** In the `Off` proof of `srch_bin_d12_n30_s2`:

- 30,231 lines are `rup`: the table's 25,344 value removals, about 490
  backtracks, and the literal layer's own RUP steps;
- 2,242 `red` and 377 `pol` are the shared literal layer;
- the rest are `core` and `del` bookkeeping and comments.

On the OPB side, the table's own rows grow as `2m + 1`, plus a unit row per
tuple a constant position rules out, while the shared layer's plateau at arity ×
domain; see [OPB encoding](#opb-encoding).

## Status, gaps, and next steps

### Proof-logging gaps

- `AutoTable`'s inferences have no rows and no hint in a hints-only proof. That
  is not a gap, since the full proof justifies them, but it is the one place in
  this family where reconstruction needs a search.

Two gaps this audit found are closed: overlapping rows made the solution line
fail (#1115, fixed by #1202; see [OPB encoding](#opb-encoding)), and a tuple
entry far from its position's domain, or a far view, could abort a solve in
`define_proof_model` or, through a view, in pass 1 (#1117, closed by #1215
refusing such tuple values, with #1214 refusing such view offsets; see
[Robustness and limits](#robustness-and-limits)).

Propagation strength does not change with proofs on, for any rule.

### Known limitations

- A tuple value outside `S` is refused with `IntegerOverflow` when the
  `Table` or `NegativeTable` is constructed (#1215), even where a view could
  take it.
- A `Table` of eight or more tuples, or any `Table` under a forced
  `table::CompactTable`, over a very wide variable spends time proportional to
  the width once, at the root, and over all of `S` it does not finish. With
  `table::CompactTable` forced, whatever the tuple count, it also writes about
  34 proof lines per value, whose size grows with the width.
- A `Table` whose tuples have a wildcard in a column over a very wide variable
  spends time proportional to the width on every call, under any algorithm and
  with any number of tuples, until the node where the last live wildcard row
  there dies. It then removes the unsupported values one at a time. Every
  such episode costs width-proportional time, but only the first costs about
  33–34 proof lines per value (one of ten in the probe under [Interval
  efficiency](#interval-efficiency)); each later one costs one line per value.
- `NegativeTable` is not generalised arc consistent.
- A repeated variable in `Table` weakens propagation below GAC on that variable.
- There is no reified table; MiniZinc's decomposition stops at five variables.
- The table propagator's search is 1.1–4.2× slower than Gecode's on the same
  tree on Crossword, Dubois and the synthetic matrix; #508 put most of that in
  the engine (#503). On Renault its search is 6–47× slower, which posting
  more than makes up for on six instances but not on Renault-small and
  Renault-small-pos (1.8× end to end). Measured at `c9ceea25`.
- `table::Auto` runs the live set on a table woken only a few times, however
  large, so Renault-like instances run 2× slower than they could (at
  `c9ceea25`).

### Next steps

1. **Fix the overlapping-tuples proof failure (#1115).** **Done by #1202**,
   by the second of this item's three options: reify each row both ways and
   keep only an at-least-one, which is cake's encoding (see [OPB
   encoding](#opb-encoding)). It covers wildcard overlaps, and #1202's body
   reports `yumi-static` 2022's proof now verifying (`s VERIFIED BOUNDS 242 <=
   obj <= 735`, from a 60 s run). The first option, deduplicating exact
   `SimpleTuples` rows in `prepare`, is still open, now as a cost saving
   rather than a fix: MiniZinc posts `SimpleTuples` (`fzn_glasgow.cc:1265`),
   and #1202's body counts 1,868 duplicates among the 2,204 rows of
   `yumi-static`'s six large tables. It would cut OPB rows and propagation
   work, and would not reach XCSP3's duplicates, which arrive as
   `SharedWildcardTuples`. Not filed.
2. **Fix the root-width walks (#1116).** Running the root trim before the
   rasteriser and before the compact dispatch fixes the first two paths. It is
   a small change that closes a guard trip on the default path, and it makes
   the "same proof under every algorithm" contract true. **It does not touch
   the wildcard path**, which moving the trim leaves as it is: the trim
   skips a wildcard column, and so do the rasteriser and the residues.
   - While a wildcard row is live, that row supports every value, so the scan
     could skip the column without visiting any value.
   - Once the last live wildcard row in a column dies, the column needs a trim
     or support pass over the values the remaining live rows hold, not over
     the domain.
   - Anything cached for either case has to stay right across backtracking,
     which restores the wildcard rows.

   Audit rows: eight tuples; each algorithm; a live wildcard over a wide
   domain; a wildcard row already dead at the root; and one lost and
   restored during search. The last is a proposed regression case, not one
   the probes here time on its own.
3. **Cheaper RUPs for the table rules.** Verification is about 800× solve on
   an arity-5 table (see [Proof performance](#proof-performance); #1202 made
   checking slightly slower, not cheaper), probably because each unhinted RUP
   propagates over the whole database. **Every tuple's forward
   half is in a removal's dependency set**. Those of the tuples that use the
   removed value are not enough, because the others are what rule their own
   flags out under the negated conclusion. Both sound shapes below also need
   the **literal layer** for the scope:
   - the `=`, `≥` and range-literal definitions, whether in the OPB or
     introduced by a `red` in the proof;
   - the order-ladder lines derived between them;
   - the **link lines** the logger derives when it creates a range literal,
     `¬[y = v] ∨ [y ∈ a..b]` and `¬[y ∈ a..b] ∨ …`. Each is RUP from the
     definitions, but unit propagation over the definitions cannot get from
     `¬[y ∈ a..b]` to `¬[y = v]` without them.

   The reverse halves, `[f]`, are never needed (see [What licenses rules
   2–5](#inference-catalogue) for why), and the bound rows were not needed in
   any probe. Examples of what each part is for:
   - In `x, y ∈ 0..3` with the tuple `(3, 1)`, removing `y = 1` under `x = 0`
     needs `x ≥ 3 ⇒ x ≥ 1`.
   - With a wildcard, some `=` definitions exist only as `red` lines in the
     proof.
   - With `x ∈ 0..2`, `y ∈ {0, 3, 4, 5}` and the tuples `(0,1) (0,2) (1,0)
     (2,3) (1,4)`, the root removal of `x = 0` has `[y ∈ 1..2]` in its reason,
     and fails without the two forward link lines `¬[y = 1] ∨ [y ∈ 1..2]` and
     `¬[y = 2] ∨ [y ∈ 1..2]`.

   The two shapes:
   - **Hint the whole dependency set.** The at-least-one row, every tuple's
     forward half in this table, and the literal layer. That limits a RUP to one table's
     rows, rather than every table's in the model.
   - **Derive a per-value support clause first**, `¬[x = v] ∨ ⋁_{j ∈ supp(x,v)} f_j`,
     where `supp(x, v)` holds every tuple with `v` or a wildcard at `x`. Derive
     it once, from the at-least-one row, the forward halves of the tuples that
     do *not* support `x = v`, and the literal layer. It is a static fact about
     the table, so it can live at `Top`. Each removal of `x = v` then hints
     only that clause, the forward halves of the tuples in `supp(x, v)`, and
     the literal layer. The reason's literals need no hint, since they come from negating
     the claim.

   Both shapes were checked with VeriPB 3.0.2 on hinted RUPs. Only the
   hand-built cases were re-checked against #1202's flag rows; everything
   else in this item is from `c9ceea25`, against the selector rows, where
   "every tuple row" played the forward halves' part and the selector's
   at-least-one the `@c[id][al1]` row's.
   - **Hand-built cases.** Codex's Boolean example (`c9ceea25` only), and four
     real GCS tables over `x, y`, removing `y = 1` under `x = 0`:
     `(0,0) (1,0) (1,1) (2,2)` over `0..2`; `(0,0) (1,1) (3,1) (2,2)` over
     `0..3`; `(0,0) (1,*) (3,1) (2,2)` over `0..3`; and `(0,0) (1,1)` over
     `0..2`. Re-checked at `0a5b4ec6`
     (`tmp/fd871-comments-1008/tables/probes/dep.cc` and `depset_flags.py`, a
     port of `dep2/depset.py`): the stated set verifies on all four. It fails
     if you hint only the forward halves of the tuples using the value, leave
     out any one forward half or the at-least-one, or hint the reverse halves
     in place of the forward ones; adding the reverse halves changes nothing.
     It also fails if you drop the literal layer from the support clause's
     second step, or hint the `=` definitions alone (on the two `0..3`
     tables). The support-clause shape verifies on all four. The two-tuple
     table now needs its at-least-one like any other; at `c9ceea25` its
     selector was one bit with no at-least-one row, and the two rows alone
     conflicted.
   - **The link-line counterexample above** (`c9ceea25`). The set without the link lines
     fails. Adding the two forward links makes it verify, and the inverse link
     `¬[y ∈ 1..2] ∨ [y = 1] ∨ [y = 2]` alone does not.
   - **The second fact-check's campaign** (`c9ceea25`). It ran 920 table inferences over
     226 random instances, with views, negated views, holes, wildcards and
     out-of-domain entries.
     The counts below are from the third fact-check's strict classification
     by this wording (`factcheck3/fc3_worded.py`), which also counts as ladder
     lines those the proof derives by `pol` against line numbers.
     - The stated set verifies all 920.
     - Without the link lines it verifies 918. The forward links are needed
       in 2 and the inverse links in 1.
     - The `≥` definitions and the proof-introduced ladder lines cover for
       each other. Dropping either alone fails none; dropping both fails 113.
     - Dropping every ladder line fails 3.
     - Dropping the range-literal definitions, once the links are in, fails
       none. The bound rows, which the set leaves out, are never missed.
     - The `=` definitions alone verify only 40.
     - The support-clause shape verifies all 841 value removals in both
       steps; without the link lines, 839. Its second step without any of the
       literal layer verifies only 210, by the second fact-check's count.

     A rerun on four fresh seeds (38 instances, 160 inferences) agrees:
     dropping both the `≥` definitions and the proof-introduced ladders fails
     14, and nothing else that is dropped fails.

   Probes: `tmp/fd-table/codex-r1/dep_*`, `r_*.pbp`, `t_*.pbp`,
   `dep2/depset.py`, `dep3/worded.py` (the counterexample; its set adds the
   bound rows and counts only label-form ladders), `dep3/camprun/` and
   `dep4/`, plus the fact-checks' `factcheck/dep/`, `factcheck2/` and
   `factcheck3/` (whose `fc3_worded.py` is the strict classification).
   Measure first, on `srch_k5_d5_n12`. Whether a hint is needed is for the
   justifier to show.
4. **Minimal reasons.** Both classes use the whole-scope generic reason. For
   `NegativeTable` the minimal one is `k − 1` equalities, and it is known at
   the inference site. Not measured; it would shrink proofs and help the
   conflict observer.
5. **Declare `NegativeTable`'s holes as none.** A one-line change; it matters
   only when an `Element` under `consistency::Auto` shares a variable with a
   `NegativeTable`. Not measured.
6. **Add an XCSP3 `<extension>` lane**, covering supports, conflicts, `*` and
   `extensionAs`. **Mostly done by #1202**: `xcsp_extension_overlap` covers
   supports, `*`, `extensionAs` (through a `<group>`) and duplicates. What is
   left is a lane for `<conflicts>`.
7. **Revisit `Auto`'s rule (#1118).** Forced compact
   is 2.2× faster on Renault, where the wake-count gate never lets `Auto`
   decide. A per-wake cost estimate (live tuples × arity against the mask
   build) might separate Renault from Dubois. Costs a benchmarking session;
   buys up to 2× on configuration instances.
8. **Fix the extreme tuple values (#1117).** **Done by #1215**, a different
   way from this item's proposal, which was to drop a row whose entry its
   posted position cannot take, in `prepare`. Instead every input, tuple
   values and view offsets included, must lie in `S`, and the constructor
   refuses one outside it with `IntegerOverflow` (see [Robustness and
   limits](#robustness-and-limits)); nothing is dropped. The item's control,
   `Table({x + 2^62}, {(2^62), (2^62 + 1)})`, can no longer be built, and
   `integer_ranges_test`'s `Table` edge solves are the in-range control.
9. **Cake conformity:** check whether the table chain cases would now pass
   `aux` or `strict`, since #358, which the registration cited, is closed.
   **Answered since #1202**: they do not, and the registration comment now
   gives the reason, the `≥`-literal definitions at a variable's bounds, not
   #358 (see [Cake conformity](#cake-conformity), checked by hand at
   `0a5b4ec6`). That difference is in the shared literal layer, not in this
   family's rows.

## Prior art

- **Propagation:** the live-set path is STR1's tuple pass (Ullmann,
  *Information Sciences*, 2007), which re-tests every position of every live
  tuple per call, with none of STR2's `S_sup` / `S_val` restriction (Lecoutre,
  *Constraints* 16(4), 2011). Support is then not collected during that
  traversal, as STR1 does, but checked per value against a residue, with a
  fallback scan of the live list (residual supports: Lecoutre and Hemery,
  IJCAI 2007; `extensional_utils.cc:864-900`). So: STR1's tuple pass plus
  residue-based support checks. And Compact-Table (Demeulenaere,
  Hartert, Lecoutre, Perez, Perron, Régin and Schaus, CP 2016): the
  `table::CompactTable` path, including its choice between a delta update and
  a reset by whichever value set is smaller. The algorithms are theirs; the
  lazy switch between them (`table::Auto`) and its thresholds are ours (#804).
- **Negative tables:** two watched literals over one clause per forbidden tuple
  is the SAT solver's scheme applied tuple by tuple. It is weaker than
  generalised arc consistency for a conflict table, for which dedicated
  algorithms exist; none was surveyed here.
- **Proofs:** McIlree's thesis (2026) gives the table encoding (EP 3.10) and the
  two justification procedures, JP 3.3 and 3.4, which rules 4 and 5 follow
  exactly and rules 2 and 3 extend to bounds and ranges. Since #1202 GCS's
  encoding is EP 3.10's rows, reified both ways, with an at-least-one in
  place of its exactly-one, which is what admits overlapping tuples; it is
  `cake_pb_cp`'s encoding. Before #1202 GCS half-reified the rows on a
  selector, which admitted overlaps but broke the solution check when they
  occurred (#1115).
- **What is ours:**
  - the root trims (rules 2 and 3) as bound and range conclusions;
  - an auxiliary with no solver state that no proof line needs to cite:
    the proof-only selector (#796), and since #1202 the tuples' proof flags;
  - `NegativeTable`'s rules.

## Further reading

- `propagator-performance.md`: the table project's worked examples. Look for
  "Don't throw from a propagator that fails in bulk" (#832, 1.7× on Dubois),
  "Adding a second algorithm to a hot function slows down the first one" (the
  compact table's cost to the live set, and how it was bought back), and
  "Data derived from a shared input belongs to the input" (shared support
  masks).
- `large-domains.md`: the history of `Table`'s rows, which started as
  `KnownTrip` and became `Clean` through the residue sizing and the gap trim.
- `refined-triggers.md`: the refined-watch engine `NegativeTable` runs on.
- `/cluster/ciaran/claude/tmp/table-propagator-handoff.md` and
  `table-passbudget.md` (outside the repository): #508's full measurement
  record, including the per-pass budget and the ACE and Gecode comparisons.

## Developer commentary

**`Auto` against the forced arms, re-measured.** The header comment on
`table::Auto` says it is within 2% of the better of the two forced arms
everywhere except `srch_bin_d10_n20_s2`, where it is 4% behind (#804). The same
harness, re-run at `c9ceea25` with the same pinning and tunables as [CPU
performance](#cpu-performance) but in the earlier sitting (18:41–18:59), which
may have overlapped other work, says otherwise
(`tmp/fd-table/bench-algo-{matrix,real}-{live,compact}.txt`). Node counts agree
in every row.

| instance | `Auto` / `LiveSet` (solve) | `Auto` / `CompactTable` (total) |
|---|---|---|
| Crossword-words-vg-10-10 | 0.2× | 1.0× |
| Dubois-018 | 1.0× | **0.7×** (compact 5.52 s against 4.12 s) |
| Renault-big-pos | 1.0× | **2.2×** (0.0371 s against 0.0170 s) |
| Renault-master-pos | 1.0× | **2.3×** |
| Renault-megane-pos | 1.0× | 1.4× |
| srch_bin_d10_n20_s1 | 0.8× | 1.2× |
| srch_bin_d10_n20_s2 | 1.1× | 1.1× |
| srch_k5_d5_n12 | 0.3× | 1.0× |
| enum_shared_k2_n12 | 1.0× | 0.7× |

So `Auto` is right to leave the live set, by up to 3.9× on the matrix
(`srch_k5_d5_n12`, 0.3509 s against 0.0889 s) and 4.7× on Crossword, and right
to stay off compact on Dubois and the small enumeration instances. But it
leaves 2.2–2.3× on the table on Renault. Renault wakes a table only a few times
per search (about four for megane, per the code's comment), so `Auto` never
reaches its 32-wake decision, and there a lazily built compact table pays even
for so few wakes.
It is also 5–15% behind forced compact on six of the thirteen `srch_*`
instances. The doc comment is stale, and the decision rule, which gates on
wake count, cannot see Renault's case at all: few wakes, each over a very large
live set. Filed as #1118.
