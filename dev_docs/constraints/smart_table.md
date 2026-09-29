# Smart table: `SmartTable`

> **Maturity** production (the propagator); nothing in a front end posts it ·
> **Audited** 2026-09-27 at `c9ceea25` ·
> **Open issues** filed from this audit: an entry over a variable outside the
> scope aborts the solve (#1119); a short-reason flag defined on every call and
> never deleted, 20 times the checking time on an enumeration (#1120);
> `LexSmartTable` and `AtMostOneSmartTable` hints naming no constraint (#1121).
> Filed from the review of this audit: building the proof model does up to
> quadratic work in a unary-entry variable's width (#1127); every tree of a row copies
> the whole scope's domains on every call (#1128).
> **Not filed**, and cited below by a short name in italics: a value removal
> asserted with no reason at the `Definitions`, `Links` and `Inferences`
> assertion levels, so the hints-only proof asserts false clauses, a defect
> `Circuit` shares (*assertion reasons*), left by decision until the hints-only
> mode is taken up for the justifier; the `cake_pb_cp` chain failing on the
> solver's row-flag names (*chain row flags*); and the rest of the per-call
> cost (*per-call cost*), both low priority. Already open and touching this family:
> #833 (the large-domain policy, whose audit lane marks all three smart-table
> rows `KnownTrip`), #364 (incrementality survey), #868 (cross-solver). Tracked
> under #871.

`SmartTable(X, T)` holds when at least one smart tuple of `T` holds, and a
smart tuple is a conjunction of unary and binary comparisons and set
memberships over the variables of `X`. It is Mairy, Deville and Lecoutre's
constraint, with the propagator their paper describes and the proof logging
McIlree and McCreesh added (CP 2023; McIlree's thesis, Chapter 4). It is the
engine behind two classes kept as baselines, `LexSmartTable` and
`AtMostOneSmartTable`; no front end posts any of the three, and the `.scp`
reader is its only way in from a file.

Three things to know before touching it.

- **It is generalised arc consistent, and its proofs are the thesis's.** A
  brute-force check over 5,000 random tables, with holes, views in entries and
  in the scope, and repeated scope variables, found no unsupported value at any
  search node. Each value removal is justified by one RUP step per tuple under
  the reason, after a lemma for each filtering step of the tuple's trees; those
  lemmas are what the thesis's Example 4.3 needs, and removing them makes VeriPB
  refuse it.
- **The hints-only mode is wrong here.** At the `Definitions`, `Links` and
  `Inferences` assertion levels, a removal is asserted as a bare unit clause
  with no reason. On an at-most-one enumeration, 184 of the 194 `smart_table`
  assertions are falsified by a solution the same proof logs later. VeriPB
  cannot see this, because it does not check assertions. `Circuit`'s SCC
  propagator has the same defect from the same commit (*assertion reasons*).
- **It is slow and its proofs are slow to check, for reasons that are not the
  algorithm.** Every call rebuilds hash maps of every variable's values, one
  per tree of every live row (#1128); on the
  same search trees it is 17–23 times slower than the native `AtMostOne` and
  8–15 times slower than the native `Lex`. With the default short reasons, it
  defines a reason flag on every call whether or not anything follows, and never
  deletes it; on one enumeration that takes checking from 0.79 s to 15.9 s.

## What it is

### Semantics

```
SmartTable(vars, tuples)
```

`tuples` is a `SmartTuples`, a vector of rows, each a vector of `SmartEntry`.
An entry is one of:

| Entry | Spelling | Meaning |
|---|---|---|
| `BinaryEntry{a, b, op}` | `SmartTable::less_than(a, b)` and so on | `a op b` |
| `UnaryValueEntry{a, c, op}` | `SmartTable::less_than(a, 3_i)` and so on | `a op c` |
| `UnarySetEntry{a, S, In}` / `{…, NotIn}` | `SmartTable::in_set(a, {…})`, `not_in_set` | `a ∈ S`, `a ∉ S` |

with `op` one of `<`, `≤`, `=`, `≠`, `>`, `≥`. The constraint holds when
every entry of at least one row holds. A scope variable a row does not mention
is unrestricted in that row, the wildcard. An entry may name a view of a scope
variable (`a + 1`, `−a`), and it then constrains the underlying variable.

Within a row the binary entries must form a **forest** over the underlying
variables. The constructor throws `InvalidProblemDefinitionException` for:

- a binary entry whose two sides share an underlying variable, including
  `x` against `x + 1` and a constant against the same constant;
- a binary entry that closes a cycle, including a second entry on a pair
  already joined (#1014, fixed by #1016).

An exact repeat of an entry is allowed, because `AtMostOneSmartTable` produces
them when its array repeats a variable.

Degenerate shapes, checked by probe at `c9ceea25`
(`tmp/fd-smarttable/edge/edge.cc`, over `x, y, z ∈ 0..2`; every proof
verified):

- **No rows**: unsatisfiable, a contradiction at the root. Tested (#254).
- **An empty row**: always true. 27 solutions.
- **An empty scope**: allowed; with one empty row it constrains nothing.
- **`in_set(x, {})`**: that row is dead. **`not_in_set(x, {})`**: no
  restriction.
- **Set or value entries outside the domain**: handled as their meaning
  says. `in_set(x, {−5, 1, 7})` is `x = 1`; `x = 9` kills its row.
- **A repeated scope variable, or the scope listing a view**: allowed, and
  generalised arc consistent in the brute-force check below.
- **An entry over a variable outside the scope**, including a constant
  operand not listed in the scope (`less_than(x, 2_c)` with scope `{x, y}`):
  **accepted at construction, then the solve aborts** with an uncaught
  `std::out_of_range` from `unordered_map::at`. From the `.scp` it is a
  `terminate`. `cake_pb_cp` accepts the same file and encodes the entry
  (#1119). Listing the constant in the scope works: 18
  solutions for `x < 2_c`.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `SmartTable` | `n/a`[^mznst] | `?`[^xst] | `?`[^cst] | ✓ `smart_table` | chain-verifies only on narrow shapes; see [Cake conformity](#cake-conformity) |

[^mznst]: MiniZinc has no smart-table global. The retiring
    `frontend-support-matrix.md` row says ✓, but nothing under `minizinc/`
    names `SmartTable`.

[^xst]: The XCSP3-CPP-Parser the build fetches has no smart or hybrid table
    element, so nothing reaches the class from an XCSP3 file today. Whether
    the XCSP3 specification defines one, which would make this a frontend
    gap rather than `n/a`, was not checked for this audit.

[^cst]: `gcspy` has no binding. Whether CPMpy has a smart-table global was not
    checked; CPMpy is not installed on the audit machine.

The `.scp` form is `(label smart_table ((entry …) …) (vars …))`, with an entry
`(v1 op v2)`, `(v op c)` or `(v in|notin (c …))`. It is cake's row-delimited
shape. The reader makes a comparison a binary entry when its right-hand side
names a declared variable and a unary one when it is an integer.

### Options

**`with_short_reasons(std::optional<bool>)`**, default `true`. With proofs on,
at every assertion level, each call defines a fresh flag fully reifying its
reason; at `AssertionLevel::Off` it states its justifications under that one
literal instead of the whole reason; see [Proof-time state](#proof-time-state). It does not change the
OPB model, only the proof. `std::nullopt` leaves it on. `LexSmartTable` and
`AtMostOneSmartTable` build their `SmartTable` with the default and cannot
change it. `smart_table_random` defaults it **off**, and turns it on with
`--short-reasons`.

What it buys depends on how many calls infer something. The thesis, on random
single-table instances, found it a large saving in proof size, about two orders
of magnitude on the larger ones (Section 4.3, which also discusses checking
time).
On an enumeration where most calls
infer nothing it doubles the proof and multiplies checking time by 20, because
the flag is made whether or not a justification reads it
([Proof performance](#proof-performance), #1120).

No `with_consistency()`: the propagator is `GAC` and there is no other arm.

### Variable kinds and views

The scope takes any `IntegerVariableID`: plain, constant, or a view. Entries
may name views of scope variables (`a + 1 < b`, `−c ∉ {−1}`), and since #1090
(closing #238) the propagator keys every domain copy by the underlying
variable, converting through the view on the way in and out, so every view of
one variable in a row reads and narrows the same set.

**The proof handles views.** Its literals are stated over the view, which has
its own range literals (#904). The `smart_table_constraint_views` modes check
the exact solution set and generalised arc consistency at every node for one
table whose entries mix every relation, on three domain settings, and one
whose entries name views directly, on two. `smart_table_constraint_views_view_mixed` runs them with the scope
wrapped in views. The full wrap sweep (18 wraps, each position) is registered
only under `GCS_ENABLE_VIEW_WRAP_SWEEP`.

`provable_entry_member`, which once refused binary entries over negated views,
views with a negative offset, and constants, is dead code: its only call is
commented out.

### Reification

`None.` Nothing asks for one: a reified smart table is another row set.

### Relation to other families

**Into this family.** `LexSmartTable` (the `lex` family) and
`AtMostOneSmartTable` (the `at_most_one` family) each build a `SmartTable` in
`prepare()` and install it as a child. Both are kept as baselines for their
native classes, `LexGreaterThan` and `AtMostOne`, which are what the front ends
post. They inherit everything in this document: the triggers, the hole
sensitivity, the rules, the hint, and the findings. The rows they build are the
thesis's Equation 4.1 and Encoding Procedure 4.3, and are those documents'
business.

One inheritance is a bug of theirs: they do not pass their constraint ID to the
child, so every assertion the child makes carries
`smart_table:((constraint_id unnamed))`. Every other constraint that delegates
this way calls `set_constraint_id` first (#1121).

**Posts as children.** Nothing.

**Shares code.** Nothing. The positive and negative table propagators, and the
runtime tables `AutoTable` and `tabulation.cc` build, share
`extensional_utils`; `SmartTable` uses none of it. Its view helpers (`deview`,
`to_view_value`) are private to `smart_table.cc`.

**Presolvers.** None reads or rewrites it. `AutoTable` builds a plain table.

**Reached only through a decomposition?** From files, only through the `.scp`.
In code, through the class itself and the two baselines.

**The candidate merge with `table`, settled: separate.** The family list
proposed one extensional document. The two share no code, and their encodings
differ in kind. `Table` has a proof-only integer selector and one row per
allowed tuple, half reified on the selector's value. `SmartTable` has one proof flag per row and a flag
per entry, and a different propagation algorithm. They are also reached
differently: `Table` from every front end, `SmartTable` from none.

## The proof model

### OPB encoding

The thesis's Encoding Procedure 4.1 for the rows. The entries differ from its
Encoding Procedure 4.2 in several places, listed after the table.

```
Σ_i t_i ≥ 1                                    at least one row holds
t_i ⇒ Σ_{e ∈ row i} flag(e) ≥ |row i|          row i holds if selected
¬t_i ⇒ Σ_{e ∈ row i} ¬flag(e) ≥ 1              ... and only then
```

So `t_i` is fully reified and set by unit propagation on a complete assignment,
which `solx` needs. The entry flags:

| Entry | Flag | Rows |
|---|---|---|
| `a < b`, `a ≤ b`, `a > b`, `a ≥ b` | `bin_lt` etc., fully reifying `BinEnc(b) − BinEnc(a) ≥ 1` and so on | 2 |
| `a = b` | `bin_eq`: `bin_eq ⇒ BinEnc(a) − BinEnc(b) = 0`, and `¬bin_eq ⇒ gt ∨ lt` with `gt`, `lt` fully reified | 7 |
| `a ≠ b` | its own `bin_eq` flag, the two halves swapped | 7 |
| unary entries on one variable, consolidated | `inset`: `inset ⇒ Σ_{v ∈ D₀ \ S} [a ≠ v] ≥ |D₀ \ S|`, `¬inset ⇒ Σ_{v ∈ S} [a ≠ v] ≥ |S|` | 2, or 1 when `S` is empty |

A binary entry's flag is shared by every row that has the same entry, keyed
on `(a, b, op)`.

**Where the entries differ from the thesis.**

- **Unary entries are consolidated.** Before encoding a row, every unary entry
  on one variable, value or set, is merged into a single `in` set: the values
  of the variable's **initial domain** `D₀` that satisfy all of them. The
  reason is #40, found by random testing: with stacked unary entries encoded
  separately, "unsupported values fail to unit propagate", in the words of the
  `stacked_unary` test. The thesis encodes a value entry `a ≥ 5` as the literal
  itself; here it becomes a set over `D₀`, one equality literal per value.
- **Sets** are stated over every value of `D₀`: `inset ⇒ [a ≠ v]` for each
  `v ∈ D₀ \ S`, and the reverse direction `¬inset ⇒ Σ_{v ∈ S} [a ≠ v] ≥ |S|`.
  The thesis's `GenericR` (Equation 3.45) states the set by its two bounds
  plus one `[a ≠ v]` per missing value inside them. Both are per value.
- **Every order relation** (`<`, `≤`, `>`, `≥`) and `≠` gets a flag of its own
  here. The thesis's Encoding Procedure 4.2 has cases only for `≥`, `<`, `=`
  and `≠`, reusing the `≥` and `=` flags, negated, for `<` and `≠`.
- **`=`** is a half reification of an equality plus a disjunction of strict
  flags. The thesis makes it a conjunction of two `≥` flags. Both are set by
  unit propagation on a complete assignment.

**Definitional**, and a function of the declared domains. **Size**: the flag
and row counts above, plus the literal definitions the shared layer writes. A
binary entry is logarithmic in width; a unary entry is **linear in its
variable's initial width**, through the equality literals of the consolidated
set. Measured at `c9ceea25` (`tmp/fd-smarttable/width/`, two variables in
`0..W`, one row):

| Row | OPB lines at W = 10² | 10³ | 10⁴ |
|---|---|---|---|
| `{x < y}` | 11 | 11 | 11 |
| `{x ≥ 5, y ≤ W − 5}` | 825 | 8,025 | 80,025 |

### Labels

`None` that anything uses. The fully reified entry flags' two definition rows
carry the flag's own labels, `@f[N][bin_lt][r]` and `@f[N][bin_lt][f]`, but no
proof line cites a label: every step is a RUP against the database. The row
rows, the at-least-one row and the set rows are unlabelled. The flags are named
`f[N][t<i>]`, `f[N][bin_lt]`, `f[N][gt]`, `f[N][inset]` and so on, where `N`
is the proof model's global flag counter, so a flag's name depends on what was
posted before it.

### Cake conformity

| Case | Chain | `opbdiff` |
|---|---|---|
| `scp_chain_smart_table_sat` (`{A ≤ B}`, enumerate) | full workflow 2 | `none` |
| `scp_chain_smart_table_unsat` (two rows each forcing a value out of its domain) | full workflow 2 | `none` |

Both chain-verify at `c9ceea25`, and both are deliberately narrow. Cake
names the rows and entries differently: `x[_1][k]` for row `k`,
`x[_1][k_j][slt]` for its entries, and `c[_1][al1]` for the at-least-one row.
Beyond those two cases, run through `run_scp_chain.bash` at `c9ceea25`
(`tmp/fd-smarttable/scp/`):

| Extra case | Result |
|---|---|
| `{A = B}`, enumerate | verifies |
| two tables of binary entries, UNSAT | verifies |
| three rows of binary entries `<`, `=`, `>`, `≠`, `≥`, enumerate | fails: a tree-filtering lemma cites `f[0][t0]`, which cake's OPB never defines |
| two rows of order entries only (`(A < B) (B ≤ C)`, `(A > C) (B ≥ A)`), enumerate | fails at the lemma `rup 1 ~f[0][t0] 1 ~i[A][ge3] 1 i[B][ge4] >= 1`: on cake's OPB, `f[0][t0]` is set and nothing follows from it. The same proof verifies against our own OPB |
| two rows, binary plus one unary `B ≥ 2`, enumerate | fails: the proof cites `i[B][ge0]`, defined in our OPB (for the consolidated set) and not in cake's |
| the `smart_table_small` rows, enumerate | fail the same way |
| the `smart_table_small` rows plus a second table `((C = 2) (A = 1))`, UNSAT | verifies on our OPB; on cake's, VeriPB stops at proof line 4: "The label `@i[A][ge4][r]` is not assigned", a literal definition our OPB has and cake's does not |

So two causes, not one. The comment above the chain cases gives the row-flag
names as the reason for `none`, but puts the enumeration limit on equality and
set entries and #358, and a table of order entries alone fails too. The same
comment says "The refutation (unsat) verifies regardless (RUP)". That is true
of the in-tree case but not in general: the UNSAT case in the last row fails,
by the second cause below. The first cause is the row flags' names,
which matters for any proof whose steps need a row flag. The second is the
consolidated unary encoding's literals, which is #358's divergence, closed as
wontfix on 2026-06-30 (*chain row flags*).

### Proof-time state

- **At the root**: nothing beyond the OPB. No initialiser, no scaffolding.
- **Lazily, per call, at any assertion level**: with short reasons on, a
  flag `f[N][sr]`, two `red` lines fully reifying the call's whole reason, at
  `ProofLevel::Top`. It is made after the call has worked out which rows are
  live and which values are unsupported, but without looking at either, so it
  is made whether or not anything follows; at an assertion level nothing cites
  it. Because the information is already there, making it lazily is a local
  change. It is **never
  deleted**: the `delete_range` is commented out. So a proof carries one per
  propagator call.
- **Lazily, per call, at `AssertionLevel::Off` only**:
  - **Tree-filtering lemmas**, one per filtering step of a binary entry, at
    `ProofLevel::Current`. Each is `¬t_i ∨ conclusion ∨ ¬premise`, the entry's
    own inference with the row flag in its reason. They are globally valid, so
    deleting them at backtrack is only housekeeping. They are written in every
    call that filters, whether or not it infers.
  - **Per-tuple steps** at `ProofLevel::Temporary`, inside each removal's and
    each contradiction's justification, deleted with it.
- **Naming.** No row a justification depends on is labelled. An external
  tool finds the row flags by
  their `t<i>` suffix in row order under the constraint's comment in the OPB:
  `* constraint smart_table _N`, or the parent's type and ID under a
  baseline (`* constraint lex_smart_table _8`). It finds the entry flags by structure
  only.
- **OPB versus proof.** Row and entry flags are in the OPB, and all are set by
  unit propagation on a solution. The `sr` flags are proof-only extension
  variables.
- **Proof-only vectors.** `_pb_selectors` is empty with proofs off, and the
  propagator takes a pointer into it only under a logger. `_selectors`, one
  `{0, 1}` `State` variable per row, exists whether or not proofs are on.

## The implementation

### Initialisation and global data

- **The constructor**: the aliasing and cycle checks, a union-find per row.
- **`prepare()`**: allocates one `{0, 1}` `State` variable per row, the
  solver-side selector.
- **`define_proof_model()`**, with proofs on only: consolidates each row's
  unary entries by walking each such variable's initial domain, and writes the
  rows above. The rows it writes are linear in that width, but the work of
  building them is up to quadratic in it (#1127). Each initial-domain value is
  looked up in the consolidated set `S` with a linear `std::count`, so
  `|D₀| × |S|` comparisons per consolidated entry: `W(W + 1)` for `x ≥ 1` over
  `0..W`, but `6(W + 1)` for `x ≤ 5`. The consolidation itself takes each input
  set entry by value, copying and scanning it once per domain value, so
  `|D₀| × Σ|input set|` more. It is quadratic when `S` or an input set is
  `Θ(W)`. See [Interval efficiency](#interval-efficiency).
- **`install_propagators()`**: builds each row's forest once
  (`build_forests`), rooting each tree at the row's first-mentioned variable
  that is not yet in a tree.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| the smart-STR propagator | `on_change` on every scope variable | derived | 1, 2 | always | not claimed; is (see below) | no |

**Idempotence.** Not claimed. One call reaches generalised arc consistency: a
value kept is supported by a solution of some live row whose values were all
kept, so an immediate rerun removes nothing and kills no row. A build claiming
it (`tmp/fd-smarttable/mut/st_idem.cc`) passes `GCS_CHECK_IDEMPOTENT_CLAIMS`
over the 5,000-table brute-force check and both baseline benchmarks. The claim
would save 1.4% of calls on the at-most-one benchmark and 0.3% on the lex one,
with no measurable time. Not worth an issue.

It never disables itself, even once every remaining assignment satisfies a row.

### Mutable state and incrementality

**Nothing persists but the selectors**, one `State` variable per row, set to 0
when a row is found dead and restored by the `State` on backtrack. Every call
rebuilds everything else from the current domains:

- a hash map from each underlying variable to a vector of its values;
- a copy of that map per tree of every live row, each holding every scope
  variable, not only the tree's own (#1128);
- the filtered copies, the unsupported sets and the removals.

Every live row is revisited on every call, whatever changed.

**What maintaining it would buy.** #364's survey names "tree-walk frontier
caching". The cost measured here is more basic: allocation and hash lookups
are a third of the samples, and half with the map helpers ([CPU performance](#cpu-performance),
*per-call cost*). Copying only each tree's own variables would remove the
factor the whole-scope copies add (#1128). STR's usual economies, skipping
variables already fully supported and variables unchanged since the last
call, are not used.

### Interior values and optional pruning

**What this family offers:** `None.`

**What this family observes:** holes in every scope variable. The propagator
is generalised arc consistent, so a hole anywhere can remove a row's last
support for another value, and every scope variable is watched `on_change`.
The triggers tell the truth. A variable that appears in a smart table keeps a
neighbour's interior pruning alive, whatever its entries look like: an
order-only entry such as `x < y` still loses supports when a hole appears.

### Robustness and limits

- **Unbounded domains.** Per value throughout. Two variables over `0..10⁶`
  with one row `{x < y}` take 1.27 s and 146 MB for four propagator calls
  (release, `c9ceea25`, fataepyc-09, 2026-09-26, pinned with `taskset -c 40`
  and `GLIBC_TUNABLES`). `10⁹` was not run. Separately, with proofs on, one unary
  entry `x ≥ 1` over `0..128,000` takes 4.1 s to reach the start of the proof,
  against 1.75 s once its linear membership scan becomes a binary search
  (#1127; release, `c9ceea25`, fataepyc-10, 2026-09-29). See [Interval
  efficiency](#interval-efficiency).
- **Negative values and zero.** Tested (`wide_constants` over `−59..58`,
  `stacked_unary` over `−1..4`) and in the brute-force checks. The 5,000-table
  check draws domains from `−2` up, value constants from `−2..4` and set values
  from `−3..5`; negated views reach `−6`. The 200 wider tables draw domains
  from `−6` and set values from `−8`.
- **Degenerate shapes**: see [Semantics](#semantics). The one that fails is an
  entry outside the scope.
- **Overflow.** The only arithmetic is a view's `−v + c` on domain values and
  the shared layer's `BinEnc` differences for binary entries; nothing
  multiplies.

### Interval efficiency

**Not fine at any width**: a genuine per-value support scan, with no weaker arm
behind it.

1. **Propagation.** Each call walks every scope variable's values
   (`each_value_immutable`) into vectors, copies all of them once per tree of
   each live row (#1128), and sorts, intersects and differences them per entry.
   Everything is proportional to values, not intervals. Nothing here uses
   `IntervalSet` operations.
2. **Reasons.** `generic_reason(vars)`, one literal per bound and one per run
   of missing values (#935), so per run. It is built eagerly and not guarded on
   `want_reasons()`, which costs well under 1% of a profile with proofs off.
   With short reasons, the `sr` row restates it once per call.
3. **Proofs.** One justification per removed value, each `|T| + 1` RUP steps.
   A `=` entry's filtering lemmas are one per discarded value, the order entries'
   one per side, `≠`'s one. There is no width gate anywhere. The encoding is
   linear in a unary-entry variable's width ([OPB encoding](#opb-encoding)),
   but **building it is up to quadratic** in that width (#1127):
   `define_proof_model` looks each initial-domain value up in the consolidated
   set `S` with a linear scan (`|D₀| × |S|`), and the consolidation copies and
   scans each input set entry once per value (`|D₀| × Σ|input set|`). That is
   quadratic when `S` or an input set is `Θ(W)`, as in both rows below; an
   entry `x ≤ 5` costs only `6(W + 1)` comparisons. Measured on a release
   build of `c9ceea25`, fataepyc-10, 2026-09-29, pinned to one core, as the
   median of three runs of the wall time from entering `solve_with` to
   `after_proof_started`, with the OPB and proof written to tmpfs
   (`tmp/fd-smarttable/codex-r1/construct.cc`, `construct_shm.out`; one
   variable over `0..W`, one row, short reasons off):

   | Row | W = 16,000 | 32,000 | 64,000 | 128,000 |
   |---|---|---|---|---|
   | `{x ≥ 1}` | 0.23 s | 0.53 s | 1.45 s | 4.14 s |
   | same, sorted lookup | 0.20 s | 0.42 s | 0.86 s | 1.75 s |
   | `{x ∈ {1..W}}` | 0.32 s | 0.93 s | 3.44 s | 12.0 s |
   | same, sorted lookup and no per-value copy | 0.20 s | 0.43 s | 0.87 s | 1.77 s |

   The "sorted lookup" rows link a variant of `smart_table.cc`
   (`codex-r1/st_sortedscan.cc`, and `st_sortedscan_v2.cc`, which also takes
   the set entry by reference). Each writes an OPB and a proof byte-identical to
   the unmodified build's at every width above, and grows linearly. Without
   proofs, `define_proof_model` does not run and none of this is paid.
4. **The audit lane.** Three rows, all `KnownTrip`: `SmartTable` (two wide
   variables, one row `{v0 = v1}`), `LexSmartTable` and `AtMostOneSmartTable`.
   None is in the proof-size case. The rows do not vary unary or set entries,
   which is where the encoding's width cost is, and do not vary views or
   proofs. Since the propagation side trips anyway, the proof-side hazard is
   unrecorded rather than unseen. A large-domain arm is #833's question: the
   issue lists `SmartTable` among the constraints with nowhere to fall back to.

## Inference catalogue

Two rules, both instances of the thesis's Justification Procedure 4.1
(Section 4.2.2), whose smart-table special case is Section 4.1.2.

The propagator also marks a row dead, setting its solver-side selector to 0.
That is bookkeeping in rule 1's algorithm, not an inference the proof sees:
the selector has no proof counterpart, and it is set with
`NoJustificationNeeded`. What a later justification needs about a dead row,
`¬t_i` under the then-current reason, follows by RUP. If a binary entry
killed the row, it follows from the tree-filtering lemmas written by the call
that found the row dead. Those are at `ProofLevel::Current`, so they survive
into every node below it, and the dead row writes no new ones. If only a
unary entry killed it, no lemma was written and none is needed: the set's
flag rows give it from the encoding alone.

**Lemmas from earlier calls are load-bearing.** A mutation that keeps each
call's lemmas only until that call ends
(`tmp/fd-smarttable/factcheck2/percall/st_percall2.cc`, from the second fact-check) still
verifies every in-tree mode. On a probe with an Example 4.3 row plus random
rows (`factcheck2/percall/probe.cc`), it fails VeriPB on 5 of 60 seeds (29, 45, 46, 51,
52), where the unmutated build verifies all 60. So later calls do cite earlier
calls' lemmas, and nothing in the tree tests it.

**The wire inventory.** One hint, `hints::SmartTable`, wire
`smart_table:((constraint_id N))`, carrying `originator` (`ConstraintID`) and
no subhint. Under `LexSmartTable` and `AtMostOneSmartTable` it reads
`constraint_id unnamed` (#1121).

**What licenses them.** Each removal and each contradiction is a `RUP
sequence`:

1. **Tree-filtering lemmas.** While filtering a live row's trees, each
   binary-entry step that narrows a domain copy logs `¬t_i ∨ conclusion`
   under that step's one-literal premise. For `a < b` narrowing `b` above
   `min(a)`, this is `¬t_i ∨ [b ≥ min(a) + 1] ∨ ¬[a ≥ min(a)]`. Each is RUP
   from the entry's flag rows, by the equality and inequality procedures
   (JP 3.1, 3.2, 3.12).
2. **One step per row**, `¬t_i ∨ conclusion` under the reason. With the
   lemmas in place, unit propagation from the reason and `t_i` reproduces the
   row's tree filtering, and so reaches a contradiction for every row that
   does not support the value.
3. **The conclusion by RUP** against `Σ t_i ≥ 1`.

The thesis proves the sequence correct (the correctness proof of JP 4.1,
resting on Theorem 3.2). Its precondition is that each row's binary entries
form a forest, which the constructor enforces. Unary entries need no lemma:
the consolidated set's flag gives the equality literals directly.

**Why the lemmas are needed.** The thesis's Example 4.3: `W < X < Y < Z` over
`−2..0`, one row. Unit propagation over the bit-sum encoding of `W < X` does
not reach `X`'s bits, so the per-row step does not follow without the lemmas.
The build `tmp/fd-smarttable/mut/st_nolemma.cc` drops every lemma. With it,
VeriPB refuses that instance at offsets `−2`, `0` and `3`, which the unmutated
build verifies.

**Tightness.** No mutation lane. By hand, at `c9ceea25`, with every
tree-filtering lemma dropped:

- VeriPB refuses Example 4.3 and the in-tree `mixed_same_var` mode.
- It accepts every other `smart_table_test` mode, including `dead_tuple` and
  `deep_tree`.
- It accepts 200 random tables.

So the lemmas are load-bearing, and one in-tree fixture would notice them
gone. Example 4.3 is the better fixture for a lane: an unsatisfiable root with
no search.

### Rule: unsupported-value

(Rule 1.)

- **Infers** — `x ≠ v`, for every value of every scope variable that no live
  row supports.
- **Fires when** — the propagator, on any change to a scope variable, when at
  least one row is still live.
- **Strength** — `GAC` on the constraint, over the underlying variables.
  Checked by brute force at every search node
  (`tmp/fd-smarttable/gac/gac_probe.cc`):
  - 5,000 random tables, three or four variables, domains of two to five
    values with holes;
  - each row a random forest of binary entries, plus value and set entries;
  - entries over `x`, `x + k` and `−x + k`, and scopes with a repeated
    variable or a view;
  - every solution set exact, 0 failures, 4,171 instances that searched;
  - 300 of them with proofs, short reasons on and off, every proof verified.

  200 more over wider domains (up to fifteen values) give 0 failures too.
  `dead_tuple`, `deep_tree` and `views` also check GAC at every node.
- **Algorithm** — smart STR (Mairy, Deville and Lecoutre 2015):
  - for each live row, filter a copy of the domains over each of its trees,
    leaves up, and mark the row dead if a copy empties;
  - otherwise filter each tree root down, and count the values that remain as
    supported;
  - wildcard variables are fully supported.

  The two passes, as Mairy et al. publish them, are what reach GAC on a tree
  without iterating. #1007 (closing #994) made the implementation match: its
  second pass had gone leaves up, and it had counted support before the pass
  finished. Cost per call, as a worst case: for each live row, one copy of
  the whole scope's current domains per tree of the row, then the values of
  each entry's variables; plus the map building (see [Mutable
  state](#mutable-state-and-incrementality)). In values, not intervals. The
  copies are not bounded by what the row mentions (#1128). A row with `q`
  trees over a scope holding `D` values copies up to `qD` values: each
  tree's copy is made just before that tree is filtered, so it is paid
  whatever that tree's filtering removes, and only a tree that kills the row
  stops the copies after it. So one row of
  `n` independent unary entries over `n` variables of `d` values copies
  `Θ(n²d)`. `LexSmartTable`'s `n` rows, over distinct variables, have `1, …, n` trees
  over a scope of `2n` variables, so while all are live they copy `Θ(n³d)`. The growth shows
  at the root, in wall time to the first search node, one propagator call
  (`tmp/fd-smarttable/codex-r1/forest.cc`, `forest_reps.out`; release build of
  `c9ceea25`, fataepyc-10, 2026-09-29, pinned to one core, median of five
  runs):

  | Model | n = 100 | 200 | 400 | 800 |
  |---|---|---|---|---|
  | one row `{x[i] ≥ 0 : i < n}`, `x ∈ 0..99`: `n` trees | 0.0097 s | 0.036 s | 0.143 s | 0.561 s |
  | one row `{x[i] ≤ x[i+1] : i < n − 1}`, same variables: one tree | 0.0035 s | 0.0070 s | 0.014 s | 0.028 s |

  `LexSmartTable` over `0..9` takes 0.0033, 0.018, 0.114 and 0.814 s at
  `n = 25, 50, 100, 200`: 5.5, 6.3 and 7.1 times per doubling, approaching
  the cubic 8. Every run makes one propagator call and removes nothing. The
  times include the solver's setup and the whole call, so the copies' share
  of them is not isolated.
- **Why it is true** — each row is a conjunction whose binary entries form a
  forest, so after the two passes each tree's domain copies hold exactly the
  values that appear in some solution of that tree. The trees of a row share no
  variable, so a value supported by every tree it appears in is supported by the
  row. A value supported by no row appears in no solution of the constraint.
- **Proof technique** — `RUP sequence`: the tree-filtering lemmas written
  while filtering, then `|T|` steps `¬t_i ∨ x ≠ v` under the reason, then
  `x ≠ v` under the reason by RUP. The procedure is the thesis's JP 4.1
  (Section 4.2.2; the smart-table case is Section 4.1.2), and its precondition is a forest per row. It is also McIlree
  and McCreesh 2023.
- **Reason** — `generic_reason(vars)`: every scope variable's bounds and its
  runs of missing values. Not minimal: a row's support depends only on the
  variables it mentions. With short reasons (the default), the justification
  and the conclusion are stated under the single literal `sr`, which the call
  defines to be equivalent to that reason. Per run. Built eagerly, not guarded
  on `want_reasons()`.
- **Assertion** — what it should be: `x ≠ v ∨ ¬reason`, or `x ≠ v ∨ ¬sr`.
  At `AssertionLevel::Off` that is the conclusion written. **At `Definitions`,
  `Links` and `Inferences` the `a` line is the bare `x ≠ v`**, with no reason, because the
  assertion path reuses the proofs-off call with `NoReason`. Every
  `smart_table` assertion in the three examples' proofs at `Inferences` is one
  literal. On `smart_table_small`, `a 1 ~i[C][eq1] >= 1` is asserted, and a
  later `solx` has `C = 1`. On the at-most-one enumeration measured below, 184
  of the 194 `smart_table` assertions are falsified by a later `solx`, and none
  of the 13,867 others is. At `Backtracking` no inference is asserted, so that
  level is unaffected. `Circuit`'s SCC propagator has the same defect, from the
  same change, in its `prune_skip` and `fix_req` rules (*assertion reasons*).
- **Hint** — `hints::SmartTable`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `offline` once the assertion carries its
  reason, which is the fix (*assertion reasons*): JP 4.1 run on the reason's domains and the `.scp`'s rows rebuilds the
  lemmas and the per-row steps, with nothing chosen. The clause the rule
  **does** assert at `Definitions`, `Links` and `Inferences` is not implied by
  the model, so no
  derivation of it exists.
- **Proof size** — per removed value: `|T|` per-row steps plus the conclusion,
  each naming the reason (per run) or `sr`. Per call, with short reasons on:
  two `red` lines with the reason's literals. Per filtering call: the lemmas,
  of which a `=` entry writes one per discarded value. So values, not runs.
- **Gaps** — at `Off`, `None.` At `Definitions`, `Links` and `Inferences`,
  the assertion is wrong (see **Assertion**).
- **Tightness** — see the preamble. The lemmas are load-bearing; no lane.

### Rule: no-live-row

(Rule 2.)

- **Infers** — a contradiction.
- **Fires when** — the propagator, when every row is dead after this call's
  first pass, including a table with no rows.
- **Strength** — `GAC`, as rule 1.
- **Algorithm** — the first pass of rule 1.
- **Why it is true** — no row can hold, and the constraint is their
  disjunction.
- **Proof technique** — `RUP sequence`: the lemmas, `|T|` steps `¬t_i` under
  the reason, then the contradiction by RUP against `Σ t_i ≥ 1`. JP 4.1's
  infeasible branch.
- **Reason** — as rule 1 at `Off` (the `sr` literal with short reasons); the
  full `generic_reason` at `Definitions`, `Links` and `Inferences`.
- **Assertion** — an explicit `contradiction()`, so `¬reason` (`¬sr` at
  `Off` with short reasons). Unlike rule 1, the assertion path passes the
  reason.
- **Hint** — `hints::SmartTable`.
- **Offline reconstructibility** — `offline`, as rule 1.
- **Proof size** — `|T| + 1` steps plus the lemmas.
- **Gaps** — `None.`
- **Tightness** — Example 4.3 is this rule, and the lemma mutation is refused
  there.

## Evidence

### Tests

| Lane | What it checks |
|---|---|
| `smart_table_constraint_{lex_gt, lex_ge, lex_lt, lex_le}` and `_fixed` | lex rows on six shapes; **only that each solution found is lex-ordered**, not the solution set; VeriPB |
| `smart_table_constraint_{am1_eq, am1_in_set, al1_eq, al1_in_set}` | at-most-one / at-least-one rows; the same soundness-only check; VeriPB |
| `smart_table_constraint_mixed_same_var` | one variable in `≠`, `in` and `>` entries of one row; exact solution set; VeriPB |
| `smart_table_constraint_stacked_unary` | stacked unary entries (#40); exact set, one UNSAT; VeriPB |
| `smart_table_constraint_wide_constants` | unary constants over `−59..58`; exact set, **truncated** by the default cap on its largest instance |
| `smart_table_constraint_degenerate` | no rows, fixed variables both ways, one variable (#254); exact set |
| `smart_table_constraint_dead_tuple`, `_deep_tree` | #994's two bugs; exact set and GAC at every node |
| `smart_table_constraint_views`, `_views_view_mixed` | #238's views; exact set and GAC at every node |
| `smart_table_dup` | the aliasing and cycle rejections (#1014), and `LexSmartTable({a, b}, {b, a})` rejected at solve time |
| `smart_table_{small, lex, am1, random}` | the examples, through `run_test_and_verify.bash` |
| `scp_chain_smart_table_{sat, unsat}` | the cake chain ([Cake conformity](#cake-conformity)) |

- **Seeds.** The test's instances are fixed, including the `mixed` view
  wraps, so the seed it announces changes nothing. The `smart_table_random`
  lane passes no `--seed`, so it draws a fresh table every run and prints the
  seed only under `--stats`: a failure there could not be reproduced.
- **Caps.** The default caps (`GCS_TEST_MAX_SOLUTIONS=300`,
  `GCS_TEST_MAX_RECURSIONS=1500`) apply to the `solve_for_tests` modes. At
  `c9ceea25` they fire on `wide_constants`' first instance only (300 of 2,106
  solutions, with and without proofs), which is then checked for soundness only.
  The lex and at-most-one modes call `solve_with` directly, so no cap applies
  to them.
- **No lane sets or clears a cap.**
- **No real instance** has been ported: there is none, since no front end
  posts the constraint.
- **Tightness.** No mutation lane and no control (see the catalogue preamble).

**What the tests do not cover.**

- **Completeness of the lex and at-most-one modes.** They check that each
  solution satisfies the relation, not that every solution is found. The
  brute-force check above covers completeness for random tables, and the
  at-most-one and lex benchmarks below find the same solution counts as their
  native classes.
- **Any assertion level.** No lane runs `GCS_ASSERTION_LEVEL`, which is how
  the bare assertions went unnoticed.
- **Entries outside the scope**: no test, and they crash.
- **Wide domains**: the widest variable in any lane is `−59..58`.
- **A load-bearing lemma**: only `mixed_same_var` needs one, and no in-tree
  mode needs a lemma from an earlier call (see the catalogue preamble).
- **Short reasons off**: every lane runs the default except
  `smart_table_random`, which runs with it off.

### Benchmarks and examples

No MiniZinc Challenge or XCSP3 instance reaches the constraint. The in-repo
examples are smoke tests: `smart_table_small` (the thesis's worked example,
8 solutions), `smart_table_lex`, `smart_table_am1` (`--n`, default 3) and
`smart_table_random` (`-n`, default 6). `smart_table_random` to a first
solution stays under 3 ms at `n = 16`.

- **CPU**: `AtMostOneSmartTable` at `n = 6`, over `0..6` with `y = 6` (2.4 s, 110,108 recursions) and
  `LexSmartTable` at `n = 4`, `0..4` (1.8 s, 244,095 recursions), all
  solutions. The native classes find the same trees, which makes the comparison
  exact.
- **Proofs**: the at-most-one rows at `n = 5`, over `0..5` with `y = 5`, with short reasons on and off
  (4.2 MB and 2.2 MB, 15.9 s and 0.8 s to check). `LexSmartTable` at `n = 3`,
  `0..4` takes 27 s to check.

### CPU performance

Release build at `c9ceea25`, fataepyc-09 (AMD EPYC 7643), 2026-09-26 and 27, pinned
with `taskset -c 40`, `GLIBC_TUNABLES` mmap and trim thresholds pinned, one run
each, all solutions in input order, smallest value first. The driver is
`tmp/fd-smarttable/bench/bench.cc`. Recursions and solutions are identical
within each pair, which is what makes the ratio a per-node one.

| Model | Recursions | Solutions | `propagations` (smart / native) | SmartTable | native | ratio |
|---|---|---|---|---|---|---|
| at most one of `x[0..3] ∈ 0..4` equals `y = 4` | 654 | 512 | 675 / 675 | 0.0115 s | 0.000627 s | 18× |
| same, `n = 5`: `x[0..4] ∈ 0..5`, `y = 5` | 7,617 | 6,250 | 7,773 / 7,773 | 0.123 s | 0.00709 s | 17× |
| same, `n = 6`: `x[0..5] ∈ 0..6`, `y = 6` | 110,108 | 93,312 | 111,663 / 111,663 | 2.42 s | 0.107 s | 23× |
| `x >lex y`, `n = 3`, `0..4` | 9,745 | 7,750 | 9,882 / 493 | 0.0599 s | 0.00757 s | 7.9× |
| same, `n = 4`, `0..4` | 244,095 | 195,000 | 244,908 / 3,554 | 1.83 s | 0.140 s | 13× |
| same, `n = 4`, `0..6` | 3,362,758 | 2,881,200 | 3,365,801 / 13,999 | 24.1 s | 1.85 s | 13× |
| same, `n = 5`, `0..4` | 6,103,695 | 4,881,250 | 6,108,652 / 24,323 | 53.7 s | 3.57 s | 15× |

The at-most-one rows widen the domain and move the distinguished value with
`n` (`x[0..n−1] ∈ 0..n`, `y = n`, so `2nⁿ` solutions): they are not an
arity-only series. The lex rows give `n` and the domain separately.

The native `LexGreaterThan` wakes on bounds and disables itself, so it is
called far less; the at-most-one pair make the same calls, and there the
ratio is per call. Each lex row `i` is `i + 1` one-edge trees, so while its
rows are live a call copies the scope's domains `Θ(n²)` times (#1128); how
much of the lex ratio's growth with `n` that explains was not isolated.

**Where the time goes**, from `perf` on the `n = 6` at-most-one run, the top ten by self
time are:

- `free` 8.7%
- the `unordered_map` lookup 8.7%
- `malloc` 7.0%
- `get_for_actual_var` 6.1%
- `operator new` 5.3%
- `set_for_actual_var` 4.3%
- `remove_supported` 4.1%
- the propagator's lambda 3.8%
- `get_unrestricted` 3.8%
- `_int_malloc` 3.5%

Allocation (`free`, `malloc`, `operator new`, `_int_malloc`) and the hash
lookup alone are 33%; with the map helpers and the propagator lambda, the ten are 55%. The binary-entry filtering itself,
`filter_edge`, is 2.9% self time, so the table algorithm is a small share.
The profile is of a run with proofs off (*per-call cost*). Each at-most-one
row is one tree, so it copies the scope once, and #1128's extra factor is
absent from this profile.

**What these benchmarks do not exercise.**

- The at-most-one rows are all `≠` entries sharing one variable, so each row
  is one star-shaped tree. The lex rows are forests: row `i` is `x[j] = y[j]`
  for each `j < i` and `x[i] > y[i]`, independent pairs, so `i + 1` one-edge
  trees.
- Neither has unary or set entries, and neither ever reaches rule 2
  (0 failures).
- Neither is a model anyone posts: both baselines exist to be compared with
  their native classes.

Cross-solver: `Not measured.` (#868).

### Proof performance

Same build and machine, VeriPB 3.0.2 with `--force-checked-deletion`, all
solutions, every proof verified.

| Model | Proof lines | Proof bytes | VeriPB | native: lines, bytes, VeriPB |
|---|---|---|---|---|
| at most one, `n = 4` (`0..4`, `y = 4`) | 6,774 | 333,960 | 0.15 s | 4,454, 130,397, 0.04 s |
| at most one, `n = 5` (`0..5`, `y = 5`) | 75,529 | 4,217,044 | 15.86 s | 49,930, 1,639,186, 0.61 s |
| lex, `n = 3`, `0..3` | 24,807 | 1,479,650 | 2.11 s | 17,859, 667,081, 0.13 s |
| lex, `n = 3`, `0..4` | 86,651 | 5,174,670 | 27.40 s | 63,899, 2,333,643, 0.68 s |

**Short reasons.** The at-most-one rows posted as a `SmartTable` at `n = 5`
(`x[0..4] ∈ 0..5`, `y = 5`),
with and without them, and with the flag created only when a call has
something to justify (`tmp/fd-smarttable/mut/st_lazysr.cc`):

| | `sr` definitions | lines | bytes | VeriPB |
|---|---|---|---|---|
| on (the default) | 7,773, one per call | 75,529 | 4,217,044 | 15.86 s |
| off | 0 | 59,358 | 2,184,691 | 0.79 s |
| on, made only when needed | 156 | 59,670 | 2,113,681 | 1.11 s |

On `smart_table_random` to a first solution (`n = 8, 12, 16`, seeds 1–3),
short reasons cut the proof's bytes by up to 5.8 times, though one proof
(`n = 8`, seed 3) grew by 10%. At `n = 16` they go from 0.64–0.90 MB to
0.12–0.15 MB, with checking time 0.07–0.13 s either way. So
the option is right and the per-call flag is not (#1120).

**Own versus shared.** Not separated by measurement. What can be said: with
short reasons off, the at-most-one proof at `n = 5` has 59,358 lines against
the native class's 49,930 on the same search. Its 6,250 solution-blocking RUPs
are common to both.

**At `AssertionLevel::Inferences`** (short reasons off, same run), 194 of the
proof's 14,061 assertions carry `smart_table`. The proof is 41,955 lines and
3.13 MB. All 194 are single literals, the bug of rule 1, so the checking
time at this level measures nothing useful.

## Status, gaps, and next steps

### Proof-logging gaps

- **Assertion levels.** Rule 1's assertion has no reason at `Definitions`,
  `Links` and `Inferences` (*assertion reasons*). The asserted clauses are not consequences of
  the model; VeriPB accepts them because it does not check assertions.
- **The propagator is not weakened by proofs.** At `Off`, every inference is
  justified.

### Known limitations

- An entry naming a variable that is not in the scope, or a constant operand
  not listed in it, aborts the solve (#1119).
- Two binary entries that close a cycle within a row are rejected, not
  handled.
- Wide domains are unusable: the propagator walks values, and a unary entry
  makes the OPB linear in its variable's width (#833) and the work of building
  it up to quadratic (#1127).
- Its proofs chain through `cake_pb_cp` only on narrow shapes (*chain row
  flags*).
- No front end posts it.

### Next steps

1. **Pass the reason in the assertion path** (*assertion reasons*). A
   one-line change here and two in `circuit_scc.cc`, and it is the one finding
   that makes a proof wrong. The `circuit` document, when written, inherits
   this finding for `prune_skip` and `fix_req`. Add a
   lane running `smart_table_test` at `GCS_ASSERTION_LEVEL=Inferences`, with
   a check that no asserted clause is falsified by a later `solx`.
2. **Make the short-reason flag lazily** (#1120). Small, and
   worth 14 times the checking time on the enumeration measured. While there,
   decide whether to delete it after use, as the commented-out code meant to.
3. **Reject or absorb out-of-scope entries** (#1119). A
   choice between a construction-time check and cake's semantics, which treat
   every named variable as in scope.
4. **Pass the constraint ID to the child** in `LexSmartTable` and
   `AtMostOneSmartTable` (#1121). Two lines.
5. **Two mutation lanes, each with its control.** One on Example 4.3,
   dropping the tree-filtering lemmas: the fixture needs no search and shows
   the lemmas load-bearing. One that forgets each call's lemmas when the call
   ends, on a fixture where a later call cites them (`factcheck2/percall/probe.cc` seed
   29 is one), since no in-tree mode does.
6. **The per-call cost**: copy only each tree's own variables' domains, not
   the whole scope's once per tree (#1128), keeping #994's rule that no tree
   grants support until every tree of its row is feasible. Then, unfiled
   (*per-call cost*): a flat per-variable index instead of the hash maps,
   reused buffers, and `get_unrestricted` per row precomputed. **And the
   construction cost** (#1127): look each initial-domain value up in the
   consolidated set by binary search or a sorted merge, not `std::count`, and
   take each input set entry by reference and sorted, not by value. Both leave
   the OPB and proof byte-identical on the probes in [Interval
   efficiency](#interval-efficiency). Low priority while nothing posts the
   constraint.
7. **The chain** (*chain row flags*): whether it is wanted, and if so cake's
   names for the row and entry flags. The chain-case comment should say what
   limits it either way.
8. **Tidying.** Remove `provable_entry_member` and its commented-out call.
   Claim idempotence (it holds, and buys under 2% of calls). Do not drop the
   tree-filtering lemmas of calls that infer nothing: later calls cite earlier
   calls' lemmas (catalogue preamble), so any such saving needs a proof that
   the dropped ones are never cited. Give the
   `smart_table_random` lane a fixed `--seed`, or print the seed it drew.

## Prior art

- **The constraint and its propagator** are Mairy, Deville and Lecoutre,
  *The Smart Table Constraint* (CPAIOR 2015). It is smart STR, with trees
  filtered in two passes when each row's binary entries are acyclic.
  Verhaeghe, Lecoutre, Deville and Schaus (CP 2017) extend Compact-Table to
  basic smart tables, and Verhaeghe's PhD thesis (UCLouvain, 2021), *The
  Extensional Constraint*, is on extensional
  constraints. No Compact-Table arm exists here.
- **The certification** is McIlree and McCreesh, *Proof Logging for Smart
  Extensional Constraints* (CP 2023), and McIlree's thesis, Chapter 4:
  - the encoding (Encoding Procedures 4.1 and 4.2);
  - the lemma-then-per-row-RUP justification (Section 4.1.2, generalised as
    JP 4.1 in Section 4.2.2, with its correctness proof);
  - Example 4.3, which shows the lemmas are needed;
  - smart-table decompositions of lex (Equation 4.1), at-most-one,
    not-all-equal, value-precede, increasing, element and array max
    (Section 4.1.4);
  - the short-reasons optimisation and its measurement (Section 4.3).

  The implementation here is the thesis's, which describes it as a
  straightforward implementation of Mairy et al.
- **What is ours.** The consolidation of unary entries into one set per
  variable (#40), the view handling (#1090) and the cycle rejection (#1016).
  The two-pass tree filtering, leaves up then root down, is Mairy et al.'s;
  #1007 made the implementation match it.

## Further reading

- McIlree's thesis, Chapter 4 (a copy in `tmp/thesis/` on the audit machine),
  for the encoding, the justification procedure and its proof, and the
  experiments behind short reasons.
- [`view-proof-logging.md`](../view-proof-logging.md), for how `SmartTable`
  joined the view sweep (#238).
- [`constraints.md`](../constraints.md), on aliasing and on why
  `SmartTable`'s `Equal` flag uses two half-reifications.
