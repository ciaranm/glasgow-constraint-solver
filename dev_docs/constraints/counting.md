# Counting: `Count`, `Among`, `NValue` and `GlobalCardinality`

> **Maturity** production ·
> **Audited** 2026-09-23 at `347e2f8c` ·
> **Open issues** filed by this audit: #1026 (wrong answers at `GAC` on an
> unsorted open cover; fix open as #1030), #1028 (`GlobalCardinality`'s default
> arm), #1029 (`Count` on a constant value of interest). Already open and
> touching this family: #843 (`NValue`'s encoding is per value), #876 (the `GAC`
> arm has no large-domain row), #488 (`NValue`'s occurrence rows disagree with
> cake's), #944 (Hall proofs cost values × variables²), #868 (cross-solver).
> More to file from [Next steps](#next-steps). Tracked under #871.

Four constraints that count occurrences of values in an array. `Count` counts one
value, which may be a variable. `Among` counts membership in a fixed set.
`NValue` counts distinct values. `GlobalCardinality` counts every value of a
fixed cover at once, with bounds consistent and generalised arc consistent arms
and an optional closed restriction. The family list grouped them as a *candidate
merge*. They share no propagation code and have four different encodings, so they
stay four classes. They are documented together because they answer the same
question, and because the most useful finding here is about how they relate. See
[Relation to other families](#relation-to-other-families).

Three things to know before touching it.

- **The constraint the models use is `Count` with a constant value.** Of 1,816
  `Count` posts across one instance of each of 298 MiniZinc Challenge models,
  1,464 have a constant value of interest; the other 352 are all in four models.
  `Among` appears in none. On that shape `Count` propagates exactly as a
  one-value `GlobalCardinality`, with an identical search tree, and is slower on
  eight of the nine models measured. That is #1029, and the decision (Ciaran,
  2026-09-23) is to make `Count` faster, not to rewrite it into another
  constraint in a front end.
- **`GlobalCardinality`'s default arm is the slower one.** `consistency::BC`
  searches for Hall intervals over every contiguous pair of cover values, every
  call. It is up to 235 times slower than `consistency::GAC` on the instances
  measured, and about level on the rest, never meaningfully faster. Its proofs,
  though, are several times smaller. The default is #1028.
- **`GlobalCardinality` at `GAC` loses solutions** on an open constraint whose
  cover is not in ascending order (#1026), until #1030 merges. No test covered
  it, and neither MiniZinc nor XCSP3 reaches that arm; only a `.scp` term
  recording it does.

## What it is

### Semantics

- **`Count(vars, y, n)`** — `n = |{i : vars[i] = y}|`. `y` may be a variable.
  Empty `vars` forces `n = 0`. `y` may also appear in `vars`, directly or as a
  view. No test posts that shape; this audit's differential did, and found
  nothing wrong (see [Tests](#tests)).
- **`Among(vars, S, n)`** — `n = |{i : vars[i] ∈ S}|`, `S` a set of constants.
  The constructor sorts `S` and removes duplicates. An empty `S`, or empty
  `vars`, forces `n = 0`.
- **`NValue(n, vars)`** — `n = |{vars[i]}|`, the number of distinct values
  taken. Empty `vars` forces `n = 0`. Note the argument order: `n` comes
  first, unlike the other three.
- **`GlobalCardinality(vars, values, counts)`** — for each `j`,
  `counts[j] = |{i : vars[i] = values[j]}|`. With `.with_closed()`, every
  variable must also take a cover value. Values outside the cover are free
  otherwise. The cover must be pairwise distinct and the two lists the same
  length; the constructor throws otherwise (#922), and front ends whose input
  may repeat a value call `fold_repeated_cover_values()` first and post the
  `Equals` it returns. At `347e2f8c` only `clone()` sorts the cover, and only
  under `BC`; #1030 (open) moves the sort into the constructor, for both arms. Empty `vars` makes every count zero. An empty cover is no
  constraint at all when open, and when closed it makes any non-empty `vars`
  unsatisfiable.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Count` | ✓ `fzn_count_eq`; `decompose` for the other five `count_*` and for `at_least`, `at_most`, `exactly`[^mzncount] | ✓ `count` with one value; `atMost`, `atLeast`, `exactly` with a constant or a variable count[^xcount] | ? | ✓ `count` | |
| `Among` | ✓ `fzn_among` | ✓ `among`; `count` with several values[^xcount] | ? | ✓ `among` | appears in no corpus model |
| `NValue` | ✓ `fzn_nvalue` | ✓ `nValues`, without `except`[^xnv] | ? | ✓ `nvalue` | |
| `GlobalCardinality` | ✓ `fzn_global_cardinality`, `_closed`, `_low_up`, `_low_up_closed`[^mzngcc] | ✓ `cardinality`, constant cover; occurrences constant, variable or interval[^xgcc] | ? | ✓ one of four names, recording the level and the closed flag | the level is not selectable from either front end |

[^mzncount]: Each `fzn_count_{leq,geq,lt,gt,neq}` in `minizinc/mznlib/`
    introduces `z ∈ 0..length(x)`, posts `glasgow_count_eq(x, y, z)` and
    compares `z` with `c`; `fzn_at_least_int` and `fzn_at_most_int` do the
    same with `v` and `n`, and `fzn_exactly_int` posts `glasgow_count_eq`
    directly. The directions were checked against the standard library's
    documentation: `count_leq(x, y, c)` means `c ≤ count`, so it posts `z ≥ c`.

[^xcount]: The binding posts `Count` with a constant value when `<count>` has
    one value, and `Among` when it has several; `apply_count_condition` then
    applies the condition to a fresh count variable. The parser pre-dispatches
    `atMost`, `atLeast`, `exactlyK` and `among` to their own callbacks, which
    post `Count` or `Among` over a count in `[0, k]`, `[k, |vars|]`, or pinned
    to `k` for `exactlyK` and `among`. `<count>` over variable
    values is not overridden, so it is the base class's `unsupported`.

[^xnv]: `nValues` posts `NValue` over a fresh count variable in `[1, |vars|]`.
    Over an empty list that domain is empty, where `NValue` of nothing is 0.
    Whether the parser can produce an empty list was not checked; see [Known
    limitations](#known-limitations).

[^mzngcc]: The `low_up` forms give each cover value a fresh count variable in
    `lbound[i]..ubound[i]` and reuse the counts form. The glue copies the cover
    before folding repeats out of it, because `arg_as_array_of_integer` hands
    back a pointer into the model's shared constant arrays.

[^xgcc]: `post_gcc` folds repeated cover values and posts `Equals` for each
    fold. `frontend-support-matrix.md` still says `cardinality` decomposes to
    `Count`; it has not since the binding started posting `GlobalCardinality`,
    and the matrix is being retired rather than updated.

`gcspy` binds `Count` (`post_count`), `GlobalCardinality` (with the closed
flag, folding repeats) and `NValue`. `Among` has no binding. Whether the CPMpy
side reaches any of them was not checked.

### Options

`Count`, `Among` and `NValue` have none.

**`GlobalCardinality::with_consistency()`** takes
`GlobalCardinalityConsistency = std::variant<consistency::BC, consistency::GAC>`,
which is the closed list. The default is `consistency::BC`, and no front end
changes it. `examples/frequency_square` takes `--consistency bc|gac`, defaulting
to `gac`, and is the only in-tree caller that asks for `GAC`, apart from
`scp_reader.cc` re-posting a `gac…` term, which posts the cover in the order
the term records.

- `consistency::BC` installs `propagate_bounds_global_cardinality`: the
  per-value rules (16–19) and the Hall interval rules over contiguous runs of
  the sorted cover (20–25).
- `consistency::GAC` installs `propagate_gac_global_cardinality`: rules 16 and
  17, then Régin's flow network (rules 26–30). It is arc consistent on `vars`
  **relative to the counts' bounds**, never their holes, because full GAC over
  count domains with holes is NP-hard (#413; the comment in
  `gac_global_cardinality_test.cc` says why, and that test checks `vars` at
  bounds consistency for that reason).

Neither tag is a policy, and the family offers neither `consistency::Auto` nor
`consistency::Dynamic`. The level changes the propagation and the proof strategy
and never the OPB model; the `.scp` term's name records it
(`boundsglobalcardinality`, `gacglobalcardinality`, each with a `closed` suffix
when closed), because `cake_pb_cp`'s parser and `scp_reader.cc` expect it.

**`GlobalCardinality::with_closed()`** does change the model. It adds one row per
variable (see [OPB encoding](#opb-encoding)) and installs a propagator of its
own. That is right: closed is a different constraint, not a strategy.

### Variable kinds and views

Every position of every class takes any `IntegerVariableID`: plain variables,
constants and views. The proof handles views, because every rule speaks in
`var == v`, `var != v`, bound and range literals, all of which a view has, and
the encodings name only `var == v` atoms and order atoms. The view lanes
`count_constraint_view_mixed`, `among_constraint_view_mixed` and
`n_value_constraint_view_mixed` post mixed views and verify their proofs.
`GlobalCardinality` has no view lane; this audit ran a differential with repeated
variables, offset views and negated views in the scope, against brute force, and
found nothing wrong. See [Tests](#tests).

A family whose facts are all `==`, `!=`, bounds and ranges is outside #882's view
problem by construction: every literal it states is one a view has.

### Reification

`None.` There is no reified form of any of the four. MiniZinc's `*_reif` forms
fall through to the standard library's decompositions, and none of the four is
listed with a reified binding in `minizinc/mznlib/`. Nobody has asked for one.

### Relation to other families

**Into this family.** The MiniZinc `count_*`, `at_least`, `at_most` and
`exactly` predicates decompose into `Count` plus a comparison. XCSP3's
`atMost`, `atLeast`, `exactlyK`, `among`, `count`, `nValues` and `cardinality`
all land here.

**Child constraints.** None. `GlobalCardinality` used to post an `In` per
variable for the closed restriction; since `76c8eeab` it emits the rows and runs
the propagator itself.

**Shared code.** `recover_am1` (`constraints/innards/`) is called by `Among`'s
root initialiser and by both `GlobalCardinality` arms' demand pols, and also by
`all_different`, `disjunctive`, `inverse`, `min_distance`, `sort` and
`subcircuit`. Its complementary-pair derivation exists because of this family
(#557). `NamesAndIDsTracker::need_constraint_saying_variable_takes_at_least_one_value_over_cover`
is used by `Among` and both GCC arms, as well as by `all_different`,
`bin_packing` and `min_distance`. `global_cardinality/justify.{hh,cc}` is shared
between the two GCC arms only.

**Presolvers.** None targets this family. `AutoTable` tabulates whatever
constraints sit over the variables its caller names, these included.

**Reached only through a decomposition?** No: every class has a direct binding
in both front ends.

**The candidate merge, settled: four classes, one document.** The family list
asked whether `among`, `count`, `global_cardinality` and `n_value` are one
family. As code, no, and the audit found no reason to merge them. Each has its
own encoding, which `cake_pb_cp` fixes for three of them, and no propagator is
shared. As a document, yes: they are four answers to one question, and the one
thing a reader most needs is how they relate.

**The wrapper question, and its answer.** Ciaran asked whether the specialised
three should become thin wrappers over `GlobalCardinality`, which was harder to
write and came later, or whether the specialised propagators earn their keep by
being faster. Measured on the corpus (see [CPU performance](#cpu-performance)):

- `Count` with a variable value of interest, `Among` over more than one value,
  and `NValue` are **not** `GlobalCardinality` without auxiliary variables and
  extra constraints. A wrapper would weaken each of them.
- **`Count` with a constant value is exactly a one-value open
  `GlobalCardinality`**, and exactly `Among` over one value. All three spellings
  give identical search trees, and the one-value GCC explores 1.4 to 3.7 times
  as many nodes in the same time on seven of nine `Count`-heavy models. It also
  writes about half the OPB and verifies in about 60% of the time on `roster`.
  **The specialised constraint is the slow one**.
- The decision is to **make `Count` fast** on the constant case (#1029), and
  **not** to route it to `GlobalCardinality` in a front end. Ciaran does not
  want the MiniZinc front end doing anything too clever, and a front-end
  rewrite is where #987's wrong answers hid.

Several models also post many constant `Count`s over one array — `league`
posts 34 over a 100-element array, `gfd-schedule` 50, `on-call-rostering` 10 per
array. That is a `GlobalCardinality` written out value by value, and it
forgoes the Hall reasoning a single GCC would do. Whether gathering them would pay
is not measured; see [Next steps](#next-steps).

## The proof model

### OPB encoding

All four encodings are **definitional**. `x=v` is the direct-encoding atom of
`x = v`, and `BinEnc(x)` the bit sum.

**`Count(X, Y, Z)`** is Encoding Procedure 3.7 of McIlree's thesis exactly, and
`cake_pb_cp`'s `count` encoding byte for byte:

```
for each position i:
    ge_i  ⇔  BinEnc(X_i) − BinEnc(Y) ≥ 0        flag x[id][i][ge], halves [r]/[f]
    le_i  ⇔  BinEnc(X_i) − BinEnc(Y) ≤ 0        flag x[id][i][le]
    eq_i  ⇔  ge_i + le_i ≥ 2                    flag x[id][i][eq]
Σ_i eq_i − BinEnc(Z) = 0                        labelled le / ge
```

That is `O(n)` rows, independent of any domain, and it is the same **whether or
not `Y` is a constant**. With a constant value of interest the three flags per
position restate what the `X_i = c` atom already says. That is why `Count`'s OPB
is 1.8 times the size of the other two spellings on `roster`. It is also why
#1029 can only fix the CPU side: the encoding is cake's.

**`Among(X, S, Z)`**:

```
Σ_i Σ_{v ∈ S} X_i=v  =  BinEnc(Z)                labelled le / ge
```

That is `n · |S|` terms in one row, with constants in `X` folded into the
right-hand side. It is linear in `|S|`, so a set given as a wide range costs a
wide row, and MiniZinc hands `fzn_among` its set as an explicit list.

**`NValue(Z, X)`** is Encoding Procedure 3.8, restricted: for each value `v`
in the union of the variables' **initial** domains,

```
w_v  ⇔  Σ_{i : v ∈ D(X_i)} X_i=v ≥ 1              flag v[id][v], halves [r]/[f]
Σ_v w_v − BinEnc(Z) = 0                            labelled le / ge
```

The thesis, and cake, sum over **every** `i` in the flag's definition. Ours sums
only over the variables whose initial domain holds `v`. That is #488, and it is
why `nvalue` is `none` rather than `strict` in the chain. It is **linear in the
width of the union of the domains**, which is #843: at widths `10³` and `10⁴`,
14,032 and 140,032 OPB rows.

**`GlobalCardinality(X, V, C)`**:

```
for each cover index j:
    Σ_i X_i=V_j  =  BinEnc(C_j)                    labelled <j>_le / <j>_ge
if closed, for each position i:
    Σ_{j : X_i=V_j not literally false} X_i=V_j ≥ 1        labelled <i>_al1
```

That is `O(n · m)` terms, independent of any width. A closed variable whose
domain misses the cover gets the row `0 ≥ 1`, deliberately: the constraint is
then unsatisfiable, and saying so in the model is better than leaving a
propagator to discover it. The level never changes the encoding.

### Labels

The labels are cake's, and matter to `opbdiff`'s label matching. The propagators
do not refer to them; they reach the rows by the `ProofLine` numbers the model
hands back.

| Rows | Labels | Used by |
|---|---|---|
| `Count`'s flag definitions and sum | `x[id][i][ge\|le\|eq]` with `[r]`/`[f]` halves; `c[id][le]`, `c[id][ge]` | nothing reads them by line; rules 1–8 reach the flags as literals and the sum by RUP |
| `Among`'s sum | `c[id][le]`, `c[id][ge]` | rules 9–12, by line number (`_sum_line`) |
| `NValue`'s flags and sum | `v[id][v]` with `[r]`/`[f]` halves; `c[id][le]`, `c[id][ge]` | nothing; rules 13 and 14 are bare RUPs |
| `GlobalCardinality`'s count rows | `c[id][<j>_le]`, `c[id][<j>_ge]` | rules 20, 21, 23, 25 and 26–30, by line number (`_count_lines`) |
| `GlobalCardinality`'s closed rows | `c[id][<i>_al1]` | rule 15, by RUP; nothing reads the line number |

With the cover sorted in the constructor (#1030), `<j>` is the position in the
**sorted** cover under both arms. At `347e2f8c` that is so under `BC` only; at
`GAC` it is the posted order. The two agree with cake either way, because cake
rebuilds from the `.scp`, which is written from the same object.

### Cake conformity

| Case | Chain | `opbdiff` | Why not `strict` |
|---|---|---|---|
| `count_sat`, `count_unsat` | full workflow 2 | `strict` | — |
| `among_sat`, `among_unsat` | full workflow 2 | `none` | the eq-literal encoding gap (#358), shared with `element` and `table` |
| `nvalue_sat`, `nvalue_unsat`, `nvalue_neg_sat` | full workflow 2 | `none` | #358, and the occurrence-row membership of #488 |
| `global_cardinality_{sat,unsat,closed_sat,closed_unsat}` | full workflow 2 | `none` | #358 |
| `global_cardinality_gac_{sat,unsat,closed_sat}` | full workflow 2 | `none` | #358 |

All 14 report `OK: full workflow-2 chain passed` at `347e2f8c`, with
`cake_pb_cp` and `opbdiff` on the path. #488 is the one real divergence rather
than a shared gap. It shows up as elaboration failures on about 4 in 43
`n_value_test` instances per seed (measured in #488, not re-measured here),
none of them among the curated cases. There is no `gac_closed_unsat` case. Every
case posts its cover ascending, so the chain never saw #1026.

### Proof-time state

- **`Count`**: all state is in the OPB (the three flags per position). Every
  justification line is `ProofLevel::Temporary`. Nothing is emitted at the root.
- **`Among`**: when a proof is being logged at `AssertionLevel::Off` and
  `|S| > 1`, a root initialiser derives, **for every variable**, an at-most-one
  over its `X_i=v` atoms for `v ∈ S`. It uses `recover_am1` at
  `ProofLevel::Top`, built from `C(|S|, 2)` pairwise RUPs at `Temporary`,
  **each preceded by a proof comment** (`among am1 recover follows`). The lines
  are identified by number only, in a `map<IntegerVariableID, ProofLine>` the
  propagator holds; nothing names or labels them. They are never deleted.
  Rules 10 and 12 add them into their `pol`s. At any other assertion level
  nothing is emitted and the map stays empty, which is safe only because rules
  10 and 12 then emit no steps either.
- **`NValue`**: all in the OPB. The two rules are bare RUPs.
- **`GlobalCardinality`**: the OPB rows, plus the names-and-IDs tracker's
  at-least-ones "over a cover", which are cached and emitted at `Top` the first
  time any family asks for them (see `all_different.md`'s preamble). Every Hall
  and flow justification builds its at-most-ones afresh, at `Temporary`, from
  pairwise RUPs (`recover_am1`); nothing is cached across firings. That is the
  per-value pairwise cost #944 describes, and it is most of the `GAC` arm's
  proof ([Proof performance](#proof-performance)).
- **Proof-only vectors**: `Count::_flags`, `Among::_sum_line` and
  `GlobalCardinality::_count_lines` are filled by `define_proof_model`, which
  does not run with proofs off. They are read only inside justifications, which
  do not run then either. `NValue::_possible_values` is the other way round: it
  is built in `prepare()`, which **does** run with proofs off, value by value
  over every domain, but only `define_proof_model` reads it.
- **Justifications read `state`**, not the reason, in every explicit rule of
  `Count`, `Among` and both GCC arms. They ask `state.in_domain`,
  `state.domains_intersect` and `state.bounds` which values each variable still
  has. That is safe for the reason `all_different.md` gives: at
  `AssertionLevel::Off` the steps are emitted before any literal of the
  inference is applied, and at every other level no steps are emitted. It would
  stop being safe in a mode that re-emitted justifications later. The reasons
  here do state everything the justifications read, so the fix, if one is ever
  needed, is the one #885 made in `equals`.

## The implementation

### Initialisation and global data

- **`Count`**: builds the whole-scope `generic_reason` once, at install time, and
  shares it across calls.
- **`Among`**: sorts and de-duplicates `S` in the constructor, and builds its
  interval set once at install. The root initialiser is described under
  [Proof-time state](#proof-time-state). It costs `n · C(|S|, 2)` pairwise lines
  plus as many comments, whether or not rules 10 or 12 ever fire. **Measured**,
  with three variables over `[0, W]`, `S = [1, W − 1]` and the count pinned at 3,
  to the first solution (4 search nodes):

  | `\|S\|` | OPB rows | proof lines | proof size |
  |---|---|---|---|
  | 10 | 138 | 510 | 18 kB |
  | 100 | 1,218 | 31,020 | 1.2 MB |
  | 1,000 | 12,018 | **3,009,120** | **120 MB**; VeriPB 4 min 30 s |

  That is `3 · C(|S|, 2)` lines, doubled by the comments. With proofs off every
  row is microseconds. No large-domain row varies `|S|`; see [Interval
  efficiency](#interval-efficiency).
- **`NValue`**: `prepare()` walks every value of every variable into a
  `map<Integer, list<IntegerVariableID>>`, for the encoding only (see above).
  With proofs off that is wasted work, and it is per value. It is the "H2 in
  prepare" half of the `NValue` row's `KnownTrip`.
- **`GlobalCardinality`**: validates and (since #1030) sorts the cover. With
  `with_closed()` it builds the cover's interval set once for the closed
  propagator. The `GAC` arm allocates one opaque scratch object per installed
  propagator; see [Mutable state](#mutable-state-and-incrementality).

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| `Count` | `on_change`: `vars`, `y`, `n` | derived, but `n` overstated when `y` is a constant | 1–8 | always | not claimed | no |
| `Among` | `on_change`: `vars`; `on_bounds`: `n` | derived | 9–12 | always | not claimed | yes, once every variable is decided |
| `Among` root initialiser | — | — | scaffolding for 10, 12 | proofs at `AssertionLevel::Off` and `\|S\| > 1` | — | — |
| `NValue` | `on_change`: `vars`; `on_bounds`: `n` | derived | 13, 14 | always | not claimed | no |
| GCC closed | `on_change`: `vars` | derived | 15 | `with_closed()` | not claimed | no |
| GCC bounds | `on_change`: `vars`; `on_bounds`: `counts` | derived | 16–25 | `consistency::BC` (the default) | not claimed | no |
| GCC flow | `on_change`: `vars`; `on_bounds`: `counts` | derived | 16, 17, 26–30 | `consistency::GAC` | not claimed | no |

**Self-disabling.** `Count` returns `DisableUntilBacktrack` only on its
failure exits: a `_or_stop` inference that emptied a domain, or the per-value
loop's `stop`. It never disables itself on success. `Among` disables itself
until backtrack after rule 11 or rule 12. Either leaves every variable decided
and the count fixed, so nothing can wake it usefully until something is undone.

**Idempotence.** None of the seven claims it. The closed propagator's comment
calls it idempotent ("once a domain is inside the cover it stays there"), and it
is, but it returns `Enable`, not `EnableButIdempotent`. So the claim is not made
to the engine, and `GCS_CHECK_IDEMPOTENT_CLAIMS` does not check it. The others
genuinely are not: `Count`'s array pruning (rule 8) can fix variables that rule
2 then counts on the next call.

**Holes affect**, beyond "derived":

- **`Count`'s `n` is watched `on_change`** since #966, because with a
  *variable* `y`, a hole in `n` can leave a value of `y` without support. With a
  **constant** `y` it cannot. The counts that support `X_i = c` and `X_i ≠ c`
  are the intervals `[must + 1, might]` and `[must, might − 1]`. Once rules 1
  and 2 have clipped `n` to `[must, might]`, any two values left in its domain
  support both, and one value is a bound. So for the constant case, the shape
  the corpus uses, the column overstates `n`'s sensitivity. That is never
  unsound. It keeps somebody else's optional pruning on `n` alive for no gain,
  and wakes `Count` for nothing (#1029).
- **`Among`'s and `NValue`'s `n` and GCC's `counts` are `on_bounds`**, which is
  the truth. `Among` counts membership in a fixed set, so its count's supports
  are intervals, as for constant `Count`. `NValue` reads only `n`'s bounds.
  Both GCC arms read only `state.bounds(counts[j])`: the flow's capacities are
  the count bounds, and #413 is why that is deliberate.
- **Every propagator's `vars` are `on_change`**, and every one of them reads
  the variables' holes: which values are still there is the whole content of
  counting.

### Mutable state and incrementality

**Backtrackable**: none, in any of the four.

**Not backtrackable, and deliberately so**:

- the `GAC` arm's `GacGlobalCardinalityScratch`: the Dinic network, the
  original-edge and flow records, the flat `m × n` assignment-edge index, the
  residual graph, Tarjan's state and the reachability buffers. All of it is
  `clear()`ed or `assign()`ed at its point of use, so capacity ratchets up to the
  largest wake (`55783337`, the same change that introduced #1026's binary
  search).
- `Among`'s at-most-one line map, written once at the root.

**Recomputed per call, and what maintaining it would buy.**

- **`GlobalCardinality`'s flow** is rebuilt from nothing every call. There is no
  persistent flow the way `AllDifferent` keeps its matching (#526). Keeping one
  and repairing it is the textbook incremental form. Nobody has measured what it
  would buy.
- **The bounds arm's Hall search** recomputes every contiguous pair's capacity,
  demand and confined/potential sets every call: `O(m²)` pairs × `n` variables ×
  up to `|H|` membership tests. That is the whole of #1028's cost. An
  incremental form is not the obvious fix. A real bounds-consistent GCC
  algorithm (Quimper et al., 2003) is linear once the variables are sorted by
  their bounds.
- **`Count`** recounts `must` and `might` from scratch per value of `y`, and
  walks the array up to four times per call (#1029).
- **`Among`** copies and partitions its whole scope, and **materialises a
  whole-scope reason**, on every call. The reason is not guarded on
  `want_reasons()`, so this happens with proofs off too. On `ptv`, with its
  arrays of 750–1,050 variables, `perf` puts `materialise_generic` at 12.5% and
  `memmove` at 10.7% of the run. Two copies could account for the second: the
  scope, to partition it, and the materialised reason, which is copied again
  into `vars_and_bounds_reason`. The profile does not separate them. (These
  runs posted each constant `Count` as `Among` by the local switch; `Among`
  itself is in no corpus model.)
- **`NValue`** rebuilds a `std::set` of every value of every domain every call,
  to take its size. On `gfd-schedule` 2015 and 2022 that is 31% and 42% of
  propagation time, from 0.4% and 0.9% of the calls.

### Interior values and optional pruning

**What this family offers:** `None.` No class installs an
optional-interior-pruning pair, and no class accepts `consistency::Auto`. The
nearest thing is `GlobalCardinality`'s two arms, whose differences go well
beyond interiors, so a pair would not keep the first promise anyway.

**What this family observes.** Every propagator reads its `vars`' interiors,
because deciding whether a variable can take a value is what counting is. So all
of them keep other constraints' optional pruning on their array variables alive,
correctly. The counts are the interesting half:

- **`Among`'s, `NValue`'s and both GCC arms' count variables** are
  **bounds-only**, stated in those words: holes in them change nothing any of
  those propagators infers. They are also declared that way, so a neighbour's
  optional pruning on a count variable can be dropped when nothing else reads
  its interior.
- **`Count`'s `n`** is declared hole-sensitive, and is so only when `y` is a
  variable. For a constant `y` the declaration overstates. The fix is part of
  #1029: watch `n` `on_bounds` when `y` is a constant. It is not a correctness
  question, and nothing measured here says how often it matters.
- **`Count`'s `y`** is hole-sensitive for real. A value of `y` is supported
  only if its achievable count range meets `n`'s domain, per value (rule 5).

### Robustness and limits

- **Unbounded domains.** No class restricts domain width. What width costs is
  under [Interval efficiency](#interval-efficiency). `NValue` is unusable on a
  wide domain even with proofs off, and so is a wide `y` in `Count`.
- **Negative values and zero.** Nothing in the family special-cases either.
  `GlobalCardinality`'s covers spanning zero broke the demand pol once (#557),
  through a `{0, 1}` variable's bit-aliased atoms. `recover_am1`'s
  complementary-pair derivation fixed that, and both GCC tests carry rows for it.
  `nvalue_neg_sat` covers negative labels in the chain.
- **Degenerate shapes.**
  - Empty arrays: all four handle them. #254's rows test them for `Count`,
    `Among` and both GCC arms, and `NValue`'s boundary rows do the same.
  - A single variable, a constant in the array: tested in all four.
  - Aliasing. A repeated variable in the array is tested for `Count`, `Among`
    and `NValue` (`run_dup_*_test`), and the count variable inside the array for
    `Count` and `Among` (`run_count_result_in_array_test`,
    `run_self_ref_among_test`), not `NValue`. **The value
    of interest inside `Count`'s own array is not**: a differential for this
    audit (value of interest, an offset view of it, or its negation, among the
    array; 3,000 instances against brute force, 300 with VeriPB) found nothing
    wrong. **`GlobalCardinality` over repeated variables or views** is not tested
    either: 6,000 instances against brute force under both arms, open and
    closed, and 600 with VeriPB, found nothing wrong.
  - An unsorted cover at `GAC`: wrong answers, #1026, fixed by #1030.
  - A repeated cover value is rejected by the constructor (#922), and every
    front end folds repeats first.
- **Overflow.** Counts are bounded by `|vars|` and summed as `Integer`.
  `GlobalCardinality`'s `cap` and `demand` sum up to `m` count bounds, which a
  user can make arbitrarily large (`[0, 10¹⁸]` counts, say). Those sums are
  checked `Integer` arithmetic and throw on overflow rather than wrap. The `GAC`
  arm puts `c_hi.raw_value` straight into a `long long` capacity, and computes
  `need` as a sum of excesses. With several huge count upper bounds that sum
  could exceed `2⁶³`. Not probed; the realistic bound is `n`, and clipping the
  capacities to `n` would remove the question.
- **The two `UnexpectedException`s in `Among`** ("something's wrong,
  at_least_how_many != at_most_how_many") are sound invariants, not bugs
  waiting to fire. By the time they are read, rules 9 and 10 have clipped `n`
  to `[must, n − must_not]`, so `must = ub` forces `lb = ub`, and so does
  `must + either = lb`.

### Interval efficiency

The four classes answer this very differently, so each question is answered per
class.

**1. The propagation side.**

- **`Count`** walks `y`'s values: `each_value_mutable(value_of_interest)`, and
  per value a pass over the array. That is a genuine per-value support scan (a
  value of `y` is supported or not on its own count range), with no weaker arm
  behind it. It is the `Count` row's `KnownTrip` (H1c). For a constant `y` it is
  one value. Everything else is interval-level: `domains_intersect`, the
  `some_count_between` hole test by `domain_intersects_with`, and rule 8's
  `contains_all_of` and `each_interval_minus`.
- **`Among`** reaches for `State`'s per-value iterators **nowhere at all**,
  which can be checked by reading `among.cc`. Its partition asks each domain
  `domain_intersects_with(S)` and `domain_is_subset_of(S)`. Rule 11 lists one
  literal per value of `S`, which is bounded by `S`. Rule 12 removes the
  complement of `S` as ranges.
- **`NValue`** is per value throughout: `prepare()`, the per-call `std::set`
  over every domain, and the encoding. It is the `NValue` row's `KnownTrip`
  (H2 and H2′, #843). Rule 13 needs the size of the union of the domains, which
  an interval union gives directly; nothing needs the values one by one.
- **GCC closed** removes each variable's non-cover runs by `each_interval_minus`
  against the cover's interval set (#877). `Clean`.
- **GCC bounds.** Part 1 asks `in_domain` per cover value per variable, bounded
  by the cover. Rule 19 removes everything but the value as ranges, one more
  than the domain has intervals (#860). Part 2's `domain_subset_of_hall` walks a domain with an early exit at
  the first value outside the Hall set, so it is bounded by `|H| + 1`. **Rule
  25 is not bounded**: `for (val : each_value_mutable(var)) if (! hall_contains(val)) infer(var != val)`
  removes a potential variable's non-Hall values **one at a time over its whole
  domain**. That is the `GlobalCardinality/hall` row's `KnownTrip`. Its
  justification names the removed value, which is why #860 left it.
- **GCC flow** (#876). The dummy-edge test, the Hall-subset test and the SCC
  path's subset test are early-exit walks bounded by the cover. **Rule 30 is not
  bounded**: it removes a variable's non-cover values one at a time over its
  whole domain, which is the same shape as rule 25.

**2. The reason side.**

| Class | Reason | Literals per | Finding the runs | Guarded on `want_reasons()` |
|---|---|---|---|---|
| `Count` | whole-scope `generic_reason`, built once | run (#935) | per run | lazy: materialised only when read |
| `Among` | `eager_reason(generic_reason(vars))` **every call**, plus `n`'s bounds | run | per run | **no**: built on every call, with proofs off too |
| `NValue` | whole-scope `generic_reason`, built once | run | per run | lazy |
| GCC closed | `NoReason` | — | — | — |
| GCC per value (16–19) | `var == v` / `var != v` per variable, gathered only when the rule fires | variable | — | by construction: only on firing |
| GCC Hall and flow, capacity | per confined variable, its bounds plus one range per gap between consecutive Hall values (#936); the cut values' count upper bounds | run | per Hall gap, `O(\|H\|)` | lazy (`LazyReasonOver`) |
| GCC Hall and flow, demand | `var != v` for every non-potential variable and every Hall value; the cut values' count lower bounds | **value**, bounded by the Hall set | per value, bounded | lazy |

`Among`'s unguarded eager reason is the one hazard on the propagation path. It is
a per-call cost proportional to the scope's runs, paid whether anyone reads it or
not ([Mutable state](#mutable-state-and-incrementality) has the `ptv` profile).

**3. The proof side.** No class picks its form by a width gate, and no class
picks by a variable's kind either.

- **`Count`**'s justifications are per value of `y`'s domain. Rule 1 writes
  `|D(y)| + 1` lines per variable that cannot meet `y`, and rules 6 and 7 write
  per value, and rule 7 per value and variable. Rule 7 finds its runs by
  `each_interval_minus`, then expands them value by value. For a constant `y`
  all of this is one value.
- **`Among`**: the root initialiser is `n · C(|S|, 2)` lines, in values of
  `S`. Per firing, rule 9's at-least-ones name only the values of `S` each
  variable still has, and rule 12 writes one line per value of `S` per removed
  run. Nothing is per value of a domain.
- **`NValue`**: two bare RUPs; the width cost is in the encoding.
- **GCC**: the at-least-ones name the Hall values a variable still has (#939's
  per-firing cover). The at-most-ones are `recover_am1` over the Hall set per
  potential variable, `C(|H|, 2)` pairwise lines each: in cover values, never
  domain width, but quadratic, and rebuilt every firing (#944). Rules 25 and 30
  write one justification per removed value, because the pruning is per value.

**4. Where the family stands in the audit lane** (`gcs/large_domain_audit_test.cc`
at `347e2f8c`):

| Row | Outcome | What it reaches |
|---|---|---|
| `Among` | `Clean` | rule 12, both sides of `S` |
| `Among/holey` | `Clean` | the per-call reason over holey wide domains (#935) |
| `Count` | `KnownTrip` | the per-value scan over a wide `y` (H1c) |
| `NValue` | `KnownTrip` | `prepare()` and the encoding (H2, H2′) |
| `GlobalCardinality` | `Clean` | rule 19's range removal |
| `GlobalCardinality/hall` | `KnownTrip` | rule 25's per-value removal |
| `GlobalCardinality/closed` | `Clean` | rule 15 |

And in `"Large domain proof sizes"`: `GlobalCardinality/confined` and
`Among/confined`, each at most 2,000 proof lines at width `10⁴`.

**Which axes those rows do not vary:**

- **The `GAC` arm, at all** (#876). Every GCC row posts the default `BC`.
  #876's own measurement shows both of its unbounded sites trip at once.
- **`|S|` for `Among`, and `m` for GCC.** `Among`'s rows post two values; the
  GCC rows post one (`GlobalCardinality`, `/closed`) or two (`/hall`). Neither is
  a width axis in the template's sense, but both are where this family's real
  costs are. `Among`'s root proof is quadratic in `|S|` (the table under
  [Initialisation](#initialisation-and-global-data)). The bounds arm's per-call
  CPU is at least quartic in `m` when `n ≈ m` (#1028: 0.38 s at `m = 40`, 275 s
  at `m = 160`, root to first solution, proofs off). A lane that pins proof
  lines or node throughput against these would catch both. Neither exists.
- **A constant `y` for `Count`.** The row uses `v[0]` as `y`, so it probes the
  variable-`y` path only. The constant path has no per-value site.
- **With proofs on, `Count`** has no proof-size row. Its justifications are per
  value of `y`, so a wide `y` would show it; the `KnownTrip` fires first anyway.

## Inference catalogue

Thirty rules: eight for `Count`, four for `Among`, two for `NValue`, and sixteen
for `GlobalCardinality`. Of GCC's, rule 15 is the closed restriction, 16 and 17
are shared by both arms, 18–25 belong to the bounds arm and 26–30 to the flow
arm. Two of them, 22 and 24, are dead code. They are catalogued anyway, because
the code is there and someone will read it.

Five facts hold across them and are not repeated per entry.

**The wire inventory is four forms, one per class, and all of them bare.**

| Wire form | Hint type | Rules |
|---|---|---|
| `count:((constraint_id N))` | `hints::Count` | 1–8 |
| `among:((constraint_id N))` | `hints::Among` | 9–12 |
| `nvalue:((constraint_id N))` | `hints::NValue` | 13, 14 |
| `global_cardinality:((constraint_id N))` | `hints::GlobalCardinality` | 15–30 |

Each hint carries only `originator` (`ConstraintID`). **No subhint
distinguishes rules**, so a reconstructor has to tell them apart from the
asserted clause's shape and from the constraint's `.scp` term. That can be done
within a class: a bound on the count, a value removed from `y`, and a value
removed from an array variable are different shapes. It cannot always be done
between rules of the same shape. Rules 1 and 7 both bound `n` from above, and
rules 18, 23, 25, 28, 29 and 30 all remove a value from an array variable. This is
recorded, not raised as an issue: whether a reconstructor needs a subhint is
for the justifier implementation to find out, as with
[`element`](element.md)'s rules 1–4 and 6, which share one bare wire form too.

**What licenses them.** The thesis gives the encodings of `Count` and `NValue`
(Encoding Procedures 3.7 and 3.8), and justification procedures for none of the
four. So:

- rules 2, 4, 13–19 are single RUPs against the encoding (rule 15 against
  the closed row, 18 and 19 against a count row);
- `Count`'s explicit rules (1, 3, 5–8) are **ours**, argued in each entry;
- `Among`'s `pol`s (9–12) are ours, built from the sum row, at-least-ones
  (Theorem 3.2's shape) and at-most-ones recovered by Theorem 2.3;
- the GCC Hall and flow rules (20–30) generalise **JP 3.16 and 3.17** from a
  matching to a flow with capacities. The sum is the same shape, one at-least-one
  per confined variable (capacity side) or one at-most-one per potential
  variable (demand side), added to the count rows of the cut values. Each count
  row is resolved against the count's bound (`add_for_literal`) so that its bits
  cancel. The capacity/demand duality and the bound resolution are ours; there
  is no published procedure for a GCC cut.

**Justifications read `state`**, in every explicit rule. See [Proof-time
state](#proof-time-state) for why that is safe today and when it would stop
being.

**No mutation lane exists in this family**, so every rule's **Tightness** is
`Not shown.`. Per the template's policy that is an ordinary state.

**Propagator-level strength**, as the tests check it (see [Tests](#tests) for
the harness's levels): `Count` is `GAC` on `y` and the array and `bounds(Z)` on
`n`; `Among` is `GAC` on everything; `NValue` is checked by no test; the GCC
bounds arm is `bounds(Z)` on the array and the counts; the GCC flow arm is
`GAC` on the array **relative to the counts' bounds** by construction, but its
test checks the array only at `bounds(Z)`, and the counts not at all. Each rule's **Strength** is what that rule contributes.

### Rule: count-upper-by-candidates

(Rule 1.)

- **Infers** — `n < |vars| − k + 1`, where `k` is the number of variables whose
  domain does not meet `y`'s.
- **Fires when** — every `Count` call; changes something when a variable has
  lost its last value in common with `y`.
- **Strength** — `partial`: an upper bound on `n` that ignores which value `y`
  takes.
- **Algorithm** — one pass, `domains_intersect(y, var)` per variable: `O(n)`
  intersections, each in intervals.
- **Why it is true** — a variable whose domain shares nothing with `y`'s cannot
  equal `y`, so it contributes nothing to the count.
- **Proof technique** — `RUP sequence`, ours. For each such variable, and for
  each value `v` of `y`, `y ≠ v ∨ ¬eq_i` under the reason; then `¬eq_i` under the
  reason. The final RUP against the sum row concludes.
- **Reason** — the whole scope's `generic_reason`: every variable's domain,
  `y`'s and `n`'s. Not minimal: only the non-meeting variables' domains and
  `y`'s are needed. Per run; lazy.
- **Assertion** — `n ≤ |vars| − k ∨ ¬reason`.
- **Hint** — `hints::Count`: `originator`.
- **Offline reconstructibility** — `hinted`. The variables to zero are exactly
  those whose domain in the reason misses `y`'s domain in the reason.
- **Proof size** — `k · (|D(y)| + 1)` lines, then one RUP. In **values of
  `y`**; one value when `y` is a constant.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: count-lower-by-fixed

(Rule 2.)

- **Infers** — `n ≥ f`, where `y` is fixed to `c` and `f` variables are fixed
  to `c`; with `y` unfixed, `n ≥ 0`, which changes something only when `n`'s
  domain reaches below zero.
- **Fires when** — every call; changes something once `y` is fixed and more
  variables are fixed to it than `n`'s lower bound says.
- **Strength** — `partial`.
- **Algorithm** — one pass of `optional_single_value` over the array, only when
  `y` is fixed.
- **Why it is true** — each variable fixed to `y`'s value is one occurrence.
- **Proof technique** — `RUP`: the fixed variables' `eq_i` flags propagate from
  the encoding, and the sum row gives the bound.
- **Reason** — the whole-scope `generic_reason`. Not minimal.
- **Assertion** — `n ≥ f ∨ ¬reason`.
- **Hint** — `hints::Count`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: count-value-too-few-candidates

(Rule 3.)

- **Infers** — `y ≠ v`, for a value `v` of `y` that fewer variables can take
  than `n`'s lower bound needs.
- **Fires when** — the per-value loop over `y`'s domain finds
  `might(v) < lb(n)`.
- **Strength** — `partial`; with rules 4 and 5, `GAC` on `y` relative to `n`.
- **Algorithm** — per value of `y`, one pass over the array counting `must`
  (fixed to `v`) and `might` (can be `v`): `O(|D(y)| · n)` membership tests.
- **Why it is true** — if `y = v`, the count is at most `might(v)`, which is
  below every value `n` can take.
- **Proof technique** — `RUP sequence`, ours. Per variable that cannot be `v`:
  `y ≠ v ∨ X_i ≠ v ∨ eq_i` (a plain RUP, not under the reason), then
  `y ≠ v ∨ ¬eq_i` under the reason. The final RUP against the sum row concludes.
- **Reason** — the whole-scope `generic_reason`.
- **Assertion** — `y ≠ v ∨ ¬reason`.
- **Hint** — `hints::Count`.
- **Offline reconstructibility** — `hinted`: the variables to zero are those
  whose domain in the reason lacks `v`.
- **Proof size** — two lines per variable lacking `v`, then one.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: count-value-too-many-fixed

(Rule 4.)

- **Infers** — `y ≠ v`, for a value `v` to which more variables are already
  fixed than `n` allows.
- **Fires when** — the per-value loop finds `must(v) > ub(n)`.
- **Strength** — `partial`, as rule 3.
- **Algorithm** — as rule 3.
- **Why it is true** — if `y = v`, the count is at least `must(v)`, above every
  value `n` can take.
- **Proof technique** — `RUP`: the fixed variables' `eq_i` flags propagate once
  `y = v` is assumed.
- **Reason** — the whole-scope `generic_reason`.
- **Assertion** — `y ≠ v ∨ ¬reason`.
- **Hint** — `hints::Count`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: count-value-count-in-hole

(Rule 5, #966.)

- **Infers** — `y ≠ v`, where the counts achievable with `y = v`,
  `[must(v), might(v)]`, all fall in a hole of `n`'s domain.
- **Fires when** — the per-value loop finds neither of rules 3 and 4 applies,
  but `some_count_between(must, might)` is false.
- **Strength** — `partial`; it is what makes rules 3–5 `GAC` on `y` rather than
  bounds-relative on `n`.
- **Algorithm** — the rule 3 pass, plus `in_domain` at each end of the range and
  one `domain_intersects_with` for its interior.
- **Why it is true** — every count between `must` and `might` is achievable by
  switching candidates one at a time, and none of them is a value `n` can take.
- **Proof technique** — `RUP sequence`, ours. It derives both conditional bounds
  under the reason — `y = v ⇒ n ≤ might`, by zeroing the flags of the variables
  lacking `v` as in rule 3, and `y = v ⇒ n ≥ must` — and then `y ≠ v` follows,
  because the reason excludes the whole interval from `n`.
- **Reason** — the whole-scope `generic_reason`, which carries `n`'s holes.
- **Assertion** — `y ≠ v ∨ ¬reason`.
- **Hint** — `hints::Count`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — two lines per variable lacking `v`, plus two.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` The test reaches it (16 firings at seed 1); no
  corpus model does.

### Rule: count-lower-over-values

(Rule 6.)

- **Infers** — `n ≥ min over surviving v of must(v)`.
- **Fires when** — after the per-value loop, when that minimum exceeds `lb(n)`.
- **Strength** — `partial`: part of `bounds(Z)` on `n`.
- **Algorithm** — the minimum is gathered in the rule 3 pass.
- **Why it is true** — whichever value `y` takes, at least `must` of that
  value's variables are already fixed to it.
- **Proof technique** — `RUP sequence`, ours: per value `v` of `y`,
  `y ≠ v ∨ n ≥ lowest` under the reason, each RUP from the fixed variables'
  flags; then the conclusion by RUP over `y`'s domain.
- **Reason** — the whole-scope `generic_reason`.
- **Assertion** — `n ≥ lowest ∨ ¬reason`.
- **Hint** — `hints::Count`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — `|D(y)|` lines, then one. In values of `y`.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: count-upper-over-values

(Rule 7.)

- **Infers** — `n ≤ max over surviving v of might(v)`.
- **Fires when** — after the loop, when that maximum is below `ub(n)`.
- **Strength** — `partial`: part of `bounds(Z)` on `n`.
- **Algorithm** — the maximum is gathered in the rule 3 pass. The
  justification finds, per variable, the values of `y` it lacks by
  `each_interval_minus`, then walks those runs value by value.
- **Why it is true** — whichever value `y` takes, at most `might` variables can
  equal it.
- **Proof technique** — `RUP sequence`, ours. For each `(v, X_i)` with
  `v ∈ D(y) \ D(X_i)`: `y ≠ v ∨ ¬eq_i` and `y ≠ v ∨ X_i ≠ v` under the reason.
  Then per `v`, `y ≠ v ∨ n ≤ highest`, then the conclusion.
- **Reason** — the whole-scope `generic_reason`.
- **Assertion** — `n ≤ highest ∨ ¬reason`.
- **Hint** — `hints::Count`.
- **Offline reconstructibility** — `hinted`. Same shape as rule 1's assertion:
  a reconstructor holding only the clause cannot tell which of the two ran, but
  either derivation works for either conclusion when it is true.
- **Proof size** — two lines per `(value of y, variable lacking it)`, plus one
  per value of `y`. In values; `O(|D(y)| · n)` worst case.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: count-array

(Rule 8, #996.)

- **Infers** — on unfixed array variables whose domain contains all of
  `D(y)`: remove `w`, the one surviving value of `y` that does not take every
  candidate; or remove every value outside `D(y)` (as ranges, the gaps between
  `y`'s values); or, with `y` fixed and `n` at its maximum, fix them to `y`'s
  value. (With `y` fixed, the domain condition is just that the variable can
  take `y`'s value.)
- **Fires when** — after the per-value loop, when no surviving value of `y`
  leaves room below its maximum count (every one "takes every candidate"), or
  exactly one does and it leaves no room above its minimum.
- **Strength** — `partial`; with rules 3–5 it gives `GAC` on the array, which
  is what #996 was.
- **Algorithm** — one more pass over the unfixed variables: per variable,
  `contains_all_of(D(y))`, then `each_interval_minus` for the gaps. In
  intervals.
- **Why it is true** — for `y = v`, a variable that can be `v` but is unfixed
  is supported at `v` iff `n` allows a count above `must(v)`, and at other
  values iff `n` allows one below `might(v)`. The two cases above are exactly
  where one side has no support for any `v`.
- **Proof technique** — `RUP sequence`, ours, emitted once for the whole batch
  (`infer_all`). Per value `v` of `y`, and per pruning: the conditional count
  bounds `y ≠ v ∨ pruned ∨ n ≤ count_hi` and `… ∨ n ≥ count_lo`, when the count
  falls in a hole rather than off an end, after zeroing the flags of the
  variables lacking `v`; then, with `y` unfixed, `y ≠ v ∨ pruned`. The pruning
  is then RUP over `y`'s domain.
- **Reason** — the whole-scope `generic_reason`.
- **Assertion** — one per pruned literal: `X_i ≠ c`, `X_i ∉ [lo, hi]` or
  `X_i = c`, each `∨ ¬reason`.
- **Hint** — `hints::Count`.
- **Offline reconstructibility** — `hinted`. Each assertion carries its own
  reason; the batching is an optimisation.
- **Proof size** — per value of `y`, per pruning, up to three lines, plus the
  flag zeroing once per value. `O(|D(y)| · (n + prunings))`.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: among-lower

(Rule 9.)

- **Infers** — `n ≥ k`, where `k` variables have domains inside `S`.
- **Fires when** — every `Among` call; changes something when a variable has
  just lost its last value outside `S`.
- **Strength** — `partial`; with rule 10, `GAC` on `n` (its supports are an
  interval, so bounds are enough).
- **Algorithm** — the scope is copied and partitioned into must-not-match,
  must-match and can-be-either by `domain_intersects_with(S)` and
  `domain_is_subset_of(S)`: `O(n)` interval questions.
- **Why it is true** — each variable confined to `S` contributes one.
- **Proof technique** — `pol` then `RUP`, ours: the `sum ≤ n` half plus, per
  must-match variable that is not a constant, the tracker's at-least-one naming
  the values of `S` it still has. After the reason zeroes the rest, the sum
  collapses to `n ≥ k`. The comment says why the scaffolding is needed: RUP
  cannot re-derive an at-least-one over `S` from the bit encoding once a domain
  is wider than one value.
- **Reason** — `eager_reason(generic_reason(vars))`: every array variable's
  domain, materialised **every call**. Not minimal: only the must-match
  variables' domains are needed.
- **Assertion** — `n ≥ k ∨ ¬reason`.
- **Hint** — `hints::Among`.
- **Offline reconstructibility** — `hinted`: the must-match variables are those
  whose domain in the reason lies inside `S`, which the `.scp` gives.
- **Proof size** — one `pol` over `1 + k` rows, one RUP; the at-least-ones are
  cached by the tracker.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: among-upper

(Rule 10.)

- **Infers** — `n ≤ |vars| − j`, where `j` variables miss `S` entirely.
- **Fires when** — every call; changes something when a variable has just lost
  its last value in `S`.
- **Strength** — `partial`; see rule 9.
- **Algorithm** — the rule 9 partition.
- **Why it is true** — each variable that cannot be in `S` contributes nothing,
  and each of the others contributes at most one.
- **Proof technique** — `pol` then `RUP`, ours: the `sum ≥ n` half plus, per
  variable that can still match, its root at-most-one over `S`. Omitted when
  `|S| = 1`, where one atom per variable needs no at-most-one.
- **Reason** — as rule 9.
- **Assertion** — `n ≤ |vars| − j ∨ ¬reason`.
- **Hint** — `hints::Among`.
- **Offline reconstructibility** — `hinted`, provided the reconstructor derives
  the per-variable at-most-ones itself. The ones in the proof are root lines
  known to the solver by number only.
- **Proof size** — one `pol` over up to `n + 1` rows, one RUP, plus the root
  initialiser's `n · C(|S|, 2)` once.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: among-exclude

(Rule 11.)

- **Infers** — for every can-be-either variable, `X_i ≠ v` for every `v ∈ S`.
- **Fires when** — the must-match variables already reach `n`'s upper bound,
  which the invariant makes `n`'s value. The propagator then disables itself
  until backtrack.
- **Strength** — `partial`; with rule 12, `GAC` on the array.
- **Algorithm** — one `infer_all` per can-be-either variable, of `|S|` literals.
  Bounded by `|S|`, not the domain.
- **Why it is true** — the count is already met, so no further variable may
  match.
- **Proof technique** — `pol` then `RUP` per literal, ours: the `sum ≤ n` half
  plus the must-match variables' at-least-ones, as rule 9. Assuming any extra
  match pushes the sum past `n`.
- **Reason** — the array's domains plus `n`'s two bounds.
- **Assertion** — `X_i ≠ v ∨ ¬reason`, one per `v ∈ S`.
- **Hint** — `hints::Among`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — one `pol` per variable, and one RUP per value of `S`.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: among-include

(Rule 12.)

- **Infers** — for every can-be-either or must-match variable, `X_i ∉ [lo, hi]`
  for every run of its domain outside `S`.
- **Fires when** — the must-match and can-be-either variables together only
  just reach `n`'s lower bound, again `n`'s value. The propagator then disables
  itself until backtrack.
- **Strength** — `partial`; see rule 11.
- **Algorithm** — per variable, `each_interval_minus(S)` over a copy of its
  domain. In runs; the `Among` row pins it `Clean`.
- **Why it is true** — every variable that can match must, to reach the count.
- **Proof technique** — `RUP sequence`, then `pol` and `RUP`, ours. For each
  `v ∈ S`, one order atom rules it out given the range (`X_i < lo` or
  `X_i ≥ hi + 1`, picking the side `v` is on), then `pol`: the `sum ≥ n` half
  plus the at-most-ones of every other variable that can match. The comment in
  `among.cc` says why the side has to be picked explicitly: a range pins no bits
  of `X_i`, so unit propagation needs the chain.
- **Reason** — the array's domains plus `n`'s two bounds.
- **Assertion** — `X_i ∉ [lo, hi] ∨ ¬reason`, one per run.
- **Hint** — `hints::Among`.
- **Offline reconstructibility** — `hinted`, with rule 10's caveat about the
  at-most-ones.
- **Proof size** — per run, `|S|` RUPs and one `pol` over up to `n` rows.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: nvalue-upper

(Rule 13.)

- **Infers** — `n ≤ |⋃_i D(X_i)|`.
- **Fires when** — every `NValue` call.
- **Strength** — `partial`: a bound on `n` only, and a weak one. It is the
  trivial upper bound, far below what published `NValue` propagators do; see
  [Prior art](#prior-art).
- **Algorithm** — a `std::set` of every value of every domain, rebuilt every
  call: `O(Σ |D(X_i)| log)` in **values**.
- **Why it is true** — the variables cannot take more distinct values than their
  domains hold between them.
- **Proof technique** — `RUP`: every `w_v` for a value in no domain is falsified
  by its `[r]` half, and the sum row bounds `n`.
- **Reason** — the whole-scope `generic_reason`.
- **Assertion** — `n ≤ u ∨ ¬reason`.
- **Hint** — `hints::NValue`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line; the cost is the per-value encoding (#843).
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: nvalue-lower

(Rule 14.)

- **Infers** — `n ≥ max(1, |{values of fixed variables}|)`, or `n ≥ 0` for an
  empty array.
- **Fires when** — every call.
- **Strength** — `partial`: weak in the same way as rule 13. Nothing prunes the
  array: when `n`'s upper bound equals the number of distinct fixed values,
  every unfixed variable must take one of those, and `NValue` does not say so.
- **Algorithm** — a `std::set` of the fixed variables' values, per call.
- **Why it is true** — distinct fixed values are distinct values taken, and a
  non-empty array takes at least one.
- **Proof technique** — `RUP`: fixed variables force their values' `w_v`.
- **Reason** — the whole-scope `generic_reason`.
- **Assertion** — `n ≥ l ∨ ¬reason`.
- **Hint** — `hints::NValue`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: gcc-closed-cover

(Rule 15.)

- **Infers** — `X_i ∉ [lo, hi]` for every run of `X_i`'s domain outside the
  cover.
- **Fires when** — the closed propagator, under `with_closed()`, finds a domain
  not inside the cover. `domain_is_subset_of` answers "nothing to do" without
  copying, which is every call after the first per variable.
- **Strength** — `partial`: the closed restriction alone.
- **Algorithm** — `each_interval_minus` against the cover's interval set, built
  once (#877). In runs.
- **Why it is true** — a closed variable takes a cover value.
- **Proof technique** — `RUP` against the variable's `<i>_al1` row: asserting
  `X_i ∈ [lo, hi]` walks the order chain past every cover value and falsifies
  the row.
- **Reason** — `NoReason`: the conclusion holds unconditionally.
- **Assertion** — `X_i ∉ [lo, hi]`, as a unit.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per run.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: gcc-count-lower-by-fixed

(Rule 16; both arms.)

- **Infers** — `C_j ≥ must_j`, the number of variables fixed to `V_j`.
- **Fires when** — `must_j > lb(C_j)`.
- **Strength** — `partial`: part of `bounds(Z)` on the counts.
- **Algorithm** — one pass per cover value: `in_domain` and `has_single_value`
  per variable, `O(m · n)` per call. The reason is gathered only when this
  fires, in the same variable order and from the same state.
- **Why it is true** — each variable fixed to `V_j` is one occurrence.
- **Proof technique** — `RUP` against the `<j>_ge` row.
- **Reason** — `X_i = V_j` for each such variable. Minimal.
- **Assertion** — `C_j ≥ must_j ∨ ¬reason`.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: gcc-count-upper-by-candidates

(Rule 17; both arms.)

- **Infers** — `C_j ≤ can_j`, the number of variables that can still be `V_j`.
- **Fires when** — `can_j < ub(C_j)`.
- **Strength** — `partial`, as rule 16.
- **Algorithm** — the rule 16 pass.
- **Why it is true** — only variables that can take `V_j` can count towards it.
- **Proof technique** — `RUP` against the `<j>_le` row.
- **Reason** — `X_i ≠ V_j` for each variable that cannot take it. Minimal.
- **Assertion** — `C_j ≤ can_j ∨ ¬reason`.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: gcc-saturated-capacity

(Rule 18; bounds arm only.)

- **Infers** — `X_i ≠ V_j` for every unfixed `X_i` that can take `V_j`.
- **Fires when** — `must_j = ub(C_j)`: the value's capacity is used up by fixed
  variables.
- **Strength** — `partial`.
- **Algorithm** — the rule 16 pass; the inferences are one per candidate.
- **Why it is true** — any further occurrence would exceed the count's upper
  bound.
- **Proof technique** — `RUP` against the `<j>_le` row.
- **Reason** — the fixed variables' `X = V_j`, and `C_j ≤ ub`. Minimal.
- **Assertion** — `X_i ≠ V_j ∨ ¬reason`.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per removal.
- **Gaps** — `None.` The flow arm has no equivalent. It gets the same removals
  from rule 29, by a cut `pol` rather than one RUP; see [Proof
  performance](#proof-performance).
- **Tightness** — `Not shown.`

### Rule: gcc-just-met-demand

(Rule 19; bounds arm only.)

- **Infers** — `X_i = V_j` (as range removals) for every unfixed `X_i` that can
  take `V_j`.
- **Fires when** — `can_j = lb(C_j) > 0`: every candidate is needed.
- **Strength** — `partial`.
- **Algorithm** — per candidate, `each_interval_minus({V_j})`: its domain minus
  the value, as ranges. That is two for a contiguous domain, and one more than
  the domain's interval count in general (#860).
- **Why it is true** — fewer occurrences than all the candidates would fall
  below the count's lower bound.
- **Proof technique** — `RUP` against the `<j>_ge` row, through the ge-atom
  chain.
- **Reason** — the absent variables' `X ≠ V_j`, and `C_j ≥ lb`. Minimal.
- **Assertion** — `X_i ∉ [lo, hi] ∨ ¬reason`, one per run.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per run.
- **Gaps** — `None.` The flow arm has no equivalent; see rule 18.
- **Tightness** — `Not shown.`

### Rule: hall-count-lower

(Rule 20; bounds arm.)

- **Infers** — `C_j ≥ confined − (cap − ub_j)` for `j` in a contiguous run
  `[a, b]` of the sorted cover, where `confined` variables have domains inside
  `V[a..b]` and `cap` is the sum of the run's count upper bounds.
- **Fires when** — that bound exceeds `lb(C_j)`, for any pair `a < b`.
- **Strength** — `partial`: part of the arm's `bounds(Z)`.
- **Algorithm** — for every pair `(a, b)`, a pass classifying every variable as
  confined (early-exit walk, bounded by `|H| + 1`) and potential. `O(m²)` pairs
  × `n` variables × `O(|H|)`, every call. This is #1028.
- **Why it is true** — the confined variables all take values in the run; the
  other run values can absorb at most `cap − ub_j` of them; the rest take `V_j`.
- **Proof technique** — `pol` then `RUP`, ours, a generalisation of JP 3.16's
  sum. For `v ≠ j` in the run, the `<v>_le` row resolved against `C_v ≤ ub_v`
  by `add_for_literal`; the at-least-one over the run's values each confined
  variable still has; and `<j>_le`. The result is
  `C_j − Σ_{non-confined} X=V ≥ lower`, closed by RUP.
- **Reason** — `LazyReasonOver`: each confined variable's bounds, plus one range
  per gap between consecutive run values inside them (#936), and `C_v ≤ ub_v`
  for the other run values.
- **Assertion** — `C_j ≥ lower ∨ ¬reason`.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `hinted`: the run is the cover values whose
  count bounds the reason names plus `j`, and the confined variables are those
  it names.
- **Proof size** — one `pol` over `(b − a + 1)` count rows, a bound resolution
  for each of the `b − a` others whose count is not a constant, and one at-least-one per confined variable (cached); one
  RUP.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: hall-count-upper

(Rule 21; bounds arm.)

- **Infers** — `C_j ≤ potential − (demand − lb_j)`, the dual of rule 20:
  `potential` variables can meet the run, and `demand` is the sum of the run's
  count lower bounds.
- **Fires when** — that bound is below `ub(C_j)`.
- **Strength** — `partial`.
- **Algorithm** — as rule 20.
- **Why it is true** — the other run values need at least `demand − lb_j` of
  the potential variables, and each variable is one occurrence at most.
- **Proof technique** — `pol` then `RUP`, ours, JP 3.16's dual. Per potential
  variable an at-most-one over the run's values, **recovered afresh by
  `recover_am1` at `Temporary`**, which is `C(b − a + 1, 2)` pairwise RUPs; the
  `<v>_ge` rows resolved against `C_v ≥ lb_v` for `v ≠ j`; and `<j>_ge`.
- **Reason** — `LazyReasonOver`: `X ≠ v` for every run value and every variable
  that cannot meet the run, and `C_v ≥ lb_v` for the others.
- **Assertion** — `C_j ≤ upper ∨ ¬reason`.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — `potential · C(|H|, 2)` pairwise lines plus a fold each, then
  a `pol` and a RUP. In **cover values**, quadratic, never width (#944).
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: hall-capacity-violator

(Rule 22; bounds arm. **Dead code.**)

- **Infers** — a contradiction, when more variables are confined to a run than
  its capacity.
- **Fires when** — `confined > cap`. **It never does.** The loop over
  `j ∈ [a, b]` just above it runs first and is never empty. With
  `confined > cap`, its first `j` computes
  `lower = confined − (cap − ub_j) > ub_j`, so rule 20's inference fails and the
  propagator leaves before this line. The audit's counters saw it fire on none
  of 30 seeds of `bounds_global_cardinality_test`, nor on the four GCC corpus
  models counted (`gbac` 2016, `lot-sizing` 2019, `blocks-world`, `mondoku`).
- **Strength** — `partial`.
- **Algorithm** — as rule 20.
- **Why it is true** — pigeonhole: more variables than the run's values can hold
  between them.
- **Proof technique** — `pol` then `RUP`, as rule 23 without a removal.
- **Reason** — as rule 23.
- **Assertion** — `¬reason`.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — as rule 23.
- **Gaps** — the justification is never exercised by anything, so nothing shows
  it is right. The contradiction it would have reported is reported by rule 20,
  whose justification is exercised.
- **Tightness** — `Not shown.`

### Rule: hall-capacity-removal

(Rule 23; bounds arm.)

- **Infers** — `X_i ≠ v` for every run value `v` and every non-confined `X_i`.
- **Fires when** — `confined = cap`: the run is a Hall interval.
- **Strength** — `partial`.
- **Algorithm** — as rule 20, plus a pass over the non-confined variables.
- **Why it is true** — the confined variables use the run's entire capacity.
- **Proof technique** — `pol` then `RUP` per removal, ours, the analogue of JP
  3.17: every `<v>_le` row in the run resolved against `C_v ≤ ub_v`, plus the
  confined variables' at-least-ones, giving
  `Σ_{non-confined, v in run} X=v ≤ 0`.
- **Reason** — `LazyReasonOver`, the capacity reason (rule 20's, for the whole
  run). **Re-materialised per removal**: each removal is its own `infer` with
  its own lazy reason, and nothing is shared across the batch.
- **Assertion** — `X_i ≠ v ∨ ¬reason`.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — **one `pol` per removal**, not per Hall set: the `pol` is
  rebuilt for each `(X_i, v)`.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: hall-demand-violator

(Rule 24; bounds arm. **Dead code**, for the mirror reason.)

- **Infers** — a contradiction, when fewer variables can meet a run than its
  demand.
- **Fires when** — `potential < demand`. **It never does**: rule 21 runs first
  for every `j` in the run, computes `upper = potential − (demand − lb_j) < lb_j`
  and fails.
- **Strength** — `partial`.
- **Algorithm** — as rule 21.
- **Why it is true** — pigeonhole, the dual of rule 22.
- **Proof technique** — `pol` then `RUP`, as rule 25 without a removal.
- **Reason** — as rule 25.
- **Assertion** — `¬reason`.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — as rule 25.
- **Gaps** — as rule 22.
- **Tightness** — `Not shown.`

### Rule: hall-demand-removal

(Rule 25; bounds arm.)

- **Infers** — `X_i ≠ w` for every value `w` outside the run, for every
  potential `X_i`.
- **Fires when** — `potential = demand`: every variable that can meet the run
  is needed by it.
- **Strength** — `partial`.
- **Algorithm** — `each_value_mutable(X_i)`, **one value at a time over the
  whole domain**, and one inference per non-run value. This is the
  `GlobalCardinality/hall` row's `KnownTrip`.
- **Why it is true** — the run's demand uses every potential variable.
- **Proof technique** — `pol` then `RUP`, ours, the dual of rule 23. It uses the
  `<v>_ge` rows resolved against `C_v ≥ lb_v`, and per potential variable an
  at-most-one over the run's values, **plus `w` for the variable being pruned**,
  recovered afresh.
- **Reason** — the demand reason; lazy, re-materialised per removal.
- **Assertion** — `X_i ≠ w ∨ ¬reason`.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — per removed **value**: `potential · C(|H|, 2)` pairwise lines,
  folds, a `pol` and a RUP. Per value of a domain, so unbounded in width, and
  quadratic in the run.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: flow-capacity-violator

(Rule 26; flow arm.)

- **Infers** — a contradiction, when the max flow with lower bounds leaves a
  variable unassigned.
- **Fires when** — the flow is infeasible and the violator search from an
  unassigned variable grows a set of cover values whose confined variables
  outnumber their capacity.
- **Strength** — `GAC` relative to the count bounds: infeasibility detection.
- **Algorithm** — Dinic's max flow on value and variable nodes with the
  lower-bound reduction, rebuilt every call. Then alternating growth from the
  unassigned variable over value adjacency and flow: `O(m · n)` per step. Régin
  (1996) for the flow.
- **Why it is true** — as rule 22, for the set found.
- **Proof technique** — `pol` then `RUP`, by `emit_gcc_capacity_pol`
  (`justify.cc`): the cut values' `<v>_le` rows, their count upper bounds, and
  the confined variables' at-least-ones over the cut values each still has.
  JP 3.16's shape with capacities.
- **Reason** — `gcc_capacity_reason`: confined variables' bounds and gap ranges
  (#936), and the cut values' count upper bounds.
- **Assertion** — `¬reason`.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `hinted`: cut values and confined variables
  are both named by the reason.
- **Proof size** — one `pol` and one RUP, plus cached at-least-ones.
- **Gaps** — `None.` If neither violator search finds anything, the arm throws
  `UnexpectedException` rather than emit an unjustified contradiction. For a
  closed constraint whose unassigned variable has no cover value left, it
  returns without inferring, and leaves the closed propagator (rule 15) to
  refute it.
- **Tightness** — `Not shown.`

### Rule: flow-demand-violator

(Rule 27; flow arm.)

- **Infers** — a contradiction, when some cover value cannot get its lower bound
  of flow.
- **Fires when** — the flow is infeasible, rule 26's search found nothing, and
  growth from an under-supplied value finds cover values whose demand exceeds
  the variables that can supply them.
- **Strength** — as rule 26.
- **Algorithm** — as rule 26, from the value side.
- **Why it is true** — as rule 24, for the set found.
- **Proof technique** — `pol` then `RUP`, by `emit_gcc_demand_pol`: the cut
  values' `<v>_ge` rows and count lower bounds, and an at-most-one over the cut
  values per supplier, recovered afresh.
- **Reason** — `gcc_demand_reason`: `X ≠ v` for every cut value on every
  variable that cannot meet the cut, and the cut values' count lower bounds.
- **Assertion** — `¬reason`.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — `suppliers · C(|cut|, 2)` pairwise lines, folds, a `pol` and
  a RUP.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: flow-capacity-cut

(Rule 28; flow arm.)

- **Infers** — `X_i ≠ V_j` for an edge with no flow between two strongly
  connected components of the residual graph, when the source is reachable from
  `X_i`.
- **Fires when** — after a feasible flow, for each such edge.
- **Strength** — `GAC` on the array relative to the count bounds (with rules 29
  and 30).
- **Algorithm** — an iterative Tarjan over the residual graph, rebuilt every
  call. Then, **per pruned edge**, a breadth-first reachability from the
  variable to extract the cut, and a pass classifying every variable as confined
  or not. `O(edges)` per pruning, in values.
- **Why it is true** — the cover values not reachable from the variable are
  full: every maximum flow saturates them, so no flow can route through this
  edge.
- **Proof technique** — `pol` then `RUP`, by `emit_gcc_capacity_pol` over the
  unreachable values and their confined variables; JP 3.17's shape.
- **Reason** — `gcc_capacity_reason`, lazy.
- **Assertion** — `X_i ≠ V_j ∨ ¬reason`.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `hinted`. The cut is recoverable from the
  reason, but the reconstructor would rebuild the residual graph to know which
  cut it was. The reason names it, so it need not.
- **Proof size** — one `pol` and one RUP per pruning. The cut is rebuilt per
  pruning and not shared across the edges it would explain.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: flow-demand-cut

(Rule 29; flow arm.)

- **Infers** — `X_i ≠ V_j` for a no-flow edge between components, when the
  source is **not** reachable from `X_i`.
- **Fires when** — as rule 28.
- **Strength** — as rule 28.
- **Algorithm** — as rule 28; the cut is the cover values reachable from the
  variable.
- **Why it is true** — the cover values in the cut are at their lower bounds and
  need every variable that can supply them, this one included.
- **Proof technique** — `pol` then `RUP`, by `emit_gcc_demand_pol`, with the
  pruned variable's at-most-one extended by the pruned value.
- **Reason** — `gcc_demand_reason`, lazy.
- **Assertion** — `X_i ≠ V_j ∨ ¬reason`.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — per pruning, `potential · C(|cut|, 2)` pairwise lines plus
  folds, a `pol` and a RUP. **This is the rule that makes the flow arm's proofs
  large.** On `frequency_square 12 --all` all 4,916 of the arm's prunings are
  this rule. The bounds arm makes the same prunings with rules 18 and 19, at one
  RUP each.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: flow-non-cover-removal

(Rule 30; flow arm.)

- **Infers** — `X_i ≠ w` for every non-cover value `w` of an open constraint's
  variable, when the variable cannot route through the dummy value.
- **Fires when** — the dummy edge carries no flow and crosses components.
- **Strength** — as rule 28.
- **Algorithm** — reachability for the cut, then
  `each_value_mutable(X_i)`, **one value at a time over the whole domain**,
  removing each non-cover value (#876's unbounded site). **This is also where
  #1026 lived**: the cover test was a binary search over a cover only sorted
  under `BC`, so a cover value could be taken for a non-cover one and removed.
- **Why it is true** — the cut's cover values need this variable, so it cannot
  take a value outside the cover.
- **Proof technique** — `pol` then `RUP` per value, by `emit_gcc_demand_pol`
  with the pruned value added.
- **Reason** — `gcc_demand_reason`, lazy.
- **Assertion** — `X_i ≠ w ∨ ¬reason`, per value.
- **Hint** — `hints::GlobalCardinality`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — rule 29's per removed **value**, over a whole domain.
  Unbounded in width. Removing the non-cover values as runs, with one
  derivation for the batch, would fix both halves.
- **Gaps** — `None.` Before #1030 the rule removed cover values on an unsorted
  cover, and VeriPB rejected the justification. That was a soundness bug in the
  propagator, which the proof caught; not a gap in the logging.
- **Tightness** — `Not shown.`

## Evidence

### Tests

**What exists.**

| Lane | Harness | Checked consistency | Covers |
|---|---|---|---|
| `count_constraint` | `solve_for_tests_checking_consistency` | `y` `GAC`, `n` `BC`, array `GAC` | random rows over `y` variable and constant; #254's degenerate rows; `run_dup_count_test` (a repeated array variable) and `run_count_result_in_array_test` via plain `solve_for_tests` |
| `count_constraint_view_mixed` | as above, positions wrapped in views | as above | |
| `among_constraint` | `solve_for_tests_checking_consistency` | `n` `GAC`, array `GAC` | random `S` in `[−10, 10]`; #254's rows; `run_dup_among_test`, `run_self_ref_among_test` |
| `among_constraint_view_mixed` | as above | as above | |
| `n_value_constraint` | plain `solve_for_tests` | **none** | random rows; constant arrays; `run_dup_n_value_test` |
| `n_value_constraint_view_mixed` | as above | none | |
| `bounds_global_cardinality_constraint` | `solve_for_tests_checking_consistency` | array and counts `BC` | fixed rows (Hall sets, holes, spans across zero, #557), #254's rows, 24 random rows |
| `gac_global_cardinality_constraint` | as above | array `BC`, counts none (#413) | the same shapes at `GAC`; from #1030 also three unsorted-cover rows, and random rows with shuffled covers |
| `scp_chain_*` (14) | `run_scp_chain.bash` | — | see [Cake conformity](#cake-conformity) |
| `xcsp_count`, `xcsp_count_among`, `xcsp_n_values`, `xcsp_cardinality{,_occvars,_intervals,_repeated}` | cached solution counts | — | the XCSP3 bindings |
| `minizinc-{count,countops,among,nvalue,globalcardinality,…closed,…lowup,…repeated,…repeatedclosed}` | `run_minizinc_test.bash`, against Gecode | — | the MiniZinc bindings |
| `large_domain_audit` rows | guard build only | — | see [Interval efficiency](#interval-efficiency) |

The harness's `BC` is `bounds(Z)`: a support need only lie within its partners'
bounds. VeriPB runs in every data-driven lane whenever it is on the path, for
the `proofs = true` half of each instance list. Every lane is seeded
(`establish_and_announce_seed`) and byte-reproducible with `--seed=N`.

**Runtime caps.** The suite-wide default caps (300 solutions, 1,500 search nodes
per solve, `GCS_TEST_CAP_DEFAULTS`) apply to every lane here, and none of this
family's lanes sets or clears one. **They fire.** Measured with a local-only
print in `solve_for_tests_with_callbacks`, the caps passed in the environment,
over three reseeded runs: `count_constraint` 16, 14 and 14 solves truncated;
its view lane 10, 12 and 8; `among_constraint` 4, 2 and 4; its view lane 2, 2
and 4; `n_value_constraint` 4, 2 and 8; its view lane 4, 4 and 6; both GCC
lanes 0. A truncated solve checks soundness and a partial proof only. The
figures in this document come from a build with `-DGCS_TEST_CAP_DEFAULTS=OFF`,
where every solve runs to completion: 43/43 of the family's lanes pass at
`347e2f8c` with MiniZinc 2.9.7, `cake_pb_cp` and `opbdiff` on the path, and
925/925 of the whole suite on #1030's branch.

**Real instances ported:** none. The corpus models used below live outside the
tree.

**Tightness:** no mutation lane exists for any rule; see the catalogue
preamble.

**Rules the tests reach.** Counted by a local-only counter at every rule site,
seed 1: `count_test` reaches all eight of `Count`'s rules (rule 5 16 times,
rule 6 16 times); `among_test` all four; `n_value_test` both;
`gac_global_cardinality_test` rules 15–17 and 26–30. `bounds_global_cardinality_test`
reaches 15–21, 23 and 25, **and never 22 or 24, over 30 seeds**. Those two are
unreachable; see their entries.

**What the tests do not cover**, which is the point of this section:

- **An unsorted cover under `GAC`**, until #1030. Every test row built its
  cover ascending, from a `std::set` or by hand. That is how #1026 survived
  from `55783337` in July to this audit. A random differential found it in its
  first 2,000 instances.
- **`GlobalCardinality` over repeated variables or views.** There is no GCC view
  lane. This audit's differential (6,000 instances against brute force, 600 with
  VeriPB) found nothing, but it is not in the tree.
- **`Count` with `y` inside its own array**, as itself, an offset view or its
  negation. The same: differential clean (3,000 plus 300 verified), not in the
  tree.
- **`NValue` has no consistency check at all**, and no test would notice if it
  pruned less. It prunes little enough that this is not much of a gap.
- **The flow arm's scale.** Every `GAC` test instance has at most four
  variables and three cover values; the random rows, at most three and two. `frequency_square` is the only larger `GAC`
  caller, and it is an example, not a ctest lane.
- **`|S|` and `m`.** The widest `S` any lane posts is a handful of values, and
  the largest cover three. Both are where this family's costs are.
- **`Count`'s constant-`y` shape** is tested, but nothing measures its
  per-call cost or its wake count. #1029 had to find it from the corpus.
- **The MiniZinc shape lanes of #1006** cover `all_different`'s globals only.
  Step 3, which includes `global_cardinality*`, has not started.

### Benchmarks and examples

- **`examples/frequency_square`** is the family's own benchmark: a
  `GlobalCardinality` over every row and column of a partially filled square,
  cover `1..n`, with `--consistency bc|gac` (default `gac`). The defaults finish
  in milliseconds, and `--all` beyond `12` explodes. The right sizes:
  - for **CPU**: `12 --holes 5 --all --seed 2` (27,759 recursions, 2.7 s at
    `GAC`) and `12 --holes 5 --lambda 3 --all` (41,913 recursions, 2.6 s);
  - for **proofs**: `12 --all` (569 recursions, 282 solutions, 86,014 proof
    lines at `GAC`, VeriPB 0.8 s).
- **MiniZinc Challenge models**, one instance of each, flattened with our
  `mznlib`: `Count` in 30 models, `GlobalCardinality` in 23, `NValue` in 5,
  `Among` in none. The `Count`-dominated ones are `league`,
  `on-call-rostering`, `gfd-schedule`, `ptv`, `jp-encoding` and `roster`; only
  `roster` (2011, 2015 and 2023) finishes inside a minute. The GCC ones that
  are usable to the Nth solution are `gbac` (2016, 2017, 2020), `lot-sizing`
  2019, `chessboard` 2023, `community-detection` 2024 and `mondoku` 2025.
- **No example posts `Count`, `Among` or `NValue`.**

Never run `frequency_square --all` above size 12 uncapped.

### CPU performance

All figures in this section: `347e2f8c` plus two local-only switches in
`fzn_glasgow.cc` (not on any branch), Release, GCC 15.2.0, `-DGCS_WERROR=ON`,
fataepyc-09 (2 × EPYC 7643, boost off, flat 2.3 GHz), `taskset`-pinned with
memory bound to the core's node, 2026-09-23. The corpus runs are **one run
each**; the `frequency_square` runs are the minimum of three.

**Where the family is the cost.** Share of propagation time
(`GCS_PROPAGATOR_STATS=time`, 20 s, unpinned survey):

| Model | Class | Share of calls | Share of time |
|---|---|---|---|
| 2012 league | `Count` | 58.9% | 96.4% |
| 2019 ptv | `Count` | 54.4% | 99.9% |
| 2018 on-call-rostering | `Count` | 27.8% | 91.4% |
| 2016 gfd-schedule | `Count` | 18.4% | 87.4% |
| 2017 jp-encoding | `Count` | 3.3% | 86.1% |
| 2015 roster | `Count` | 72.6% | 78.2% |
| 2019 lot-sizing | GCC bounds | 1.7% | 77.9% |
| 2022 gfd-schedule | `NValue` | 0.9% | 41.9% |
| 2015 gfd-schedule | `NValue` | 0.4% | 30.8% |

**The wrapper A/B.** Each constant-valued `Count` posted as itself, as
`Among({c})`, or as a one-value `GlobalCardinality` at `BC` and at `GAC`.
Solution sequences are identical under all four on every model, and the node
counts are identical on the two that finish (`roster` 2011: 1,812; 2015:
2,605). Nodes explored in 30 s:

| Model | `Count` | `Among({c})` | GCC `BC` | GCC `GAC` |
|---|---|---|---|---|
| 2012 league | 55,373 | 96,080 | 93,633 | 23,466 |
| 2013 on-call-rostering | 129,169 | 166,264 | 239,959 | 52,533 |
| 2018 on-call-rostering | 248,305 | 337,704 | 485,182 | 104,631 |
| 2016 gfd-schedule | 17,704 | 33,011 | 65,634 | 5,033 |
| 2018 gfd-schedule | 58,929 | 65,133 | 168,103 | 14,863 |
| 2019 ptv | 3,035 | 1,939 | 9,991 | 770 |
| 2014 jp-encoding | 137,266 | 156,186 | 120,339 | 83,423 |
| 2017 jp-encoding | 23,330 | 35,696 | 32,253 | 11,558 |
| 2019 lot-sizing | 81,204 | 85,204 | 91,140 | 57,088 |

`perf` on `league` under `Count`: `optional_single_value` 16.8%, `in_domain`
14.2%, the propagator 11.2%, `domains_intersect` 4.0%. That is the four passes
per call #1029 describes. On `ptv`, `Among` is slower than `Count`, because of
its per-call reason and scope copy; only the GCC `GAC` spelling is slower
still. The 2014 `jp-encoding` row, where the GCC
is slower than `Count`, is a single run and wants repeating.

**The two GCC arms**, same search tree, time to the Nth solution:

| Instance | N | nodes (both) | `BC` | `GAC` |
|---|---|---|---|---|
| `frequency_square 12 --holes 5 --all --seed 2` | all 13,608 | 27,779 / 27,759 | 11.70 s | 2.67 s |
| `frequency_square 12 --holes 5 --lambda 3 --all` | all 20,543 | 41,921 / 41,913 | 6.00 s | 2.58 s |
| 2016 gbac | 15 | 969 | 1.20 s | 1.07 s |
| 2017 gbac | 23 | 7,717 | 1.82 s | 1.54 s |
| 2019 lot-sizing | 29 | 26,919 | 10.60 s | 2.93 s |
| 2020 gbac | 92 | 143,714 | 27.58 s | 20.94 s |
| 2023 chessboard | 10 | 147,934 | 12.53 s | 9.38 s |
| 2024 community-detection | 46 | 573 | 10.99 s | 11.28 s |
| 2025 mondoku | all | 20,367 | 2.83 s | 2.27 s |

Only on `frequency_square` does `GAC` prune more, by 20 and 8 recursions. At
fixed time, where the tree could not be confirmed identical, the gaps widen
with the cover: `oocsp_racks` (cover 30) 6,357 against 133,784 nodes,
`evm-super-compilation` (cover 54) 2,346 against 121,910. A synthetic `m`
variables over `[1, m]` with cover `1..m`, root to first solution, proofs off:
0.38 s against 0.017 s at `m = 40`, 9.58 s against 0.13 s at 80, 275 s against
1.17 s at 160. This is #1028.

**What these benchmarks do not exercise.** From the rule counters:

- `Count`'s constant-`y` models reach rules 1, 2 and 8 only. `ptv` reaches just
  1 and 2. `amaze`, with a variable `y`, adds 3 and 7. **Rules 4, 5 and 6 are
  reached by no corpus model**, only by the test.
- `frequency_square` at `GAC` reaches rule 16 and **rule 29 alone** (4,916
  prunings); at `BC`, rules 16, 18, 19, 23 and 25, mostly 18 and 19.
- The GCC corpus models reach 16–21, 23 and 25 at `BC`. `blocks-world` reaches
  only 16–18.
- `NValue`'s two models reach both its rules; they are all it has.
- Nothing reaches rules 22 and 24, which cannot fire.

A per-inference cost quoted from any of these is an average over those rules.

**Cross-solver.** `Not measured.` #868 is open for the whole arc; for this
family, the right target is `frequency_square` against Gecode's
`count`/`gcc` with `ICL_DOM`.

### Proof performance

`347e2f8c`, same machine, VeriPB 3.0.2.

**`frequency_square 12 --all`**, both arms, identical tree (569 recursions,
282 solutions):

| Arm | OPB rows | proof lines | size | VeriPB | solve | `rup` / `pol` / `del` | at `inferences`: lines, GCC assertions |
|---|---|---|---|---|---|---|---|
| `GAC` | 4,321 | 86,014 | 3.7 MB | 0.80 s | 0.13 s | 36,001 / 17,009 / 30,149 | 8,040, 4,919 of 5,770 |
| `BC` | 4,321 | 10,966 | 1.2 MB | 0.45 s | 0.28 s | 5,817 / 899 / 1,216 | 7,951, 4,830 of 5,681 |

**Own against shared.** In the OPB the family is small: 288 of the 4,321 rows
are the 24 constraints' count rows, and 4,032 are the literal definitions. In
the proof it is the other way round. The tree and the search lines are the same
under both arms, and the inference counts at `inferences` differ by 2%. So the
difference between the arms, about 30,000 `rup`, 16,000 `pol` and 29,000 `del`
lines, is the flow arm's own justifications: rule 29's per-pruning at-most-ones,
recovered afresh (#944). At `inferences` the GCC assertions are 85% of the
proof's assertions under both arms.

**The same constraint under three spellings** (`roster`, finishes):

| | OPB rows | proof lines | VeriPB |
|---|---|---|---|
| 2011, `Count` / `Among({c})` / GCC | 18,975 / 10,407 / 10,407 | 74,582 / 62,778 / 57,111 | 11.9 / 7.4 / 7.1 s |
| 2015, `Count` / `Among({c})` / GCC | 21,072 / 11,552 / 11,552 | 60,268 / 44,378 / 40,903 | 14.0 / 7.7 / 7.2 s |

All six verify. `Count`'s extra rows are its three flags per position, which
are cake's encoding, so #1029 does not touch them.

**`Among`'s root scaffolding** is the table under
[Initialisation](#initialisation-and-global-data): 3,009,120 lines, 120 MB, at
`|S| = 1,000` over three variables. It is quadratic in `|S|`, and doubled by a
proof comment per pair.

**The test lanes at both assertion levels** (seed 1, every proof kept):

| Lane | proof lines, `Off` | proof lines, `inferences` | family assertions |
|---|---|---|---|
| `count_test` | 104,562 | 62,912 | 2,245 |
| `among_test` | 26,818 | 15,654 | 986 |
| `n_value_test` | 37,565 | 30,354 | 2,448 |
| `bounds_global_cardinality_test` | 6,302 | 2,123 | 374 |
| `gac_global_cardinality_test` | 5,261 | 1,714 | 350 |

Every family assertion is bare. The others, which in the `Count` lane outnumber
the family's (13,054 `backtrack` and 6,527 `solx_block` against 2,245), are
search and enumeration lines, and in the GCC lanes `in` from the holey
variables the tests build.

**Too large to verify:** none found, but `Among` comes close for its size. At
`|S| = 1,000` over three variables the proof verifies, and VeriPB takes
**4 min 30 s** on an instance solved in four search nodes, all of it the root
initialiser. The flow arm's proofs at `m = 40` (1.1 million lines to the first
solution) were not checked.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference in the family is justified, nothing is asserted, and no
propagator changes strength when proofs are on. The one thing a proof changes is
whether `Among`'s root initialiser runs, and that initialiser only adds
scaffolding.

Two qualifications. Rules 22 and 24 have justifications that nothing has ever
run, because the rules cannot fire; they are not gaps, since the
contradictions they would report are reported, with exercised justifications, by
rules 20 and 21. And two comments still say otherwise:
`bounds_global_cardinality.cc`'s "These two true facts are asserted" and
`gac_global_cardinality.cc`'s "Demand-driven infeasibility … is still
asserted". Both date from before `ce47d70a` (2026-06-04), which removed the
family's last assertion. A third stale comment, in the flow arm's
closed-deferral branch, says "the per-variable In constraint certifies this";
no `In` has been posted since `76c8eeab`, and it is the closed propagator
(rule 15) that does.

### Known limitations

- **`GlobalCardinality` with `consistency::GAC` can lose solutions** when it is
  open and its cover is not in ascending order (#1026), until #1030 merges. A
  proof-logged run fails verification instead. Neither MiniZinc nor XCSP3
  reaches this arm.
- **`GlobalCardinality`'s default is slow on large covers.** Posting it at
  `consistency::GAC` from C++ is faster or level on every model measured, but
  gives larger proofs (#1028). Neither front end can ask for `GAC`.
- **`GlobalCardinality` at `GAC` is only arc consistent relative to the counts'
  bounds.** A count domain with holes is treated as its hull (#413), which is
  deliberate: full GAC there is NP-hard.
- **`Count` is slow on its most common shape**, a constant value of interest
  (#1029). It propagates correctly but costs 1.4 to 3.7 times what the same
  constraint does written as a one-value `GlobalCardinality`.
- **`NValue` propagates weakly**: bounds on the count from the union of domains
  and the fixed values, and nothing on the array. It is unusable on wide domains
  even with proofs off (#843).
- **`Among` writes a quadratic proof at the root**: `n · C(|S|, 2)` pairwise
  lines, 120 MB and 4.5 minutes of VeriPB at `|S| = 1,000`.
- **A value of interest with a wide domain** makes `Count` walk every value of
  it, on every call.
- **No reified form** of any of the four.
- **XCSP3 `nValues` over an empty list** would get an empty count domain. Not
  checked whether the parser can produce one.

### Next steps

Ranked by what they buy for what they cost.

1. **#1030** (fixes #1026). Open. A wrong answer, a one-line cause, and a
   test that fails on every seed before it.
2. **#1029 — make `Count` fast on a constant value of interest.** One pass for
   `must` and `might`, then the bounds and #996's pruning. Watch `n`
   `on_bounds` in that case. The one-value GCC shows 1.4–3.7 times as many nodes
   per second is available on seven of nine models, on the constraint the
   corpus uses most. Medium cost; the variable-value path stays as it is.
3. **#1028 — `GlobalCardinality`'s default arm.** Experiments at several scales,
   proofs on and off separately. Three options, not exclusive: flip to `GAC`
   after #1030; give the `GAC` arm rules 18 and 19 first, so the prunings they
   make cost one RUP instead of a rule 29 cut (on `frequency_square` that is all
   4,916 of them); replace rules 20–25 with a real bounds-consistent algorithm.
4. **`NValue`, three small fixes, unfiled.** Build `_possible_values` in
   `define_proof_model`, not `prepare()`, which removes all its per-value work
   with proofs off. Take rule 13's count from an interval union rather than a
   `std::set` of values, which is 31–42% of propagation time on
   `gfd-schedule`. And say, in the class comment at least, how weak it is. A
   real propagator (Bessiere et al.'s bounds, or Beldiceanu's pruning for the
   at-most side) is a project, not a fix; the encoding is #843.
5. **`Among`, two cheap fixes, unfiled.** Build the per-call reason lazily over
   a prebuilt `generic_reason`, as `Count` and `NValue` do, and stop copying the
   scope to partition it. That is 12.5% plus 10.7% of the run on `ptv`, with
   proofs off. Then make the root initialiser lazy, and drop its per-pair proof
   comment, which halves it. Replacing the pairwise at-most-ones with something
   linear in `|S|` is #944's question. `Among` is in no corpus model, so this is
   low priority for all its size.
6. **`GlobalCardinality` tidying, unfiled.** Delete rules 22 and 24, or reduce
   each to a comment saying why it cannot happen, and correct the three stale
   comments under [Proof-logging gaps](#proof-logging-gaps). Make rules 23 and 28 one `infer_all` per Hall set or cut
   instead of one `pol` per removal. Make rules 25 and 30 remove ranges rather
   than values (#876, and the `GlobalCardinality/hall` `KnownTrip`); both need
   a range-shaped justification, which is why #860 left them.
7. **Tests.** Add a GCC view and aliasing lane. Add `Count` rows with `y` in the
   array, large-domain rows for the `GAC` arm
   (#876), and a row varying `|S|` and `m`. The differentials in this audit are
   the templates. Consider `frequency_square` as a lane at `12 --all`: it is
   the only larger instance either arm sees.
8. **Gathering constant `Count`s over one array into one `GlobalCardinality`**
   would add Hall reasoning where `league`, `gfd-schedule` and
   `on-call-rostering` have none. Not measured. If it ever pays, it belongs in a
   presolver, which can certify the rewrite, never in a front end.
9. **#868** — cross-solver, against Gecode's `count` and `gcc` on
   `frequency_square`.

## Prior art

Not re-checked against the papers for this document; the attributions are the
standard ones.

- **`Among`** was introduced in CHIP (Beldiceanu and Contejean, 1994). GAC on
  it is polynomial and simple, which is what `among.cc` does (Bessiere et al.,
  *Among, common and disjoint constraints*, 2005).
- **`GlobalCardinality`**: Régin's flow-based GAC (AAAI 1996) is the flow arm.
  Quimper, van Beek, López-Ortiz, Golynski and Sadjad (CP 2003) gave the
  linear-time bounds-consistent algorithm, which the bounds arm is **not**. GAC
  that also respects the count variables' domains is NP-hard, which is why the
  flow arm works relative to the counts' bounds.
- **`NValue`**: Pachet and Roy (1999); Beldiceanu (2001) for pruning the
  at-most side; Bessiere, Hebrard, Hnich, Kiziltan and Walsh (*Constraints*,
  2006) for the NP-hardness of GAC and the bounds algorithms. Ours implements
  none of it.
- **Proof logging.** McIlree's thesis gives the encodings of `Count` and
  `NValue` (Encoding Procedures 3.7 and 3.8), and `AtMostInValues`, which is
  `Among`'s shape, as a smart-table decomposition (Encoding Procedure 4.12). It
  gives justification procedures for none of the four. The GCC Hall and flow
  justifications here generalise its JP 3.16 and 3.17 from matchings to flows
  with capacities, and the capacity/demand duality and the count-bound
  resolution are ours. Whether any earlier VeriPB or other certifying work
  covered a global cardinality constraint was not surveyed.

## Further reading

- [`all_different.md`](all_different.md): the Hall-set proofs this family's
  flow arm generalises, the tracker's cached at-least-ones, and why
  justifications reading `state` is safe for now.
- [`justification-techniques.md`](../justification-techniques.md): JP 3.16 and
  3.17 and the unit-propagation facts under them.
- [`large-domains.md`](../large-domains.md): the H1c (`Count`), H2 and H2′
  (`NValue`) hazards, and `GlobalCardinality` as "the canonical
  counterexample" to defaulting to `BC`.
- [`optional-interior-pruning.md`](../optional-interior-pruning.md): what the
  `Holes affect` column is for.
- #413 on why the flow arm ignores count holes; #922 on repeated cover values;
  #966 and #996 on `Count`'s value-of-interest and array pruning.

## Developer commentary

**A comment stating an invariant is a claim about every path.** "`values` is
sorted and distinct (`GlobalCardinality::sort_cover_values`)" was true of the
path its author was on, since `sort_cover_values` runs in `clone()`, and false
of the other, since it runs there only under `BC`. The closed propagator, three
screens away, knew better and sorted a copy. Every test built its cover
ascending, so the suite could not disagree. What found it was a differential
that broke the invariant on purpose, reversing the cover, on its first run. For
any `binary_search`, `lower_bound` or `insert_at_end` over data the caller
supplies, that differential is cheap.

**"The specialised one is faster" wanted measuring, and was false.** `Count`,
`Among` and `NValue` were written first because they were easy.
`GlobalCardinality` came later, and was expected to be the heavy one. On the
shape the models use, the one-value GCC is faster than `Count`, smaller in the
OPB, quicker to verify, and identical in search. And GCC's own "cheap" bounds
arm is the slower of its two. In both cases the reason is the same:
recomputing too much per call, not algorithmic weakness.

**Count rule firings before trusting a catalogue.** A local-only counter at each
rule site, printed at exit, took ten minutes to add. It found two rules that
cannot fire, and showed which rules each benchmark reaches, which the bare hints
cannot. It also showed that `frequency_square`'s `GAC` proof is one rule,
repeated 4,916 times. That turned "`GAC` proofs are bigger" into something
specific enough to fix. The recipe: a header with an `atexit` dump behind an
environment variable, and an `audit_rule("name")` call at each site, conditioned
on the inference changing something.

**CPU and proof size can point opposite ways, and the default is chosen on
CPU.** The flow arm is up to 235 times faster and writes 8 times the proof. The
tree's policy is that propagator defaults favour the no-proofs case, so the
proof side is a thing to fix (next step 3's second option), not a reason to keep
the slow default.
