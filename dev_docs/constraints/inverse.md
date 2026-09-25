# Inverse: two arrays that are each other's inverse permutation

> **Maturity** production ·
> **Audited** 2026-09-23 at `00797a97`; re-audited 2026-09-25 at `61112ed0` ·
> **Open issues** filed by this audit: #1048 (8–10× slower than Gecode at equal
> node counts). Filed by this audit and since fixed: #1047 and #1049; see
> [Re-audit](#re-audit-2026-09-25). Found here but not this family's: #1046
> (`GlobalCardinality` proofs break on a constant in the array), still open.
> Already open and touching this family: #522 (the generalised arc consistent
> `AllDifferent` rebuilds its components every wake), #944 (Hall proofs cost
> one pairwise at-most-one per value), #364 (incremental propagators). Tracked
> under #871.

`Inverse(x, y)` says that `x` and `y` are inverse permutations of each other's
index sets: `x[i] = j` exactly when `y[j] = i`. Since #1088 it also takes a
first array **shorter** than the second, which is XCSP3's one-directional
`channel`: then only `x[i] = j ⇒ y[j] = i` holds, `x` is an injection into
`y`'s indices, and an entry of `y` that nothing names is unconstrained. It is
one class with one propagator. That propagator channels between the two arrays
and then runs [`all_different`](all_different.md)'s generalised arc consistent
algorithm on `x`, so most of this family's inference and proof machinery belongs
to that family, and this document says what is different when `Inverse` drives
it.

### Re-audit, 2026-09-25

Two of the three issues this audit filed against the family itself have been
fixed; #1048 (the CPU gap to Gecode) is still open. Every section below has been brought into line with `61112ed0`. **Figures not marked
as re-measured are still from `00797a97`**, the first audit's commit; that
covers the CPU and Gecode comparison, the `perf` profile and the corpus survey,
none of which the two fixes touch.

| Issue | Fixed by | What it changed here |
|---|---|---|
| #1047: a repeated variable from MiniZinc printed `=====ERROR=====`, and XCSP3's `channel` over lists of different lengths aborted | #1088 (37c65d6a) | A repeated variable is now accepted and refuted at the root ([repeated-variable-contradiction](#rule-repeated-variable-contradiction)). A first array shorter than the second is the new **injection form**: no rows from `y` to `x`, no bounds on `y`, no [channel-y](#rule-channel-y), and a new rule for a value every matching takes ([needed-value](#rule-needed-value)). It is written to the `.scp` as `inverse_injective`. A first array longer than the second is still rejected, now by the constructor, and XCSP3 reports it as `s UNSUPPORTED` |
| #1049: every value's at-most-one written at the root, `n·C(n, 2) + 2n` lines | #1089 (a9a951a6) | The root initialiser is deleted. The Hall justification builds each at-most-one on first use and caches it, as `AllDifferent` does. `Inverse` no longer calls `recover_am1`. [Proof-time state](#proof-time-state), rules 4 and 5, and [Proof performance](#proof-performance) are rewritten |

**Re-measured at `61112ed0`:**
- the scaling probe's proof lengths;
- `black-hole` 2013/12's proof at `AssertionLevel::Off`;
- the family's lanes;
- the new rules' `a` lines;
- the injection form's width behaviour;
- a brute-force check of root `GAC` on random small instances of both forms.

Those are the only two commits under `gcs/constraints/inverse` since
`00797a97`. Two framework commits also landed: #1086 (7aeac3ae), which makes
the test harness refuse to run with its idempotence checker off, and #1087
(a8dd8c33), which removes the short proof-name option. Neither changes anything
here; see [Propagator inventory](#propagator-inventory) for the first.

Three things to know before touching it.

- **It is generalised arc consistent, but only when every position is a
  different variable.** Its fixpoint is channel consistency plus `GAC` on
  `AllDifferent(x)`, plus the needed-value rule in the injection form, and that
  is `GAC` on the whole constraint when no underlying variable appears twice,
  within an array or across the two.
  `Inverse(x, x)`, which XCSP3's single-list `channel` posts for an involution,
  is weaker: it needs search to refute #413's triangle. So is an array holding
  two views of one variable.
- **It is the cost on `black-hole`, and there it is 8–10 times slower than
  Gecode, over the same number of nodes to the same first solution** (#1048).
  Each pass rescans every `(i, value)` pair through the per-value domain
  generators, with a full `AllDifferent` run, and a call that changes anything
  makes at least two passes (2.4 per call there). Walking intervals instead
  buys 18%; the rest is the design.
- **Its two forms differ in more than a length check.** The bijection has rows
  both ways and bounds on both arrays. The injection form has rows from `x` to
  `y` only and leaves `y` unbounded. So its `y`-side pruning comes from a Hall
  argument ([needed-value](#rule-needed-value)), not from a channelling row, and
  it is written to the `.scp` under a keyword, `inverse_injective`, that
  `cake_pb_cp` does not know. (Until #1089 the proof also began with a cubic
  root cost, one at-most-one per value; that is gone, see the
  [re-audit](#re-audit-2026-09-25).)

## What it is

### Semantics

`Inverse(x, y, x_start = 0, y_start = 0)`, with `m = |x|` and `n = |y|`, and
`m ≤ n`. There are two forms, and the lengths alone pick between them.

**The bijection**, `m = n`. For every `i` and `j` in `0..n−1`:

```
x[i] = j + y_start  ⇔  y[j] = i + x_start
```

So `x`'s values are `y`'s indices and the other way round, which is why a
starting index is needed for each array: `x`'s values are numbered from
`y_start`, and `y`'s from `x_start`. `x` is a permutation of `y`'s index set, and
`y` is its inverse. The header's comment says the arrays are zero-indexed by
default, which is right.

**The injection**, `m < n` (#1088). For every `i` in `0..m−1` and `j` in
`0..n−1`:

```
x[i] = j + y_start  ⇒  y[j] = i + x_start
```

Only that direction. `x` takes distinct values among `y`'s indices, since two
entries naming one `y[j]` would ask it to take two values. An entry of `y` that
no entry of `x` names is **unconstrained**: it can take any value in its domain,
including one outside `x`'s indices. That is XCSP3's definition of `channel`
over two lists with the first shorter. Its 2023 `CoveringArray` model posts it.
It is the one shape the XCSP3 specification defines for unequal lengths.

Degenerate shapes:

- **Two empty arrays**: satisfied. A data row in `inverse_test`.
- **One variable each**: `x[0] = y_start` and `y[0] = x_start`, by the bounds
  alone. Two data rows.
- **A first array shorter than the second**: the injection form, above.
  **Longer**: the **constructor** throws `InvalidProblemDefinitionException`,
  since `x` would be all different over fewer values than it has entries.
  `exception_test` covers it. MiniZinc's glue never reaches either: it posts
  `false` for any two lengths that differ, which matches the standard library
  (#997). XCSP3 reports a longer first list as `s UNSUPPORTED`.
- **One array empty**: `Inverse({}, y)` is the injection form with nothing to
  name, so every `y[j]` is free. A data row in `inverse_test`.
- **The same variable twice in `x`, or twice in `y` in the bijection form**:
  unsatisfiable, and accepted since #1088. The constructor notices the
  repeat by comparing handles, and the constraint installs a root
  contradiction instead of its propagator
  ([repeated-variable-contradiction](#rule-repeated-variable-contradiction)).
  It also reports a `StatsNote` saying so. Until #1088 the constructor threw,
  and MiniZinc's aliasing reached that from ordinary models (#1047). **The same
  variable twice in `y` in the injection form is satisfiable**, as long as
  nothing names both entries, and is propagated as usual. **The same constant
  twice is accepted**: it is two positions pinned to one value, and the #171
  data rows show it failing at the root.
- **The same variable in both arrays** is legal. `Inverse(x, x)` constrains `x`
  to be an involution, and XCSP3's single-list `channel` posts exactly that.
- **All constants**: decided at the root (#254's three rows).

The constructor's repeat check compares handles. Two identical views (the same
variable, negation and offset) compare equal and are a repeat. Two views that
differ, such as `x` and `x + 1`, are not a repeat to it. They are propagated as
independent positions;
see [Variable kinds and views](#variable-kinds-and-views).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Inverse` | ✓ `inverse`, via `glasgow_inverse` with both arrays' first indices[^mzninv]; `decompose` for `inverse_reif`, `inverse_in_range`, `inverse_set`, `inverse_opt`[^mznstd] | ✓ `channel` over two lists of equal length; ✓ `channel` over two lists with the first shorter, as the injection form[^xunequal]; ✓ `channel` over one list, as `Inverse(x, x)`; `unsupported` for a first list longer than the second, and for the one-to-many form (list and value) | ✓ `Inverse`, through `gcspy`'s `post_inverse`, 0-based | ✓ `inverse` for the bijection; `inverse_injective` for the injection form[^scpinj] | `gcspy` has no start arguments |

[^mzninv]: `fzn_inverse` posts `false` when the lengths differ, `true` when both
    arrays are empty, and otherwise `glasgow_inverse(f, invf, min(index_set(f)),
    min(index_set(invf)))`. Until #997 the glue assumed both started at 1, and a
    non-1-based model got a wrong `UNSATISFIABLE` that verified through the whole
    `cake_pb_cp` chain; see `all_different.md`. An array entry that MiniZinc
    aliases to another, for example through `f[1] = f[2]`, reaches the
    constructor as a repeated handle. Until #1088 that printed
    `=====ERROR=====`; it is now `=====UNSATISFIABLE=====`, as Gecode says, and
    the `minizinc-inverses-aliased` lane checks that the repeat really reaches
    `glasgow_inverse`. MiniZinc's `inverse` never produces the injection form,
    since the glue posts `false` for unequal lengths.

[^mznstd]: The standard library's decompositions: `inverse_reif` as a reified
    conjunction of `element` equalities, `inverse_in_range` as conditional ones
    plus redundant `global_cardinality` constraints, `inverse_opt` over optional
    values, and `inverse_set` over set variables, which MiniZinc turns into
    Booleans for us. None reaches this class. One small model of each gave
    the same solution count as Gecode (729, 34, 34 and 64).

[^xunequal]: XCSP3 defines `channel` over lists of different lengths as an
    injection, `list1[i] = j → list2[j] = i`. Until #1088 the binding posted
    `Inverse`, whose `prepare()` threw, and the solver aborted with exit status
    134. It now posts the injection form, and `xcsp_channel_unequal` and
    `xcsp_channel_unequal_free` find ACE's 12 and 120 solutions. The binding
    also catches `InvalidProblemDefinitionException` now, so no constructor's
    rejection can abort it again. **ACE errors on this shape unless `list1`'s
    domain is exactly `list2`'s index set**, which is why `_free`'s first list
    ranges over `0..3` and no wider. Widening one of these instances needs its
    expected file checked by hand, because `regenerate_expected.bash` records an
    ACE error as zero solutions.

[^scpinj]: The injection form is written as `inverse_injective`, with the same
    argument shape as `inverse`, and `scp_reader` checks that each keyword's
    lengths are its own. **`glasgow_scp_solver` round-trips it:** the `.scp`
    that `xcsp_channel_unequal_free` writes reads back to a byte-identical
    `.opb`, and the proof verifies. **`cake_pb_cp` does not know the keyword.**
    Checked on 2026-09-25 against the local build: it prints `unsupported
    constraint: inverse_injective`, writes no OPB, and exits 0. So the injection
    form cannot go through the verified chain, and no `scp_chain` case posts it.
    Spelling it `inverse` would not help: over unequal lengths cake writes a
    single `BAD_INPUT >= 1` row, a model with no solutions.

CPMpy's upstream GCS interface, checked 2026-09-23, lists `inverse` among its
supported globals and posts it as `post_inverse(fwd, rev)`. CPMpy's `Inverse`
is 0-based, which is what `gcspy` assumes.

### Options

`None.` There is no `with_consistency()`, and nothing else to set.

### Variable kinds and views

Any `IntegerVariableID`: plain, constant or view, in either array. The
propagator asks `in_domain` of a partner and never looks through a view. The
proof handles views through the framework's literals, as every family does.
`inverse_constraint_view_mixed` wraps positions in views of fresh variables.

**Views that alias another position.** The first audit's probe posted, against
brute force and with every proof checked: two views of one variable inside `x`,
a negated view of one in `x`, a variable shared across the arrays directly and
through a negated view, and `Inverse(x, x)` over four values (10 involutions).
All five matched, and every proof verified. Since #1088 `inverse_test` posts
aliased shapes itself, seven of them in its bare configuration (no `GAC`
check): a repeat in `x` in both forms, a repeat in `y` in both forms, an
involution, and two and three offset views of one variable in the injection
form's `x`. The constructor's repeat check compares handles, so two views of
one variable that differ in offset or negation are not caught by it. They need not be for soundness: answers and
proofs are right. But propagation is no longer `GAC`, because the matching
treats the two positions as independent; see rule 5. The needed-value rule
guards against the same thing: two views can delete a matched edge behind the
matching's back, and it then falls back from a component to the whole Hall
set.

### Reification

`None.` MiniZinc's `inverse_reif` decomposes through the standard library. A
reified form would need its own propagator and encoding. Nothing asks for one.

### Relation to other families

**Into this family.** MiniZinc's `inverse`; XCSP3's `channel`, both list forms,
and two lists with the first shorter; CPMpy's `Inverse`; the `.scp` reader, under
both keywords. `examples/talent` posts it to link scenes to slots.

**Posts as children.** Nothing. `prepare()` narrows each variable of `x` to
`y`'s index range, and in the bijection form each variable of `y` to `x`'s, with
`define_bound`. That writes an OPB row and installs an initialiser, but posts no
constraint. In the injection form `y` is left as declared.

**Shares code.**

- **`propagate_gac_all_different`** is [`all_different`](all_different.md)'s,
  and it is most of this propagator's work and most of its proof. `Inverse`
  hands it `x`, the values `x` can take (`y`'s index set), no exclusions, its
  own at-most-one cache and a scratch object. In the injection form it also
  asks for the values every matching takes, an output parameter #1088 added
  for `Inverse` alone. A caller has to hand it the right values: `Inverse` once
  passed `x`'s own indices, which failed at the root on any two arrays starting
  at different indices (#997).
- **`justify_all_different_hall_set_needs_value`**, also `all_different`'s,
  added by #1088 for the needed-value rule. It is the Hall-set sum with one
  value's at-most-one left out, and it shares its body with the ordinary Hall
  justification.
- **Not `recover_am1` any more.** Until #1089 `Inverse` called it for its root
  at-most-ones; it now gets them lazily through `all_different`'s own code,
  which folds through `recover_am1_from_pairs`. `recover_am1`'s remaining
  callers are `Among` and `GlobalCardinality`; see rule 4 for what this audit
  found in it.
- **`hints::Inverse`** and **`hints::InverseNeededValue`** are this family's
  own and used by nothing else.

**Presolvers.** None reads or rewrites `Inverse`.

**Reached only through a decomposition?** No.

**Not a candidate merge.** The family list gives `inverse/` alone. It shares a
propagator with `all_different` but has its own encoding, and the channel rules
are its own. `SymmetricAllDifferent`, which means the same as `Inverse(x, x)`
(an involution is already a permutation), lives in `all_different` and has its
own propagator. That propagator is no stronger on #413's triangle.

## The proof model

### OPB encoding

Definitional, and quadratic in the lengths. For every `i` in `0..m−1` and `j`
in `0..n−1`, one clause, and in the bijection form a second:

```
x[i] ≠ j + y_start  ∨  y[j] = i + x_start       (both forms)
y[j] ≠ i + x_start  ∨  x[i] = j + y_start       (bijection only)
```

That is `2n²` rows of two literals each for the bijection, and `m·n` for the
injection, over the variables' equality literals. Plus, from `define_bound`, one
bound row for each bound of a variable's declared domain that reaches outside
the other array's index range, **only** when it does:

```
x[i] ≥ y_start,  x[i] ≤ y_start + n − 1                     (both forms)
y[j] ≥ x_start,  y[j] ≤ x_start + m − 1                     (bijection only)
```

The bounds are part of the meaning: without them a value of `x[i]` outside
`y`'s index set would satisfy every row. The injection form writes neither the
rows from `y` to `x` nor `y`'s bounds, and that is its whole difference in the
model: an unnamed `y[j]` then appears only in rows that `x` satisfies by not
naming `j`. The at-most-ones that make `x` a
permutation are **not** in the model. They follow, since two positions with one
value would force `y[j]` to two values, and that is what the proof derives
(rule 4). So the model says what the constraint means and nothing more.

**Size is independent of the declared width.** The rows name equality literals
for values inside the index range only, over `BinEnc` of the declared domain,
and the bound rows are single rows. A variable declared over `±10⁹` costs a
few more bits and two bound rows. That is measured under [Robustness and
limits](#robustness-and-limits).

### Labels

None. The rows are unlabelled, and nothing refers to them by label. The
propagator's inferences restate them (rule 1). The at-most-ones are cited by
line number through the cache.

### Cake conformity

| Case | `opbdiff` |
|---|---|
| `scp_chain_inverse_sat` | `none` |
| `scp_chain_inverse_offsets_sat` (arrays starting at 0 and 5) | `none` |
| `scp_chain_inverse_aliased_unsat` (`X0` twice in `x`, #1088) | `none` |

**The injection form has no case, and cannot have one yet**: its keyword,
`inverse_injective`, is not one `cake_pb_cp` knows (see the frontend table's
note). It is checked by VeriPB against GCS's own OPB, in `inverse_test` and the
XCSP3 lanes.

All three chain-verify: the solver's proof checks against the OPB `cake_pb_cp`
derives, and cake re-checks the elaborated core. Neither is a label match, for
three reasons:

- **Cake's rows are labelled and ours are not.** Cake writes the same
  implications as `x_eq − y_eq ≥ 0` under `c[id][i_jge]` and `c[id][i_jle]`.
  They are semantically the same rows.
- **Cake writes every variable's bound rows**, `c[id][X_k_lb]` and friends, even
  when the declared domain already fits. `define_bound` writes none in that
  case.
- **Cake's variable encoding is eager** (the whole `ge` ladder and every
  `eq ⇔ ge ∧ ¬ge` definition), where ours defines literals as rows use them.
  That is the divergence #358 recorded (now closed), shared with `element`.

This audit also checked by hand that declared domains wider than the index
range (`−3..7`, and `±10⁹`) and an out-of-range constant all verify against
cake's OPB as well as ours.

### Proof-time state

- **Nothing at the root.** Until #1089 an initialiser derived every value's
  at-most-one before search, `n·C(n, 2) + 2n` lines. It is deleted.
- **Lazily, the first time a Hall justification needs one**, one at-most-one per
  value `v`, over the whole of `x`: `C(m, 2)` pairwise clauses
  `x[a] ≠ v ∨ x[b] ≠ v` at `ProofLevel::Temporary`, each RUP through the two
  rows from `x` to `y` that force `y[v]` to two values (these exist in both
  forms). Then `recover_am1_from_pairs` folds them by induction: `m − 2` `pol`
  merges at `Temporary`, a comment, and one `ia` that pins the clique
  inequality at `ProofLevel::Top`. The last merge is deleted at once, and the
  pairwise lines later, with the justification's other temporaries. This is `all_different`'s
  own `need_value_am1s`, reached through rules 4, 5 and 7. The line numbers go
  into a `map<Integer, ProofLine>` that the propagator owns and hands to the
  justification, which builds only the values it lacks. **The at-most-ones are
  never deleted** and **carry no label**, so an external tool cannot find them
  by name. It does not need to: at every assertion level no justification
  runs, the map stays empty, and a Hall assertion's reconstructor derives the
  at-most-ones itself.
- **Also lazily**: the at-least-ones the Hall justification needs, from the
  names-and-IDs tracker, cached per variable (and per cover, for a definition
  range over the tracker's threshold, which no instance here reaches).
- **Levels.** The pairwise clauses are `Temporary`. The at-most-ones and the
  tracker's at-least-ones are `Top`. The Hall `pol` and every inference's RUP
  are at `Current`.
- **No proof flags and no proof-only variables.** Everything the justifications
  cite is in the OPB, or is an at-most-one derived from it.
- **The cache is the propagator's own**, captured as a `shared_ptr` and never
  null. It is empty when proofs are off, because nothing fills it, and it is
  not backtracked, which is sound because its lines are at `Top`.
- **The Hall justification reads `state`**, not the reason, as in
  `all_different.md`. It is safe for the same reason there.

## The implementation

### Initialisation and global data

- **The constructor** rejects a first array longer than the second, and looks
  for a repeated non-constant handle within `x`, and within `y` in the
  bijection form. That is a pair loop, `O(n²)`, once. A repeat is remembered,
  not rejected.
- **`prepare()`** calls `define_bound` twice per variable of `x`, and of `y` in
  the bijection form, once per bound. Each call does nothing if the declared
  bound already fits.
- **`define_proof_model()`** writes the `2n²` rows, or `m·n` in the injection
  form.
- **`install_propagators()`**, given a repeat, installs only the root
  contradiction and returns. Otherwise it builds `x`'s value list, the scratch
  object, the empty at-most-one cache, and in the injection form the buffer the
  `GAC` stage reports its needed values into.

There is no root cost beyond the constructor's pair loop. #1089 deleted the
at-most-one initialiser, which cost `n·C(n, 2) + 2n` lines: 129,152 of a
152,102-line proof at `n = 64`, on a search that never needed one.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| `define_bound`'s initialisers | initialiser | — | 6 | a declared bound outside the index range; for `y`, the bijection form only | n/a | one shot |
| repeated-variable initialiser | initialiser | — | 8 | the same handle twice in `x`, or twice in `y` in the bijection form. **Replaces** the propagator | n/a | one shot |
| the `Inverse` propagator | `on_change`, every `x` and `y` | derived: every variable, truthfully | 1, 3–5; 2 in the bijection form; 7 in the injection form | no repeated handle | **claims it** (`EnableButIdempotent`), ignored by the engine when positions alias | never |

**Idempotence.** The propagator loops (channel `x`, then channel `y` in the
bijection form, then `GAC` on `x`, then the needed-value rule in the injection
form) until a whole pass changes nothing, so a call ends at its own fixpoint,
and it says so in its comment. That is claimed since 74fd6b46. The test harness
sets `GCS_CHECK_IDEMPOTENT_CLAIMS`, which re-runs every honoured claim and
aborts if the re-run infers anything. The engine reads that variable once,
at its first propagation. In 100 other lanes that happened before the harness
set it (#1056), but `inverse_test`'s first propagation was already a harness
solve, so the claim was checked here at `00797a97` too. Since #1086 the harness
also refuses to run with the checker off. No lane has tripped it. **The engine ignores the
claim** whenever two positions resolve to one underlying variable
(`positions_alias` in `propagators.cc`). That covers every `Inverse(x, x)`, so
XCSP3's single-list `channel`, and `p1f` 2015, which posts
`inverse(ra, ra) :: domain`, are always requeued.

**It never disables itself**, even when every variable is fixed. It is then one
pass that finds nothing.

**Holes affect**: every variable, and the triggers tell the truth. The channel
asks whether one specific value is in a partner's domain, so a hole anywhere in
`y[j]` can remove a value from `x[i]`, and the `GAC` stage reads whole domains.
In the injection form the needed-value rule reads `x`'s domains value by value,
and asks `in_domain` of `y[j]` for the gaps it removes.
An `Inverse` is therefore a reason for a neighbour's interior pruning to stay
on, for every variable it touches.

### Mutable state and incrementality

**Nothing backtrackable.** The propagator keeps the `GacAllDifferentScratch`
across calls: the matching is kept and repaired between wakes, and the
components are rebuilt every run (#522). The at-most-one cache only grows. It
also keeps a needed-value buffer, created in both forms but handed to the `GAC`
stage, which overwrites it every run, only in the injection form.

**Recomputed per call: everything.** Each pass visits every value of every `x[i]`
and, in the bijection form, every `y[j]`, `Θ(Σ|D|)`, and asks one `in_domain`
each. Then it runs the whole `GAC` stage. In the injection form the
needed-value rule follows: a union-find over the needed values, then for each
one a scan of `x` for the entries that can take it, `O(m)` per needed value. Any pass that changes anything is followed by another, and a
`GAC` removal from `x` needs a further channel pass to reach `y`. On `black-hole`
2013/12 the propagator ran 33,693 times, made 80,550 passes, and ran the `GAC`
stage 77,445 times.

What maintaining it would buy is in [CPU performance](#cpu-performance): Gecode's
channel visits only variables whose domain has shrunk since it last looked, and
pushes their missing values across, instead of re-checking every value still
present (#1048, and the general question is #364).

### Interior values and optional pruning

**What this family offers:** `None.` There is one level, `GAC`, and no
`consistency::Auto`.

**What this family observes:** holes in every variable, as the inventory says.
This is the opposite of [`linear`](linear.md) and
[`comparison`](comparison.md): a variable in an `Inverse` keeps any neighbour's
optional interior pruning alive, and rightly, because removing a value from
`y[j]` removes a value from `x[i]`.

### Robustness and limits

- **Unbounded domains**: in the bijection form `define_bound` narrows every
  variable to the other array's index range at the root, so nothing after that
  sees a wide domain. A probe with `x[0] ∈ ±10⁹`, `x[1] ∈ 0..10⁹` and
  `y[1] ∈ −5..10⁹` solved and verified in 0.064 s with a 25 KB OPB (at
  `00797a97`). **In the injection form `y` keeps its declared domain**, and is
  never walked. Re-measured at `61112ed0`: three entries of `x` over `0..2`, with
  four of `y` over `±10`, and then over `±10⁹`. The needed-value rule narrows
  `y[0..2]` to `0..2` by bound pushes at the root, and leaves `y[3]` alone. Both
  runs write a 135-line proof, which verifies, taking 0.03 s and 0.01 s.
- **Negative values and starts**: first-class. `inverse_test` reruns every case
  once more with shifted starts, cycling through `(1, 1)`, `(3, −2)` and
  `(−2, 4)`. `scp_chain_inverse_offsets_sat` uses 0 and 5.
- **Degenerate shapes**: see [Semantics](#semantics). A constant outside the
  index range fails at the root through its bound row, and the `UNSATISFIABLE`
  verifies against cake's OPB too.
- **Overflow**: the only arithmetic is on `Integer`s (`n + start − 1`, the value
  offsets), and `Integer` arithmetic throws on overflow rather than wrapping. So
  an absurd start fails loudly.
- **Aliasing**: see [Variable kinds and views](#variable-kinds-and-views), and
  the strength caveat under rule 5.

### Interval efficiency

`Fine at any width`. In the bijection form, that is because the root narrows
every domain to `n` values. In the injection form `x` is narrowed the same way,
and `y`, which is not, is never walked by value: see item 1. But the propagator
is per value throughout, and that matters for the per-value ban even where it
does not matter for width.

1. **Propagation.** Two sites walk values: the channel loops, through
   `State::each_value_mutable`, over every `x[i]`, and over every `y[j]` in
   the bijection form only. Each is bounded by the other array's length, not by
   any declared width, because the bounds are pinned before the propagator
   runs. The injection form's needed-value rule reads `y[j]`'s bounds and asks
   `in_domain` only for the gaps between entries of `x`, so it is bounded by
   `m`. There is no interval structure to exploit
   in the check itself (each value has its own partner), but **the iteration
   can be by interval**: a local switch that walks `copy_of_values` interval by
   interval did the same work 18% faster on `black-hole` (#1048). The `GAC`
   stage's costs are in values and edges, bounded the same way; see
   `all_different.md`.
2. **Reasons.** One literal per channel inference. The `GAC` stage's reasons,
   and the needed-value rule's, are `generic_reason` over the Hall variables,
   which are entries of `x` and so narrow. They are built only when a proof or
   reasons are wanted.
3. **Proofs.** One line per channel inference. The at-most-ones are per value,
   `C(m, 2)` pairwise lines each, bounded by the array length rather than
   width, and with no width gate because there is no wide case. That per-value,
   per-pair cost is #944's. Since #1089 it is paid only for the values some
   Hall justification uses, which on a long search is most of them. The
   needed-value rule's removals from `y` are bound pushes plus the gaps between
   entries of `x`, so their proof is width-independent too: 135 lines at `±10`
   and at `±10⁹`, above.
4. **The audit lane**: one row, `Inverse`, `NoWidePosition`, over two arrays of
   three variables in `0..2`. **It varies nothing**: no declared domain wider
   than the index range (legal, and trimmed at the root), no starts, no views,
   no holes, and not the injection form, which is the one shape whose `y` stays
   wide. So it records the structural fact without probing the one path,
   `define_bound`, that a wide declared domain actually takes, or the injection
   form's untrimmed `y`.

## Inference catalogue

Eight rules. Rules 1 and 2 are the channel, and are this family's own; rule 2
runs in the bijection form only. Rules 3–5 are `all_different`'s generalised arc
consistent rules, run on `x` with `Inverse`'s constraint id, and are recorded
here for what differs when `Inverse` drives them. Rule 6 is the root bound.
Rules 7 and 8 arrived with #1088. Rule 7 is the injection form's replacement
for rule 2, and rule 8 is the root refutation of a repeated variable.

Four facts hold across them.

**The wire inventory.**

| Wire form | Hint type | Rules |
|---|---|---|
| `inverse:((constraint_id N))` | `hints::Inverse` | 1, 2, 8, and rule 7's single-entry case |
| `inverse:((constraint_id N) (subhint needed_value))` | `hints::InverseNeededValue` | 7 |
| `all_different:((constraint_id N))` | `hints::AllDifferent` | 3, under `Inverse`'s id |
| `all_different:((constraint_id N) (subhint hall))` | `hints::AllDifferentHall` | 4, 5, under `Inverse`'s id |
| `initial_bound` | `hints::InitialBound` | 6, with **no** constraint id |

**Nearly a third of this family's assertions are named for another family.** On
`black-hole` 2013/12 at `AssertionLevel::Inferences`, the 769,930 assertions this
constraint is responsible for are 545,768 `inverse` and 224,162 `all_different`,
all carrying `Inverse`'s id. A justifier dispatching on the hint name alone will
treat 29% of them as `AllDifferent`'s. For rules 4 and 5 it needs the scope the
at-most-ones span, which is `x`, and it gets that from the id through the
`.scp`, as `all_different.md` says. Rule 6's assertion names no constraint at
all.

**What licenses them.** Rules 1 and 2 assert one of the model's own rows, so
unit propagation on that row alone refutes the negation, and no theorem is
needed. Rule 6 asserts an order literal against a bound row over the bit sum,
which also needs the literal's definition: **Theorem 2.7**. Rules 3–5 are `all_different`'s JP 3.1, **JP 3.16** and **JP 3.17**,
with that document's departures and one more of our own. The pairwise clause
`x[a] ≠ v ∨ x[b] ≠ v`, which JP 3.1 takes from a not-equals row and JP 3.16 and
3.17 sum into at-most-ones, has no row here. It is RUP through **two**
channelling rows, which force `y[v]` to two values, and then **Theorem 2.7**
(opposing bounds on one bit sum) on `y[v]`. The thesis's procedures assume
Encoding Procedure 3.9's pairwise clauses. Here each clause is derived instead,
which is sound, but it is a step the procedures do not have. Rule 7 is ours:
JP 3.17's sum with one at-most-one left out. Rule 8 is a sequence of single
RUPs against the model's rows.

**Conflicts take two shapes here.** Rules 1–4, 6 and 7 conflict by an ordinary
inference whose literal is already false, and then the assertion is the same
line they emit when they succeed; the backtrack closes the conflict. Rules 5
and 8 are the family's only explicit contradictions, and assert `¬reason`
(rule 5 through `FalseLiteral`, rule 8 through `contradiction()` with no
reason, so its assertion is the empty clause `>= 1`). Both shapes were checked
against `a` lines at `AssertionLevel::Inferences` at `61112ed0`.

**Tightness.** No mutation lane exists in this family. #1088's commit message
reports hand mutations of rule 7 (the rule off, the needed value's at-most-one
put back into the sum, no `pol`, and an empty reason on each of its two paths)
and of rule 8's per-value RUPs, each of which made `inverse_test` fail. Those
were not re-run for this re-audit.

### Rule: channel-x

(Rule 1.)

- **Infers** — `x[i] ≠ v`, or a contradiction when that empties `x[i]`.
- **Fires when** — the `Inverse` propagator's first loop finds `v ∈ D(x[i])`
  with `i + x_start ∉ D(y[v − y_start])`.
- **Strength** — `partial`: support for `x[i] = v` in the one channelling pair
  that mentions it. Not arc consistency on each binary channelling constraint:
  `x[m]` fixed to `d` does not by itself remove `y[d] = j` for `j ≠ m`. Rule 3
  and rule 2 do that between them.
- **Algorithm** — for each `i`, each value of `x[i]`, one `in_domain`. `Θ(Σ|D(x)|)`
  per pass, in **values**, each bounded by `n`.
- **Why it is true** — if `x[i] = v` then `y[v − y_start] = i + x_start`, and that
  value is gone.
- **Proof technique** — `RUP`. The assertion **is** the model row
  `x[i] ≠ v ∨ y[v − y_start] = i + x_start`, so unit propagation on that row
  refutes its negation.
- **Reason** — `{y[v − y_start] ≠ i + x_start}`, one literal. Minimal. Built
  unconditionally, in a `ReasonLiterals` whose inline storage holds it without
  an allocation.
- **Assertion** — `x[i] ≠ v ∨ y[v − y_start] = i + x_start`, verbatim the OPB row.
- **Hint** — `hints::Inverse`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `offline`: the assertion is an input
  constraint.
- **Proof size** — one line of two literals. On `black-hole` 2013/12, 23,292
  firings.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: channel-y

(Rule 2.)

- **Infers** — `y[j] ≠ w`, or a contradiction.
- **Fires when** — the second loop finds `w ∈ D(y[j])` with
  `j + y_start ∉ D(x[w − x_start])`. **The bijection form only**: the injection
  form has no rows from `y` to `x` to justify it, and nothing to enforce, since
  `y[j] = w` does not require `x[w] = j` there. Rule 7 does its job.
- **Strength** — as rule 1, mirrored.
- **Algorithm** — as rule 1, over `y`.
- **Why it is true** — as rule 1, mirrored.
- **Proof technique** — `RUP` against the other row of the pair.
- **Reason** — `{x[w − x_start] ≠ j + y_start}`.
- **Assertion** — `y[j] ≠ w ∨ x[w − x_start] = j + y_start`, the OPB row.
- **Hint** — `hints::Inverse`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line. On `black-hole` 2013/12, 522,476 firings: most of
  this family's volume. The `GAC` stage removes from `x`, and every removal has
  to come back across to `y` through this rule.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: forced-value-deletion

(Rule 3; `all_different.md` rule 3.)

- **Infers** — `x[k] ≠ d`, where `d`'s matched position `m` is fixed to `d`.
- **Fires when** — the `GAC` stage, as in `all_different.md`.
- **Strength** — `GAC` on `AllDifferent(x)`.
- **Algorithm** — as `all_different.md`.
- **Why it is true** — `m` takes `d`, and two positions of `x` cannot share a
  value.
- **Proof technique** — `RUP`. **Different from `AllDifferent`'s**, which is
  JP 3.1 against one pairwise not-equals row. Here there is no such row.
  `x[k] = d` gives `y[d − y_start] = k + x_start` by one channelling row, and
  `x[m] = d` gives `y[d − y_start] = m + x_start` by another. Two values of one
  variable then conflict by **Theorem 2.7**. Still one RUP, two propagation
  steps deeper.
- **Reason** — `{x[m] = d}`, one literal, under the sinks-first ordering
  argument in `all_different.md`.
- **Assertion** — `x[k] ≠ d ∨ x[m] ≠ d`.
- **Hint** — `hints::AllDifferent`, with `Inverse`'s id.
- **Offline reconstructibility** — `offline`: an unhinted RUP of the assertion
  succeeds, whichever rows it goes through.
- **Proof size** — one line. On `black-hole` 2013/12, 210,932 firings.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: hall-set-deletion

(Rule 4; `all_different.md` rule 2.)

- **Infers** — `x[k] ≠ d` for every edge in no maximum matching, batched by
  component.
- **Fires when** — the `GAC` stage.
- **Strength** — `GAC` on `AllDifferent(x)`.
- **Algorithm** — Régin's, as `all_different.md`.
- **Why it is true** — a Hall set of positions uses up its values.
- **Proof technique** — `pol` then `RUP`, by **JP 3.17**, with
  `all_different.md`'s departures. The at-most-ones it sums come from
  `Inverse`'s cache. Since #1089 they are built there on first use by
  `all_different`'s `need_value_am1s`, from pairwise clauses that are each RUP
  through two channelling rows (as rule 3), and folded by
  `recover_am1_from_pairs`. See [Proof-time state](#proof-time-state).
- **Reason** — as `all_different.md`: each Hall variable's domain.
- **Assertion** — `x[k] ≠ d ∨ ¬reason`.
- **Hint** — `hints::AllDifferentHall`, with `Inverse`'s id. Its
  `value_am1_constraint_numbers` points at `Inverse`'s cache, and its
  `all_vars` at `x`.
- **Offline reconstructibility** — `hinted`, as in `all_different.md`. The
  at-most-ones span `x`, which the tool finds from the constraint id through
  the `.scp`. Each pairwise clause is an unhinted RUP whichever rows it goes
  through, so nothing else about `Inverse` needs to be known.
- **Proof size** — one `pol` per component and a RUP per deletion. The first
  time each value's at-most-one is needed, `C(m, 2)` pairwise RUPs, `m − 2`
  `pol` merges, a comment, the `ia` pin and a `del`, and never again (on
  `black-hole`, each 52-member build is 1,326 RUPs, 50 `pol`s, one `ia`, one
  `del` and a comment); values no Hall justification touches cost
  nothing. Until #1089 every value paid that at the root.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

**The polarity of `recover_am1`'s atoms**, found by the first audit.
Until #1089 `Inverse` passed `recover_am1` the atoms `x[k] ≠ v` and pairwise
lines `x[a] ≠ v + x[b] ≠ v ≥ 1`, and got back `Σ x[k] ≠ v ≥ n − 1`, which is
the at-most-one. `Among` does the same. `recover_am1`'s header documented only
the opposite convention (atoms `aₖ`, pairwise lines `¬aᵢ + ¬aⱼ ≥ 1`), and
`GlobalCardinality` uses that one. The helper's #171 shortcut, which emits
`0 ≥ 1` when two atoms are false, is only right for the negated convention.
`GlobalCardinality`'s bounds arm, over a constant, can reach it, and then emits
a line VeriPB rejects (#1046, found by this audit). #1089 moved `Inverse` off
`recover_am1` and corrected the header to describe both conventions and say
which one the shortcut needs. **#1046 itself is still open**: the header now
states the constraint, but `GlobalCardinality` still breaks it.

### Rule: hall-violator

(Rule 5; `all_different.md` rule 1.)

- **Infers** — a contradiction.
- **Fires when** — the `GAC` stage's matching leaves a position of `x`
  uncovered.
- **Strength** — `GAC` on `AllDifferent(x)`, when `x`'s positions are
  different variables. **Together with rules 1 and 2 at their common fixpoint,
  `GAC` on the bijection**, when no underlying variable appears twice anywhere:
  at the fixpoint `v ∈ D(x[i])` exactly when `i ∈ D(y[v])`, and `x`'s `n`
  positions have `n` values. So a supporting matching for `x[i] = v` is a
  permutation, and its inverse is a support in `y`. **Together with rules 1 and
  7, `GAC` on the injection form**, under the same condition. A matching
  supporting `x[i] = v` names only values `i` can reach through rule 1, and
  leaves every other entry of `y` free. A value `j` that some matching avoids
  leaves `y[j]` entirely free. A value every matching takes restricts `y[j]` to
  the entries that can take `j`, and each of those is on some matching. The
  tests check this at every node, for both forms
  (`solve_for_tests_checking_gac`). Re-checked for this re-audit by brute force
  at the root. Random bijections and injections of up to four entries of `x`
  were posted, with `y` one or two longer in the injection form and `y`'s
  domains straying outside `x`'s indices. Across 6,000 instances over two
  seeds, all 4,973 whose root did not fail matched the brute-force supports
  exactly. **With aliasing it is not**, because the
  matching treats aliased positions as independent. `Inverse(x, x)` over #413's
  triangle (`{1, 2}`, `{0, 2}`, `{0, 1}`) has no solution, and needs three
  recursions and two failures to prove it. And `x = [a, a + 1, b]` with
  `a ∈ 0..1`, `b ∈ 0..2`, over `y` in `0..2`, keeps `b = 1` at the root, though
  its only solutions are `(a, b) = (0, 2)` and `(1, 0)`.
- **Algorithm** — as `all_different.md`.
- **Why it is true** — Hall's theorem.
- **Proof technique** — `pol` then `RUP`, by **JP 3.16**, with the same
  at-most-ones as rule 4.
- **Reason** — the violator's domains.
- **Assertion** — `¬reason`.
- **Hint** — `hints::AllDifferentHall`, with `Inverse`'s id.
- **Offline reconstructibility** — `hinted`, as rule 4.
- **Proof size** — as rule 4. Rules 4 and 5 together carry 13,230 `hall`
  assertions on `black-hole` 2013/12, averaging 35.5 literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: index-range-bound

(Rule 6.)

- **Infers** — `x[i] ≥ y_start`, `x[i] ≤ y_start + n − 1`, and in the
  bijection form the same for `y` with `x_start`, at the root. The injection
  form leaves `y` unbounded.
- **Fires when** — `define_bound`'s initialiser, for each bound the declared
  domain exceeds.
- **Strength** — `partial`: the two bounds a variable takes from the other
  array's index range, which is a unary part of the relation and which this
  leaves `GAC`. It says nothing about `Inverse` as a whole; that is rule 5's
  entry. (The first audit wrote `bounds(Z)` here, which names a level of the
  whole constraint and was not what the rule achieves.)
- **Algorithm** — `O(1)` each.
- **Why it is true** — `x[i]` indexes `y`.
- **Proof technique** — `RUP` against the bound row `define_bound` added to the
  OPB.
- **Reason** — none: it holds at the root.
- **Assertion** — the bound.
- **Hint** — the solver-wide `hints::InitialBound`, which carries no constraint id.
- **Offline reconstructibility** — `offline`: the assertion is an input row.
- **Proof size** — one line per trimmed bound.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: needed-value

(Rule 7. The injection form only; added by #1088.)

- **Infers** — for a value `j + y_start` of `y`'s index set that **every
  matching of `x` takes**: `y[j]` can only name an entry of `x` that can still
  take that value. Let `first` and `last` be the lowest and highest such
  entries, as indices numbered from `x_start`. Then `y[j]` gets the bound pushes
  `y[j] ≥ first` and `y[j] ≤ last`, and `y[j] ≠ v` for each value `v` in a gap
  between two such entries. If only one entry `x[i]` can take the value, and it
  is already fixed to it, the rule instead infers `y[j] = i + x_start`.
- **Fires when** — the `Inverse` propagator, after the `GAC` stage, in the
  injection form, for each needed value whose `y[j]` still has something to
  lose. The `GAC` stage reports the needed values. The injection form always
  has more values than entries, so these are the values that no alternating
  path reaches from a value the matching leaves free.
- **Strength** — with rules 1 and 3–5, `GAC` on the injection form when no
  underlying variable appears twice; see rule 5.
- **Algorithm** — the needed values come out of the `GAC` stage's existing
  sweep at `O(n)` extra. Then a union-find over them groups the entries of `x`
  whose domains lie inside the needed values into components, linked by the
  values they share. After `GAC` an entry's domain is either inside the needed
  set or disjoint from it. For each needed value, a scan of `x` finds the
  entries that can take it: `O(m)` per needed value, in **entries**, and the
  gaps it walks lie inside `x`'s index range.
- **Why it is true** — the Hall-set argument. After `GAC`, let `H` be the
  entries whose domains lie within the needed values `N`. Every matching takes
  every value in `N`, and only entries in `H` can take them, so `|H| = |N|` and
  `H` is a Hall set that uses up exactly `N`. So does each connected component
  of it, on its own values. So in every solution some entry of the needed
  value's component takes it, and the row from that entry to `y` makes `y[j]`
  name it. A `y[j]` naming any entry that cannot take the value would leave the
  component's entries fewer values than there are entries.
- **Proof technique** — `pol` then `RUP`, **ours**: JP 3.17's Hall-set sum with
  one term left out, in the new shared helper
  `justify_all_different_hall_set_needs_value`. The sum adds each component
  entry's at-least-one, over the values its domain still holds, and the
  at-most-one of every component value **except the needed one**. The
  at-most-ones are the same lazily built ones as rule 4. Summing all of them
  would be the violator's contradiction. Leaving one out leaves exactly one unit
  of slack, which says that some component entry takes the needed value. Each
  deletion is then one RUP. Assuming `y[j]` names something else, the reason
  falsifies every component entry that cannot take the value, and the row
  from `x` to `y` rules out each one that can. The single-entry case is a plain
  `RUP` against that entry's row. When two views of one variable split a
  component unevenly, the sum falls back to the whole Hall set, which is still
  as big on each side.
- **Reason** — `generic_reason` over the component's entries: their domains.
  The single-entry case's reason is `x[i] = j + y_start`, one literal.
- **Assertion** — one line per removal, `removal ∨ ¬reason`: for example
  `y[j] < last + 1 ∨ ¬reason`. Checked at `AssertionLevel::Inferences` on three
  entries of `x` over `0..2` and four of `y` over `0..3`. Each of `y[0..2]`
  gets `¬(y[j] ≥ 3) ∨ ¬(x[0..2] ∈ [0, 2])`, the reason written as two bound
  literals per entry.
- **Hint** — `hints::InverseNeededValue`, wire form
  `inverse:((constraint_id N) (subhint needed_value))`, whose only field is
  `originator`. The single-entry case carries plain `hints::Inverse`.
- **Offline reconstructibility** — `hinted`. The subhint names the procedure,
  and the assertion names `y[j]`, hence the needed value. The reason names the
  component's entries, and the union of their domains is its values. The
  at-least-ones and at-most-ones are all derivable from the model's rows from
  `x` to `y`, found through the constraint id. The single-entry case is
  `offline`: its assertion is one of the model's rows.
- **Proof size** — one `pol` per needed value with something to remove, plus
  one RUP per removal, plus any at-most-one not yet in the cache. The shared
  helper asks for the at-most-ones of all the component's values, the needed
  one included, although this sum leaves that one out. It is cached, and in a
  component of two or more values the other values' removals use it. (A
  one-value component has one entry, which `GAC` has fixed, and takes the
  single-entry path.) Independent of `y`'s width: 135 lines at `±10` and at `±10⁹` under
  [Robustness and limits](#robustness-and-limits).
- **Gaps** — `None.`
- **Tightness** — `Not shown` by a lane. #1088's commit reports five hand
  mutations, each caught by `inverse_test`, which was not re-run here; see the
  catalogue's opening.

### Rule: repeated-variable-contradiction

(Rule 8. Added by #1088.)

- **Infers** — a contradiction at the root.
- **Fires when** — the constructor found the same non-constant handle twice in
  `x`, or twice in `y` in the bijection form. Then this initialiser replaces
  the propagator; `prepare()`'s `define_bound` initialisers are still
  installed. A `StatsNote` at `Important` level says so. Two identical views
  are the same handle and reach this rule. Two views that differ in offset or
  negation do not.
- **Strength** — `GAC`, in the trivial sense: the constraint has no solution,
  and the root says so.
- **Algorithm** — the constructor's pair loop, then one RUP per value of the
  other array's index range.
- **Why it is true** — a variable in two entries of `x` takes one value `j`,
  and then the two rows from `x` to `y` ask `y[j]` to name both entries. A
  repeat in `y` is the mirror, through the rows from `y` to `x`, which only
  the bijection form has.
- **Proof technique** — `RUP sequence`, ours: one RUP of `var ≠ v` at
  `Temporary` for each value `v` of the other array's index range, each through
  the two rows that name it, and then the closing RUP of `>= 1`, since
  `define_bound`'s rows confine the variable to that range.
- **Reason** — none.
- **Assertion** — the empty clause, `>= 1`, through `contradiction()`. Checked
  at `AssertionLevel::Inferences`: `a >= 1::inverse:((constraint_id _1));`.
- **Hint** — `hints::Inverse`.
- **Offline reconstructibility** — `hinted`. The assertion names nothing, so
  the constraint id is what leads to the `.scp`, and the repeat is visible in
  its lists. From there, each lemma is one RUP.
- **Proof size** — one line per value of the other array's index range and the
  justification's closing `rup >= 1`, then a `del range` of the temporaries, a
  comment and the tracker's own `rup >= 1`, once. With `x = [a, a, c]` over
  three values the justification is four lines and the footprint seven.
- **Gaps** — `None.` `scp_chain_inverse_aliased_unsat` takes it through the
  whole `cake_pb_cp` chain.
- **Tightness** — `Not shown` by a lane. #1088's commit reports that the
  per-value RUPs are load-bearing under mutation; not re-run here.

## Evidence

### Tests

| Lane | What it checks |
|---|---|
| `inverse_constraint` | `inverse_test`. Since #1088: 39 instances, each at starts `(0, 0)` and at one shifted pair, with and without proofs, under `solve_for_tests_checking_gac`, so `GAC` at every node. They are 23 fixed rows (13 bijections, and 10 injections, including the #1047 instance, an empty `x`, and four Hall-set rows that make rule 7 load-bearing), 8 random bijections of 2–4 entries and 8 random injections of 1–3 entries into one or two more. Then seven aliased cases without the `GAC` check: repeats in `x` and in `y` in both forms, an involution, and two and three views of one variable. And the longer-first constructor throw |
| `inverse_constraint_view_mixed` | the same, positions wrapped in views of fresh variables; the aliased cases run in the bare configuration only |
| `exception_test` | a first array longer than the second throws at construction |
| `solve_test` | a repeated variable in `x` reports its `StatsNote` |
| `scp_chain_inverse_sat`, `scp_chain_inverse_offsets_sat`, `scp_chain_inverse_aliased_unsat` | see [Cake conformity](#cake-conformity) |
| `xcsp_channel_self`, `xcsp_channel_two` | the two XCSP3 list forms, three variables each |
| `xcsp_channel_unequal`, `xcsp_channel_unequal_free`, `xcsp_channel_aliased` | the injection form, against ACE's 12 and 120 solutions, and a repeated entry, which is unsatisfiable (#1047) |
| `minizinc-inverses`, `-offset`, `-shapes`, `-negative`, `-unequal`, `-aliased` | non-1-based and enum-indexed arrays, an array that is its own inverse, the same three variables in two orders, negative index sets and empty arrays, unequal lengths (#997, #1011), and two equated entries (#1047), where the lane checks that the repeat reaches `glasgow_inverse`. `inverses` and `-offset` compare against MiniZinc's default solver, `-shapes` against it and the standard library's decomposition, `-negative` and `-unequal` against the decomposition alone, and `-aliased` expects `UNSATISFIABLE` |
| `talent` | the example, with its proof verified |
| `large_domain_audit` | one `NoWidePosition` row, guard build only |

At `61112ed0` the 16 lanes that `ctest -R 'inverse|channel'` selects all pass,
and so does `talent`. That run had default caps, MiniZinc 2.9.7, and
`cake_pb_cp` and `opbdiff` on the path. The chain case was confirmed to run
cake's verified step rather than the fallback. VeriPB runs in both data-driven
lanes. At `--seed=1`, `inverse_test` checks 85 proofs (39 instances twice, plus the 7 aliased cases), and all verify. Both
lanes are seeded (`establish_and_announce_seed`) and byte-reproducible with
`--seed=N`. (At `00797a97`, the first audit's 12 lanes passed with caps off,
and `--seed=1` checked 42 proofs.)

**Runtime caps.** No lane sets or clears one. **The default caps never fired
here at `00797a97`**, the first family in the arc where that was true: three
unseeded runs of each data-driven lane, with the default 300-solution and
1,500-recursion caps passed in the environment, printed no truncation from a
local-only print in `solve_for_tests_with_callbacks`, which fired 16 times at
`GCS_TEST_MAX_SOLUTIONS=2`. That print was not re-run at `61112ed0`. The
largest expected solution count across seeds 1–5 is 146 there, under the
300-solution cap; the recursion cap was not re-checked. The instances are
small: at most five entries of `x`, and six of `y` in the injection form. So the
default capped run very probably still checks completeness here.

**Rules the tests reach**, from local counters at `00797a97`: rules 1 and 2,
and the `GAC` stage, in both data-driven lanes; the `GAC` stage's rules were
counted together. Rule 6 is reached by the one fixed row that declares a
position wider than its index range (a single position over `0..5`); the random
rows draw every domain inside `0..n−1`. Rules 7 and 8 were not counted. The
four Hall-set injection rows exist to make rule 7's `pol` load-bearing, as
#1088's PR description and the test's own comment say. Rule 8 is reached by
three aliased rows, which are the unsatisfiable ones: a repeat in `x` in each
form, and a repeat in `y` in the bijection form. The other four have 4, 4, 8
and 60 solutions, and the two view cases cannot reach it.

**What the tests do not cover:**

- **The injection form through the verified chain.** `cake_pb_cp` does not
  know `inverse_injective`, so no `scp_chain` case can post it; its proofs are
  checked by VeriPB against GCS's own OPB only.
- **A wide `y` in the injection form**, which is the one place a declared
  domain survives the root; only this re-audit's probe. The audit lane's single
  row is a narrow bijection.
- **A view of another position under the `GAC` check.** Since #1088
  `inverse_test`'s aliased cases post two and three views of one variable, and
  `Inverse(x, x)`, but check solutions only, rightly, since the propagation is
  weaker there. The shapes the first audit's probe covered beyond those
  (negated views, a variable shared across the arrays through a negated view)
  are still only the probe's.
- **Anything of realistic size.** Five entries of `x` at most, so each lazy
  at-most-one is a handful of lines, and the per-call cost that dominates
  `black-hole` is invisible.
- **Assertion levels.** Nothing checks that at `Inferences` every assertion
  carries `Inverse`'s id.

### Benchmarks and examples

- **In-repo**: `examples/talent`, which links scenes to slots with one
  `Inverse` among many other constraints; its lane verifies a proof. No
  benchmark isolates the family.
- **The corpus.** Of one instance of each of 298 MiniZinc Challenge models,
  twelve reach `Inverse` and flatten: `black-hole` (2011, 2013, 2025),
  `elitserien` (2014, 2016, 2018, 2023), `p1f` 2015, `p1f-pjs` (2020, 2021) and
  `tdtsp` (2015, 2017). The corpus JSON used by earlier audits predates #997 and
  no longer parses. These were flattened again with the current library.
- **For CPU**: `black-hole` 2013/12 (3 s), 2013/18, 2011/9 and 2011/20 (74–134
  s). `Inverse` is 87% of the solve on 2013/12 and 88% on the 2025 instance. On
  the four instances compared with Gecode, it searches the same number of nodes
  to the same first solution. `elitserien` spends 7–15% of its solve in
  `Inverse` and most of it outside propagation; `p1f` 13–15%; `tdtsp` nothing.
- **For proofs**: `black-hole` 2013/12, a 300 MB proof that VeriPB checks in 15
  minutes (at `00797a97`). The scaling probe below for what the removed root
  at-most-ones cost.

### CPU performance

All at `00797a97`, Release, GCC 15.2.0, fataepyc-09 (EPYC 7643, boost off),
pinned with `numactl --cpunodebind=0 --membind=0 taskset -c N setarch -R`,
2026-09-23, one run each unless stated. Counters were compiled out for timing.

**Against Gecode 6.3.0**, through `minizinc --solver gecode` on the same model
and data. `black-hole` writes `inverse(x, y) :: domain`, so Gecode posts its
domain-consistent channel.

| instance | nodes (both) | GCS | Gecode | ratio | GCS propagations | Gecode propagations |
|---|---|---|---|---|---|---|
| 2013/12 | 14,031 | 3.035 s | 0.366 s | 8.3× | 400,311 | 651,867 |
| 2013/18 | 312,905 | 74.5 s | 7.20 s | 10.4× | 10,357,959 | 14,369,803 |
| 2011/9 | 346,973 | 90.2 s | 9.75 s | 9.2× | 10,369,837 | 16,207,493 |
| 2011/20 | 916,488 | 134.3 s | 12.9 s | 10.4× | 17,862,592 | 26,666,085 |

Equal node counts and the same first solution on all four. That is what equal
strength on this model would give, though it does not show the trees are the
same node for node. The two solvers count propagations differently, but ours is
not the larger. Three other instances fail at Gecode's root, and three do not
finish in 120 s.

**Where the time goes**, on 2013/12. `GCS_PROPAGATOR_STATS=time`: `Inverse`
2.654 s of 3.052 s, over 33,693 calls, 79 µs each. `perf`:
`propagate_gac_all_different` 15.6%, the per-value generator 16.6%,
`IntervalSet::each` 12.0%, `State::in_domain` 10.0%, the propagator's own
lambda 8.2%, `find_strongly_connected_components` 5.1%, and allocation about 6%.
So the per-value generators are 29% and the `GAC` stage about a fifth.

**An interval walk alone** (`copy_of_values`, then `each_interval` and a plain
loop), as a local switch: 2.463, 2.470 and 2.476 s against 3.011, 2.995 and
3.026 s, same nodes. That is 18%, and leaves the gap to Gecode at about 6.7×.

**Why Gecode is faster.** Its domain channel (`gecode/int/channel/dom.hpp`) has
the same shape as ours: channel, domain-consistent `distinct` on `x` only,
channel back. But it keeps each view's last-propagated size, visits only views
whose size changed, and walks the complement of their domain within the
bounds it last saw, pruning the partner. It makes one ordered pass rather than looping, keeps its `distinct`
graph between calls, and handles an assignment-only event by value propagation
alone. Ours re-checks every value still present, at least twice per effectful
call, and rebuilds the `AllDifferent` components each time (#522). #1048 has the
options.

**What this benchmark exercises**, on 2013/12: rules 1 and 2 (23,292 and
522,476 firings, from counters), and from the `Inferences` proof's assertions,
210,932 forced-value deletions and 13,230 Hall assertions. Rule 6 never fires: every domain is
declared `1..52`.

### Proof performance

**`black-hole` 2013/12**, 52 cards, 14,031 nodes. The first four rows are the
first audit's, at `00797a97`; the last is this re-audit's.

| | solve | proof | VeriPB |
|---|---|---|---|
| proofs off | 3.04 s | — | — |
| `AssertionLevel::Off` | 6.47 s | 1,416,686 lines, 300 MB | 908.6 s, `VERIFIED SATISFIABLE` |
| `Off`, root at-most-ones skipped (local switch) | 6.48 s | 1,391,794 lines, 285 MB | 919.9 s, `VERIFIED SATISFIABLE` |
| `AssertionLevel::Inferences` | 6.51 s | 1,251,276 lines, 310 MB | 6.4 s, `UNDER ASSERTIONS SATISFIABLE` |
| `AssertionLevel::Off` at `61112ed0` | 6.22 s | 1,391,794 lines, 285 MB | 738.3 s, `VERIFIED SATISFIABLE` |

At `61112ed0` the ordinary proof is **line for line the length the local switch
predicted**: #1089 made that switch the code. It builds 32 of the 52
at-most-ones, one `ia` line each, and the search is the same 14,031 nodes and
13,998 failures. The solve and check times are single runs on different
days, and this one unpinned, so they are not a comparison
with the rows above.

Checking the justified proof takes **140 times** as long as checking the
asserted one, and 300 times the solve without proofs. Its 1.30 million RUP
steps carry no VeriPB antecedent hints. Where the checking time goes was not
measured further.

**Assertions at `Inferences`**, by wire form: `inverse` 545,768 (two literals
each), `table` 399,321, `all_different` 210,932 plain and 13,230 `hall`,
`comparison` 25,898, and the solver's own `backtrack` 13,998 and `solx_block` 1.
This constraint is responsible for 769,930 of 1,209,148, or **64%**. The
`inverse` count equals the counters' firings of rules 1 and 2 exactly.

**Own against shared**, as a function of `n`: a probe posting one `Inverse` over
full domains and taking the first solution in input order. That is the identity
permutation, where no Hall set fires. All verified. The first three columns
are the first audit's, at `00797a97`; the last is re-measured at `61112ed0`.

| n | OPB rows | proof lines at `00797a97` | of which root at-most-ones | proof lines at `61112ed0` |
|---|---|---|---|---|
| 4 | 192 | 152 | 32 | 120 |
| 8 | 704 | 650 | 240 | 410 |
| 16 | 2,688 | 3,470 | 1,952 | 1,518 |
| 32 | 10,496 | 21,782 | 15,936 | 5,846 |
| 64 | 41,472 | 152,102 | 129,152 | 22,950 |

The `61112ed0` column is exactly the first audit's figure with the root
at-most-ones taken away, as #1089's own measurement also found. It is
`1.5·n(n − 1)` lines of this family's own inferences (rules 1–3), plus the
shared literal layers, `4n² + 8n` (`2n²` order-literal `pol`s, `2n² + 4n`
`core` moves, `4n` unit bounds), plus 6 fixed header and footer lines. The at-most-ones had added exactly
`n·C(n, 2) + 2n` (pairwise RUPs, folds and deletions), 85% of the proof at
`n = 64`. On `black-hole`, where the search needs 32 of the 52 at-most-ones
eventually, removing them saved only 1.8% of the lines. At `00797a97` a local
switch doing the same made checking no faster. On `inverse_constraint` at
`--seed=1` it saved 11%.

**The injection form**, the same probe with `x` of `m` entries into `y`'s `n`
indices, `y` over `x`'s indices, branching on `x` then `y`: 152 lines for 4 into
6, 1,430 for 16 into 18, and 19,502 for 64 into 66, all verified, at
`61112ed0`. #1089's own figures for the same sizes through the XCSP3 binding are
157, 1,459 and 19,627; the shapes differ in branching and in `y`'s domain. That
PR measured the saving as `n·C(m, 2) + 2n`, one at-most-one per value of `y`'s
index set, which is 133,188 lines at 64 into 66.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified, and nothing is asserted at
`AssertionLevel::Off`. The propagator is the same with proofs on and off. At the
assertion levels, the Hall assertions (rules 4 and 5) carry an `all_different`
hint whose at-most-one cache is empty, so a reconstructor derives the
at-most-ones itself, over the scope it finds from the constraint id. Rule 7's
`needed_value` assertions are in the same position, with the extra step of
leaving the needed value's at-most-one out.

**Not a gap, but a limit on checking**: the injection form's `.scp` keyword is
unknown to `cake_pb_cp`, so its proofs are checked against GCS's own OPB and
never through the verified chain.

### Known limitations

- **Slow**: 8–10 times Gecode's time at equal node counts, where it dominates
  (#1048; measured at `00797a97`, and neither fix since touches the per-call
  cost).
- **The injection form cannot go through `cake_pb_cp`**, which does not know
  `inverse_injective`.
- **A first array longer than the second is rejected**, not answered: the
  constructor throws, and XCSP3 reports `s UNSUPPORTED`. The XCSP3
  specification does not define that shape.
- **Not generalised arc consistent under aliasing.** `Inverse(x, x)`, or an
  array holding two views of one variable, can need search to refute.
  `SymmetricAllDifferent` is no stronger on #413's triangle.
- **No reified form.**

### Next steps

Ranked by what they buy for what they cost.

1. **#1046** — not this family's, but found here: `GlobalCardinality` proofs
   can abort (both arms) or be rejected (the bounds arm) when its array holds a
   constant, in 135 of 300 random instances (at `00797a97`). It is reachable
   from MiniZinc, and it is the most serious finding of this audit. #1089
   documented the constraint in `recover_am1`'s header but did not fix it.
2. **#1048** — walk intervals (18%, and it removes this family's only per-value
   iteration), then make the channel incremental and push-based, and skip `GAC`
   runs that cannot find anything. Re-measure on the four `black-hole` instances
   above. A real project; the first step is an afternoon.
3. **Tests.** A larger instance in `inverse_test` (a few dozen positions, so the
   per-call cost is visible), a wide declared domain in the audit-lane row plus
   an injection-form row with a wide `y`, and an inferences-level check that
   every assertion carries `Inverse`'s id. Unfiled.
4. **Cake support for the injection form**, which would let an `scp_chain` case
   post it. That is a change to `cake_pb_cp`, not to this repository. Unfiled.

Done since the first audit: #1047 (#1088) and #1049 (#1089); see the
[re-audit](#re-audit-2026-09-25).

## Prior art

Channelling between a permutation and its inverse is the classic dual-model
constraint. Hnich, Smith and Walsh (*Dual modelling of permutation and
injection problems*, JAIR 2004) compare the propagation strengths of
channelling and `AllDifferent` on either side. The fact used here, that
channel consistency together with `GAC` on `AllDifferent(x)` is `GAC` on the
pair when every position is a different variable, has a short argument, given
under rule 5. It is why the propagator runs
`AllDifferent` on one side only, which dacd1eea ("Only need to alldiff on one
side", 2024) made so. Régin (1994) is the matching algorithm. Gecode's `channel` is the
reference implementation. On the proof side, nothing is published for `Inverse`
specifically. The channel is a single RUP against its own model row, and the
`AllDifferent` part is McIlree's JP 3.16 and 3.17, with the at-most-ones
derived through the channelling rows rather than read from a clique encoding.
That step is ours. So are the injection form's needed-value rule, whose `pol`
is JP 3.17's sum with one at-most-one left out, and the repeated-variable
refutation. Hnich, Smith and Walsh's title covers injection problems too; how
their dual model represents a value that nothing takes was not compared with
the injection form, which leaves that entry of `y` unconstrained.

## Further reading

- [`all_different.md`](all_different.md): the generalised arc consistent
  algorithm, its Hall justifications, the sinks-first order that the proof
  depends on under aliased views, and the history of `Inverse`'s value-set bug.
- [`justification-techniques.md`](../justification-techniques.md): the
  unit-propagation facts behind JP 3.1, 3.16 and 3.17.
- `gcs/constraints/all_different/symmetric_all_different_test.cc`: the instances
  on which channelling plus bipartite matching is weaker than an involution's
  `GAC` (#413's triangle), which apply to `Inverse(x, x)` as they stand.

## Developer commentary

**Checking a helper's callers found a bug in another family.** Reading how
`Inverse` called `recover_am1` (it no longer does) showed that its three callers disagree about the
atoms' polarity, and the helper's shortcut for two false atoms is right for only
one of them. A 300-seed sweep of `GlobalCardinality` with constants in its
array then found the wrong `0 ≥ 1` in 8 runs, and an unrelated missing case
(an at-least-one over a constant) aborting 127 more. The counting audit had
read every rule of that constraint and missed both, because its tests put
constants only in all-constant rows. A shared helper's contract is worth
checking against every caller whenever one of them is being audited.

**A constraint built from another family's propagator inherits its proof
precondition silently.** JP 3.16 and 3.17 assume a clique of pairwise
not-equals rows. `Inverse` has none, and its proofs verify anyway, because each
pairwise clause is one more unit-propagation step away through the channelling
rows. That is fine for VeriPB, and invisible to a justifier that dispatches on
the hint name, which is `all_different`'s. The constraint id is what tells the
two apart.

**A one-directional channel gets its reverse pruning from a Hall set, not a
row.** Dropping the rows from `y` to `x` for the injection form also drops the
only thing that justified rule 2. What replaces it, restricting `y[j]` to the
entries that can take a value every matching takes, is a counting argument,
and the `GAC` stage already knew which values those were. #1088 exposed that
from `propagate_gac_all_different` rather than recomputing it, and justified
it by reusing the Hall sum with one term missing. Both choices kept the new
rule to one function of about 90 lines, and the brute-force check above found it `GAC` on every
instance tried.
