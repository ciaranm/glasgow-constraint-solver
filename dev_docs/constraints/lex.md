# `Lex`: one array is lexicographically above another, optionally reified

> **Maturity** production (`LexCompareGreaterThanOrMaybeEqual` and its twelve
> named forms); benchmarking only (`LexSmartTable`) ·
> **Audited** 2026-09-29 at `c9ceea25` ·
> **Open issues** none filed by this audit yet; see [Next steps](#next-steps)
> for what it would file, first of all a **proof VeriPB rejects**: under the
> general constructor's `NotIf`, a correct inference of the condition's negation
> is justified under the wrong half of the condition. Already open and touching
> this family: #1121
> (`LexSmartTable`'s hints say `unnamed`), #1128 (`LexSmartTable`'s trees each
> copy the whole scope), #833 (the large-domain policy), #868 (cross-solver
> comparisons; this document gives one, by hand). Tracked under #871.

`LexCompareGreaterThanOrMaybeEqual(vars_1, vars_2, cond, or_equal)` enforces
`vars_1 >_lex vars_2`, or `≥_lex`, under a reification condition. Twelve
named classes construct it: `LexGreaterThan`, `LexGreaterEqual`,
`LexLessThan` and `LexLessThanEqual`, each plain, `If` and `Iff`; the `Less`
forms swap their arguments first. One stateful propagator maintains the
leftmost position `α` that is not yet fixed equal, and it is Frisch, Hnich,
Kızıltan, Miguel and Walsh's algorithm on bounds. The proof is a
flag-per-position encoding that matches `cake_pb_cp`'s, and each inference is
a short sequence of RUP lemmas. `LexSmartTable`, the other class here, is the
same constraint written as a [`SmartTable`](smart_table.md) and kept for
benchmarking.

Five things to know before touching it.

- **Under `NotIf`, VeriPB rejects the proof.** When the condition is open and
  the bounds show the comparison holds, the solver correctly infers the
  condition's negation, but states the justifying lemmas under the condition's
  negation, over rows that `NotIf` half-reifies on the condition itself. So the
  lemmas are not RUP. No named class exposes `NotIf`; the general constructor
  and the `.scp` reader (`…_not_if`) do. 50 of 160 random `NotIf` proofs
  fail: exactly the 50 in which this inference writes its scaffold lemma,
  which it does when the common prefix is non-empty. Every `If`, `Iff` and
  `MustNotHold` proof tried verifies. See
  [Proof-logging gaps](#proof-logging-gaps).
- **It is generalised arc consistent on distinct variables, holes and unequal
  lengths included**, and slow per call: every call copies both arrays into one
  and materialises a bounds reason over all of them, whether or not anything
  reads it. Building the reason only when it is needed gives **1.58 times** the
  node throughput on `zephyrus` 2016 and **3.0 times** on `mqueens` 2014; the
  reason's content does not change, and the two builds' proofs on `zephyrus`
  and their first intermediate solutions on `mqueens` agree.
- **Its proofs are quadratic in the array length per inference.** Each
  justification writes `O(n)` lemmas, and each lemma carries the whole-scope
  reason of `O(n)` literals. At `n = 200`, 211 inferences make a 654 MB proof.
  `opd` posts arrays of 350.
- **A repeated variable weakens it, and a variable shared at one position can
  cost the width of its domain.** Repeats within one array, sharing at one
  position, and sharing across positions all lose generalised arc consistency.
  The one width hazard is sharing at one position, which is treated as if the
  pair could still differ: `[z, a] ≥_lex [z, b]` with `a < b` forced is
  unsatisfiable, but the propagator only finds that out after pushing `z`'s
  bounds in by one value at each end per call, 5 million calls at a domain of
  width 10⁷. Lex-leader symmetry breaking shares variables at and across
  positions, and seven corpus models post it with repeated variables, over
  small domains.
- **`LexSmartTable` ignores the arrays' lengths,** so when `vars_1` is the
  longer it gives wrong answers: `[a₀, a₁, a₂] >_lex [b₀, b₁]` over `0..2` has
  135 solutions and it finds 108. Only the C++ API and the `.scp` reader reach
  it.

## What it is

### Semantics

`vars_1 >_lex vars_2` compares position by position from the front. At the
first position where the two differ, the larger element wins. If the common
prefix, of length `n = min(|vars_1|, |vars_2|)`, is entirely equal, **the
longer array is the greater**, and two arrays of equal length are equal. So
`[1, 2] <_lex [1, 2, 0]` holds, and `[1, 2, 0] ≤_lex [1, 2]` does not. The
arrays need not be the same length. The strict form holds when the equal-prefix
case is decided in `vars_1`'s favour; the non-strict form also accepts equality.

The reification condition is any `IntegerVariableCondition`: `If{cond}` means
`cond ⇒ C`, `Iff{cond}` means `cond ⇔ C`. The general constructor also takes
`MustNotHold` and `NotIf`, which no named class exposes.

- **Empty arrays:** `[] ≥_lex []` holds, `[] >_lex []` does not, `[x] >_lex []`
  holds, `[] >_lex [x]` does not (#254 made the empty operand safe).
- **Constants** are ordinary operands.
- **A shared variable** is accepted anywhere: `[x, y] ≤_lex [x, z]` reduces to
  `y ≤ z`. See [Robustness and limits](#robustness-and-limits) for what it
  costs.

`LexSmartTable(vars_1, vars_2)` is documented as `vars_1 >_lex vars_2`, but
means strict lex on the common prefix only: see [its
section](#lexsmarttable).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `LexLessThan` | ✓ `fzn_lex_less_int`, `fzn_lex_less_bool` | ✓ `lex` with `lt`[^xlex] | ?[^gcspy] | ✓ `lex_less_than` | also `lex_greater`, `lex_chain_less`, `strict_lex2`[^mznlex] |
| `LexLessThanEqual` | ✓ `fzn_lex_lesseq_int`, `fzn_lex_lesseq_bool` | ✓ `lex` with `le` | ?[^gcspy] | ✓ `lex_less_equal` | also `lex_greatereq`, `lex_chain_lesseq`, `lex2`[^mznlex] |
| `LexGreaterThan`, `LexGreaterEqual` | via the `Less` forms[^mznlex] | ✓ `lex` with `gt`, `ge` | ?[^gcspy] | ✓ `lex_greater_than`, `lex_greater_equal` | |
| `LexLessThanIff`, `LexLessThanEqualIff` | ✓ `fzn_lex_less_*_reif`, `fzn_lex_lesseq_*_reif` | n/a | ?[^gcspy] | ✓ `…_iff` | |
| `LexGreater*Iff` | via the `Less` forms | n/a | ?[^gcspy] | ✓ `…_iff` | |
| the four `If` forms | n/a: there is no `_imp` builtin, so MiniZinc uses the `_reif` one in a half-reified context | n/a | ?[^gcspy] | ✓ `…_if` | |
| `MustNotHold`, `NotIf` | — | — | — | ✓ `…_not`, `…_not_if` | general constructor only; no cake counterpart |
| `LexSmartTable` | — | — | — | ✓ `lex_smart_table` | C++ and `.scp` only |

[^mznlex]: The standard library defines `lex_greater(x, y)` as
    `lex_less(y, x)` and `lex_greatereq` likewise, `lex_chain_less(a)` and
    `lex_chain_lesseq(a)` as `lex_less` / `lex_lesseq` between adjacent
    columns, and `lex2` / `strict_lex2` as a lex chain on the rows and another
    on the columns. All of them arrive at the four builtins in
    `minizinc/mznlib/fzn_lex_*.mzn`.

[^xlex]: `buildConstraintLex` over several lists posts the relation between
    each adjacent pair; `buildConstraintLexMatrix` posts it between adjacent
    rows **and** adjacent columns, which is XCSP3's `lexMatrix`.

[^gcspy]: `gcspy` binds nothing in this family.

Positions are all that matter, and MiniZinc compares "from first to last
element, regardless of indices", as this class does, so no index set can be
mistranslated. `lexltunequal.mzn`, `lexgtunequal.mzn`, `lexlequnequal.mzn` and
`lexgequnequal.mzn` pin the unequal-length semantics against the reference
solver, and `lexreif.mzn` the reified forms.

### Options

`None.` There is no consistency tag.

### Variable kinds and views

Plain variables, constants and views of either sign. The propagator reads
`bounds()` only. The proof handles views: the half-reified equality and
comparison rows are written over each view's own proof variable, and the
`lex_constraint_view_mixed` lane runs the whole matrix with views mixed in.

### Reification

Full. `If` and `Iff`, and `NotIf` through the general constructor, via the
shared reified dispatcher (`gcs/constraints/innards/reified_dispatcher.hh`;
see [`reification.md`](../reification.md)):

- **condition fixed true** under `If` or `Iff` (or `MustHold`): the enforce
  pass, rules 1–4, on the "greater" encoding;
- **condition fixed false** under `Iff`, **or true** under `NotIf` (or
  `MustNotHold`): the same pass on the negation, `vars_2 ≥_lex vars_1` with
  `or_equal` flipped, on the "less" encoding;
- **condition open**: a detection pass, rules 5 and 6, which infers the
  condition when the bounds decide the comparison.

The detection is **incomplete** (rules 5 and 6): it decides only at the first
position that is not fixed equal, and only when that position is strictly
separated, or when the whole common prefix is fixed equal. `[x] >_lex [2]` with
`x ∈ 0..2` cannot hold, since `x` cannot exceed 2 and equality does not
satisfy a strict comparison, but the condition stays open.

### Relation to other families

- **Decomposes into it:** nothing in the solver. The standard library's
  `lex_chain`, `lex2` and friends decompose into it.
- **Child constraints:** none for the propagator class. `LexSmartTable` is
  nothing but a child `SmartTable`.
- **Shares code:** the reified dispatcher, with every reified family.
- **Presolvers:** none reads it.
- **The merge question with `smart_table`:** settled as separate, and
  `LexSmartTable` stays here as a reference encoding. It shares no code with the
  propagator class, and [`smart_table.md`](smart_table.md) owns the engine.

## The proof model

### OPB encoding

For one direction, `vars_1 (>|≥)_lex vars_2`, with `n = min(|vars_1|,
|vars_2|)`, and `c` the half-reification condition when there is one:

```
pref[0] is true (no flag);  pref[i], i = 1..n       proof flags x[id][i][pref]
dec[i],  i = 0..n-1                                 proof flags x[id][i][dec] (or [inc])
for i in 0..n-1:
  pref[i+1] ⇒ pref[i]                        (i ≥ 1)
  dec[i]    ⇒ pref[i]                        (i ≥ 1)
  pref[i+1] ⇒ vars_1[i] = vars_2[i]          two rows
  dec[i]    ⇒ vars_1[i] − vars_2[i] ≥ 1
c ⇒ Σ dec[i] + [eps]·pref[n] ≥ 1
```

where `eps` holds when an equal common prefix satisfies the constraint:
`vars_1` strictly longer, or equal lengths and non-strict. Every row is also
half-reified on `c`, so that under `¬c` the flags are unconstrained and a
solution can leave them anywhere.

`pref[i]` means "the first `i` positions are equal" and `dec[i]` means "the
comparison is decided at `i`, in `vars_1`'s favour". **`pref` is shared** by
the two directions, since it is symmetric in the arrays; only the decision
flag is per direction, named `dec` for the greater side and `inc` for the less
side, as cake names them.

- `If{c}`: the greater direction, half-reified on `c`.
- `Iff{c}`: both directions, the greater one on `c` and the less one (strict
  and non-strict swapped) on `¬c`.
- `NotIf{c}`: the less direction only, half-reified on `c`; `MustNotHold`
  builds it unreified (`define_proof_model`). The [`NotIf` proof
  gap](#proof-logging-gaps) comes from this: its less rows are active under
  `c`, not `¬c`.

**It is definitional:** the flags are defined, not constrained beyond their
meaning, and the at-least-one row is the constraint. **Size:** about `5n` rows
and `2n` flags per direction, over bit sums, so **independent of domain width**
and linear in the array.

### Labels

`None` load-bearing. The rows carry no labels. The flags are named
`x[id][i][pref]`, `x[id][i][dec]` and `x[id][i][inc]`, and the justifications
cite the flags by name, which is how an external tool finds them.

### Cake conformity

Fourteen chain cases, all `none`: `lex_{greater,less}_{than,equal}_{sat,unsat}`,
`_if_sat` for two of them, and `_iff_sat` for all four. They chain-verify,
reified ones included, because the flag names and the shared `pref` set match
cake's (#432). They stay `none` because the operands' `=` and `≥` literal
encodings still diverge (#358). The writer spells the or-equal forms
`lex_greater_equal` / `lex_less_equal`, as cake does. `_not` and `_not_if`
round-trip through the solver's own reader but have no cake counterpart.

`LexSmartTable` writes `lex_smart_table`, cake's keyword, but its OPB is the
full `SmartTable` encoding, several times the size of cake's rows, so it does
not chain and has no case.

### Proof-time state

- **At the root:** nothing.
- **During search:** each inference's lemmas, at `ProofLevel::Temporary`, so
  deleted when the inference is done. Nothing a later step depends on is
  deleted: every lemma is re-derived when it is next needed.
- **Naming:** the flags as above.
- **Proof-only auxiliaries determined on a solution:** yes. On a full
  assignment with `c` true, each `pref[i]` is forced by the equalities it
  implies holding or failing and by the chain, and each `dec[i]` by `pref[i]`
  and the comparison at `i`. Under `¬c` the half-reification leaves them free,
  which is deliberate: VeriPB checks a `solx` against the constraints, and they
  are vacuous there.

## The implementation

### Initialisation and global data

`prepare()` evaluates the reification condition against the initial state and
allocates the backtrackable `LexState` holding `α`. There is no initialiser.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| dispatcher, must hold | `on_bounds`, every operand | derived: **nothing** | 1–4 | `MustHold` (the plain classes); `If` or `Iff` with the condition true at install | never claims | yes: when the prefix is equal to the end and that satisfies, or when strict is forced at `α` |
| dispatcher, must not hold | as above | derived: **nothing** | 1–4 on the negation | `MustNotHold`; `NotIf` with the condition true, or `Iff` with it false, at install | never claims | as above |
| dispatcher, undecided | `on_bounds` operands, **and** the condition | derived: **the condition only, and only for an `=`, `≠` or range condition** | 5, 6, and 1–4 once decided | `If`, `Iff` or `NotIf` with the condition open | never claims | on any verdict |

**`on_bounds` is exact for the operands.** Every pass reads `state.bounds()`
and nothing else, so no hole can change what it infers. The condition variable
goes through `add_trigger_for()` (`triggers.cc`), which puts an `=`, `≠` or
range condition on `on_change` and a `<` or `≥` condition on `on_bounds`, as
for every reified family.

**Idempotence.** Not claimed, and not true: the pass tightens at `α`, and if
that fixes both sides of `α` equal, `α` should advance and the pass run again,
which it does only on the next call.

### Mutable state and incrementality

**`α`, backtrackable** (`add_constraint_state`, `LexState`). Each call advances
it over any newly fixed-equal prefix before doing anything else, so the prefix
already known equal is not re-read. It is shared by the two directions of an
`Iff`, which is safe since "fixed equal" is symmetric.

What is **not** incremental is the reason: every call builds `vars_1 ++ vars_2`
as a fresh vector and materialises its bounds, `O(n)` allocation and reads per
call, used only if something infers. See [CPU performance](#cpu-performance).

### Interior values and optional pruning

**Offers.** `None.` The pass already reaches GAC on distinct variables, and
has one arm.

**Observes.** **Nothing, on the operands.** The family's whole vocabulary is
bounds, so a `Lex` over some variables is never a reason for another family's
interior pruning on them to stay on. The one exception is the reification
condition, which is `on_change` like every reified family's, and vacuous for the
usual `{0, 1}` condition variable.

### Robustness and limits

**Unbounded domains.** Fine on distinct variables: the pass is `O(n)` bounds
reads. The shared-variable case below is the exception.

**Negative values and zero.** Tested (`lex_test`'s ranges include 0), and
nothing here depends on sign.

**Degenerate shapes.**

- *Empty operands, singletons, all-fixed arrays:* covered by `lex_test` per
  #254, in all four directions.
- ***Repeated variables lose generalised arc consistency, in three shapes.***
  No solution is lost in any of them. Root GAC failures in 3,000 random
  instances per relation, seed 1, split by shape (`lexcheck.cc`, the
  fact-check's independent checker, modes 2 to 4;
  `tmp/fd-ordering/probes/lexcheck_s1_*.txt`):

  | Shape | `>` | `≥` | `<` | `≤` |
  |---|---|---|---|---|
  | a repeat within one array | 197 | 80 | 180 | 72 |
  | the same variable at the same position of both | 342 | 180 | 336 | 177 |
  | a variable shared across different positions | 18 | 15 | 17 | 14 |

  (`ordcheck.cc`'s pooled `alias` mode, seed 2, mixes all three: 591, 90, 594
  and 115 of 2,000.) A repeat within one array is not an ordinary pair of
  positions: `[x, x] ≥_lex [1, 2]` with `x ∈ {1, 2}` keeps `x = 1` at the root,
  though `[1, 1] <_lex [1, 2]`.
- ***A variable shared at one position*** is the shape with a mechanism of its
  own: the pass treats the pair as one that might still differ. At `α`, it
  pushes `x ≥ lb(x)` and `x ≤ ub(x)`, which do nothing. Beyond `α`, it counts
  the pair as a possible witness (`ub(x) > lb(x)`), which it can never be, and
  so stops looking. Besides the weaker propagation above, that gives:
  - **A width-proportional failure.** When the comparison must be decided at a
    shared position, the pass pushes both of the variable's bounds in by one
    per call, until the domain empties. `[z, a] ≥_lex [z, b]` with
    `a ∈ 0..1`, `b ∈ 5..6` and `z ∈ 0..W` is unsatisfiable: at W = 10⁵ it takes
    50,001 propagations and 0.043 s; at W = 10⁷, 5,000,001 and 4.2 s, proofs
    off. With proofs, W = 10⁵ writes 1.15 million lines, 97 MB, and at W = 200
    the proof verifies. `[x, y] >_lex [x, y]` is worse, quadratic: 501,502
    propagations over 1,002 nodes at W = 1,000. `[x] >_lex [x]` is the single
    step, W/2 calls. Release build of `c9ceea25`, fataepyc-10, 2026-09-29
    (`probes/aliaswide.cc`).

  **These are real shapes.** A lex-leader constraint `x ≤_lex σ(x)` puts the
  same variable on both sides wherever `σ` fixes a position, and at different
  positions elsewhere. Six corpus models share at a position: `mqueens` 2014,
  `neighbours` 2018, `peacable_queens` 2021 and `chessboard` 2023 in every one
  of their lex constraints (6 or 7 each), and `neighbours` 2024 and
  `peacable_queens` 2024 in 1 of 3 and 2 of 7. Every one of those posts also
  shares across positions. `neighbours` 2021 shares only across positions, and
  its three posts are lex-leader constraints too (2,000 variables, the second
  array a permutation of the first with no fixed point), so seven models post
  lex-leader constraints with repeated variables; `pattern-set-mining-k2` 2012,
  which repeats within an array, makes eight with some repeat (the
  fact-check's `corpus_lex_cross.py`). Their domains are small, so the width
  cost does not bite. On `mqueens` the missed propagation costs no nodes:
  given 120 s, the audited build proves objective 5 optimal after 618,951
  nodes (55 to 56 s in two runs), and the fact-check's build of next step 2,
  which treats an identical pair as equal, explores the identical 618,951
  nodes (56.9 s; `tmp/fd-ordering/factcheck/lex_r2/mq_{orig,same}_120s.txt`).
  The other models were not measured, since their 20 s runs finish nothing
  and nodes explored in fixed time mix strength with speed.

**Overflow.** None to guard: the pass compares bounds and pushes them to other
existing bounds, adding or subtracting at most 1 inside `infer_*`.

### Interval efficiency

**Fine at any width on distinct variables.** `lex.cc` has no loop over values.

1. **The propagation side.** An `O(n)` scan from `α` for a witness or a
   blocking position, and `O(1)` inferences. The exception, again, is a call
   count: the shared-variable failure above makes W/2 calls.
2. **The reason side.** `O(n)`, two bound literals per operand, never per
   value, but **materialised on every call, unguarded**, for inferences that
   mostly do not happen. That is the per-call cost measured below, not a width
   cost.
3. **The proof side.** Each inference writes `O(n)` lemmas of `O(n)` literals
   each: **quadratic in the array length**, and independent of width. See
   [Proof performance](#proof-performance).
4. **The audit lane.** Two rows. `LexCompareGreaterThanOrMaybeEqual`, pinned
   `Clean`: `LexGreaterEqual` over two arrays of three distinct plain variables
   in `0..10⁹`. It varies neither a shared variable (the one width hazard here,
   which a per-call counter would not see anyway, since no call walks
   anything), nor strictness, reification or views. `LexSmartTable`, pinned
   `KnownTrip`: its smart-table encoding walks values, as
   [`smart_table.md`](smart_table.md) documents.

## Inference catalogue

Six rules. Rules 1 to 4 are the enforce pass, in whichever direction the
condition demands; rules 5 and 6 are the detection pass's verdicts on the
condition.

Four facts hold for all six.

**Each is a `RUP sequence`, and the procedure is ours.** No published
justification procedure covers lexicographic ordering. Every rule emits some
lemmas at `ProofLevel::Temporary`, each a RUP under the rule's reason, and then
closes with the conclusion by RUP (`JustifyExplicitly` with `ThenRUP::Yes`).
The lemmas say that flags are false: `¬dec[k]` for positions that cannot decide
the comparison, and `¬pref[k+1]` (or a bound `∨ ¬pref[k+1]`) for prefixes that
cannot be equal. With all of them in place, the negated conclusion leaves the
at-least-one row with no true term. Each lemma is licensed by the facts in
[`justification-techniques.md`](../justification-techniques.md): a reified
row's consequent (Theorem 2.6), a bound crossing a difference row with
`B ∈ {0, 1}` (Theorem 2.9, for the half-reified equality halves and the
comparison row), and the `pref` chain's implications, which are clauses.

**The reason is the whole scope.** Every rule's reason is the bounds of every
operand (two literals, or one if fixed), plus the condition literal. It is
enough, and it is not minimal: rule 1 needs only the fixed-equal prefix and one
bound at `α`.

**Each lemma carries the whole reason**
(`emit_rup_proof_line_under_reason`), which is what makes a rule's proof
quadratic in the array.

**Two wire forms.** `hints::Lex`, `(constraint_id <id>)`, for rules 1–4, and
`hints::LexUnsatScaffold`, `(constraint_id <id>) (subhint unsat_scaffold)`,
for rules 5 and 6. Measured on the probe enumerations at `Definitions`: 43 base
annotations for `LexLessThan` over two arrays of three in `0..2`, 30 for
`LexGreaterEqual`, 73 for `LexLessThanEqualIff`; the verdict form appears when
the condition is decided before branching, as in `probes/lexreif.cc`.

### Rule: tighten-at-alpha

- **Infers** — `vars_1[α] ≥ lb(vars_2[α])` and `vars_2[α] ≤ ub(vars_1[α])`,
  as one `infer_all`.
- **Fires when** — any operand's bounds move, in the enforce pass, after `α`
  has been advanced over the fixed-equal prefix.
- **Strength** — `GAC` on distinct variables, with rules 2 to 4. Checked by
  brute force at the root over random domains **with holes**, and unequal
  lengths from 0 to 3 (`tmp/fd-ordering/ordcheck.cc`, 2,000 instances each of
  `>`, `≥`, `<` and `≤`, at seeds 1 and 2): no GAC failure. `lex_test` also
  checks GAC at every node, on interval domains. Frisch et al. prove the
  algorithm GAC for the equal-length case; the pass is theirs with the "equal
  prefix satisfies" condition generalised to lengths.
- **Algorithm** — two bound pushes at `α`. `O(1)`, after the `O(n)` scan.
- **Why it is true** — every position before `α` is fixed equal, so the
  comparison is decided at `α` or later; either way `vars_1[α] ≥ vars_2[α]`.
- **Proof technique** — `RUP sequence`, ours. `α` lemmas `¬dec[k]`, `k < α`
  (each RUP: `dec[k]` would need `vars_1[k] > vars_2[k]`, and both are fixed
  equal); then, for every `k ≥ α`, two lemmas
  `vars_1[α] ≥ L ∨ ¬pref[k+1]` and `vars_2[α] ≤ U ∨ ¬pref[k+1]` (each RUP:
  `pref[k+1]` implies `pref[α+1]` down the chain, which implies equality at `α`,
  and the other side's bound crosses it). The closing RUP: under the negated
  conclusion every `pref[k+1]`, `k ≥ α`, is false, so every `dec[k]`, `k > α`,
  is false through `dec[k] ⇒ pref[k]`; `dec[α]` is false because the
  comparison at `α` cannot be won; and the `¬dec[k]` lemmas cover `k < α`.
- **Reason** — the whole-scope bounds reason, plus the condition. Not minimal.
- **Assertion** — one clause per pushed bound, `pushed literal ∨ ¬reason`.
  Measured at `Inferences`, `[x] >_lex [2]` under `cond`:
  ```
  a 1 i[x][ge2] 1 ~i[x][ge0] 1 i[x][ge3] 1 ~i[cond][b0] >= 1 ::lex:((constraint_id _1));
  ```
- **Hint** — `hints::Lex`: `originator`, the `ConstraintID`.
- **Offline reconstructibility** — `offline`. `α` is readable off the reason
  (the positions fixed equal from the front), the flags are named, and the
  procedure is fixed by the clause.
- **Proof size** — `α + 2(n − α)` lemmas, each carrying the `O(n)` reason, plus
  the conclusion: **`O(n)` lines and `O(n²)` literals per inference.**
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No mutation lane.

### Rule: strict-at-alpha

- **Infers** — `vars_1[α] > lb(vars_2[α])` and `vars_2[α] < ub(vars_1[α])`.
- **Fires when** — after rule 1, when no later position can decide the
  comparison in `vars_1`'s favour, and either an equal common prefix would not
  satisfy the constraint or some later position is already decided against
  `vars_1` (it is "blocked").
- **Strength** — `GAC`, with rules 1, 3 and 4; see rule 1.
- **Algorithm** — the `O(n)` scan from `α + 1` for a witness (`ub(vars_1[k]) >
  lb(vars_2[k])`) or a block (`ub(vars_1[k]) < lb(vars_2[k])`), then two bound
  pushes.
- **Why it is true** — the comparison cannot be decided after `α` in
  `vars_1`'s favour, and falling through to the end, or to the blocked position,
  loses; so it must be decided at `α`.
- **Proof technique** — `RUP sequence`, ours. `n − 1` lemmas `¬dec[k]`,
  `k ≠ α`, and, when the equal prefix would otherwise satisfy but a later
  position blocks it, one lemma `¬pref[b+1]` at the blocking position `b`.
  Then the conclusion by RUP: only `dec[α]` is left in the at-least-one row,
  and the negated conclusion falsifies it.
- **Reason** — the whole-scope bounds reason. Not minimal.
- **Assertion** — `pushed literal ∨ ¬reason`, per pushed bound.
- **Hint** — `hints::Lex`.
- **Offline reconstructibility** — `offline`: the blocking position is readable
  off the reason's bounds.
- **Proof size** — `O(n)` lemmas of `O(n)` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: contradiction-equal-prefix

- **Infers** — a contradiction.
- **Fires when** — `α` reaches `n`, so the whole common prefix is fixed equal,
  and that does not satisfy the constraint (strict with equal lengths, or
  `vars_1` shorter).
- **Strength** — part of `GAC`, with the others.
- **Algorithm** — the `α` advance. `O(n)` at worst.
- **Why it is true** — nothing is left to decide the comparison.
- **Proof technique** — `RUP sequence`: `n` lemmas `¬dec[k]`, then the
  at-least-one row has no true term.
- **Reason** — the whole-scope bounds reason.
- **Assertion** — `¬reason`, from `contradiction()`.
- **Hint** — `hints::Lex`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — `n` lemmas of `O(n)` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: contradiction-no-witness

- **Infers** — a contradiction.
- **Fires when** — rule 2 would fire, but `α` cannot be decided in `vars_1`'s
  favour either (`ub(vars_1[α]) ≤ lb(vars_2[α])`).
- **Strength** — part of `GAC`.
- **Algorithm** — as rule 2.
- **Why it is true** — no position can decide the comparison for `vars_1`, and
  the fall-through loses.
- **Proof technique** — `RUP sequence`: `n` lemmas `¬dec[k]`, plus `¬pref[b+1]`
  when a block is what rules out the fall-through.
- **Reason** — the whole-scope bounds reason.
- **Assertion** — `¬reason`. Measured at `Inferences`, `[x] >_lex [2]` once
  rule 1 has pushed `x ≥ 2`:
  ```
  a 1 ~i[x][ge0] 1 i[x][ge3] 1 ~i[cond][b0] >= 1 ::lex:((constraint_id _1));
  ```
- **Hint** — `hints::Lex`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — `n` lemmas of `O(n)` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: condition-must-hold

- **Infers** — the condition, for `Iff`; its negation, for `NotIf`
  (`cond ⇒ ¬C`); nothing for `If`, where holding implies nothing about the
  condition.
- **Fires when** — the condition is open and the detection pass finds the
  comparison decided for `vars_1`: at the first position not fixed equal,
  `lb(vars_1[k]) > ub(vars_2[k])`, or the whole common prefix is fixed equal and
  that satisfies.
- **Strength** — `partial`. The pass looks only at that first open position,
  and decides only on strict separation. So a comparison that can be decided
  only through equality at `k` followed by the tail is missed. Checked by brute
  force at the root (`ordcheck.cc`, seed 1): the condition is left open without
  support on 17 of 2,000 random `Iff` instances for `>`, and 17 for `≤`, which
  by construction are the same instances with the condition's sense flipped.
  An example: `[1] ≤_lex [y]` with `y ∈ 1..3` always holds, and the condition
  stays open.
- **Algorithm** — the `O(n)` walk to the first open position.
- **Why it is true** — the comparison is decided at `k` for `vars_1`, whatever
  the later positions hold.
- **Proof technique** — `RUP sequence`, ours, under the negation of the
  inferred literal: the condition false switches on the *less* direction's
  at-least-one (half-reified on `¬c`), and the scaffold shows it has no true
  term. One lemma `¬pref[k+1]` at the separated position (if there is one),
  then `n` lemmas `¬dec'[k]` over the less direction's decision flags, each
  under the reason extended with `¬c`. This is `hints::LexUnsatScaffold`'s
  `emit_justification`. **That is right for `Iff` and wrong for `NotIf`:**
  under `NotIf` the inferred literal is `¬c`, so the negation to work under is
  `c`, and the less direction's rows are half-reified on `c`, not `¬c`
  (`define_proof_model`). The code states the scaffold under `¬c` for both, so
  under `NotIf` the lemmas are not RUP and VeriPB rejects the proof (see
  [Proof-logging gaps](#proof-logging-gaps)).
- **Reason** — the operands' bounds, without the condition.
- **Assertion** — `c ∨ ¬reason`. Measured at `Inferences`, `[2, a] >_lex
  [b, c]` with `b ∈ 0..1`:
  ```
  a 1 i[cond][b0] 1 ~i[a][ge0] 1 i[a][ge3] 1 ~i[b][ge0] 1 i[b][ge2] 1 ~i[cvar][ge0] 1 i[cvar][ge3] >= 1
    ::lex:((constraint_id _1) (subhint unsat_scaffold));
  ```
- **Hint** — `hints::LexUnsatScaffold`: `originator`, plus, for
  `emit_justification` only and not on the wire, the state, the reason, the two
  lists, `n` and the other direction's flag tables. On the wire it is the
  default identity-plus-subhint form.
- **Offline reconstructibility** — `hinted`. The subhint names the procedure;
  the separated position is readable off the reason.
- **Proof size** — `n + 1` lemmas of `O(n)` literals.
- **Gaps** — **under `NotIf`, the justification is wrong and VeriPB rejects
  it.** The inference itself is right. `None` for `Iff`.
- **Tightness** — `Not shown.`

### Rule: condition-must-not-hold

- **Infers** — the negation of the condition, for `If` and `Iff`; nothing
  for `NotIf`, where failing implies nothing about the condition.
- **Fires when** — the detection pass finds the comparison decided against
  `vars_1`: at the first open position `ub(vars_1[k]) < lb(vars_2[k])`, or the
  common prefix fixed equal and that does not satisfy.
- **Strength** — `partial`, for the same reason as rule 5: `[x] >_lex [2]`
  with `x ∈ 0..2` cannot hold and the condition stays open. Over 2,000 random
  `≥ If` instances the probe finds 1, 7, 6 and 2 such misses at seeds 1, 2, 3
  and 42.
- **Algorithm** — as rule 5.
- **Why it is true** — the comparison is decided at `k` against `vars_1`.
- **Proof technique** — `RUP sequence`, the mirror of rule 5: under the
  condition true, the *greater* direction's at-least-one is active, and the
  scaffold shows it has no true term.
- **Reason** — the operands' bounds.
- **Assertion** — `¬c ∨ ¬reason`. Measured at `Inferences`, `[0, a] >_lex
  [b, c]` with `b ∈ 1..2`:
  ```
  a 1 ~i[cond][b0] 1 ~i[a][ge0] 1 i[a][ge3] 1 ~i[b][ge1] 1 i[b][ge3] 1 ~i[cvar][ge0] 1 i[cvar][ge3] >= 1
    ::lex:((constraint_id _1) (subhint unsat_scaffold));
  ```
- **Hint** — `hints::LexUnsatScaffold`.
- **Offline reconstructibility** — `hinted`.
- **Proof size** — `n + 1` lemmas of `O(n)` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## `LexSmartTable`

A benchmarking reference: `vars_1 >_lex vars_2` written as a
[`SmartTable`](smart_table.md) over `vars_1 ++ vars_2`, with one row per
position `i < n`: `vars_1[j] = vars_2[j]` for `j < i`, and
`vars_1[i] > vars_2[i]`. Everything about its propagation, proof and cost is the
`SmartTable` engine's; what is specific to it:

- **The rows are forests of independent pairs.** Over distinct variables, row
  `i` is `i + 1` one-edge trees, and each tree copies the whole scope's domains
  (#1128). So its rows cost `Θ(n³d)` to filter while all are live, which may
  account for part of the growth of its lex benchmark ratio in
  [`smart_table.md`](smart_table.md); that document notes the share was not
  isolated.
- **It ignores the lengths, and so loses solutions when `vars_1` is the
  longer.** There is no row for the equal-prefix case, so it enforces strict
  lex on the common prefix only. Measured (`probes/lexst.cc`), over `0..2`:

  | Length of `vars_1` | Length of `vars_2` | `LexGreaterThan` | `LexSmartTable` |
  |---|---|---|---|
  | 2 | 2 | 36 | 36 |
  | 3 | 2 | 135 | **108** |
  | 2 | 3 | 108 | 108 |
  | 1 | 0 | 3 | **0** |

  The missing 27 are the assignments whose two-long prefixes are equal, where
  the longer `vars_1` should win. This contradicts its own header's
  `vars_1 >_lex vars_2` and the propagator class's documented semantics. Only
  the C++ API and the `.scp` reader can post it (one example,
  `examples/smart_table_lex`, uses equal lengths), so no front-end model is
  affected. The proofs verify, against its own OPB: the OPB is the table, and
  the table is what is wrong.
- **A variable shared between the arrays can make a row cyclic**, which
  `SmartTable` rejects (#1014): `{a, b} >_lex {b, a}` throws
  `InvalidProblemDefinitionException` when the problem is prepared, as the
  header says.
- **Its hints say `unnamed`** (#1121), because it does not pass its constraint
  ID to its child.

## Evidence

### Tests

- **`lex_test`** (`lex_constraint`, plus `lex_constraint_view_mixed`): for
  each of the four directions, pairs and triples over several ranges, arrays of
  six, and unequal lengths (both directions, asymmetric domains, one against
  three, #254's empty and all-fixed operands), under
  `solve_for_tests_checking_gac`, so GAC at every node, on interval domains,
  in the uncapped run (the caps truncate some of these; see below).
  Then `If` and `Iff` for each direction over nine shapes (pairs, triples and
  four unequal-length cases, all small positive domains; no arrays of six and
  none of #254's cases), under plain `solve_for_tests`: enumeration and the
  proof, no consistency check. `NotIf` and `MustNotHold` are not tested. With
  and without proofs; VeriPB runs when on the path. Seeded.
- **Duplicate-variable runs**, bare lanes only: `lex(xs, xs)` in all four
  directions, a shared first position, and repeats within one array, by
  enumeration over `0..2` and `1..3`.
- **`scp_chain_lex_*`**, fourteen cases: see [Cake
  conformity](#cake-conformity).
- **MiniZinc:** `lexless.mzn`, `lexlesseq.mzn`, `lexbool.mzn`, `lexreif.mzn`,
  and the four `lex*unequal.mzn`.
- **XCSP3:** `lex.xml`, `lex_matrix.xml`.
- **`LexSmartTable`:** only `smart_table_dup_test`'s cyclic-row rejection, the
  `smart_table_lex` example (equal lengths) and the audit lane.
  `smart_table_test`'s `lex_*` modes build their own lex tables rather than
  posting this class.
- **Audit lane:** the two rows above.

**Runtime caps.** No lane sets or clears one. The default caps **fire** in both
lanes: 32 of 368 bare runs and 32 of 352 `view_mixed` runs are truncated, each
checking 300 solutions for soundness only. They are the free-domain pairs and
triples (two `1..6` against two, and three `1..3` or `1..5` against three) and
all eight arrays-of-six runs (2,016 and 2,080 solutions), up to 7,875 solutions
(`GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500 lex_test --seed=1`, at
`c9ceea25`). So the capped run checks GAC at every node of the whole tree only
on the rest; the arrays of six are checked in full only uncapped. Uncapped, the
bare lane passes in 18.5 s.

**Tightness:** no mutation lane.

**What the tests do not cover.**

- **Holes**, for the per-node GAC check. The root probe covers them.
- **Strength of the reified forms,** deliberately unchecked, which is how the
  incomplete detection went unrecorded.
- **`NotIf` and `MustNotHold`,** which is how the rejected `NotIf` proof went
  unnoticed. No SCP chain case covers them either: cake has no such keyword.
- **A shared variable over a wide domain,** or a lex-leader shape with a fixed
  point of `σ`, the corpus's own. The duplicate runs are over `0..2`.
- **`LexSmartTable` on unequal lengths.** Nothing posts it on unequal
  lengths.
- **Real instances:** none ported.

### Benchmarks and examples

- **In the repository:** `examples/smart_table_lex` posts `LexSmartTable`. No
  example posts the propagator class.
- **Corpus:** 1,503 `lex_lesseq_int`, 28 `lex_less_int` and 2 `lex_less_bool`
  posts across 17 of the 285 flattened MiniZinc Challenge models, arrays of 3 to
  2,000. The family dominates two of them: `zephyrus` 2016 (264 posts of
  length 4; 5.45 s of a 10 s run, 0.83 µs a call) and `mqueens` 2014 (6 of
  length 121; 7.07 s of 10 s, 11 µs a call). On `opd` 2015 (358, up to 350) it
  is about a tenth: 1.04 s of 10 s at 20 µs a call in this audit's run, 1.09 s
  at 17.8 µs in the fact-check's (`GCS_PROPAGATOR_STATS=time`). No corpus model
  posts a reified form.
- **For CPU:** `zephyrus` 2016 for many short arrays, `mqueens` 2014 for a few
  long ones, and the identical-tree enumeration below for Gecode.
- **For proof verification:** `probes/lexsize.cc`, below, whose size is set by
  the array length.

### CPU performance

*Release build of `c9ceea25` (GCC 15.2.0, `-O3 -march=native`); Gecode 6.3.0,
built locally; fataepyc-10, boost off, `taskset -c 4`, fixed malloc thresholds;
2026-09-29.*

**Against Gecode, on an identical tree.** Enumerating `k` strictly
lex-increasing 0/1 rows of length `n` (`bench/lex_gcs.cc`, `lex_gecode.cc`,
input order, smallest value first). Both solvers are GAC here, and the trees
agree node for node: GCS's recursions equal Gecode's nodes, and the failures
match. Median of five runs, wall time of the whole solve, proofs off.

| k | n | Solutions | Nodes | Failures | GCS | GCS, lazy reason | Gecode |
|---|---|---|---|---|---|---|---|
| 3 | 7 | 341,376 | 682,753 | 1 | 0.635 s | 0.601 s | 0.150 s |
| 4 | 5 | 35,960 | 71,981 | 31 | 0.080 s | 0.067 s | 0.017 s |

GCS takes 4.2 to 4.8 times Gecode's time, more than the 2.5 to 2.7 times of
[`increasing`](increasing.md) on a similar enumeration. The lazy-reason column
is the A/B below.

**The reason built on every call.** A/B on the corpus, same build, the only
difference being `lex.cc` with the reason left as a deferred
`bounds_reason(...)` instead of `eager_reason(bounds_reason(...), state)`,
linked into `fzn-glasgow` ahead of the library
(`tmp/fd-ordering/ab/lex_lazy.cc`). Nodes explored in 10 s, median of three,
proofs off, `numactl` on node 0:

| Model | Lex posts, length | Nodes, as it is | Nodes, reason deferred | Ratio |
|---|---|---|---|---|
| `mqueens` 2014 | 6, 121 | 127,146 | 380,202 | 3.0 |
| `zephyrus` 2016 | 264, 4 | 259,646 | 408,875 | 1.58 |
| `opd` 2015 | 358, 10 to 350 | 18,224 | 20,106 | 1.10 |
| `pattern-set-mining-k2` 2012 | 2, 56 and 159 | 75,722 | 81,671 | 1.08 |
| `products-and-shelves` 2025 | 210, 3 | 70,375 | 72,657 | 1.03 |

The tree is the same by construction, since the reason's content does not
change, only when it is built. Two checks: on `zephyrus` the fully justified
proofs of the two builds after 1.5 s are identical for the first 767,848 lines,
which is all of the shorter one but its conclusion (770,058 lines in the
fact-check's rerun); on `mqueens` the first four intermediate solutions of 20 s
runs, objectives 10 down to 7, are identical (`ab/mq_sols_*.txt`). The deferred
build then goes on to objective 5 and proves it optimal (17.3 s, 618,951 nodes),
while the audited build stops at 7 when the 20 s runs out (243,300 nodes;
`tmp/fd-ordering/factcheck/lex_r2/mq_{lazy,orig}.txt`). Given 120 s, the audited
build proves the same optimum after the identical 618,951 nodes, in 55 to 56 s:
the same tree, about three times slower. The gain is per call and grows with the
arrays, and with proofs on it shrinks (13% more nodes on `zephyrus`, in one
1.5 s run each), since a proof materialises the reason at each inference
anyway.

**What the benchmarks do not exercise.** The reified forms (no corpus model has
one), and shared variables over wide domains.

### Proof performance

*Same build and machine; VeriPB 3.0.2 with `--force-checked-deletion`.*

**Against the array length.** `LexLessThanEqual` over two 0/1 arrays of length
`n`, branching `a₀, b₀, a₁, b₁, …` on the largest value, stopping at the 200th
solution (`probes/lexsize.cc`):

| n | Lex inferences | Lines, `Off` | Bytes, `Off` | Bytes per inference | VeriPB, `Off` | Bytes, `Inferences` |
|---|---|---|---|---|---|---|
| 25 | 36 | 4,396 | 1.85 MB | 51 KB | 0.07 s | 518 KB |
| 50 | 61 | 8,471 | 11.4 MB | 187 KB | 0.39 s | 1.07 MB |
| 100 | 111 | 22,246 | 82.3 MB | 741 KB | 2.56 s | 2.35 MB |
| 200 | 211 | 72,296 | 654 MB | 3.1 MB | 19.5 s | 5.83 MB |

"Lex inferences" counts the `lex`-hinted assertions at `Inferences`.
**Bytes per inference quadruple as `n` doubles**, as the catalogue predicts:
`O(n)` lemmas, each carrying the whole `O(n)`-literal reason. The rest of each
proof is small here (200 solutions), so almost all of it is the family's.
Asserting the inferences cuts it by 3.6 to 112 times, growing with `n`, and
what is left is dominated by the reasons in the `a` lines themselves.

**Assertion levels.** At `Off` every probe proof verifies: `<`, `≥`, unequal
lengths, `≤ Iff`, `> If`, and `LexSmartTable` (`probes/runfam.sh`). At
`Definitions` and `Inferences` each is accepted under assertions
(`s UNDER ASSERTIONS`, not `VERIFIED`), since the family's inferences are `a`
lines there, so only `Off` checks the family. At `Links` none is accepted,
and each fails at a `solx` step, which is generic rather than this family's
(`LexSmartTable` fails the same way, as do other families' probes).

## Status, gaps, and next steps

### Proof-logging gaps

**One: under `NotIf`, a correct inference gets a proof VeriPB rejects.**

- **When.** The general constructor's `reif::NotIf{cond}`, which the `.scp`
  reader also posts for `lex_…_not_if`, with the condition open, when the
  detection pass finds the comparison holds (rule 5).
- **What the solver does.** It infers `¬cond`, correctly.
- **What goes wrong.** Its scaffold is stated under `reason ∧ ¬cond` over the
  less direction's flags, as for `Iff`. For `NotIf` those rows are
  half-reified on `cond`, so under `¬cond` they are inactive and the lemmas are
  not RUP.
- **Evidence** (Release `c9ceea25`, fataepyc-10, VeriPB 3.0.2 with
  `--force-checked-deletion`, 2026-09-30):
  - `[2, a] >_lex [b, c]` with `b ∈ 0..1` finds its 18 solutions, and VeriPB
    rejects line 44 as not RUP (`tmp/fd-ordering/factcheck/lex/fc_notif.cc`,
    `notif_holds`, rebuilt as `probes/notif_repro.cc`).
  - Of 160 random `NotIf` proofs
    (`tmp/fd-ordering/factcheck/lex/fc_proofsweep.cc` and `proofsweep.sh`, 40
    seeds for each of strict or not, shared variables or not; strict and
    non-strict share each seed's instance), 50 are rejected, deterministically.
    They are exactly the 50 in which rule 5 writes its scaffold lemma
    (`rup 1 ~x[…] … 1 i[cond][b0] >= 1`); the 110 without one verify.
    Stating the scaffold under `cond` instead makes all 160 verify
    (`tmp/fd-ordering/factcheck2/lex/lex_notiffix.cc`).
  - `If`, `Iff` and `MustNotHold` verified on every seed tried.
- **Status.** Filed as #1137, marked a proof failure.

Otherwise every inference is justified at `Off`, and the propagator is the same
with proofs on or off.

### Known limitations

- **A reified lex under `NotIf` can write a proof VeriPB rejects.**
- **A lex constraint that repeats a variable propagates less than it could,**
  whether within an array, at one position of both, or across positions. When
  a variable is shared at one position that decides the comparison, it takes
  time proportional to the variable's domain to fail. Lex-leader symmetry
  breaking produces these shapes.
- **A reified lex does not decide its condition in every case it could:** only
  when the first open position is strictly separated, or the prefix is fixed
  equal to the end.
- **Its proofs grow with the square of the array length per inference,** which
  makes long arrays expensive to verify: 654 MB for 211 inferences at 200.
- **`LexSmartTable` gives wrong answers when `vars_1` is the longer array.**

### Next steps

0. **Fix the `NotIf` scaffold.** State the must-hold verdict's scaffold under
   the negation of the inferred literal: `¬cond` for `Iff`, `cond` for
   `NotIf`. Add `NotIf` and `MustNotHold` to `lex_test`'s reified runs. Small,
   and first: it is a proof failure. Filed as #1137.
1. **Build the reason only when it is needed.** Leave it as a deferred
   `bounds_reason`, and build the concatenated scope once, at install, rather
   than per call. The A/B above is the first half, on the same tree: up to 3.0
   times the node throughput on the corpus. Small. Filed as #1141. Per #907's
   lesson it wants a proof diff and a check under dom/wdeg, as the zephyrus
   prefix check above began.
2. **Treat an identical pair as equal.** Advance `α` over it and never count it
   as a witness or a block; decide the rule-2 case at such a pair as rule 4.
   That removes the width-proportional failure and the same-position loss of
   GAC. The fact-check built it (`fc_lex_same.cc`): same-position sharing then
   has no failing root, and `[z, a] ≥_lex [z, b]` fails in one call at W = 10⁷.
   It does **not** touch sharing across positions (18 failing roots for `>`
   either way) or repeats within an array, and every corpus lex-leader post that
   shares at a position also shares across positions. So it does not make
   lex-leader constraints GAC. What would needs a design of its own. On
   `mqueens` it gains no nodes: with and without it, the proof of optimality
   takes the same 618,951 nodes (see [Robustness](#robustness-and-limits)); the
   other five same-position models were not measured. Filed as #1143.
3. **Make the proof linear per inference.** Give each rule its minimal reason
   (the fixed-equal prefix and the bounds it uses), and check which lemmas the
   closing RUP actually needs: the `2(n − α)` bound lemmas of rule 1 may reduce
   to one `¬pref[α+1]`. Per the arc's standing rule, which lemmas are needed is
   an empirical question. Filed as #1142, with the table above.
4. **Fix `LexSmartTable`'s lengths:** add the equal-prefix row when
   `|vars_1| > |vars_2|` (and for the non-strict reading, if one is wanted), or
   reject unequal lengths. Small. Filed as #1138.
5. **Complete the reified detection.** Continue past a position whose only
   overlap is equality, as the enforce pass's scan does. Moderate: each verdict
   then needs its own scaffold. Not worth an issue until a reified lex turns up
   in a model.

## Prior art

Frisch, Hnich, Kızıltan, Miguel and Walsh (*Global constraints for lexicographic
orderings*, CP 2002, and *Propagation algorithms for lexicographic ordering
constraints*, AIJ 2006) give the linear-time GAC algorithm with the two pointers
`α` and `β`; this propagator is theirs, with `β` recomputed per call and the
length rule added. Gecode's `rel` on two arrays implements the same. The
encoding is `cake_pb_cp`'s. Certified lex is not new: McIlree and McCreesh
(*Proof Logging for Smart Extensional Constraints*, CP 2023, LIPIcs 280,
26:1–26:17) and McIlree's thesis certify `LexGreater` through its smart-table
decomposition (Equation 4.1, in the Chapter 4 introduction, p. 100), settling
that it has efficient PB proof logging (Section 4.1.4); that is what
`LexSmartTable` runs. Section 4.1.4 also proposes running the SmartTable
propagator purely as the proof procedure for domain-consistent inferences found
by a different algorithm, which could in principle justify this propagator's
equal-length, unreified inferences through the decomposition instead. That is a
route, not a published justification of this propagator. What is this family's
own is the dedicated propagator's flag-per-position justification, the lemma
sequences of rules 1 to 6, which as far as this audit knows is unpublished.

## Further reading

- [`smart_table.md`](smart_table.md): the engine under `LexSmartTable`, and its
  lex benchmark.
- [`reification.md`](../reification.md): the dispatcher behind the reified
  forms.
- [`justification-techniques.md`](../justification-techniques.md): the
  theorems each lemma leans on.
