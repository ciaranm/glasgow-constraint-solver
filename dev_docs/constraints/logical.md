# Logical: `And`, `Or`, and their half-reified forms

> **Maturity** production ·
> **Audited** 2026-09-23 at `f28fdef8` ·
> **Open issues** filed by this audit: #1060 (every wake rescans the
> literals from the front; one 2,774-literal clause is three quarters of
> `network_50_cstr`'s propagation). Already open and touching this family: #310
> (range literals cannot be written into the model, so a range literal here
> throws with proofs on), #953 (`cake_pb_cp` has no rule for `and_if` /
> `or_if`), #868 (cross-solver). Tracked under #871.

Four classes over one propagator. `And(lits, r)` says `r ⇔ ∧ lits`, and
`Or(lits, r)` says `r ⇔ ∨ lits`. `AndIf` and `OrIf` are their half-reified
forms, `r ⇒ ∧ lits` and `r ⇒ ∨ lits`. One template, `install_propagators_logical`,
implements all four: `Or` is `And` over the negated literals and reification,
and the half forms keep one direction of it. MiniZinc's `bool_clause` is an `Or`
with a true reification: 391,679 clauses in 155 of the corpus's 297 models.
Only the `equals` and `linear` families are posted more.

Three things to know before touching it.

- **It is generalised arc consistent when its literals are over different
  variables, and cheap per call except on a long clause.** Two literals over
  one variable break the first: the propagator sees them as two undecided
  literals, so `Or{x < 3, x ≥ 5}`, which is what MiniZinc's `set_in` glue
  posts, never prunes 3 or 4. For the second, each call scans the literals
  until it has seen two undecided ones, from the start of the list, and
  nothing remembers where it got to. For the short clauses most models post
  that is typically 0.14–0.4 µs a call. But `network_50_cstr`
  posts one clause over 2,774 literals, which the search fixes from the front,
  and there that one constraint is 76% of the propagation time, at 32 µs a call
  (#1060). Watched literals are the textbook answer.
- **Every inference is one RUP against one of two model rows.** The encoding is
  `cake_pb_cp`'s: a `pos` row saying the reification implies the conjunction
  (or disjunction), and a `neg` row for the converse, each linear in the number
  of literals. The half forms have the `pos` row only, which is why they cannot
  chain through cake yet (#953).
- **The half-reified forms are reachable only from CPMpy and the `.scp`.**
  MiniZinc turns a half-reified Boolean into plain clauses for this library,
  and XCSP3 has no such form. The `.scp` path is tested; the Python tests of the
  `gcspy` path are not registered with `ctest`.

## What it is

### Semantics

Over a list of literals `lits` and a reification literal `r`:

| Class | Meaning | Constructors |
|---|---|---|
| `And` | `r ⇔ ∧ lits` | `(Literals, Literal)`; `(vector<IntegerVariableID>, IntegerVariableID)`, reading each as `≠ 0`; `(vector<IntegerVariableID>)`, with `r` true |
| `Or` | `r ⇔ ∨ lits` | the same three |
| `AndIf` | `r ⇒ ∧ lits` | `(Literals, Literal)`; `(vector<IntegerVariableID>, IntegerVariableID)` |
| `OrIf` | `r ⇒ ∨ lits` | the same two |

A literal is any `IntegerVariableCondition` (`=`, `≠`, `<`, `≥` and the range
forms) or a constant `TrueLiteral` / `FalseLiteral`, so the family is not
confined to Booleans: MiniZinc's `set_in` glue posts `Or{x < l, x ≥ u}` over
integer variables. **A range literal throws with proofs on**: the model cannot
yet write one (#310), and nothing here avoids it. With proofs off it is
correct.

Degenerate shapes:

- **No literals**: `And()` is true and `Or()` false, so the reification is fixed
  at the root. Tested (#254).
- **A constant literal**: a false literal in an `And` forces `¬r` at the root,
  and so does a true one in an `Or` forcing `r`. Tested.
- **A constant reification**: a true one on `And` forces every literal at the
  root and installs no propagator. A false one on `AndIf` makes it vacuous, and
  nothing is installed.
- **The reification among the literals**, `And({x, y, r}, r)`: legal, and one
  direction of it collapses to a tautology. Tested, including `{r}` and
  `{r, r}`.
- **A repeated literal**: tested for `{x, x, y}`, `{x, y, x}` and `{x, x}`.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `And` | ✓ `array_bool_and`, `bool_and` | ✓ `and` inside an expression, over an auxiliary result[^xand] | ✓ `and`, and its full reification, through `gcspy`'s `post_and` and `post_and_reif` | ✓ `and` | |
| `Or` | ✓ `bool_clause` (reification true), `bool_clause_reif`, `bool_or`; also the `set_in` and `set_in_reif` glue[^mznsetin] | ✓ `or`, top level or inside an expression; `imp`[^ximp] | ✓ `or`, its full reification, and `implies`[^cimp] | ✓ `or` | |
| `AndIf` | `unsupported`[^mznimp] | `n/a` | ✓ `post_and_reif` with `fully_reify` false | ✓ `and_if` | does not chain (#953) |
| `OrIf` | `unsupported`[^mznimp] | `n/a` | ✓ `post_or_reif` with `fully_reify` false | ✓ `or_if` | does not chain (#953) |

[^xand]: A top-level `and` is not posted as `And`: the walker posts each conjunct
    on its own. Inside an expression, `and` and `or` get a `{0, 1}` auxiliary,
    `andresult` or `orresult`, as the reification.

[^mznsetin]: `set_in` posts one `Or{x < l, x ≥ u}` per gap in the set.
    `set_in_reif` posts one `Or` per bound and one per gap for `r ⇒ x ∈ S`, and
    one per interval of the set for the converse. The corpus has 21,867
    `set_in_reif` posts.

[^ximp]: `a ⇒ b` becomes a `{0, 1}` auxiliary `not_a` with `a + not_a = 1` by a
    linear equality, then `Or{not_a, b}`, reified by `impresult` inside an
    expression. `xor` goes to `ParityOdd`; see [`parity.md`](parity.md).

[^cimp]: `post_implies(a, b)` posts `Or{b, 1 − a}`, with the negation as a view.
    `post_implies_reif(a, b, x, true)` posts `Or{b, 1 − a, 1 − x}` and, for the
    converse, `And{{a, 1 − b}, 1 − x}`.

[^mznimp]: MiniZinc emits the half-reified `_imp` builtins only for a solver
    library that declares them, and ours declares none. With our library,
    MiniZinc 2.9.7 flattens `c -> (a1 /\ a2)` into two `bool_clause`s and
    `c -> (a2 \/ a3)` into one, so a half-reified Boolean arrives as `Or`s with
    a true reification. `array_bool_or` has been deprecated since
    MiniZinc 2.7, which emits `bool_clause_reif` instead.

CPMpy's upstream GCS interface, checked 2026-09-23, reaches `post_and`,
`post_or`, their `_reif` forms, and `post_implies` and `post_implies_reif`. Its
workaround for `b → x ≠ y` calls `post_or_reif(…, False)` even under full
reification, which is another way into `OrIf`.

### Options

`None.`

### Variable kinds and views

Any literal over any `IntegerVariableID`: plain, constant or view. The
propagator only asks `test_literal`. The proof names each literal's atom, and a
view's literals are its own (#904). `logical_constraint_view_mixed` wraps the
positions of the variable-constructor rows in views; the literal-form rows run
bare only.

### Reification

This family **is** the reification of `∧` and `∨`, full (`And`, `Or`) and half
(`AndIf`, `OrIf`). There is no further level.

### Relation to other families

**Into this family.** MiniZinc's Boolean builtins and its `set_in` glue; XCSP3's
`and`, `or` and `imp`; CPMpy's `and`, `or` and `implies`; the `.scp` reader.
Much of the corpus's Boolean structure arrives here: `bool_clause` alone is 155
models.

**Posts as children.** Nothing.

**Shares code.** `cake_truthiness.hh` (`reify_tuple_term`, which writes a
literal as cake's reification tuple) with `parity`, and `add_trigger_for`, which
maps a literal to a trigger, with `parity` and others.

**Presolvers.** None reads or rewrites these classes.

**Reached only through a decomposition?** No; `AndIf` and `OrIf` only through
CPMpy and the `.scp`.

**Not a candidate merge.** The family list gives `logical/` alone. `parity`
shares its literal helpers but has its own encoding and propagator.

## The proof model

### OPB encoding

Definitional, and `cake_pb_cp`'s. With `n = |lits|`, `And` is two rows:

```
Σ lits − n·r ≥ 0          labelled pos:  r ⇒ every literal
Σ ¬lits − ¬r ≥ 0          labelled neg:  ¬r ⇒ some literal false
```

and `Or` their mirror:

```
Σ lits − r ≥ 0            labelled pos:  r ⇒ some literal
Σ ¬lits − n·¬r ≥ 0        labelled neg:  ¬r ⇒ every literal false
```

`AndIf` and `OrIf` are the `pos` row alone. Each row names each literal's atom
once, so the size is linear in `n` and independent of every domain. A constant
literal or reification folds into the row, so the rows' content matches cake's
whatever the literals are.

### Labels

`c[id][pos]` and `c[id][neg]`, cake's. The propagator cites neither by line or
label: every inference is a RUP against the database.

### Cake conformity

| Case | Chain | `opbdiff` |
|---|---|---|
| `scp_chain_and_sat` (`B1 ∧ B2 ⇔ Y`, enumerate) | full workflow 2 | `none` |
| `scp_chain_or_sat` | full workflow 2 | `none` |

Both chain-verify at `f28fdef8`. Neither is a label match, only because the
variables are `{0, 1}`: cake writes two bound lines per such variable where we
write one, the binary-encoding case of #358. The rows themselves are cake's.
`and_if` and `or_if` have no case: cake has no rule for either keyword, and
#953 asks for the `pos` row under the same label.

### Proof-time state

Nothing. No proof flags, no proof-only variables, nothing at the root beyond
the inferences themselves, nothing cached. Every justification is one RUP (and,
for one rule, some lemmas that do nothing; see rule 3).

## The implementation

### Initialisation and global data

Nothing at construction beyond copying the literals. `prepare()` records whether
the reification is already decided, which picks what `install_propagators`
does:

| Reification at `prepare()` | And-form half wanted | Installed |
|---|---|---|
| true | forward | an initialiser forcing every literal |
| true | backward only | nothing: the backward half is satisfied |
| false | forward only | nothing: the forward half is vacuous |
| otherwise, with a constant false literal | forward | an initialiser forcing `¬r` |
| otherwise, with a constant false literal | backward only | nothing |
| otherwise | | the propagator |

"And-form" because `Or` and `OrIf` reach this code over negated literals and
reification: `Or`'s false reification is the And-form's true one.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| root forcing | initialiser | — | 1, 2 | a decided reification or a false literal, per the table above | n/a | one shot |
| the logical propagator | per literal: `on_change` for `=`, `≠` and range literals, `on_bounds` for `<` and `≥`; the same for `r` | derived, truthfully | 1–5 | otherwise | not claimed, and nothing to claim | **yes**, after every inference |

**Idempotence and disabling.** Every call that infers anything returns
`DisableUntilBacktrack`, and every call that returns `Enable` inferred nothing.
So the engine never requeues it for its own inferences, and an idempotence claim
would buy nothing. Once it has disabled itself, nothing wakes it until
backtrack; that is safe because each disabling case leaves the constraint
entailed or fully propagated.

**Holes affect**: `=`, `≠` and range literals are watched `on_change`, because a
hole at the literal's value decides it; `<` and `≥` literals `on_bounds`,
because only a bound decides them. The triggers tell the truth, per variable.

### Mutable state and incrementality

**Nothing persists.** Each call walks the literal list from the start, asking
`test_literal` of each. With the reification false (a clause, in the Or
reading) it stops at the second undecided literal; with the reification
undecided it walks the whole list. It does not stop at a false And-form
literal either, so a clause already satisfied by a true literal, with two
undecided ones after it, returns `Enable` and is rescanned at every wake though
it is entailed. Nothing remembers where the undecided literals were, so a long
clause whose front has been fixed is rescanned from the front at every wake.

**What maintaining it would buy.** Two watched literals, the SAT solver's
scheme, would make a clause's wake constant work until a watch is lost. The
engine already has refined per-literal watches (`refined-triggers.md`). On
`network_50_cstr`, one clause of 2,774 literals is 76% of propagation time at
32 µs a call, and most of that is presumably the rescan; no watched-literal
variant was measured (#1060). For the short clauses most models post, it
would buy little.

### Interior values and optional pruning

**What this family offers:** `None.`

**What this family observes:** holes at the values its `=`, `≠` and range
literals name, through `on_change` watches, and nothing about variables watched
only through `<` and `≥`. A variable that appears here only in order literals,
as MiniZinc's `set_in` glue writes them, does not keep a neighbour's interior
pruning alive.

### Robustness and limits

- **Unbounded domains.** Nothing here walks a domain. A probe posting
  `Or{x < 10, x ≥ W − 10}` over `x ∈ [10, W]` wrote a 21-line proof at
  `W = 10³`, `10⁶` and `10⁹`.
- **Negative values and zero.** The variable constructors read `x ≠ 0` as true,
  so a negative value is true. Tested over `[−2, 5]` domains.
- **Degenerate shapes**: see [Semantics](#semantics).
- **Overflow.** The `pos` / `neg` rows carry the coefficient `n`, the number of
  literals, as an `Integer`. Nothing else is arithmetic.

### Interval efficiency

`Fine at any width`, and the family's cost is in literals.

1. **Propagation.** No value walks at all: one `test_literal` per literal, which
   is a bound or membership test on the variable. Bounded by the array, as #1060
   says, not the domain.
2. **Reasons.** One literal per literal of the constraint, or one, depending on
   the rule. Built unconditionally, in proportion to the array.
3. **Proofs.** One RUP per inference. The literal definitions the RUP needs are
   the shared layer's, and cost nothing for a `{0, 1}` variable, whose literal is
   its bit.
4. **The audit lane.** Two rows, `And` and `Or`, both `NoWidePosition` over
   three `{0, 1}` variables, which is what the lane's comment says the family
   takes. It takes more: an order literal over a wide variable, as the `set_in`
   glue posts, is the shape a width probe should vary, and no row does. The
   probe above shows it flat.

## Inference catalogue

Five rules, written in the And-form the code uses: literals `L`, reification `r`.
Each rule serves all four classes, through the negation `Or` and `OrIf` apply
before calling the template. Rules 1 and 2 are the forward half, which `And`,
`Or` and `AndIf` run; rules 3–5 the backward half, which `And`, `Or` and `OrIf`
run.

| Rule | And-form | as `And` | as `Or` (a clause when `r` is true) |
|---|---|---|---|
| 1 | `r` ⇒ every `l` | reification true: every literal true | reification false: every literal false |
| 2 | some `l` false ⇒ `¬r` | a literal false: reification false | a literal true: reification true |
| 3 | every `l` true ⇒ `r` | all true: reification true | all false: reification false |
| 4 | `¬r`, all but one `l` true ⇒ the last false | reification false, all but one true: the last false | reification true, all but one false: the last true (unit propagation) |
| 5 | `¬r`, every `l` true: conflict | | reification true, every literal false: the clause fails |

Three facts hold across them.

**The wire inventory.**

| Wire form | Hint type | Classes |
|---|---|---|
| `and:((constraint_id N))` | `hints::And` | `And`, `AndIf` |
| `or:((constraint_id N))` | `hints::Or` | `Or`, `OrIf` |

Each carries `originator` (`ConstraintID`) and no subhint. The hint name says
which reading of the literals the assertion is in; the originator says which of
the two classes, through the `.scp`.

**The rows, by reading.** The proof-technique fields below name the And-form's
rows. For `And` and `AndIf` those are the rows' own labels. For `Or` they swap:
the And-form `pos` row is `Or`'s `neg`, and the And-form `neg` row is `Or`'s
`pos`. `OrIf` has only the row the And-form calls `neg`, labelled `pos`; so a
clause's unit propagation (rule 4) is against `Or`'s `pos` row.

**What licenses them.** Every rule is `RUP` against one of the two rows.
With the rule's literals fixed, the row's slack forces the conclusion by unit
propagation over that one row (**Proposition 2.1**, a constraint propagates a
literal exactly when its slack is below the literal's coefficient), and
**Theorem 2.6** accounts for stating it under a reason. No lemma is needed. The
atoms are the literals' own, defined by the shared layer. The encoding is
cake's; the thesis gives no encoding or procedure for `And` or `Or`, so the
rules are ours, though nothing about them is more than one step of unit
propagation.

**Tightness.** No mutation lane.

### Rule: reif-forces-literals

(Rule 1; forward half.)

- **Infers** — every literal of `L` true (for `Or`: every literal false).
- **Fires when** — the root initialiser, when `r` is true at `prepare()`; or the
  propagator, when `r` becomes true.
- **Strength** — `partial`; with rules 2–5, `GAC` on the constraint when its
  literals are over different variables. Not otherwise: two literals over one
  variable count as two undecided literals, so a repeated literal, or
  `Or{x < 3, x ≥ 5}`, is not pruned until search decides it. Sound either way.
- **Algorithm** — one inference per literal, `O(n)`.
- **Why it is true** — a true conjunction has every conjunct true.
- **Proof technique** — `RUP` against `pos`: with `r` true, `Σ L ≥ n` forces
  every literal.
- **Reason** — `{r}` per literal, at the root and in the propagator.
- **Assertion** — `l ∨ ¬r`, per literal.
- **Hint** — `hints::And` or `hints::Or`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `offline`: an unhinted RUP of the assertion
  succeeds.
- **Proof size** — one line per literal. Over `{0, 1}` variables that is the
  whole of it: a probe forcing `n` literals wrote `n + 7` lines. Over `0..9`,
  `15n + 7`, the rest being literal definitions.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: false-literal-forces-not-reif

(Rule 2; forward half.)

- **Infers** — `¬r`.
- **Fires when** — the root initialiser, when a literal is the constant false;
  or the propagator, when a literal becomes false and `r` is undecided.
- **Strength** — `partial`, as rule 1.
- **Algorithm** — the scan that finds the literal, `O(n)`.
- **Why it is true** — one false conjunct makes the conjunction false.
- **Proof technique** — `RUP` against `pos`.
- **Reason** — `{¬l}`, one literal; none at the root.
- **Assertion** — `¬r ∨ l`.
- **Hint** — `hints::And` or `hints::Or`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: all-true-forces-reif

(Rule 3; backward half.)

- **Infers** — `r`.
- **Fires when** — the propagator, with `r` undecided and every literal true.
- **Strength** — `partial`, as rule 1.
- **Algorithm** — the scan, `O(n)`.
- **Why it is true** — a conjunction whose conjuncts all hold holds.
- **Proof technique** — `RUP` against `neg`, which is all it needs. The code
  emits a lemma `l ≥ 1` under the reason for each literal first, and **those
  lemmas do nothing**: the reason is exactly the literals, so each lemma is its
  own hypothesis. With them removed, `logical_test` verifies at seeds 1 to 10
  and under all 18 view wraps at every position choice at seed 1 (54 runs); at
  seed 1 the switch removes 100
  lines, so it took effect.
- **Reason** — every literal of `L`. Minimal.
- **Assertion** — `r ∨ ¬reason`.
- **Hint** — `hints::And` or `hints::Or`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — `n + 2` lines as written (the lemmas, a deletion of them,
  and the RUP); one without the lemmas.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: last-literal-forced

(Rule 4; backward half.)

- **Infers** — the one undecided literal false (for `Or`: true, which is a
  clause's unit propagation).
- **Fires when** — the propagator, with `r` false, no literal false, and exactly
  one undecided.
- **Strength** — `partial`, as rule 1.
- **Algorithm** — the scan stops at the second undecided literal, from the start
  of the list; it walks the whole decided prefix every wake (#1060).
- **Why it is true** — with every other conjunct true, the last one decides the
  conjunction, which must be false.
- **Proof technique** — `RUP` against `neg`.
- **Reason** — every other literal, and `¬r`.
- **Assertion** — `¬u ∨ ¬reason`.
- **Hint** — `hints::And` or `hints::Or`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line, of `n + 1` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: conflict

(Rule 5; backward half.)

- **Infers** — a contradiction, reported by `contradiction_or_stop`, which stops
  the propagator rather than throwing. The comment says why: for a clause this is
  the failure at a large share of nodes, and on `2014_train` the unwinding was
  22% of the run.
- **Fires when** — the propagator, with `r` false and every literal true.
- **Strength** — `partial`, as rule 1.
- **Algorithm** — the scan.
- **Why it is true** — the conjunction holds, so `r` cannot be false.
- **Proof technique** — `RUP` against `neg`.
- **Reason** — every literal and `¬r`.
- **Assertion** — `¬reason`.
- **Hint** — `hints::And` or `hints::Or`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

| Lane | What it checks |
|---|---|
| `logical_constraint` | `logical_test`: 14 fixed and 10 random rows over the variable constructors, each for all four classes (the unreified rows skip `AndIf` and `OrIf`), under `solve_for_tests_checking_gac`; ten random literal-form rows (random operators and values, some decided at the start); the constant-literal rows; repeated-literal rows and the reification-among-the-literals rows under plain enumeration; all with and without proofs |
| `logical_constraint_view_mixed` | the variable-constructor rows with positions wrapped in views |
| `scp_chain_and_sat`, `scp_chain_or_sat` | see [Cake conformity](#cake-conformity) |
| `xcsp_intension_boolean` | `and(imp(a, b), iff(b, not(c)))` and `xor(a, c, d)`: the top-level `and` splits, so the only logical constraint it reaches is the `Or` from `imp` |
| `scp_reader_test` | reads `and_if` and `or_if` back and enumerates them (5 and 7 solutions), and round-trips them |
| `minizinc-arraybooland` | `array_bool_and` against MiniZinc's default solver |

All pass at `f28fdef8`, caps off, with MiniZinc 2.9.7, `cake_pb_cp` and
`opbdiff` on the path. At `--seed=1`, `logical_test` verifies 168 proofs.
Almost every other MiniZinc lane posts clauses too, through the flattening.

**Runtime caps.** No lane sets or clears one, and **the defaults fire**: three
unseeded runs each, with the 300-solution and 1,500-node caps passed in the
environment, truncated 8, 12 and 8 solves in the bare lane and 14, 8 and 12 in
the view lane. So the capped run checks soundness and a partial proof on those
solves only; the numbers here come from an uncapped build.

**Rules the tests reach**, from local counters at `--seed=1`: all five, both at
the root and in the propagator where a rule has both (rule 1 forced 76 literals
at the root and 86 in the propagator; rule 2 fired 6 and 132 times), rule 3 64
times, rule 4 36 and rule 5 16.

**What the tests do not cover:**

- **A long clause.** Every row has at most four literals, so the scan's cost is
  invisible to them (#1060).
- **Literal-form rows under views**, which run bare only.
- **Consistency on the aliased rows**, which use plain enumeration. The
  propagator is not `GAC` there; see rule 1.
- **Range literals**, which the literal-form rows never draw, so nothing shows
  that they throw with proofs on (#310).
- **`and` or `or` inside an XCSP3 expression.**
- **The `gcspy` path to the half-reified forms**: `python_test.py` has
  `test_and_if` and `test_or_if`, but they are commented out of
  `python/CMakeLists.txt`, and there is no CPMpy test in the tree.

### Benchmarks and examples

- **In-repo**: no example isolates the family; nearly every model posts it.
- **The corpus** (297 MiniZinc Challenge models, one instance each, flattened
  2026-09-05): `bool_clause` 391,679 posts in 155 models, `array_bool_and`
  126,498 in 91, `set_in_reif` 21,867 in 43, `bool_clause_reif` 14,323 in 36.
- **Where it is the cost** (share of propagation time, 10 s each, at `00797a97`,
  from `linear.md`'s survey; `logical/` is unchanged since): `Or` appears in 171
  models with a median share of 2.2%, at least half in five (`rubik` 2013 100%,
  `network_50_cstr` 2024 75%, `grid-colouring` 2011 and 2010 54%, `valve-network`
  2023 52%) and at least a fifth in 17. `And` appears in 84, median 1.2%, at most
  30% (`monomatch` 2021). `Or` typically costs 0.14–0.32 µs a call (the survey's
  10th to 75th percentiles), and `And` 0.3–0.4.
- **For CPU**: `grid-colouring` 2011 (`10_10`) to its fifth solution, 0.76 s;
  `solbat` 2010 (`sb_12_12_5_0`), all 51 solutions, 7.2 s; `network_50_cstr`
  (`MODEL1507180015`) for the long clause, which finds nothing in 30 s.
- **For proofs**: `solbat` 2010, all 51 solutions: 9.9 million lines, 7 minutes
  of checking.

### CPU performance

All at `f28fdef8`, Release, GCC 15.2.0, fataepyc-09 (EPYC 7643, boost off),
pinned with `numactl --cpunodebind=0 --membind=0 taskset -c 8 setarch -R`,
2026-09-23, unmodified build; three runs each, except `network_50_cstr`, run
once per solver. The share column is from the survey at `00797a97`, except
`network_50_cstr`'s, measured below.

**Against Gecode 6.3.0**, each flattened with its own library and run by its own
FlatZinc binary. None of these is a pure test of this family, since the models
mix constraints; the share column says how much of our propagation it is.

| instance | to | GCS nodes | GCS s | Gecode nodes | Gecode s | ratio | `Or` / `And` share |
|---|---|---|---|---|---|---|---|
| `grid-colouring` 2011 | 5th solution | 74,217 | 0.759 / 0.760 / 0.760 | 74,207 | 1.630 / 1.632 / 1.611 | **0.47×** | 54% / — |
| `solbat` 2010 | all 51 | 27,077 | 7.189 / 7.151 / 7.151 | 26,597 | 1.912 / 1.911 / 1.918 | 3.7× | 30% / 10% |
| `network_50_cstr` 2024 | 30 s, no solution | 145,102 in 30 s | | 1,169,939 in 30 s | | 8× fewer nodes | 76% / — |

On `grid-colouring` both find the same five solutions, and we are twice as fast.
On `solbat` both enumerate the same 51 solutions in the same order, at node
counts 2% apart; why they differ was not looked into. On `network_50_cstr`
neither finds a solution, and the node rates are not a like-for-like comparison
of anything but throughput.

**The long clause**, `network_50_cstr` for 20 s with `GCS_PROPAGATOR_STATS=time`:
propagation is 7.1 s of the 20.0 s solve, and `Or` is 75.7% of that, over
167,571 calls at 32.0 µs each. There is one `bool_clause` in the model, over
all 2,774 of the Booleans `Zs` that the search annotation branches on, so the
literals the search has fixed are rescanned at every wake.

**What these benchmarks exercise**: all five rules, by the shape of the models
(clauses reach rules 4 and 5, reified conjunctions all five). Not counted per
rule on the corpus.

### Proof performance

**`solbat` 2010, all 51 solutions** (27,077 nodes):

| | solve | proof | VeriPB |
|---|---|---|---|
| proofs off | 7.2 s | — | — |
| `AssertionLevel::Off` | 22.4 s | 9,864,447 lines, 2.0 GB | 429.0 s, `VERIFIED` |
| `AssertionLevel::Inferences` | 21.8 s | 7,646,467 lines, 1.8 GB | 37.7 s, `UNDER ASSERTIONS` |

**Assertions at `Inferences`**, 7,565,126: `equals` 4,572,375, `or` 1,540,555,
`linear_equality` 716,999, `and` 708,069, and the solver's own `backtrack`
27,077 and `solx_block` 51. This family is 30% of them, and each is one RUP
when justified. Across all families, the justified proof is 2.2 million lines
longer than the asserted one, for 7.6 million assertions.

**Own against shared**, from the forcing probe: an `And` over `n` literals with
`r` fixed true. Over `{0, 1}` variables the proof is `n + 7` lines, of which `n`
are this family's RUPs. Over `0..9` it is `15n + 7`: still `n` of this family's,
and `14n + 7` of the rest, mostly per-variable literal definitions at the root
and for the solution's `solx` line. So for this family the shared
layers are all of the proof beyond one line per inference, and none of it over
Booleans.

## Status, gaps, and next steps

### Proof-logging gaps

**One, already filed: #310.** A range literal (`x ∈ [l, u]` or its negation)
in any of the four classes throws `UnimplementedException` from model writing
when proofs are on, because the names-and-IDs tracker cannot yet state one in
the OPB. With proofs off the answers are right. No front end posts a range
literal here; the C++ API can. Otherwise every inference is one justified RUP,
nothing is asserted at `AssertionLevel::Off`, and the propagator is the same
with proofs on and off.

### Known limitations

- **A long clause is slow**: every wake rescans the literals from the front
  (#1060).
- **Not generalised arc consistent over two literals on one variable**, which
  is the shape MiniZinc's `set_in` glue posts.
- **A range literal throws with proofs on** (#310).
- **`AndIf` and `OrIf` do not chain through `cake_pb_cp`** (#953), and no front
  end but CPMpy posts them.

### Next steps

Ranked by what they buy for what they cost.

1. **#1060** — two watched literals for the clause case (`r` false in the
   And-form), through the engine's refined watches, and stop at a satisfying
   literal. A real change to a propagator on one of the solver's hot paths, so
   it wants the corpus's clause models as a regression set, not just
   `network_50_cstr`.
2. **The `set_in` glue.** `Or{x < l, x ≥ u}` never removes the gap `[l, u − 1]`;
   an unreified `set_in` could remove it at the root instead, as a domain
   restriction. Small, in the front end; 76 posts in 4 corpus models. The
   reified form has the same shape with a third literal. Unfiled.
3. **Drop rule 3's lemmas.** One RUP per literal that the reason already states.
   A few lines; they are 100 of `logical_test`'s 75,220 proof lines at seed 1,
   so it is tidying, not a saving. Unfiled.
4. **Tests.** A long clause in `logical_test`, so the scan cost is visible; the
   literal-form rows under views; and a width row over an order literal in the
   audit lane. Unfiled.

## Prior art

Clauses are the SAT solver's constraint, and two watched literals (Moskewicz et
al., *Chaff*, DAC 2001) the standard propagation. Gecode's propagators for a
clause with a fixed true reification, `ClauseTrue` and `NaryOrTrue`, keep two
watched views and move them (`int/bool/clause.hpp`); the reified one counts
instead. Nothing is novel on the proof side: each inference is one RUP against a
linear row of the constraint's own encoding, which is the case VeriPB's unit
propagation handles natively. McIlree's thesis treats disjunctions of
conjunctions of *constraints* (§4.2, for smart tables), which is a different
problem.

## Further reading

- [`reification.md`](../reification.md): the reification conventions the rest of
  the solver uses, of which this family is the Boolean case.
- [`refined-triggers.md`](../refined-triggers.md): the per-literal watches that
  #1060 would build on.
- [`parity.md`](parity.md): the XOR constraint, which shares this family's
  literal helpers.
