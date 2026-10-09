# Logical: `And`, `Or`, and their half-reified forms

> **Maturity** production ·
> **Audited** 2026-09-23 at `f28fdef8`; re-audited 2026-09-26 at `c9ceea25` ·
> **Open issues** filed by this audit: none left open. #1060 is fixed; see
> [Re-audit, 2026-09-26](#re-audit-2026-09-26). Already open and touching this
> family: #310 (range literals cannot be written into the model, so a range
> literal here throws with proofs on), #868 (cross-solver). `cake_pb_cp` has no
> rule for `and_if` / `or_if` (#1100; #953, which asked for `AndIf` and `OrIf`,
> closed on 2026-09-18 when #958 added them). Tracked under #871.

Four classes over one template and two propagators. `And(lits, r)` says `r ⇔ ∧ lits`, and
`Or(lits, r)` says `r ⇔ ∨ lits`. `AndIf` and `OrIf` are their half-reified
forms, `r ⇒ ∧ lits` and `r ⇒ ∨ lits`. One template, `install_propagators_logical`,
implements all four: `Or` is `And` over the negated literals and reification,
and the half forms keep one direction of it. MiniZinc's `bool_clause` is an `Or`
with a true reification: 391,679 clauses in 155 of the corpus's 297 models.
Only the `equals` and `linear` families are posted more.

Three things to know before touching it.

- **It is generalised arc consistent when its literals are over different
  variables, and cheap per call.** Two literals over one variable break the
  first: the propagator sees them as two undecided literals, so
  `Or{x < 3, x ≥ 5}`, which is what MiniZinc's `set_in` glue posts, never
  prunes 3 or 4. For the second, each call of the scan walks the literals from
  the start of the list. It stops once it has seen two undecided literals or a
  satisfying one, and nothing remembers where it got to. For the short clauses
  most models post that was typically 0.14–0.4 µs a call before #1105. A clause
  of 128 literals or more whose reification is decided at install watches two
  of its literals instead ([Options](#options)). `network_50_cstr` posts one
  clause over 2,774 literals. It used to be 76% of that model's propagation
  time, at 32 µs a call. Since #1105 it is 0.03%, at 0.57 µs. Most of that is
  the scan disabling a satisfied clause, not the watches (#1060; [CPU
  performance](#cpu-performance)).
- **Every inference is one RUP against one of two model rows.** The encoding is
  `cake_pb_cp`'s: a `pos` row saying the reification implies the conjunction
  (or disjunction), and a `neg` row for the converse, each linear in the number
  of literals. The half forms have the `pos` row only, and they cannot chain
  through cake yet: `cake_pb_cp` rejects `and_if` and `or_if` outright (#1100;
  see [Cake conformity](#cake-conformity)).
- **The half-reified forms are reachable only from CPMpy and the `.scp`.**
  MiniZinc turns a half-reified Boolean into plain clauses for this library,
  and XCSP3 has no such form. The `.scp` path is tested; the Python tests of the
  `gcspy` path are not registered with `ctest`.

## Re-audit, 2026-09-26

The audit's one issue, #1060, was fixed by #1105, merged on 2026-09-25. This
pass brings the text into line with it at `c9ceea25`, and re-measures what it
touched.

| issue | PR | what it changed here |
|---|---|---|
| #1060 | #1105 | Three changes to `logical.cc`. **(1)** The scan stops at the first false And-form literal: with `r` false that disables a satisfied clause when the scan meets a
satisfying literal before a second undecided one, and with `r` undecided rule 2 now names the first false literal, not the last. **(2)** Every reason is built only when `want_reasons()` says it will be read. **(3)** The clause case of 128 literals or more gets a new watched-clause propagator, with `with_watch_threshold()` and `GCS_CLAUSE_WATCH_THRESHOLD`. Changes the summary, [Options](#options), the initialisation table, the [inventory](#propagator-inventory), [Mutable state](#mutable-state-and-incrementality), [Interval efficiency](#interval-efficiency), rules 2, 4 and 5, [Tests](#tests), both performance sections, the limitations and Next steps. |
| #1106 | #1107 | Not this family's code. `NegativeTable` and the fixed-store `Nogoods` kept their "armed" marker outside `watch_state`, and with an `AutoTable` presolver attached they lost every watch. #1105's watched clause already kept its marker in `watch_state`, and `logical_test`'s clause sets run behind an `AutoTable` to hold it there. Changes [Mutable state](#mutable-state-and-incrementality) and [Tests](#tests). |

**Re-measured at `c9ceea25`**, on the same machine, now with malloc's
thresholds pinned: the three CPU instances, the long clause at 20 s and at
fixed work against `a94ca5ac`, `solbat`'s proofs at both levels with VeriPB,
the test counts and caps, and the Gecode baseline, in the same sitting. The
corpus survey was not re-run. `solbat`'s proof at `Inferences` has the same
number of lines as before #1105. Compared line by line with `a94ca5ac`'s,
133,260 lines differ, all of them `and`-hinted assertions, which is what rule
2's new choice of false literal predicts.

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
| `AndIf` | `unsupported`[^mznimp] | `n/a` | ✓ `post_and_reif` with `fully_reify` false | ✓ `and_if` | does not chain: cake has no rule[^cakeif] |
| `OrIf` | `unsupported`[^mznimp] | `n/a` | ✓ `post_or_reif` with `fully_reify` false | ✓ `or_if` | does not chain: cake has no rule[^cakeif] |

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

[^cakeif]: The `.scp` keeps its own `and_if` / `or_if` keywords, so the chain
    can start once `cake_pb_cp` gains a rule for them. It has none today
    (#1100); see [Cake conformity](#cake-conformity).

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

**The clause watch threshold**, `with_watch_threshold()` on `And`, `Or` and
`OrIf`, unset by default. Unset means
`innards::default_clause_watch_threshold()`: `GCS_CLAUSE_WATCH_THRESHOLD` if
it is set, read once per process, and otherwise 128. A per-constraint value
wins over the environment. `AndIf` has no such method, because it never
reaches the case the threshold is about.

The threshold matters only in the **clause case**: the And-form reification
is false at `prepare()` and the backward half is wanted, so all that is left
is "not every And-form literal holds". That is an unreified `Or` (every
`bool_clause`), an `Or` whose reification is true at `prepare()`, an `And`
whose reification is false there, and an `OrIf` whose condition is true
there. In each case, no literal may be the constant that satisfies the
clause. If one is, no propagator is installed: `And` and `Or` get only a root
initialiser forcing the reification, which already holds, and `OrIf` gets
nothing. A reification that is decided later,
during search, does not count. A clause with at least the threshold's number of literals gets the watched-clause
propagator, and a shorter one the scan ([Propagator
inventory](#propagator-inventory)).

It picks a strategy, never a model: neither `define_proof_model` nor `s_expr`
reads it, and `clone()` carries it. The two propagators reach the same
fixpoint, and each inference is the same RUP with the same reason (rules 4
and 5). What has been checked is equal recursion counts between
the two on `logical_test`'s clause sets, with and without restarts
([Tests](#tests)), and #1105's corpus runs, which saw identical nodes,
failures and solutions on the clause-heavy models it measured. The default
comes from `benchmarks/clause_watch_bench`, where watching overtook the scan
between 64 and 192 literals depending on the instance, because firing a watch
costs more than scanning a short clause. `refined-triggers.md` has the
measurements. No front end sets the threshold; the environment variable is
how the test lanes force the watched path.

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
`and_if` and `or_if` have no case: cake has no rule for either keyword. Checked
2026-09-25 with the local `cake_pb_cp` (CakePB-dev `a402078`): `and_sat.scp`
with its keyword changed to `and_if`, or `or_sat.scp` to `or_if`, prints
`unsupported constraint: and_if` (resp. `or_if`). What cake would need is the
`pos` row alone, under the same label; #958, which added the classes and
closed #953 on 2026-09-18, says so under "What to ask cake for". #1100 now
tracks the cake side; this review did not find an upstream issue.

### Proof-time state

Nothing. No proof flags, no proof-only variables, nothing at the root beyond
the inferences themselves, nothing cached. Every justification is one RUP (and,
for one rule, some lemmas that do nothing; see rule 3). The watched clause's
`watch_state` is search state. It names nothing in the proof, and a justifier
needs none of it.

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
| false, with at least the [watch threshold](#options) of literals | backward | the watched-clause propagator |
| otherwise | | the scan |

"And-form" because `Or` and `OrIf` reach this code over negated literals and
reification: `Or`'s false reification is the And-form's true one.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| root forcing | initialiser | — | 1, 2 | a decided reification or a false literal, per the table above | n/a | one shot |
| the scan | per literal: `on_change` for `=`, `≠` and range literals, `on_bounds` for `<` and `≥`; the same for `r` | derived, truthfully | 1–5 | otherwise | not claimed, and nothing to claim | **yes**, after every inference, and on meeting a satisfying literal before a second undecided one in the clause case |
| the watched clause | refined watches on two literals it picks and moves; `scope_only` over every variable the scan would trigger on, `r`'s included | declared: the variables of `=`, `≠` and range literals, and `r`'s if it is one | 4, 5 | the clause case at or above the [watch threshold](#options) | not claimed, and nothing to claim | **yes**, after every inference, and when a watched literal, or one a watch moves to, is satisfying |

**Idempotence and disabling.** For both propagators, every call that infers
anything returns `DisableUntilBacktrack`, and every call that returns `Enable`
inferred nothing. So the engine never requeues either for its own inferences,
and an idempotence claim would buy nothing. Once one has disabled itself,
nothing wakes it until backtrack. That is safe, because each disabling case
leaves the constraint entailed or fully propagated.

Both also disable on a satisfied clause, but only when they see what satisfies
it:
- The scan with `r` false disables at a false And-form literal (a true literal
  of an `Or` clause) if it meets it before a second undecided literal. Before
  #1105 it went on to the second undecided literal, if there was one, and
  returned `Enable`. A satisfied clause whose satisfying literals all come
  after two undecided ones still returns `Enable` ([Known
  limitations](#known-limitations)).
- The watched clause disables only when a watched literal, or the literal a
  watch moves to, is satisfying. Otherwise a satisfied clause keeps its watches
  and goes on waking when they fire.

The watched clause's watches go on firing while it is disabled. They are
consumed and restored like any other fire, and backtracking out of the call
that disabled it restores the watches and re-enables it together.

**Holes affect**: `=`, `≠` and range literals are watched `on_change`, because a
hole at the literal's value decides it; `<` and `≥` literals `on_bounds`,
because only a bound decides them. The scan's triggers tell the truth, per
variable. The watched clause's scope goes through `scope_only`, which keeps
each variable's degree what the scan gives it, so a degree-based brancher
searches the same tree either way. But `scope_only` on its own would derive
that holes in every variable matter, the order literals' variables included.
So the propagator declares `holes_affect_propagation` to be exactly the
variables the scan puts `on_change`, the same set the scan derives.

### Mutable state and incrementality

**The scan keeps nothing.** Each call walks the literal list from the start,
asking `test_literal` of each:
- With `r` true, it forces every literal if the forward half is wanted.
- With `r` false (a clause, in the `Or` reading), it stops at the second
  undecided literal or the first false one, whichever comes first.
- With `r` undecided, it stops at the first false literal, or else walks the
  whole list.

A satisfied clause whose first true `Or` literal comes after two undecided ones
still returns `Enable`, and is rescanned at every wake until that changes.
Before #1105, the scan did not stop at a false And-form literal at all. So a
clause already satisfied by a true literal, with two undecided ones anywhere,
returned `Enable` and was rescanned at every wake. That, more than the length
of the walk, was `network_50_cstr`'s cost ([CPU
performance](#cpu-performance)).

**The watched clause keeps its place.** It has two refined watches, and two
`watch_state` entries. Key 0 packs the two watched positions into the two
32-bit halves of one word. Key 1 records whether the watches have been armed
at all. Both entries are backtrackable, restored in lockstep with the watches.
The first run arms two literals that are not entailed, searching from the
front. After that, a fire moves a watch forwards from just after the later of
the two, and never back round. Every literal before the later watch, other
than the two watched, is entailed. That holds when the watches are armed, each
move passes over only entailed literals, and a backtrack returns the positions
to ones that held it at that level. So along one branch, the watches' walks
add up to at most the clause's length. The armed flag is in `watch_state`, not
in a non-backtrackable marker, for a reason found while writing it.
The `AutoTable` presolver runs every propagator at the root of a search of its
own, then backtracks out of it. A marker that survived that backtrack would
leave the real root arming nothing, and the clause dead. `NegativeTable` and
the fixed-store `Nogoods` had exactly that bug (#1106 → #1107).

**What maintaining the scan's position would buy** is now small. On the
corpus, what matters is the early stop, which both propagators have. The
watches were worth 1.9% of user cycles over the fixed scan on each of
`network_50_cstr` and `sdn-chain` in #1105's measurements. This pass measured
2.5% of instructions on `network_50_cstr` at fixed work, and a cycles
difference within run-to-run noise. A
watch costs more than it saves on a short clause. That is what the threshold is for.

### Interior values and optional pruning

**What this family offers:** `None.`

**What this family observes:** holes at the values its `=`, `≠` and range
literals name, through `on_change` watches, and nothing about variables watched
only through `<` and `≥`. A variable that appears here only in order literals,
as MiniZinc's `set_in` glue writes them, does not keep a neighbour's interior
pruning alive. The watched clause declares the same set, rather than let its
`scope_only` scope derive every variable ([Propagator
inventory](#propagator-inventory)). So which propagator a clause gets does not
change what `consistency::Auto` sees.

### Robustness and limits

- **Unbounded domains.** Nothing here walks a domain. A probe posting
  `Or{x < 10, x ≥ W − 10}` over `x ∈ [10, W]` wrote a 21-line proof at
  `W = 10³`, `10⁶` and `10⁹`.
- **Negative values and zero.** The variable constructors read `x ≠ 0` as true,
  so a negative value is true. Tested over `[−2, 5]` domains.
- **Degenerate shapes**: see [Semantics](#semantics).
- **Overflow.** The `pos` / `neg` rows carry the coefficient `n`, the number of
  literals, as an `Integer`. The watched clause packs each of its two watched
  positions into 32 bits of one `watch_state` word. So a clause of more than
  2³² literals, whose positions reach 2³², would alias them, and nothing
  checks for one. Nothing else is arithmetic.

### Interval efficiency

`Fine at any width`, and the family's cost is in literals.

1. **Propagation.** No value walks at all: one `test_literal` per literal, which
   is a bound or membership test on the variable. The scan's walk is bounded by
   the array, not the domain. So is the watched clause's, and along one
   branch its walks add up to at most the array.
2. **Reasons.** One literal per literal of the constraint, or one, depending on
   the rule. Since #1105, every reason is built only when `want_reasons()` says
   something will read it. Before that, all of them were built unconditionally,
   in proportion to the array.
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
run. The scan runs all five. The watched clause runs rules 4 and 5 only, since
its reification is false from the start. For each, it makes the same inference
with the same reason and the same RUP as the scan, and only finds the literals
differently.

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
  scan, when `r` becomes true.
- **Strength** — `partial`; with rules 2–5, `GAC` on the constraint when its
  literals are over different variables. Not otherwise: two literals over one
  variable count as two undecided literals, so a repeated literal, or
  `Or{x < 3, x ≥ 5}`, is not pruned until search decides it. Sound either way.
- **Algorithm** — one inference per literal, `O(n)`.
- **Why it is true** — a true conjunction has every conjunct true.
- **Proof technique** — `RUP` against `pos`: with `r` true, `Σ L ≥ n` forces
  every literal.
- **Reason** — `{r}` per literal, at the root and in the scan.
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
  or the scan, when a literal becomes false and `r` is undecided.
- **Strength** — `partial`, as rule 1.
- **Algorithm** — the scan, which stops at the first false literal, `O(n)`.
- **Why it is true** — one false conjunct makes the conjunction false.
- **Proof technique** — `RUP` against `pos`.
- **Reason** — `{¬l}` for the first false literal the scan meets; none at the
  root. Before #1105 the scan walked on to the end, so it gave the last false
  literal instead. Either is minimal.
- **Assertion** — `¬r ∨ l`.
- **Hint** — `hints::And` or `hints::Or`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: all-true-forces-reif

(Rule 3; backward half.)

- **Infers** — `r`.
- **Fires when** — the scan, with `r` undecided and every literal true.
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
- **Fires when** — either propagator, with `r` false, no literal false, and
  exactly one undecided. For the watched clause, that is when a watch fires and
  only one literal that is not entailed is left among the two watched and those
  after them, or when arming finds only one. That literal is forced.
- **Strength** — `partial`, as rule 1.
- **Algorithm** — the scan walks from the start of the list, and stops at the
  second undecided literal or the first false one. So it walks the whole
  decided prefix at every wake. Before #1105 it did not stop at a false
  literal, so a satisfied clause with two undecided literals was rescanned at
  every wake, which was most of #1060. The watched clause searches forwards
  only, from after both watches.
- **Why it is true** — with every other conjunct true, the last one decides the
  conjunction, which must be false.
- **Proof technique** — `RUP` against `neg`.
- **Reason** — every other literal, and `¬r`. Like every reason here, it is
  built only when `want_reasons()` says it will be read, since #1105.
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
- **Fires when** — either propagator, with `r` false and every literal true.
  For the watched clause, that is when both watches have fired and nothing
  unentailed is left after them, or at arming when nothing is unentailed at
  all.
- **Strength** — `partial`, as rule 1.
- **Algorithm** — the scan, or the watched clause's forward search.
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
| `logical_constraint` | `logical_test`: 14 fixed and 10 random rows over the variable constructors, each for all four classes (the unreified rows skip `AndIf` and `OrIf`), under `solve_for_tests_checking_gac`; ten random literal-form rows (random operators and values, some decided at the start); the constant-literal rows; repeated-literal rows and the reification-among-the-literals rows under plain enumeration; and, since #1105, twelve random **clause sets** (below); all with and without proofs |
| `logical_constraint_view_mixed` | the variable-constructor rows with positions wrapped in views |
| `logical_constraint_watched` | the whole of `logical_test` with `GCS_CLAUSE_WATCH_THRESHOLD=0`, so every row in the clause case gets the watched clause however short it is (#1105) |
| `logical_constraint_watched_view_mixed` | the view-wrapped rows with the threshold at 0 (#1105) |
| `scp_chain_and_sat`, `scp_chain_or_sat` | see [Cake conformity](#cake-conformity) |
| `xcsp_intension_boolean` | `and(imp(a, b), iff(b, not(c)))` and `xor(a, c, d)`: the top-level `and` splits, so the only logical constraint it reaches is the `Or` from `imp` |
| `scp_reader_test` | reads `and_if` and `or_if` back and enumerates them (5 and 7 solutions), and round-trips them |
| `minizinc-arraybooland` | `array_bool_and` against MiniZinc's default solver |

**The clause sets** (`run_clause_set_test`, #1105). The other rows have at
most four literals, which gives two watches nowhere to move. There are twelve
sets:
- six over ten Boolean variables, with `=` literals;
- six over six variables in `0..2`, with `=`, `≠`, `<` and `≥` literals.

Each set has 8 to 24 clauses. Half are two or three literals long, to force
literals and fail. The rest run from two literals to two more than there are
variables, so some repeat a variable, a literal, or its complement. Each clause
is posted in one of the four forms that reach the clause case: an unreified
`Or`, an `Or` whose reification is a variable fixed at 1, an `And` over the
negated literals with a false reification, and an `OrIf` with a true
condition. Each set is solved:
- watched (threshold 0, per constraint) and then scanned (threshold ∞),
  against a brute-force enumeration and with the watched run's proof verified,
  requiring equal recursion counts;
- to one solution under Luby restarts, and again with every solution blocked by
  one more clause, which restarts 4 to 61 times at `--seed=1` before it proves
  there are none. Watched and scanned must take the same recursions and
  restarts, and the watched proofs are verified.

Every set runs with and without an `AutoTable` presolver over the fixed
variable, which is the shape that killed a non-backtrackable arming marker
([Mutable state](#mutable-state-and-incrementality)). The clause sets draw no
views and no range literals. #1105 lists the mutations they catch: no forced
inference, a dropped reason literal, a skipped candidate, a lost kept watch, a
premature disable, and the non-backtrackable marker under `AutoTable`.

At `c9ceea25`, uncapped and at `--seed=1`, `logical_test` verifies 240 proofs
in the bare lane and 240 at threshold 0. At `f28fdef8` it verified 168; the
clause sets add 72. The view-mixed lane at threshold 0 verifies 92. The nine
lanes above pass under `ctest` at `c9ceea25`, with MiniZinc 2.9.7,
`cake_pb_cp` and `opbdiff` on the path, and both chain lanes report the full
workflow 2. Almost every other MiniZinc lane posts clauses too, through the
flattening.

**Runtime caps.** No lane sets or clears one, and **the defaults fire**. At
`f28fdef8`, three unseeded runs each, with the 300-solution and 1,500-node
caps passed in the environment, truncated 8, 12 and 8 solves in the bare lane
and 14, 8 and 12 in the view lane. At `c9ceea25`, the same three runs per lane
truncated:

| lane | solves truncated | clause-set cross-checks skipped |
|---|---|---|
| bare | 16, 16, 32 | 4, 4, 8 |
| view-mixed | 8, 8, 8 | — (runs no clause sets) |
| threshold 0 | 28, 24, 8 | 4, 8, 0 |
| threshold 0, view-mixed | 8, 20, 8 | — (runs no clause sets) |

The two bare lanes make 48 `run_clause_set_test` calls each: twelve sets,
with and without `AutoTable`, with and without proofs. Each call makes two
capped solves, watched and scanned, whose comparison is what a cap skips, and
then its restart solves, which the caps do not touch. A clause set whose
solve a cap stops skips its watched-against-scanned comparison, since the two
runs stop after the same number of nodes, not at the same place. So the capped
run checks soundness and a partial proof on those solves only. The numbers
here come from direct, uncapped runs of the binary.

**Rules the tests reach**, from local counters at `--seed=1` at `f28fdef8`,
before the clause sets and the watched clause existed: all five, both at the
root and in the scan where a rule has both (rule 1 forced 76 literals at
the root and 86 in the scan; rule 2 fired 6 and 132 times), rule 3 64
times, rule 4 36 and rule 5 16. The watched clause's rules 4 and 5 were not
counted this pass. That the clause sets reach its forcing, its moves and its
disabling is shown instead by #1105's mutations, each of which they catch.

**What the tests do not cover:**

- **A clause at the default threshold.** The longest clause in the fixture has
  twelve literals, so the watched clause runs only because the clause sets and
  the threshold-0 lanes force it. No lane runs a clause of 128 literals or more
  as a model would. `benchmarks/clause_watch_bench` does, but it is a
  benchmark and checks nothing.
- **The watched clause under views or range literals.** The clause sets draw
  neither, so views reach it only through the view-mixed lane at threshold 0,
  over the variable-constructor rows.
- **Literal-form rows under views**, which run bare only.
- **Consistency on the aliased rows**, which use plain enumeration. Neither
  propagator is `GAC` there; see rule 1.
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
  from `linear.md`'s survey, so **before #1105**, which changed both propagators
  and has not been re-surveyed): `Or` appears in 171
  models with a median share of 2.2%, at least half in five (`rubik` 2013 100%,
  `network_50_cstr` 2024 75%, `grid-colouring` 2011 and 2010 54%, `valve-network`
  2023 52%) and at least a fifth in 17. `And` appears in 84, median 1.2%, at most
  30% (`monomatch` 2021). `Or` typically costs 0.14–0.32 µs a call (the survey's
  10th to 75th percentiles), and `And` 0.3–0.4.
- **For CPU**: `grid-colouring` 2011 (`10_10`) to its fifth solution, 0.54 s;
  `solbat` 2010 (`sb_12_12_5_0`), all 51 solutions, 4.6 s; `network_50_cstr`
  (`MODEL1507180015`) for the long clause, which finds nothing in 30 s. Times
  at `c9ceea25`, with malloc's thresholds pinned ([CPU
  performance](#cpu-performance)).
- **For proofs**: `solbat` 2010, all 51 solutions: 9.9 million lines, 7 minutes
  of checking.

### CPU performance

**Re-measured at `c9ceea25`**, 2026-09-26 and 2026-09-27: Release, GCC 15.2.0, fataepyc-09
(EPYC 7643, boost off). Pinned with `numactl --cpunodebind=0 --membind=0
taskset -c 8 setarch -R`, and with glibc's malloc thresholds pinned too
(`GLIBC_TUNABLES=glibc.malloc.mmap_threshold=33554432:glibc.malloc.trim_threshold=4294967295`),
which the first pass did not do. Three runs each, except `network_50_cstr`,
run once. The share column is from `GCS_PROPAGATOR_STATS=time` runs on
2026-09-26, pinned the same way; `network_50_cstr`'s is the 20 s run below.

**Against Gecode 6.3.0**, each flattened with its own library and run by its own
FlatZinc binary (`fzn-gecode` from the MiniZinc 2.9.7 bundle). Both solvers
were run in the same sitting, 2026-09-27, with the same pinning, the malloc
thresholds included, alternating run by run. None of these is a pure test of
this family, since the models mix constraints; the share column says how much
of our propagation it is.

| instance | to | GCS nodes | GCS s | Gecode nodes | Gecode s | ratio | `Or` / `And` share |
|---|---|---|---|---|---|---|---|
| `grid-colouring` 2011 | 5th solution | 74,217 | 0.537 / 0.538 / 0.542 | 74,207 | 1.600 / 1.639 / 1.654 | **0.33×** | 22% / — |
| `solbat` 2010 | all 51 | 27,077 | 4.667 / 4.655 / 4.651 | 26,597 | 1.914 / 1.910 / 1.917 | 2.4× | 27% / 8% |
| `network_50_cstr` 2024 | 30 s, no solution | 451,410 in 30 s | | 1,195,618 in 30 s | | 2.6× fewer nodes | 0.03% / — |

The ratio is of medians. On `grid-colouring` both find the same five
solutions in the same order, and we are three times as fast. On `solbat` both
enumerate the same 51 solutions in the same order, at node counts 2% apart;
why they differ was not looked into. "The same" compares the printed solution
arrays, with Gecode's `array1d(…)` wrapper stripped. Each solver's printed
solutions are also identical to its own saved output from the first pass. On
`network_50_cstr` neither finds a solution, and the node rates are not a
like-for-like comparison of anything but throughput. The day before, on
2026-09-26, three GCS runs of each took 0.535–0.539 s and 4.641–4.642 s, and
452,395 nodes in 30 s, with the same pinning.

**The first pass's figures**, at `f28fdef8` on 2026-09-23, without the malloc
thresholds pinned: `grid-colouring` 0.759 / 0.760 / 0.760 s (0.47×), `solbat`
7.189 / 7.151 / 7.151 s (3.7×), `network_50_cstr` 145,102 nodes in 30 s (8×
fewer), each ratio against Gecode run in that same sitting. Their shares, 54% / — and 30% / 10%, were the survey's at `00797a97`,
10 s per model rather than these runs' own lengths, and 76% / — was the 20 s
run below. They are not comparable with the table above, because the
thresholds move `solbat` a long way. At `c9ceea25` without them, it takes
8.80–8.82 s, against 4.64 s with them. Split with `time`, the unpinned run has
3.5 s of system time and the pinned one 0.04 s. That is malloc mapping and
unmapping per-node state copies, as `refined-triggers.md` describes. A same-sitting
A/B against `a94ca5ac`, main just before #1105 merged, shows the direction
depends on the pinning. Each arm is `fzn-glasgow` built at its commit with the
node-limit patch below applied, which does nothing unless its variable is set:

| build | thresholds | wall s | `instructions:u` | `cycles:u` |
|---|---|---|---|---|
| `a94ca5ac` | not pinned | 7.152 / 7.139 | 22.67 G | 12.33 / 12.31 G |
| `a94ca5ac` | pinned | 5.136 / 5.130 | 22.67 G | 11.86 / 11.85 G |
| `c9ceea25` | not pinned | 8.802 / 8.800 | 20.88 G | 11.70 / 11.70 G |
| `c9ceea25` | pinned | 4.651 / 4.642 | 20.88 G | 10.77 / 10.75 G |

`c9ceea25` executes 8% fewer user instructions and 5–9% fewer user cycles
either way. Its unpinned wall clock is nonetheless 23% worse, which is heap
history rather than this family.

**The long clause, before.** At `f28fdef8`, `network_50_cstr` for 20 s with
`GCS_PROPAGATOR_STATS=time`: propagation was 7.1 s of the 20.0 s solve, and `Or`
75.7% of that, over 167,571 calls at 32.0 µs each, in 87,830 nodes. There is
one `bool_clause` in the model, over all 2,774 of the Booleans `Zs` that the
search annotation branches on.

**The long clause, after** (#1105), the same run at `c9ceea25` with the
thresholds pinned: 291,655 nodes in 19.9 s, propagation 4.5 s, and `Or` 0.03%
of it, over 2,363 calls at 0.57 µs each. Without the thresholds: 279,986 nodes,
the same 2,363 calls, 0.52 µs each. Only one of those calls infers anything.

**At fixed work**, with a local patch to `fzn-glasgow` that stops the search
after a given number of trace callbacks (`GCS_BENCH_NODE_LIMIT=11000`; the patch is not in
the tree). That limit gives the 20,443 nodes at which `refined-triggers.md`
quotes its `Or` call counts, and it reproduces them. Every arm searched 20,443 nodes
with 20,442 failures and no solution. The builds are as in the A/B above, with
the thresholds pinned:

| build | `Or` calls | `instructions:u` | `cycles:u`, median of 3 |
|---|---|---|---|
| `a94ca5ac`, before #1105 | 38,555 | 20.09 G | 7.52 G |
| `c9ceea25`, threshold ∞: the scan, with its early stop | 2,543 | 11.31 G | 3.80 G |
| `c9ceea25`, default: the watched clause | 2,360 | 11.03 G | 3.78 G |

So `a94ca5ac` → `c9ceea25` is 1.82× fewer instructions. Nearly all of that is
the scan's early stop: the watches save a further 2.5% of the instructions the
scan leaves, and their cycles differ by less than the run-to-run noise. The ratio also contains the other PRs
merged in between: #1107, #1108, #1109, #1110 and #1112.

**Measured elsewhere**, and not to be mixed with the tables above: #1105's
description gives 1.690× fewer instructions for its early stop alone and 1.731×
with the watches, against its own parent at these nodes. Those are the figures
for #1105 by itself.

**What these benchmarks exercise**: all five rules, by the shape of the models
(clauses reach rules 4 and 5, reified conjunctions all five). Not counted per
rule on the corpus.

### Proof performance

**`solbat` 2010, all 51 solutions** (27,077 nodes), at `c9ceea25`, with the
malloc thresholds pinned and the two proof runs side by side on separate
cores; VeriPB 3.0.2 with `--force-checked-deletion`:

| | solve | proof | VeriPB |
|---|---|---|---|
| proofs off | 4.6 s | — | — |
| `AssertionLevel::Off` | 20.6 s | 9,864,447 lines, 2.05 GB | 427.2 s, `VERIFIED` |
| `AssertionLevel::Inferences` | 19.9 s | 7,646,467 lines, 1.83 GB | 34.3 s, `UNDER ASSERTIONS` |

The line counts are the first pass's exactly. The first pass, at `f28fdef8`
and without the thresholds, measured solves of 22.4 s and 21.8 s and checks of
429.0 s and 37.7 s. The content is not quite the same. Against `a94ca5ac`'s
proof at `Inferences`, compared line by line (line *i* against line *i*, which
the equal line counts allow), 133,260 lines differ, every one an `and`-hinted
assertion. That is rule 2 naming the first false literal where it used to name
the last. The OPB is byte-identical.

**Assertions at `Inferences`**, 7,565,126, unchanged by kind: `equals`
4,572,375, `or` 1,540,555, `linear_equality` 716,999, `and` 708,069, and the
solver's own `backtrack` 27,077 and `solx_block` 51. This family is 30% of
them, and each is one RUP when justified. Across all families, the justified
proof is 2.2 million lines longer than the asserted one, for 7.6 million
assertions.

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
nothing is asserted at `AssertionLevel::Off`, and each propagator infers the same
with proofs on and off. Only whether it builds reasons differs.

### Known limitations

- **A satisfied clause can still be rescanned.** Below the watch threshold,
  the scan stops at the second undecided literal before it can reach a
  satisfying one. So a satisfied clause whose true literals all come after two
  undecided ones returns `Enable`, and is walked again at every wake. #1105
  removed the case where a satisfying literal comes first, which is the one
  `network_50_cstr` hit, but not this one.
- **Not generalised arc consistent over two literals on one variable**, which
  is the shape MiniZinc's `set_in` glue posts.
- **A range literal throws with proofs on** (#310).
- **`AndIf` and `OrIf` do not chain through `cake_pb_cp`**, which has no rule
  for either keyword (#1100; #953, which asked for them, is closed, and #958
  added them). No front end but CPMpy posts them.

### Next steps

Ranked by what they buy for what they cost.

1. **Done: #1060 → #1105.** Both parts of this item landed: the stop at a
   satisfying literal (when the scan meets one before a second undecided
   literal; see [Known limitations](#known-limitations)), and two watched literals for the clause case through the
   engine's refined watches. They were measured on the corpus's clause models
   as a regression set, as asked (#1105's description; [CPU
   performance](#cpu-performance)).
2. **The `set_in` glue.** `Or{x < l, x ≥ u}` never removes the gap `[l, u − 1]`;
   an unreified `set_in` could remove it at the root instead, as a domain
   restriction. Small, in the front end; 76 posts in 4 corpus models. The
   reified form has the same shape with a third literal. Unfiled.
3. **Drop rule 3's lemmas.** One RUP per literal that the reason already states.
   A few lines; they were 100 of `logical_test`'s 75,220 proof lines at seed 1 at
   `f28fdef8`, before the clause sets,
   so it is tidying, not a saving. Unfiled.
4. **Tests.** The literal-form rows under views, and a width row over an order
   literal in the audit lane. Unfiled. The long-clause part of this item is
   done: #1105's clause sets are long enough for watches to move. A clause at
   the default threshold is still in no lane (see [Tests](#tests)).

## Prior art

Clauses are the SAT solver's constraint, and two watched literals (Moskewicz et
al., *Chaff*, DAC 2001) the standard propagation. Gecode's propagators for a
clause with a fixed true reification, `ClauseTrue` and `NaryOrTrue`, keep two
watched views and move them (`int/bool/clause.hpp`); the reified one counts
instead. Since #1105 ours does the same for a clause at or above the watch
threshold. Its search for a new watch never wraps round, because every literal
before the later watch is entailed. Nothing is novel on the proof side: each inference is one RUP against a
linear row of the constraint's own encoding, which is the case VeriPB's unit
propagation handles natively. McIlree's thesis treats disjunctions of
conjunctions of *constraints* (§4.2, for smart tables), which is a different
problem.

## Further reading

- [`reification.md`](../reification.md): the reification conventions the rest of
  the solver uses, of which this family is the Boolean case.
- [`refined-triggers.md`](../refined-triggers.md): the per-literal watches the
  watched clause is built on. Its "`And` / `Or` clause client" section has the
  threshold measurements, and its pitfalls list the `AutoTable` hazard (#1106).
- [`parity.md`](parity.md): the XOR constraint, which shares this family's
  literal helpers.
