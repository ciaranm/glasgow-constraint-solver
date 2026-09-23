# Parity: `ParityOdd`, and the GF(2) system over many of them

> **Maturity** production (`ParityOdd`); experimental and frontend-unreachable
> (`ParitySystem` and the propagator the `parity_system_gathering` presolver
> installs) ·
> **Audited** 2026-09-23 at `f28fdef8` ·
> **Open issues** filed by this audit: none; its measurement of the gathered
> system on `parity-learning` is posted on #983. Already open and touching
> this family: #983 (the system and its presolver are reachable from no
> front end), #649 (implied equivalences have nowhere to live), #868
> (cross-solver). Tracked under #871.

`ParityOdd(lits)` says that an odd number of the literals hold: an XOR. It is
one class with one propagator, and it is generalised arc consistent on one XOR
whose literals are over different variables, because a single parity
constraint has nothing to infer until one literal is left. All the inference a
model's XORs offer lives in their conjunction, and over GF(2) that conjunction
is tractable. `ParitySystem`, and the
`parity_system_gathering` presolver that builds one from a model's posted
`ParityOdd`s, run Gauss-Jordan elimination over the whole system with every
inference certified. The design, the proofs and their derivation are in
[`parity-system.md`](../parity-system.md), which this document summarises rather
than repeats.

Three things to know before touching it.

- **The system is certified, and no front end can reach it** (#983). MiniZinc,
  XCSP3 and CPMpy all post `ParityOdd`; nothing turns the presolver on. This
  audit wired a local switch into `fzn-glasgow` to try it.
- **On the one corpus model where parity dominates, the system prunes nothing
  and costs four times as much.** `parity-learning` 2012 proves its optimum in
  1,523,353 nodes with `ParityOdd` alone, with the gathered system, and in
  Gecode: the same count all three ways. At every node that survives
  propagation, each sample's row either still has its own output undecided, so
  it constrains nothing, or has at most one undecided input, which unit
  propagation has already settled. So elimination has nothing to add. The system
  took 227.9 s against 57.2 s, both on the audit's instrumented build.
- **`ParityOdd` is 7.4 times slower than Gecode** on that model, at the same
  node count. Its proofs are cheap: each inference is one RUP through
  `cake_pb_cp`'s accumulator chain.

## What it is

### Semantics

- **`ParityOdd(lits)`**: an odd number of `lits` are true. The constructor from
  `vector<IntegerVariableID>` reads each variable as `≠ 0`. An even parity is
  written with one literal negated.
- **`ParitySystem(rows, propagation)`**: every row odd, as for `ParityOdd`. Two
  propagation settings, below.

Degenerate shapes:

- **No literals**: odd parity over nothing is false. `ParityOdd({})` fails at
  the root through its own pins, and a `ParitySystem` with an empty row installs
  an initial contradiction.
- **A repeated literal**: `ParityOdd({x, x, y})` means `ParityOdd({y})`. The
  propagator treats the two copies as independent literals, so it forces nothing
  until `x` is decided: sound, and **not** generalised arc consistent. The system
  cancels repeats when it builds its rows (`x ⊕ x = 0`), so it does not have
  that weakness. Tested for `{x, x}`, `{x, x, y}`, `{x, y, x}` and `{x, x, x, y}`,
  under plain enumeration.
- **Constants**: a constant literal folds into the parity. Tested, through
  `random_bounds_or_constant`.
- **Two atoms over one variable in a system** (`x = 3` and `x ≠ 0` over
  `{0, 3}`): treated as independent, which loses strength and never soundness.
  `parity-system.md` calls the result "GAC on the PB relaxation of the system".

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `ParityOdd` | ✓ `array_bool_xor`[^mznxor] | ✓ `xor`, top level and inside an expression[^xxor] | ✓ `xor`, through `gcspy`'s `post_xor` | ✓ `parity` | |
| `ParitySystem` | `frontend gap (#983)` | `frontend gap (#983)` | `frontend gap (#983)` | ✓ `parity_system`, ours alone; cake has no such rule | also built by the presolver from posted `ParityOdd`s |

[^mznxor]: `bool_xor` is **not** this class. The two-argument form posts
    `NotEquals` and the reified three-argument form `EqualsIff`. The presolver
    gathers the first as a two-literal row, and skips the second as reified.

[^xxor]: At the top level, `ParityOdd` over the arguments. Inside an expression,
    a result `r` and its complement `not_r` by a linear equality, and
    `ParityOdd` over the arguments and `not_r`.

CPMpy's upstream GCS interface, checked 2026-09-23, posts `xor` as `post_xor`.

### Options

`ParityOdd`: `None.`

**`ParitySystem`'s `ParitySystemPropagation`**, a constructor argument, not a
`consistency::` tag:

- `GaussJordan` (the default): the system propagator below.
- `CheckOnly`: refute a row once every literal is assigned, and nothing else.
  Weaker than posting each row as its own `ParityOdd`, and slower. Its comment,
  and `parity-system.md`, keep it as the encoding's standing regression test, as
  `MinDistance` keeps a check-only mode. **Nothing in the tree selects it**:
  unlike `MinDistance`'s, no test runs it, so it tests nothing today.

Neither changes the OPB.

The presolver has `keeping_donor_propagators()`, which leaves the gathered
donors' own propagators running, the Boolean `Equals` / `NotEquals` as well as
the `ParityOdd`s. It exists so that its tests can check the
system subsumes them, by comparing trees node for node.

### Variable kinds and views

Any literal over any `IntegerVariableID`. The proof names each literal's atom,
and a view's literals are its own. `parity_constraint_view_mixed` and
`parity_system_constraint_view_mixed` wrap positions in views. The system's
columns are canonicalised syntactically, by `canonical_atom` (`≠` to `=`, `<` to
`≥` and so on, the negation moving to the row's parity), so two spellings of
one literal get two columns. The literal axioms in its proofs go through the
names-and-IDs tracker (`simplify_literal`), so that a view or a lazily named
atom resolves to the literal its OPB row carries and the `pol` cancels.
`parity-system.md`'s "canonicalisation must go through the tracker" is about
those axioms; its columns do not. The presolver takes a Boolean `Equals` or
`NotEquals` as a row only when it is unconditional (the rest count as
`skipped_reified`, checked first) and both operands are within `{0, 1}` at the
root (the rest count as `skipped_wide_operands`); over wider operands an
equality is not a parity.

### Reification

`None.` for the class. XCSP3's `xor` inside an expression reifies it with an
auxiliary, as above; MiniZinc's reified `bool_xor` goes to `EqualsIff`.

### Relation to other families

**Into this family.** MiniZinc's `array_bool_xor`; XCSP3's `xor`; CPMpy's
`xor`; the `.scp` reader.

**Posts as children.** Nothing. `ParitySystem` calls `define_parity_chain` once
per row rather than posting child `ParityOdd`s, because children would share
the parent's id and collide on every row label.

**Shares code.**

- `define_parity_chain` and `find_parity_chain` (`parity_chain.{hh,cc}`), between
  `ParityOdd`, `ParitySystem` and the presolver: one emitter and one lookup for
  every chain.
- `install_parity_system_propagator` (`gf2_system.{hh,cc}`), between
  `ParitySystem` and the presolver.
- `ReifiedEquals` gained accessors so that the presolver can read Boolean
  `Equals` / `NotEquals` as two-literal rows.
- `cake_truthiness.hh` and `add_trigger_for`, with `logical`.

**Presolvers.** `parity_system_gathering` reads every `ParityOdd` and Boolean
`Equals` / `NotEquals`, groups the rows into connected components by shared
atoms, installs the system propagator over each component of two or more rows,
and retires the donors' own propagators. Its detection and its stats belong to
its own presolver document, when written; the machinery it installs is
documented here, as `TEMPLATE.md`'s presolver table says.

**Reached only through a decomposition?** No. The system is reached only
through the API and the `.scp`, or the presolver, which nothing enables.

## The proof model

### OPB encoding

Definitional, and `cake_pb_cp`'s `parity` exactly: an accumulator chain over
flags `a_0 … a_n`, cake's `x[id][k]`, one per prefix of the literals.

```
a_0 = 1                                   0ge / 0le
per literal l_k:  a_k = a_{k−1} ⊕ l_k     four clauses, labelled k_0_0, k_1_1, k_1_0, k_0_1
a_n = 0                                   acc
```

Four clauses per literal and three pins: `4n + 3` rows and `n + 1` proof flags,
linear in the row length and independent of every domain. The flags are in the
OPB, as cake's are. `ParitySystem` writes one such chain per row, with the row
index threaded through the flag values and labels (`r<i>_…`) so that the
chains stay apart.

### Labels

`0ge`, `0le`, `acc` and `k_{0,1}_{0,1}` per step, published through
`ConstraintProofModelData<ParityOdd>::chain_naming()` as a `ParityChainNaming`
object. `find_parity_chain` uses them to find a donor's chain by name, all or
nothing, which is how the presolver cites rows it did not write. So here,
unlike most families, the labels are load-bearing: they are cake's names and an
API at the same time.

### Cake conformity

| Case | Chain | `opbdiff` |
|---|---|---|
| `scp_chain_parity_sat` (`A ⊕ B ⊕ C`, enumerate) | full workflow 2 | `none` |
| `scp_chain_parity_unsat` (`A ⊕ B` and `A = B`) | full workflow 2 | `none` |

Both chain-verify at `f28fdef8`. `none` only because the inputs are `{0, 1}`:
cake writes two bound lines per such variable, the binary case of #358. The
propagator's RUP inferences verify against cake's chain directly. `ParitySystem`
has no case, because cake has no rule for it; `scp_reader_test` checks that its
`.scp` form round-trips, by counting solutions.

### Proof-time state

- **`ParityOdd`**: nothing beyond the OPB. Every inference is one RUP.
- **The system**, at the root, from an initialiser at
  `InitialiserPriority::SimpleDefinition`: per row, the two **slack rows** of
  Gocht and Nordström's (4.4), `Σ l = 1 + 2B`, derived from the row's chain at
  `ProofLevel::Top`. For a chain row that is two redundance steps per literal,
  introducing a fresh flag `y_k`: the first goal-free, the second with a
  five-`pol` subproof. Then two telescoping `pol`s. About ten lines of proof
  file per literal. For a Boolean `Equals` / `NotEquals` donor it is two RUPs.
  The line numbers are held in a shared vector the propagator reads. **Nothing
  is deleted**: the `red` steps are scaffolding that `parity-system.md` shows
  could be deleted soundly, but the deletion is not implemented, so `2n + 2`
  lines per chain row stay at `Top`. The subproof lines end with their blocks.
- **The fresh flags** are proof-only, named `psys<id>r<i>_y<k>` for a posted
  system and by the presolver's own stem for a gathered one. Each is determined
  on a solution by `y_k = (a_{k−1} + l_k + a_k) / 2`, which the chain makes
  integral.
- **Per inference**: one `pol` at `Temporary` over the slack rows of the donors
  the derived row is a sum of, and a RUP.

## The implementation

### Initialisation and global data

- **`ParityOdd`**: nothing beyond copying the literals.
- **The system**: `build_gf2_system` canonicalises each literal to an atom and a
  flip, gives each atom a column, and builds one bitset row per posted row, with
  an origin bitset recording which posted rows it is a sum of. The slack-row
  initialiser runs at the root, with proofs only.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| `ParityOdd` | per literal, via `add_trigger_for` | derived, truthfully | 1–3 | always | nothing to claim | **yes**, after every inference |
| slack-row initialiser | initialiser | — | scaffolding for 5, 6 | a system with proofs on; `InitialiserPriority::SimpleDefinition` | n/a | one shot |
| system, `GaussJordan` | per literal of every row | derived, truthfully | 5, 6 | `ParitySystem` by default, or the presolver per component | **is, when every atom is over a different underlying variable; not claimed** | once every atom is decided |
| system, `CheckOnly` | per literal of every row | derived | 7 | `ParitySystemPropagation::CheckOnly` | not claimed | once every row is decided |
| empty-row refutation | initial contradiction | — | 4 | a `GaussJordan` system with an empty row (under `CheckOnly`, rule 7 refutes it on the first call) | n/a | — |

**`ParityOdd`** infers only with at most one literal undecided, and then returns
`DisableUntilBacktrack`; with two or more undecided it returns `Enable` having
inferred nothing. So a claim would buy nothing.

**The system propagator** reaches its own fixpoint in one call when its atoms
are over different underlying variables. After elimination, a unit row's atom is its
pivot, and a pivot column appears in no other row, so inferring every unit row's
atom leaves the other rows unchanged. With two atoms over one variable, fixing
one can decide the other, and then it does not. It returns `Enable` whenever an
atom is undecided. Claiming idempotence would not take effect anyway: the engine
ignores a claim when a variable appears twice among the triggers
(`positions_alias`), and the propagator registers one trigger per literal per
row, so any variable shared by two rows, which is every real system, counts as
aliasing.

**Holes affect**: per literal, `on_change` for `=`, `≠` and range literals,
`on_bounds` for `<` and `≥`. Truthful.

### Mutable state and incrementality

**`ParityOdd`**: nothing persists. Each call walks the literals until it has seen
two undecided ones.

**The system**: nothing persists either. Each call reads every atom's state,
**copies every row**, substitutes, and runs Gauss-Jordan from scratch:
`O(rows² · (atoms + rows) / 64)` word operations, the `rows` term being each
row's origin bitset, which is XORed alongside its atoms. `parity-system.md` records why it
started from scratch (elimination creates non-zero cells, so a reduced form does
not trail cleanly) and names incremental maintenance as the residue.

**What maintaining it would buy.** On `parity-learning` 2012, with 111 rows over
134 atoms, the system made each node about four times as expensive as the
`ParityOdd`s it replaced, for no pruning. Incremental elimination would cut
that. A cheaper first step would be to skip elimination when no row can have
become unit, and it was not measured.

### Interior values and optional pruning

**What this family offers:** `None.`

**What this family observes:** holes at the values its `=`, `≠` and range
literals name. For the frontend shape, `v ≠ 0` over `{0, 1}`, there are no
interiors.

### Robustness and limits

- **Unbounded domains.** Nothing walks a domain; see
  [Interval efficiency](#interval-efficiency).
- **Negative values and zero.** `≠ 0` reads a negative value as true. Tested
  over `[−2, 2]`.
- **Degenerate shapes**: see [Semantics](#semantics).
- **Overflow.** None: the only arithmetic is parity and bitsets. The `pol`
  coefficients are small integers.
- **Large systems.** The system's per-call cost grows with rows squared, and
  its root scaffolding with the total row length: `2n + 2` lines per chain row
  left at `Top`, where every later unhinted RUP pays for it (#666).

### Interval efficiency

`Fine at any width`. The family's costs are in literals and rows.

1. **Propagation.** No value walks: `test_literal` per literal. `ParityOdd`'s scan
   is bounded by its row; the system's by rows times atoms.
2. **Reasons.** One literal per decided literal of the row, or of the derived
   row's support. In literals.
3. **Proofs.** `ParityOdd`: one RUP per inference, whose unit propagation walks
   the chain, so checking it is linear in the row length. The system: one `pol`
   per inference over the donors' slack rows, plus the root scaffolding, which is
   linear in each row's length.
4. **The audit lane**: one row, `ParityOdd`, `NoWidePosition`, over three
   `{0, 1}` variables. Nothing for the system.

## Inference catalogue

Seven rules: three for `ParityOdd`, three for the system, and the check-only
setting's one. The system's slack-row derivation is scaffolding, not an
inference, and is described under [Proof-time state](#proof-time-state).

**The wire inventory.**

| Wire form | Hint type | Rules |
|---|---|---|
| `parity:((constraint_id N))` | `hints::Parity` | all |

`originator` (`ConstraintID`) only. A reconstructor tells `ParityOdd` from a
posted system by the `.scp` term. A presolver-installed system's propagator is
installed under `CurrentlyUnnamedConstraint`, so a `parity` assertion naming no
constraint can only come from one; what it cannot tell is which rows were
gathered (see rule 5).

**What licenses them.** `ParityOdd`'s rules are RUP through its own chain: with
all but one literal decided, unit propagation walks the accumulators from both
pins and meets at the last literal. The system's rules are Gocht and
Nordström's §4.3 (*Certifying Parity Reasoning Efficiently Using Pseudo-Boolean
Proofs*, AAAI 2022): a sum of slack rows, literal axioms for the support, a
division and a multiplication by two, which is one `pol`, then RUP. The
derivation of the slack rows from the chain is **ours**; their §4.4 recovers the
same rows from a CNF by brute force. `parity-system.md` has every step.

**Tightness.** No lane for `ParityOdd`. For the system, `parity-system.md`
records seven mutations: five caught (four rejected by VeriPB, one by the
solution check), and two accepted because they only weaken the derived row by a
term the OPB pins anyway.

### Rule: last-literal-forced-false

(Rule 1; `ParityOdd`.)

- **Infers** — the one undecided literal false.
- **Fires when** — every other literal is decided and an odd number of them are
  true.
- **Strength** — `partial`; with rules 2 and 3, `GAC` on one XOR whose
  literals are over different variables. Not otherwise: `ParityOdd({x = 1,
  x = 2})` over `{0, 1, 2}` sees two undecided literals, and leaves 0, which
  has no support.
- **Algorithm** — the scan, which stops at a second undecided literal. `O(n)`.
- **Why it is true** — the parity is already odd, so the last literal must add
  nothing.
- **Proof technique** — `RUP`: with the other literals fixed, unit propagation
  runs the accumulator chain from `a_0 = 1` and from `a_n = 0` and meets at the
  step for the last literal.
- **Reason** — every decided literal, as it is. Minimal.
- **Assertion** — `¬u ∨ ¬reason`.
- **Hint** — `hints::Parity`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line, as for rule 2.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: last-literal-forced-true

(Rule 2; `ParityOdd`.)

- **Infers** — the one undecided literal true.
- **Fires when** — every other literal is decided and an even number are true.
- **Strength** — as rule 1.
- **Algorithm** — as rule 1.
- **Why it is true** — the parity is even so far, and must end odd.
- **Proof technique** — `RUP`, as rule 1.
- **Reason** — as rule 1.
- **Assertion** — `u ∨ ¬reason`.
- **Hint** — `hints::Parity`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line. A probe over `n` Booleans, guessing the first
  `n − 1` false so that this rule forces the last, wrote a 7-line proof at `n` =
  10, 100 and 1,000.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: even-parity-conflict

(Rule 3; `ParityOdd`.)

- **Infers** — a contradiction.
- **Fires when** — every literal is decided and an even number are true.
- **Strength** — as rule 1.
- **Algorithm** — the scan.
- **Why it is true** — the parity is even.
- **Proof technique** — `RUP`, as rule 1.
- **Reason** — every literal, as it is.
- **Assertion** — `¬reason`.
- **Hint** — `hints::Parity`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: empty-row

(Rule 4; system.)

- **Infers** — a contradiction, before search.
- **Fires when** — a posted system has a row with no literals.
- **Strength** — `partial`.
- **Algorithm** — `O(rows)` at install.
- **Why it is true** — zero literals cannot have odd parity.
- **Proof technique** — `RUP`: the row's own `0ge`, `0le` and `acc` pin its
  single accumulator to both one and zero.
- **Reason** — none.
- **Assertion** — `0 ≥ 1`.
- **Hint** — `hints::Parity`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: system-unit

(Rule 5; system, `GaussJordan`.)

- **Infers** — an atom true or false.
- **Fires when** — after substituting the current assignment and eliminating, a
  row has exactly one atom left.
- **Strength** — `GAC` on the PB relaxation of the system, with rule 6; which is
  `GAC` on the conjunction when each variable contributes one atom.
- **Algorithm** — Gauss-Jordan over bitset rows, from scratch every call:
  `O(rows² · (atoms + rows) / 64)`.
- **Why it is true** — the unit row is a sum over GF(2) of posted rows, so it
  holds, and with the other atoms of its support fixed it fixes this one.
- **Proof technique** — `pol` then `RUP`, by Gocht and Nordström's §4.3: the
  first slack row of every donor in the row's origin, a literal axiom for each
  atom of its support (the one being inferred given its wrong value), divide by
  two, multiply by two, then the second slack rows. What is left is a clause
  with the inferred literal as its only non-falsified term, and the RUP closes
  on it. One `pol` whatever the size of the combination.
- **Reason** — the assigned atoms of the row's support before substitution:
  Gocht and Nordström's `ρ`. Per atom.
- **Assertion** — the literal `∨ ¬reason`.
- **Hint** — `hints::Parity`, with the system's id. For a presolver-installed
  system, that id is `CurrentlyUnnamedConstraint`, so the assertion names no
  posted constraint.
- **Offline reconstructibility** — `hinted` for a posted `ParitySystem`: the
  hint names the system, and a GF(2) solve over its rows, restricted to the
  assertion's atoms, recovers a combination that works, which need not be the
  solver's. `solver-side` for a presolver-installed system: the hint names no
  constraint, and which donors were gathered into it is not recoverable.
- **Proof size** — one `pol` over (donors in the origin) × 2 slack rows plus one
  axiom per support atom, and one RUP; plus the root scaffolding it cites.
- **Gaps** — `None.`
- **Tightness** — see the catalogue preamble.

### Rule: system-conflict

(Rule 6; system, `GaussJordan`.)

- **Infers** — a contradiction.
- **Fires when** — after elimination, a row has no atoms and a right-hand side
  of one: `0 = 1`.
- **Strength** — as rule 5.
- **Algorithm** — as rule 5.
- **Why it is true** — a sum of the posted rows is violated.
- **Proof technique** — as rule 5, with no pretended atom: the clause that comes
  out is falsified by `ρ` outright.
- **Reason** — as rule 5.
- **Assertion** — `¬reason`.
- **Hint** — `hints::Parity`, as rule 5.
- **Offline reconstructibility** — as rule 5.
- **Proof size** — as rule 5.
- **Gaps** — `None.`
- **Tightness** — see the catalogue preamble.

### Rule: check-only-conflict

(Rule 7; system, `CheckOnly`.)

- **Infers** — a contradiction.
- **Fires when** — a row is fully assigned with even parity.
- **Strength** — `checker` per row.
- **Algorithm** — a scan of every row every call.
- **Why it is true** — as rule 3.
- **Proof technique** — `RUP` through the row's chain, as rule 3.
- **Reason** — the row's literals.
- **Assertion** — `¬reason`.
- **Hint** — `hints::Parity`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` Not reached by any test either.

## Evidence

### Tests

| Lane | What it checks |
|---|---|
| `parity_constraint` | `parity_test`: fixed and random rows (some with constants) under `solve_for_tests_checking_gac`; five repeated-literal rows under plain enumeration; with and without proofs |
| `parity_constraint_view_mixed` | the same, positions wrapped in views, minus the repeated-literal rows |
| `parity_system_constraint`, `…_view_mixed` | `parity_system_test`: 15 fixed systems (no rows, one row, disjoint rows, a cycle that is unsatisfiable with no two rows in conflict, a repeated row, wider domains, constants, an empty row, a duplicate within a row) and 10 random ones, all under `solve_for_tests_checking_gac` at the default `GaussJordan` |
| `parity_system_gathering_presolver` | the presolver: exact stats counts, node-for-node equality with and without donor retirement, and the strength differentials `parity-system.md` tabulates; its equivalence runs use plain enumeration, so the gathered system's per-node strength is not checked |
| `scp_chain_parity_sat`, `scp_chain_parity_unsat` | see [Cake conformity](#cake-conformity) |
| `scp_reader_test`, `constraint_enumeration_test` | the `parity_system` `.scp` form: solutions counted, and a separate write → read → write round trip; the presolver's class enumeration finds `ParityOdd` and `ReifiedEquals` |
| `xcsp_intension_boolean` | `xor(a, c, d)` at the top level |
| `minizinc-arrayboolxor` | `array_bool_xor` against MiniZinc's default solver |

All pass at `f28fdef8`, caps off, with MiniZinc 2.9.7, `cake_pb_cp` and
`opbdiff` on the path. At `--seed=1`, `parity_test` verifies 32 proofs,
`parity_system_test` 25 and the presolver test 36.

**Runtime caps.** No lane sets or clears one, and the defaults **never fire**:
three unseeded runs of each of the three binaries, and one of each of the two
view lanes, with the 300-solution and 1,500-node caps passed in the
environment, printed no truncation. So the capped run checks completeness here.

**Rules the tests reach**, from local counters at `--seed=1`: all three of
`ParityOdd`'s (rule 1 56 times, rule 2 80, rule 3 16 in `parity_test`); rule 4
10 times and rules 5 and 6 114 and 6 times in `parity_system_test`, which also
derives 38 slack rows; and in the presolver test, 50 slack rows, 121 units and
12 conflicts from gathered systems.

**What the tests do not cover:**

- **`CheckOnly`**, anywhere. Rule 7 is reached by nothing, so the setting kept
  as a regression test of the encoding checks nothing.
- **A system of realistic size.** Every fixture has at most six variables,
  which is `parity-system.md`'s own caveat. This audit's `parity-learning` run
  is the first measurement at scale, and it is not in the tree.
- **The system through any front end**, because none reaches it (#983).
- **Consistency on the repeated-literal rows**, which use plain enumeration.
- **XCSP3's `xor` inside an expression**, and the `gcspy` path (`test_xor` in
  `python_test.py` is commented out of `python/CMakeLists.txt`).
- **Two spellings of one literal in a system**, such as `x ≥ 1` and `x ≠ 0` over
  `{0, 1}`, or two views of one variable. The system gives them separate
  columns, since `canonical_atom` works on syntax, and nothing tests the
  strength that loses.

### Benchmarks and examples

- **In-repo**: no example posts either class.
- **The corpus** (297 MiniZinc Challenge models, one instance each, flattened
  2026-09-05): `array_bool_xor` appears 76 times, in 2 models, `parity-learning`
  2012 and `speck-optimisation` 2023. `bool_xor`, 1,610 posts in 9 models, is
  `NotEquals` or `EqualsIff`, not this class.
- **Where it is the cost** (share of propagation time, 10 s each, at `00797a97`,
  from `linear.md`'s survey; `parity/` is unchanged since): `parity-learning`
  83.5%, `speck-optimisation` 5.0%.
- **For CPU**: `parity-learning` 2012 (`44_22_5.2`) to its proved optimum, 57 s.
  Its 44 rows are over arrays of 23, of which 6 to 17 entries (12.5 on average)
  are variables and the rest the constant false. `speck-optimisation`'s first
  instance gathers 186 rows into 46 components and takes 11 nodes either way.
- **For proofs**: the same, capped at 5 s.

### CPU performance

All at `f28fdef8`, Release, GCC 15.2.0, fataepyc-09 (EPYC 7643, boost off),
pinned with `numactl --cpunodebind=0 --membind=0 taskset -c 8 setarch -R`,
2026-09-23, one run each. The two GCS rows in the table ran on this audit's
build, which counts rule firings in `ParityOdd`'s and the system's propagators
(a map increment per call) and carries the presolver switch; the long gathered
run used core 9. On the unmodified build the first row takes 56.3 s, with the
same nodes and propagations.

**`parity-learning` 2012 (`44_22_5.2`), to the proved optimum:**

| | nodes | propagations | time |
|---|---|---|---|
| `ParityOdd` per row | 1,523,353 | 75,347,953 | 57.2 s (56.3 s unmodified) |
| the rows gathered into one system (local switch: 111 rows, 44 of them `ParityOdd` and 67 Boolean donors, 134 atoms, one component) | 1,523,353 | 9,749,762 | 227.9 s |
| Gecode 6.3.0, its own flattening | 1,523,353 | 64,723,022 | 7.7 s |

The same node count three ways. **Gathering buys nothing here.** Each sample's
chain of rows ends in its own output `computed_parities[s]`, which the search
never branches on; the objective's linear bound decides outputs once the error
count reaches the incumbent. A simulation of the search in Python, with unit
propagation on each row and that bound, reproduces the 1,523,353 nodes exactly
and asks, at every node that survives propagation, what elimination could add.
The answer is nothing, at all 761,677 of them: every row whose output is
decided has at most one undecided input, which unit propagation has already
settled, and a row whose output is undecided constrains nothing. Propagator
calls of all kinds fall to an eighth, one system replacing 111 donors, but the
solve takes four times as long. Where the time goes was not profiled; the
from-scratch elimination and the row copies are the obvious candidates. `ParityOdd` itself is 7.4 times
slower than Gecode, at the same count (on the unmodified build).

**What this benchmark exercises**: rules 1–3 without the presolver, rules 5 and
6 with it. Rule 4 only in the tests, and rule 7 nowhere.

### Proof performance

**`parity-learning` 2012, capped at 5 s** (clean build, a different core):

| | nodes | proof | VeriPB |
|---|---|---|---|
| `AssertionLevel::Off` | 35,827 | 1,843,205 lines, 473 MB | 22.8 s, `VERIFIED NO CONCLUSION` |
| `AssertionLevel::Inferences` | 42,819 | 1,556,401 lines, 502 MB | 9.8 s, `UNDER ASSERTIONS NO CONCLUSION` |

The capped runs reach different node counts, so compare per node. **Assertions
at `Inferences`**: `equals` 877,209, `parity` 298,816, `linear_equality` 214,867
and the solver's `backtrack` 42,797. `ParityOdd` is 21% of them, each a single
RUP when justified.

**Own against shared**: the probe above. A `ParityOdd` over `n` Booleans costs
`4n + 3` chain rows and `n + 1` flags in the OPB, and one proof line per
inference whatever `n` is. The system's root scaffolding, about ten file lines
per literal of which `2n + 2` per chain row stay at `Top`, was not measured at
scale.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified, and nothing is asserted at
`AssertionLevel::Off`. For a presolver-installed system, the hints name
`CurrentlyUnnamedConstraint` and the reconstruction needs the elimination's
origin rows, which no hint carries (rules 5 and 6): a gap for the external
justifier, not for the proof.

### Known limitations

- **The system is reachable from no front end** (#983).
- **Gathering can cost more than it prunes**: four times slower, for nothing, on
  `parity-learning`.
- **`ParityOdd` is not GAC over a repeated literal**; the system is.
- **Slow against Gecode**: 7.4 times, at the same node count, on
  `parity-learning`.
- **Root scaffolding is never deleted**: `2n + 2` lines per chain row stay at
  `Top`.

### Next steps

Ranked by what they buy for what they cost.

1. **#983's decision, with this measurement.** Before exposing the presolver,
   note that on the one corpus model where parity dominates it prunes nothing
   and quadruples the time. A front-end flag should be opt-in, as
   `--difference-logic` is. Posted on #983.
2. **Make each call cheaper, or rarer.** Profile the system propagator on
   `parity-learning` first; incremental elimination is the design note's
   residue, and skipping elimination when no row can have become unit is a
   cheaper test. No structural check at gathering time would have predicted
   this model's result: the rows do interact once the objective's bound
   decides their outputs, and it is the search's depth, not the system's shape,
   that leaves nothing to find. Unfiled; the evidence is one model.
3. **Delete the root scaffolding**, which `parity-system.md` already argues is
   sound. Unfiled there too. That document is stale in places: it says `7n`
   lines per row stay at `Top`, where the subproofs are `Temporary` and `2n + 2`
   stay, and its canonicalisation reads as if the columns went through the
   tracker. Correct it with the deletion.
4. **Run `CheckOnly` somewhere, or delete it.** It cannot share the `GAC`-checking
   lane, since it is weaker by design; a plain-enumeration pass over the same
   fixtures would make it the regression test it is meant to be. Unfiled.
5. **Hints for the system's rules**: the origin rows, if a hints-only mode is
   ever wanted for a gathered system. Deliberately unfiled, as for other
   families: the justifier work will show whether it is needed.

## Prior art

Parity reasoning is well developed in SAT: CryptoMiniSat runs Gauss-Jordan during
search. In CP, Rouquette and Solnon's `abstractXOR` (CP 2020) is a Choco
prototype, and CP-SAT has a TODO for it (`parity-system.md` and #647 survey
this). The certification is Gocht and Nordström (AAAI 2022). What is ours is
the bridge: deriving the slack form from the accumulator chain `cake_pb_cp`
writes, in a linear number of steps, where their §4.4 recovers it from a CNF it
did not write by enumeration. `ParityOdd`'s own propagation and proof are the
textbook ones: unit propagation on one XOR, and RUP through its CNF-shaped
chain.

## Further reading

- [`parity-system.md`](../parity-system.md): the system in full. The slack form
  and why it cannot be in the OPB, its derivation from the chain with the
  subproof, elimination as one `pol`, the §4.3 fold, the propagator, the
  presolver and its three gates, the mutation results, and the residue.
- [`logical.md`](logical.md): the literal helpers this family shares.
