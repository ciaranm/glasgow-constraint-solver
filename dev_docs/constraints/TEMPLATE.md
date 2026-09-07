# Template: a constraint family document

Every constraint family in `gcs/constraints/` gets one document under
`dev_docs/constraints/`, written to the skeleton below. This file is the
skeleton, the conventions that govern filling it in, and the controlled
vocabularies the sections draw on.

These documents are meant to serve five purposes at once, and the shape is a
compromise between them:

1. **Structure.** Give the developer documentation we already have a fixed
   place to live, per family, instead of a pile of individually-shaped design
   notes.
2. **The paper.** Supply the raw material for a "VeriPB proof logging for all
   of constraint programming" writeup — which wants a row per *inference rule*,
   naming its proof technique, its proof size, and its provenance.
3. **The external justification tool.** Matthew's tool takes a proof in which
   the solver emitted only VeriPB `a` lines plus hints, trims it, and replaces
   the remaining `a` lines with real derivations. It needs to know, per rule,
   exactly what is asserted, exactly what the hint carries, and whether the
   derivation can be rebuilt from those two things alone. GCS also needs a mode
   that emits hints only; these documents are its specification.
4. **Triage.** Flag the implementations that want more work, with enough
   detail that the flag is actionable rather than a feeling.
5. **Audit.** Give a one-family-at-a-time code review something to be written
   down in, so the result is recorded rather than re-derived next time.

## Why this shape

The obvious organisation — one narrative per family — does not serve purposes
2, 3 and 4, because all three of them key off individual *inference rules*, not
families. The paper wants a table row per rule. Matthew's tool wants a record
per rule. Triage lands on rules ("edge-finding is certified, the energetic
variant is not"). So the repeated, uniform unit in these documents is the rule,
under [Inference catalogue](#inference-catalogue), and the sections before it
exist mostly to give the rules a shared context to refer back to.

That is also why the vocabularies in the appendices are *closed lists* used
verbatim. If every family names its proof techniques, consistency levels and
reconstructibility verdicts from the same short lists, then the paper's
headline tables and the external tool's coverage matrix are a pivot over these
documents rather than a re-reading of thirty of them.

## Where these live

```
dev_docs/constraints/README.md      index: the family list, one line each
dev_docs/constraints/<family>.md    one per family
dev_docs/presolvers/<name>.md       one per presolver (see the variant below)
```

The file name is the `gcs/constraints/` directory name, so the mapping is
mechanical — with the documented exceptions in [the family
list](#provisional-family-list), which is authoritative for what counts as a
family. Do not derive the family list from `ls`: arithmetic is one family
spread over several directories and loose headers, and some directories
(`innards/`, `extensional_utils`) are not families at all.

This directory sits alongside `dev_docs/constraints.md`, which stays the
generic "how to implement a constraint" guide. These documents are about
*particular* constraints and should not restate it — link instead.

## How to fill it in

**Mandatory sections must appear even when the answer is "none".** A section
that has been considered and found empty and a section nobody looked at are
different states, and a reader cannot tell them apart if the empty one is
simply absent. Say `None.` and move on. The optional sections may be dropped
entirely.

| Section | |
|---|---|
| Status line | mandatory |
| Semantics | mandatory |
| Concrete constraints and frontend coverage | mandatory |
| Options | mandatory (`None.` if there are none) |
| Variable kinds and views | mandatory |
| Reification | mandatory |
| Relation to other families | mandatory |
| OPB encoding | mandatory |
| Labels | mandatory |
| Cake conformity | mandatory |
| Proof-time state | mandatory |
| Initialisation and global data | mandatory |
| Propagator inventory | mandatory |
| Mutable state and incrementality | mandatory |
| Robustness and limits | mandatory |
| Inference catalogue | mandatory, one entry per rule |
| Tests | mandatory |
| Benchmarks and examples | mandatory |
| CPU performance | mandatory (`Not measured.` is an acceptable answer) |
| Proof performance | mandatory (likewise) |
| Proof-logging gaps | mandatory |
| Known limitations | mandatory |
| Next steps | mandatory |
| Prior art | optional |
| Further reading | optional |
| Developer commentary | optional |

Three more rules:

**Provenance on every number.** A performance figure carries the commit it was
measured at, the date, and anything about the machine that mattered. A figure
without that is worse than no figure, because it will be quoted a year later.
Cite numbers that are in a table somewhere; do not report a remembered one.

A figure **measured elsewhere** — an issue's pre-merge A/B, another machine,
an earlier toolchain — is still worth keeping, but it goes in its own labelled
paragraph saying where it came from, never in a table beside figures from this
audit. Say outright that the two sets should not be mixed; otherwise someone
will put them in one table and compute a ratio across them.

**Vocabularies verbatim.** Proof techniques from [Appendix
A](#appendix-a-proof-technique-vocabulary), consistency levels from [Appendix
B](#appendix-b-consistency-level-vocabulary), reconstructibility verdicts from
[Appendix C](#appendix-c-reconstructibility-verdicts), frontend cells from
[Appendix D](#appendix-d-frontend-coverage-cells). If a family needs a
technique the list does not have, add it to the appendix in the same commit
rather than inventing a local name.

**Existing deep docs.** Where a family already has a design note in
`dev_docs/`, short ones (roughly under 150 lines) get appended into
[Developer commentary](#developer-commentary) and the original deleted; long
ones stay where they are and are cross-referenced from [Further
reading](#further-reading) with a sentence saying what is in them. Do not
inline a thousand-line proof-logging writeup.

**`frontend-support-matrix.md` is being retired.** Its rows migrate into each
family's [Concrete constraints and frontend
coverage](#concrete-constraints-and-frontend-coverage) table, which is why that
table inherits the matrix's cell vocabulary and footnote style. Delete the
matrix once every family document carries its rows; until then, do not update
both — update the family document and let the matrix rot.

---

# The skeleton

Everything from here down is the template. Copy it, delete these two lines,
and replace the italicised instructions with content.

---

# `Family`: one-line statement of what it enforces

> **Maturity** production | experimental | checker-only | decomposition-only ·
> **Audited** *yyyy-mm-dd* at `<commit>` · **Open issues** #nnn, #nnn

*When nothing is open, say so and point at [Next steps](#next-steps) for what
this audit would file — an empty issue list and an unaudited family should not
read the same.*

*One short paragraph: what this family is for, and the single most important
thing a reader should know before touching it.*

## What it is

### Semantics

*The precise semantics, with the signature. `Foo(X, Y, 3)` enforces that `X` is
fooed by `Y` no more than three times. Say what happens in the degenerate cases
— empty arrays, a single variable, a zero bound — because that is where the
frontends and the tests disagree.*

### Concrete constraints and frontend coverage

*One row per posted constraint in this family. Cells use [Appendix
D](#appendix-d-frontend-coverage-cells). Footnote anything non-obvious,
especially a `decompose` cell: say what it decomposes into.*

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Foo` | `fzn_foo` ✓ | `foo` ✓ | ? | ✓ | |

### Options

*Each option: what it does, its default, and why that is the default. Then the
question that matters most — does the option change the **OPB model**, or only
the propagation and proof strategy? A knob should pick a strategy, not a model;
an option that changes the model needs a reason. Note any legacy tunables kept
as no-op dummies so that one binary can benchmark every variant.*

### Variable kinds and views

*Which variable kinds the constraint accepts: plain `IntegerVariableID`,
constants, and which views. Then, separately, whether the **proof** handles
views here, because that is where the gaps are — a propagator that accepts a
view and a proof layer that can justify an inference about one are different
claims.*

### Reification

*Whether there is a reified or half-reified form, which class provides it, and
how it is encoded and justified. `None.` if there is not, and say whether one
would be wanted.*

### Relation to other families

*Five directions, because the audit needs all of them: what decomposes
**into** this family; what this family posts as **child constraints**; what
other families **share its code** (an exported helper called from elsewhere is
a coupling a reader will not otherwise see, and a change to it is a change to
them); which **presolvers** rewrite it or rewrite into it; and whether it is
reachable only via a decomposition from a frontend, in which case nothing
exercises the propagator directly.*

*If the family list marks this family as a candidate merge with another,
settle it here and say which way, so the next reader does not re-open it.*

## The proof model

### OPB encoding

*The encoding, in the style of Matthew's thesis — no need to spell out the
creation of integer encoding variables. Where variants of the constraint share
an encoding, either put conditionals in the block, or use a bowtie for
greater/less-than, or give one block per variant, whichever reads best.*

*State whether the encoding is **definitional** — the rows say what the
constraint means, and nothing more — because that is the standard here.
Consequences of the constraint belong in the proof, not the model. If the
encoding's size depends on domain size, say so explicitly and give the
formula; that is what makes a family unusable at large domains.*

### Labels

*Only for encoding rows whose labels are actually used. Give the label, the
rows it names, and which rule in the catalogue refers to it. A label nobody
refers to should not be documented as if it were load-bearing.*

### Cake conformity

*Whether the encoding matches what `cake_pb_cp` verifies, which constraints in
the family are covered by an SCP chain test, and where the two diverge. Name
the divergence even when it is benign.*

### Proof-time state

*This section exists for the external justification tool, which has to rebuild
derivations offline and therefore has to be able to find, by name, everything
the assertion refers to. Cover:*

- *what is emitted **at the root** as scaffolding, and what is emitted
  **lazily** during search;*
- *what is **deleted**, when, and whether deletion makes a later
  reconstruction impossible;*
- *the **naming and labelling convention** by which an external tool locates
  that scaffolding — this is the load-bearing part;*
- *which auxiliaries are **in the OPB** versus **introduced inside the
  proof**, per `dev_docs/variable-encodings.md`, and whether each proof-only
  auxiliary is determined by unit propagation on a solution (it must be, for
  `solx`);*
- *any proof-only vector indexed by something that dangles when proofs are
  off.*

## The implementation

### Initialisation and global data

*What `install_initialiser` does, what is computed once, and what that costs at
the root. If a family has a root cost that dominates on some instance shape,
say which shape.*

### Propagator inventory

*A table, because a family usually installs several propagators and the audit
needs to see them side by side. `Rule` names the entry in the inference
catalogue.*

| Propagator | Triggers | Priority | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| | | | | always | | |

*Then a sentence per propagator on when it disables itself
(`DisableUntilBacktrack`, or permanently), and on the idempotence claim —
`Inference::NoChange` has to mean no change.*

### Mutable state and incrementality

*What state persists between calls, whether it is backtrackable
(`add_constraint_state`) or needs no restore on backtrack, and why. What is
recomputed per call that could in principle be maintained, and what that would
buy.*

### Robustness and limits

*Mandatory, and answer every part explicitly:*

- *behaviour at **large domains** — what happens at a domain of width 1e9, and
  whether the answer is "fine", "slow", or "hangs";*
- *behaviour at **unbounded domains**;*
- *negative values, and zero;*
- ***overflow** — where the arithmetic could overflow, and what guards it;*
- *whether any cost, in the propagator or in the encoding, is proportional to
  the **number of values** rather than the number of intervals or bits.*

## Inference catalogue

*One entry per inference rule, using exactly this heading form —
`### Rule: <short-name>` — so that the whole corpus can be swept for rules.
Every field appears in every entry.*

*A rule is **one inference the propagator makes**, not one propagator: a single
propagator that pushes a bound, removes a value and detects a contradiction is
three rules. Expect this section to be the bulk of the document — the smallest
constraint in the solver has nine rules.*

*Facts that hold for **every** rule in the family — the hint type they all
share, an invariant like "no justification reads `state`" — go in a short
preamble here rather than being repeated in each entry. Anything that varies
between rules stays in the entries, even when most of them agree.*

### Rule: short-name

- **Infers** — *what is inferred: a bound push, a value removal, a
  contradiction, a flag.*
- **Fires when** — *the trigger, and which propagator from the inventory runs
  it.*
- **Strength** — *from [Appendix B](#appendix-b-consistency-level-vocabulary);
  what this rule alone achieves on its scope.*
- **Algorithm** — *what it does, its complexity, and the literature reference.
  Be explicit about what the complexity is in: genuinely the **number of
  values**, or the number of **intervals**, or **bits**, or tasks. This is the
  single most-often-fudged line.*
- **Why it is true** — *the mathematical argument, stated independently of any
  proof system. Someone should be able to check the rule is sound from this
  line without knowing what VeriPB is.*
- **Proof technique** — *from [Appendix
  A](#appendix-a-proof-technique-vocabulary), verbatim.*
- **Reason** — *which literals go into the reason, and whether that set is
  minimal. The reason is what the external tool sees; a non-minimal one costs
  it trimming work. A justification reads the reason, never `state`.*
- **Assertion** — *the PB inequality actually emitted, as a shape in terms of
  the rule's data. This is what an `a` line would contain in hints-only mode.*
- **Hint** — *the `gcs::innards::hints` type, and one line per field giving its
  type and meaning. If the hint does not exist yet, say so — that is a work
  item, and it belongs in [Next steps](#next-steps).*
- **Offline reconstructibility** — *one of the three verdicts in [Appendix
  C](#appendix-c-reconstructibility-verdicts). If `solver-side`, name the
  information that is not recoverable.*
- **Proof size** — *per firing, asymptotically; plus a measured figure with
  provenance if there is one.*
- **Gaps** — *whether this rule is logged at all, and whether the propagator is
  weakened when proofs are enabled. `None.` is the expected answer.*

## Evidence

### Tests

*What exists, and — as importantly — what it does not cover:*

- *the enumeration tests, and whether they use `solve_for_tests_checking_gac`
  (per-node GAC assertion) or plain `solve_for_tests`;*
- *whether VeriPB actually runs in the tests, which is not true everywhere;*
- *whether any test caps its runtime, and what the uncapped setting exercises;*
- *whether the tests are seeded (`--seed=N`) and so byte-reproducible;*
- *whether any real instance has been ported into a data-driven test, and
  which repros have not been;*
- *whether the derivation has been shown to be tight — a mutation that VeriPB
  should refuse, and does.*

*Then, as a separate list, **what the tests do not cover**. This is the half
that makes the section worth writing: the domain widths the suite never reaches,
the check that turns out to be weaker than its name suggests, the evidence that
was never recorded. A test section that only inventories what exists has not
audited anything.*

### Benchmarks and examples

*Which in-repo examples and MiniZinc Challenge instances exercise this family.
Then split the recommendation, because they are different jobs: which instance
and parameters are the right size for **CPU** benchmarking, and which for
**proof verification** benchmarking. Note anything that must never be run
uncapped.*

### CPU performance

*Where possible, against Gecode, Choco and ACE on an identical-search-tree
benchmark that is dominated by this family. Caveat the comparison where the
inference strengths differ, and especially where our default differs from
theirs. Include search-shape columns — `recursions` and `propagations[0]` —
because a wall-clock table without them cannot distinguish a faster propagator
from a different search.*

*Caption every table with the build, commit, date and machine.*

### Proof performance

*The proof axis, which the paper's headline table is made of: proof size, VeriPB
verification time, the ratio of verification to solve time, and which instances
are too large to verify at all. Same provenance requirement.*

*Two things to separate out, because a raw proof size conflates them. First,
this family's **own** contribution against what the shared layers (the
order-literal and equality-literal definitions, the range-literal layer) emit
around it — for a cheap constraint the shared layers dominate, and a proof-size
figure that does not say so will be read as this family's cost. Second, the
size and verification time at the **assertion levels** as well as fully
justified, since that difference is what an external justifier consumes; report
how many assertions carry this family's hint, and what share of the proof's
assertions that is.*

## Status, gaps, and next steps

### Proof-logging gaps

*Any inference the propagator makes that the proof does not justify, and any
place we rely on an unchecked assertion. Separately: whether the propagator's
strength **changes** when proof logging is enabled — that is, something we can
propagate but cannot certify. The expected answer to both is `None.`, and
anything else is either a filed issue or a new one.*

### Known limitations

*What the implementation does not do, phrased so a user would recognise their
symptom in it. Include documented proof gaps: recording a limitation is often
the right outcome, and better than a speculative solver change.*

### Next steps

*A ranked list. Each item: what to do, roughly what it would cost, what it
would buy, and an issue number if one exists. This is the triage output, and
the reason the audit was worth writing down.*

## Prior art

*Optional but wanted for the paper. Who proposed the propagation algorithm; who
has certified this constraint before, if anyone, and in what proof system; and
what is novel here. Without this the attribution has to be reconstructed for
thirty families at writing time.*

*"There is none" is a good answer when it is argued: for some families nobody
publishes a propagation algorithm and all the interesting content is on the
proof side, which is itself something a survey wants to say.*

## Further reading

*Annotated links to the long design notes that stay in `dev_docs/`. A sentence
each on what is in them, not just a link.*

## Developer commentary

*Optional. Short pre-existing design notes appended here, and any commentary
that does not fit the sections above. Some families were implemented by hand
and have no such notes; there is no need to manufacture one.*

---

# Appendices

## Appendix A: proof technique vocabulary

Use these names verbatim in the **Proof technique** field. A rule may name more
than one.

| Name | Meaning |
|---|---|
| `RUP` | plain reverse unit propagation, no hints |
| `RUP+hints` | RUP with explicit constraint-id hints |
| `pol` | a cutting-planes derivation: linear combination, with `saturate` / division as needed |
| `extended reason` | a hypothetical literal pinned into the reason so the inference becomes RUP-derivable |
| `redundance` | extension-variable introduction, i.e. defining a `ProofFlag` |
| `dominance` | a dominance-rule derivation |
| `cases` | the VeriPB 3 `cases` rule |
| `chain scaffolding` | root-level per-value chains that a later RUP resolves against, as the diagram-shaped constraints use |
| `counting argument` | pigeonhole or an at-most-one recurrence carrying an exact coefficient |
| `sorting network` | a derivation through a network's comparator rows |
| `a` oracle | an unchecked assertion — **not** a proof, and always also a gap |
| `not logged` | the inference is made but nothing is emitted — always also a gap |

Adding a name here is fine; inventing one locally is not.

## Appendix B: consistency level vocabulary

| Name | Meaning |
|---|---|
| `GAC` | generalised arc consistency on the whole constraint |
| `bounds(Z)` | bounds consistency over the integers |
| `bounds(D)` | bounds consistency over the domains |
| `range` | range consistency |
| `partial` | a named subset of the above — say which, and on which variables |
| `checker` | detects violation of a full assignment only |
| `decomposition` | whatever the posted children achieve, which is weaker than GAC on the conjunction |

GAC on two constraints separately is not GAC on their conjunction; a family
implemented by decomposition says `decomposition`, not `GAC`.

## Appendix C: reconstructibility verdicts

For the **Offline reconstructibility** field. This is the field Matthew's tool
is read off, so it is worth being strict about.

| Verdict | Meaning |
|---|---|
| `offline` | the assertion alone determines the derivation; the tool needs nothing else |
| `hinted` | the assertion plus the hint payload determines it |
| `solver-side` | it needs information not recoverable from assertion and hint — the exact Hall set, the traversal order of a DP, which of several equally-valid explanation subsets was chosen. **Name the information.** |

The `solver-side` rules are exactly the list of things the external tool cannot
rebuild, and therefore exactly what a hints-only GCS mode has to carry. Getting
this field wrong is more expensive than leaving it blank.

## Appendix D: frontend coverage cells

Inherited from `frontend-support-matrix.md`, which these tables replace.

| Cell | Meaning |
|---|---|
| ✓ | fully supported |
| `decompose` | supported by translating to other primitives at parse time — footnote how |
| `unsupported` | the frontend deliberately does not handle this shape |
| `solver gap (#nnn)` | the propagator does not exist yet |
| `frontend gap (#nnn)` | the propagator exists, the binding does not |
| `n/a` | the concept does not apply to this frontend |
| `?` | not yet investigated |

A `?` is an acceptable answer and marks a row that wants attention.

---

# The presolver variant

Presolvers get a document too, under `dev_docs/presolvers/`, but not this
template with the propagation sections deleted. A presolver does not infer; it
rewrites the model before search. The differences:

**Dropped.** Propagator inventory, mutable state and incrementality,
idempotence, consistency level. A presolver runs once.

**Replaced.** The inference catalogue becomes a **rewrite catalogue**, one
entry per rewrite, with fields: what pattern is matched; what is posted or
strengthened; whether the rewrite is posted in derived mode; the soundness
argument; the proof technique that certifies the rewrite; and whether the
rewrite is *neutral* with respect to the propagators that consume it (which is
what makes a node-for-node soundness tripwire available).

**Added, and these are the ones that matter.** Three sections with no analogue
in a constraint document:

- **Detection and its failure modes.** What the donor scan looks for, and how
  detection **fails silently**. This is the recurring bug in this part of the
  codebase: a scan couples to the constraint class it was written against and
  simply finds nothing on a model built a slightly different way. Say which
  constraint classes the scan actually recognises.
- **Evidence that it fired.** A presolver that does nothing passes every test
  in the suite. So: which counter, statistic or log line distinguishes "ran and
  found nothing" from "ran and did nothing", and what the expected count is on
  a named instance. Without this section a presolver document certifies
  nothing.
- **Can it weaken the model?** Whether the rewrite can ever lose solutions or
  lose propagation strength, and what stops it. Include the `ia` step or
  equivalent that pins the emitted row to the intended one — a sound derivation
  of the *wrong* line is the failure a soundness argument alone does not catch.

Everything else — status line, semantics, OPB and proof-time state, robustness,
tests, benchmarks, both performance sections, gaps, next steps, prior art —
carries over unchanged.

---

# Provisional family list

The work plan, and the definition of "family". Provisional: the groupings
marked *candidate merge* should be settled as the documents get written, and
this table moves to `dev_docs/constraints/README.md` once it is stable.

| Document | Covers | Notes |
|---|---|---|
| `all_different.md` | `all_different/` | GAC and VC variants, `AllDifferentExcept`, `ExceptZero` |
| `all_equal.md` | `all_equal/` | |
| `among.md` | `among/` | *candidate merge* with `count`, `global_cardinality`, `n_value` as one counting family |
| `arithmetic.md` | `multiply/`, `divide_modulus/`, `plus_minus/`, `power/`, and the `plus.hh` / `minus.hh` / `divide.hh` / `modulus.hh` headers | one family over several directories; existing note is `arithmetic-proofs.md` |
| `abs.md` | `abs/` | *candidate merge* into `arithmetic`; kept separate for now because of the view-proof gap |
| `at_most_one.md` | `at_most_one/` | |
| `bin_packing.md` | `bin_packing/` | existing note `bin-packing.md` |
| `circuit.md` | `circuit/` | includes subcircuit |
| `comparison.md` | `comparison/` | twelve classes over `ReifiedCompareLessThanOrMaybeEqual`; **not** merged with `equals` — same reified-dispatcher pattern, no shared code, separate encodings |
| `equals.md` | `equals/` | **written** — the pilot. `Equals`, `NotEquals` and the four reified forms |
| `count.md` | `count/` | see `among` |
| `cumulative.md` | `cumulative/` | the largest family; notes `cumulative-proof-logging.md`, `certified-makespan-bounds.md`, `rule-counters.md` |
| `difference.md` | `difference/` | difference constraints; note `difference-logic.md`, whose presolver half belongs under `dev_docs/presolvers/` |
| `disjunctive.md` | `disjunctive/`, `disjunctive_2d/` | one family, two dimensions; note `disjunctive-proof-logging.md` |
| `element.md` | `element/` | `Element`, `Element2D` |
| `global_cardinality.md` | `global_cardinality/` | see `among` |
| `in.md` | `in/` | note `range_literals_spec.md` |
| `increasing.md` | `increasing/` | `Increasing`, `Decreasing` |
| `inverse.md` | `inverse/` | |
| `knapsack.md` | `knapsack/` | existing note `knapsack.md`; `decision-diagram-proof-strategies.md` |
| `lex.md` | `lex/`, `lex_smart_table.hh` | |
| `linear.md` | `linear/` | note `linear-slack-waking.md`, `subset-sum-strengthening.md` |
| `logical.md` | `logical/` | |
| `mdd.md` | `mdd/` | `decision-diagram-proof-strategies.md` |
| `min_distance.md` | `min_distance/` | note `min-distance-proofs.md` |
| `min_max.md` | `min_max/` | |
| `n_value.md` | `n_value/` | see `among` |
| `nogoods.md` | `nogoods/` | search machinery rather than a posted constraint; notes `restarts-nogoods-weighting.md`, `refined-triggers.md` |
| `parity.md` | `parity/` | |
| `path.md` | `path/` | |
| `reachable.md` | `reachable/` | |
| `regular.md` | `regular/` | existing note `regular.md` |
| `seq_precede_chain.md` | `seq_precede_chain/` | |
| `smart_table.md` | `smart_table/` | *candidate merge* with `table` as one extensional family |
| `sort.md` | `sort/` | `Sort`, `ArgSort`; existing note `sortedness.md` |
| `subgraph.md` | `subgraph/` | |
| `table.md` | `table/`, `extensional_utils.{hh,cc}` | `Table`, `NegativeTable`; see `smart_table` |
| `tree.md` | `tree/` | |
| `value_precede.md` | `value_precede/` | |

Not families, and getting no document: `gcs/constraints/innards/` (shared
helpers — documented where they are used, or in `constraints.md`).

Presolvers, one document each under `dev_docs/presolvers/`: `auto_table`,
`cumulative_strengthening`, `difference_logic`, `inferred_cumulative`,
`inferred_disjunctive`. Existing notes: `cumulative-strengthening.md`,
`inferred-cumulative.md`, `inferred-disjunctive.md`, and the presolver half of
`difference-logic.md`.
