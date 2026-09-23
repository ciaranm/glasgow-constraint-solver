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
| Interior values and optional pruning | mandatory |
| Robustness and limits | mandatory |
| Interval efficiency | mandatory |
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

**Notation.** Write the bit-sum encoding of a variable as **`BinEnc(v)`**,
which is the thesis's own notation and so the one a reader of both will
recognise. Do not use `⟦v⟧`: semantic brackets already mean Boolean condition
evaluation, and they are awkward to type.

**"Lemma" is ours, informally, and stays undefined on purpose.** These
documents, ten others under `dev_docs/`, and several headers
(`comparator_network.hh` most of all) use "lemma" for an intermediate
constraint a justification derives and adds to the proof before asserting its
conclusion — normally at `ProofLevel::Temporary`, so it is deleted again. It is
**not** a VeriPB concept, and the reason it is not defined here is that the
thing it would name — a nameable, reusable derived statement — is a feature
VeriPB cannot soundly have. So there is nothing formal to point at, and
inventing a local definition would only compete with the informal usage
everywhere else. Keep using the word; if VeriPB ever grows a `lemma`, we change
the terminology across the tree in one go rather than per document.

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
> **Audited** *yyyy-mm-dd* at `<commit>`; re-audited *yyyy-mm-dd* at
> `<commit>` · **Open issues** #nnn, #nnn

*When nothing is open, say so and point at [Next steps](#next-steps) for what
this audit would file — an empty issue list and an unaudited family should not
read the same.*

*A **re-audit** is a distinct event, and the status line carries both dates,
because a reader needs to know which commit each figure was taken at. When the
audit's own issues get fixed the document has to be brought back into line with
them and re-measured; fixing four issues in one family moved its rule
catalogue, its robustness section and both performance tables. Open the
re-audit with a short `issue → PR → what it changed here` table, so the diff
against the first pass is legible, and say outright which figures were taken
again.*

*A fix to a **shared helper** does not stop at this document. Follow it into
[justification-techniques.md](../justification-techniques.md) and into every
other family that calls the helper, and bring their present-tense claims into
line. The status table records that a fix happened; it does not update a
sentence elsewhere that still describes the old behaviour as current, and
keeping the old behaviour is fine only as dated history.*

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

***`with_consistency()` gets its own paragraph*** *when the family has one: the
exact `std::variant` of `gcs::consistency` tags it accepts, the default per
posted class (they often differ — `Element`'s variable-array forms default to
`GAC` and its constant-array forms to `BC`), and, for each tag, which
propagators that selection installs. Requesting a level the family does not
list is a compile-time error, so the variant's alternatives are the closed
list; give them as such rather than describing them.*

*Two of the tags are **policies rather than levels**, and a family that accepts
either owes a sentence saying which mechanism it means, because they resolve at
different times and a reader will otherwise assume the wrong one:*

- `consistency::Auto` *resolves* **once, before search**, *from the rest of the
  model. For a family that implements it with an optional-interior-pruning pair
  this is the mechanism described under [Interior values and optional
  pruning](#interior-values-and-optional-pruning), and that section is where
  the detail goes; other families may implement it some other way (tabulating
  when the domains are small, say), and then say so here. Either way, say what
  it falls back to when nothing makes the choice — a `Propagators` on which
  nothing calls `choose_optional_interior_pruning()` keeps every pruning on.*
- `consistency::Dynamic` *decides* **afresh at every call**, *on the current
  domains. Say what "cheap" means for this family and what it drops to. It is a
  fixed rule rather than a policy, which is the point of it being a separate
  tag: requesting it explicitly survives a change to what `Auto` maps to.*

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

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| | | derived | | always | | |

*Propagators have no priority, so there is no column for one. An initialiser
does (`InitialiserPriority`); give an initialiser a row too, and say its
priority in* Enabled by *when it is not the default.*

*Then a sentence per propagator on when it disables itself
(`DisableUntilBacktrack`, or permanently), and on the idempotence claim —
`Inference::NoChange` has to mean no change.*

***Holes affect*** *is which variables' holes affect that propagator's
propagation, in the sense of
[optional-interior-pruning.md](../optional-interior-pruning.md): from any
domains, could removing values from strictly inside a variable's bounds ever
give this propagator an inference it could not already have made? Say `derived`
when the declaration comes from the triggers under the usual mapping
(`on_change` and `scope_only` yes, `on_bounds` and `on_instantiated` no, a
`refined` watch yes unless it is on a bound literal), and otherwise name the
variables the propagator declares through `Triggers::holes_affect_propagation`
**and why the triggers do not tell the truth**. Every family fills this column
in, including the families that install no optional pruning of their own,
because this is the half that other families' `consistency::Auto` reads: a
family that under-reports here silently weakens somebody else's constraint, and
nothing in the suite will say so. Getting it wrong in this direction is never
unsound — it only loses propagation — which is exactly why it needs writing
down rather than testing for.*

### Mutable state and incrementality

*What state persists between calls, whether it is backtrackable
(`add_constraint_state`) or needs no restore on backtrack, and why. What is
recomputed per call that could in principle be maintained, and what that would
buy.*

### Interior values and optional pruning

*Two questions, and every family answers both, because they are the two ends of
one mechanism: [optional-interior-pruning.md](../optional-interior-pruning.md).*

***What this family offers.** Whether it installs an optional-interior-pruning
pair (`Propagators::install_with_optional_interior_pruning()`), and under which
option — normally `consistency::Auto`. If it does, give:*

- *the **targets**, the **pruning** propagator and the **fallback**, by their
  names in the [Propagator inventory](#propagator-inventory), and which rules in
  the catalogue stop firing when the fallback is live;*
- *the argument that the pair keeps **both promises**, stated for this family,
  not cited: that the two members differ only in the targets' interiors, and
  that no other propagator of this constraint can tell whether the values the
  pruning would remove are there. The second is the load-bearing one — it is
  what lets the analysis ignore the constraint's own sensitivity to its own
  targets — and it is checked by nothing, so writing it out is the check;*
- *the **shapes that do not qualify**, and why. This is usually the more
  informative half: `Element` makes the promises only over an array of
  constants, and only when the result is not also one of its indices. A family
  that offers a pair on some shapes and not others says where the line is and
  what goes wrong on the far side of it.*

***What this family observes.** Whether anything here is affected by holes in
somebody else's variables, which is what keeps another constraint's pruning
alive. The [Propagator inventory](#propagator-inventory)'s* Holes affect
*column carries it per propagator; this is where to say anything that column
cannot, particularly a propagator whose triggers overstate or understate its
real sensitivity, and what was done about it. A family whose whole vocabulary
is bounds should say so outright and in those words — it is the case that makes
the mechanism pay, and it is worth being able to find by grep.*

*`None.` on the first question is an ordinary answer and most families will
give it. The second is never `None.`: a family with no propagators at all would
not have this document.*

*Do not restate the analysis here. Cite it, and keep to what is true of this
family.*

### Robustness and limits

*Mandatory, and answer every part explicitly:*

- *behaviour at **unbounded domains**;*
- *negative values, and zero;*
- *the **degenerate shapes** — an empty array, a single variable, an aliased
  pair, a constant operand — where the frontends and the tests tend to
  disagree;*
- ***overflow** — where the arithmetic could overflow, and what guards it.*

*Everything about **width** — what happens at a domain of width 1e9, and what
any cost is proportional to — goes in [Interval
efficiency](#interval-efficiency) instead, which is a section of its own
because it now has more to say than a bullet.*

### Interval efficiency

*A domain is an `IntervalSet<Integer>`, and the policy in
[large-domains.md](../large-domains.md) is that **every bounds-consistency path
must be independent of domain width**. This section is that document's per-family
row: what this family's work is proportional to, and where it still is not
proportional to the right thing.*

*Answer four things, and keep them apart, because a family can pass any one of
them and fail the next:*

1. ***The propagation side.*** *Every site that walks values —
   `State::each_value_*`, `State::for_each_value_*`, an `IntervalSet` the
   propagator builds and walks itself, a plain `for (v = lo; v <= hi; ++v)` —
   with one line each saying why it is acceptable: it exits early after a bounded
   number of steps, it is bounded by something other than the domain (a value
   set, an array, a task count), or it is a genuine per-value support scan with
   no interval structure to exploit and a weaker arm behind it. Name the interval
   primitive used where one is used instead: `domain_intersects_with()`,
   `domain_is_subset_of()`, `domains_intersect()`,
   `IntervalSet::each_interval_minus()`, `InferenceTracker::infer_not_in_range()`.
   "Reaches for `State`'s per-value iterators nowhere at all" is a property that
   can be checked by reading, which is worth more than a benchmark; say it when
   it is true.*
2. ***The reason side.*** *Whether a reason this family builds is one literal per
   value or one per run, and — separately — whether the **work of finding** the
   runs is one step per run or one per value. A site can get the first right and
   the second wrong, and neither the audit lane nor a proof-size survey can see
   it, because the proof was already the right size (#935). Say whether reason
   assembly is guarded on `InferenceTrackerBase::want_reasons()`: an unguarded
   width-proportional reason is a hazard on the propagation path even with proofs
   off.*
3. ***The proof side.*** *Whether any emitted line is per value, and whether the
   form is chosen by a **width gate** rather than unconditionally. The ban on
   per-value iteration does not carry over to what a proof emits: over a narrow
   definition range the interval form is about as big per line and there are more
   of them, so going to covers unconditionally cost `sudoku` 16% more proof lines
   (#939). A family that picks its form by a width test says where the threshold
   is; a family that picks by the **kind** of a variable rather than by width has
   a bug of the shape #924 and #931 fixed, and should say so here.*
4. ***Where the family stands in the audit lane.*** *Its rows in
   `gcs/large_domain_audit_test.cc` and their pinned outcomes (`Clean`,
   `KnownTrip`, `NoWidePosition`, `HazardNotReached`), plus its rows in that
   file's `"Large domain proof sizes"` case if it has any. Then the part the
   table cannot say: **which axes those rows do not vary**. A row varies width,
   holes, the variable's kind, whether a reason is materialised, which
   constructor was used and which arm the option selects — most rows vary only
   the first, and every gap this arc has found was a row that reached the
   constraint without reaching the site. A family with no row says that, and
   [Next steps](#next-steps) gets an item.*

*`Fine at any width` is a legitimate and common answer to all four, and a family
whose encoding is logarithmic in width should say so plainly. What is not
legitimate is answering only the first: three of the four sites this arc found
were on the reason and proof sides, where a search for pruning loops does not
reach.*

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
  it. If the rule belongs to one arm of a selectable consistency level, or to
  one member of an optional-interior-pruning pair, say which — a rule that does
  not run under the family's default is still a rule, and the question a reader
  has is when it runs at all.*
- **Strength** — *from [Appendix B](#appendix-b-consistency-level-vocabulary);
  what this rule alone achieves on its scope. A **policy tag is never an answer
  here**: `consistency::Auto` and `consistency::Dynamic` name how a level gets
  chosen, not a level, so a rule under one of them states the level its own arm
  achieves and leaves the choosing to [Options](#options).*
- **Algorithm** — *what it does, its complexity, and the literature reference.
  Be explicit about what the complexity is in: genuinely the **number of
  values**, or the number of **intervals**, or **bits**, or tasks. This is the
  single most-often-fudged line.*
- **Why it is true** — *the mathematical argument, stated independently of any
  proof system. Someone should be able to check the rule is sound from this
  line without knowing what VeriPB is. So no proof-line counts, no emission
  costs and no VeriPB vocabulary belong here — those go in **Proof technique**
  and **Proof size**. It is an easy field to leak into, because for a rule
  whose argument and whose derivation have the same shape the two want to be
  written as one table; keep them apart anyway, since the whole value of this
  field is being readable by someone auditing soundness rather than proofs.*
- **Proof technique** — *from [Appendix
  A](#appendix-a-proof-technique-vocabulary), verbatim, **and what licenses
  it**: the justification procedure this rule is an instance of, and the
  theorem behind that procedure, per
  [justification-techniques.md](../justification-techniques.md). Where there is
  no published procedure — the rule is ours — say so outright, because that is
  precisely what an external justifier cannot replay, and then owe the
  argument to **Why it is true**. State the procedure's **preconditions**: they
  are what tells a later reader whether the citation survives a change. This
  field describes the **derivation**, the lines a checker is given; the
  annotation an assertion carries in hints-only mode is a separate thing and
  goes in **Hint**.*
- **Reason** — *which literals go into the reason, and whether that set is
  minimal. The reason is what the external tool sees; a non-minimal one costs
  it trimming work. A justification reads the reason, never `state`. Say
  whether the literal count is **per value or per run** of the domains it
  names, and whether assembling it is guarded on `want_reasons()`; see
  [Interval efficiency](#interval-efficiency) for why the two are separate
  questions.*
- **Assertion** — *the PB inequality actually emitted, as a shape in terms of
  the rule's data. This is what an `a` line would contain in hints-only mode.
  Where the rule has **two forms** — a range assertion and a per-value one —
  give both and say what picks between them, which should be a width test and
  not a test on the kind of a variable. **A conflict has two shapes, and they
  are not the same line.** An explicit `contradiction()` asserts `¬reason`,
  since the tracker passes it `FalseLiteral`. An ordinary inference whose
  literal is already false, which is how most conflicts arise, asserts
  `attempted literal ∨ ¬reason`, exactly as if it had succeeded; the conflict is
  closed afterwards, by the backtrack. Say which one the rule takes, and check it
  against an `a` line at `AssertionLevel::Inferences` rather than the code
  path's name.*
- **Hint** — *the `gcs::innards::hints` type, and one line per field giving its
  type and meaning. This is the **reconstruction annotation** on the `a` line:
  its subhint tells an external justifier which procedure to run, and its
  payload carries any witness that procedure needs. It is not a proof
  technique, and it is not VeriPB's own RUP antecedent list. If the hint does
  not exist yet, say so — that is a work item, and it belongs in [Next
  steps](#next-steps).*
- **Offline reconstructibility** — *one of the four verdicts in [Appendix
  C](#appendix-c-reconstructibility-verdicts), judged against its baseline
  context. If `search`, name the search and its cost; if `solver-side`, name the
  information that is missing and argue that no other sufficient derivation
  exists.*
- **Proof size** — *per firing, asymptotically, and **in what**: values, runs,
  bits, or tasks. The distinction is the whole point of the field for a family
  whose domains can be wide, and "linear" without it is the line this arc has
  most often had to go back and correct. Plus a measured figure with provenance
  if there is one.*
- **Gaps** — *whether this rule is logged at all, and whether the propagator is
  weakened when proofs are enabled. `None.` is the expected answer.*
- **Tightness** — *whether a mutation of **this rule's** derivation has been
  shown to be refused by VeriPB, and which corruption. `Not shown.` is an
  ordinary answer, not a defect: mutation lanes are a development tool, worth
  their cost while a derivation is being written or changed and not worth
  adding for the sake of the tally. The field exists so that someone about to
  change a rule can see whether a lane will catch them, which is a different
  question from whether every rule has one. Where a lane's instance took work
  to build, say what the slack instances were: that part is reusable, and the
  corruption rarely is.*

## Evidence

### Tests

*What exists, and — as importantly — what it does not cover:*

- *the enumeration tests, and whether they use `solve_for_tests_checking_gac`
  (per-node GAC assertion) or plain `solve_for_tests`;*
- *whether VeriPB actually runs in the tests, which is not true everywhere;*
- *runtime caps, as two separate facts. First the **default policy**: every
  registered test runs under the suite-wide solution and search-node caps
  (`GCS_TEST_CAP_DEFAULTS`, see [`building.md`](../building.md)) unless the
  lane clears them, a truncated solve checks soundness and a partial proof
  only, and the two Ubuntu CI lanes build with the caps off. Say whether any of
  this family's lanes sets or clears a cap, and whether the default caps
  actually **fire** on them, which decides whether the capped run checked less.
  Second, the **configuration the reported results came from**, with the
  invocation recorded once. "No runtime caps" answers neither question;*
- *whether the tests are seeded (`--seed=N`) and so byte-reproducible;*
- *whether any real instance has been ported into a data-driven test, and
  which repros have not been;*
- *whether any derivation has been shown to be tight, and — where lanes exist
  — whether a **control** lane checks that the same instances verify
  uncorrupted, without which a mutation lane can be green because its instance
  does not verify either. The per-rule evidence goes in that rule's
  **Tightness** field; this is the inventory and the harness. Partial coverage
  is the expected state, so say which rules have a lane rather than treating
  the rest as outstanding work. And keep the family-level claim to what the
  lanes show: some named corruptions are rejected on some named fixtures.
  That a step is a RUP does not make a finite set of mutations exhaustive over
  its premises, its literals or the cases it applies to, so "the derivations
  are tight" is not a conclusion any set of lanes supports.*

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

*Say what the chosen benchmark does **not** exercise. A family's natural
benchmark often reaches a small minority of its rules — read that off the
proof's assertions rather than guessing — and a per-inference cost quoted from
it is an average over those. Without this line, a cross-family pivot over these
documents will silently compare unlike things.*

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
assertions that is, broken down by wire form.*

*The own-versus-shared split wants a **measurement**, not an estimate. Vary
whatever the family's cost is proportional to, count the lines each layer
emits, and give the two as functions of it. "2n against 10n + 1" is a finding;
"the shared layers dominate" is a guess that happens to be right.*

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

**A name is not an argument.** `RUP` says which VeriPB rule we emit; it does
not say why unit propagation will succeed, which depends on the shape of the
row and the encoding underneath it. So the field takes a name from this table
**and** the result that licenses it — see
[justification-techniques.md](../justification-techniques.md), which collects
the handful of unit-propagation facts the solver leans on and maps them onto
the published justification procedures. Cite a procedure and a theorem; do not
paraphrase the proof.

| Name | Meaning | Where the licence comes from |
|---|---|---|
| `RUP` | one reverse-unit-propagation step: the conclusion is RUP against the database as it stands | a justification procedure (JP 3.1, 3.2, 3.12, 3.15, …) resting on Thm 2.6–2.9 |
| `RUP sequence` | several RUP steps: lemmas at a temporary level, then the conclusion by RUP once they are in place. Say what the lemmas are and how many there are | per step, as `RUP`; the procedure that orders the steps, where one is published (JP 3.9, 3.10, 3.13) |
| `hinted RUP` | a RUP step carrying VeriPB's own antecedent list (`RUPProofRule::lines`): the checker propagates over the cited lines only, so a hinted step is cheaper to check and **fails** if the list misses part of the conflict path. See [`veripb-facts.md`](../veripb-facts.md) | as `RUP`, over the cited lines |
| `pol` | a cutting-planes derivation: linear combination, with `saturate` / division as needed | the derivation itself, stated in the rule |
| `extended reason` | a hypothetical literal pinned into the reason so the inference becomes RUP-derivable | Thm 2.6, plus whatever licenses the underlying step |
| `redundance` | extension-variable introduction, i.e. defining a `ProofFlag` | Thm 2.4 (extension variables) |
| `dominance` | a dominance-rule derivation | the dominance rule's own side conditions — state them |
| `cases` | the VeriPB 3 `cases` rule | `dev_docs/`'s `cases`-rule notes |
| `chain scaffolding` | root-level per-value chains that a later RUP resolves against, as the diagram-shaped constraints use | the family's own argument |
| `counting argument` | pigeonhole or an at-most-one recurrence carrying an exact coefficient | the family's own argument |
| `sorting network` | a derivation through a network's comparator rows | the network's comparator rows, per family |
| `a` oracle | an unchecked assertion — **not** a proof, and always also a gap | nothing; that is the point |
| `not logged` | the inference is made but nothing is emitted — always also a gap | nothing |

Adding a name here is fine; inventing one locally is not. Adding one **without**
saying what licenses it is how the table stopped being useful the first time.

**The assertion's annotation has no row here, deliberately.** An earlier version
had `RUP+hints`, meaning "RUP with constraint-id hints", and it ended up naming
two different things: a lemma-then-conclusion derivation (what `RUP sequence`
now names) and the `hints::` annotation that every assertion carries in
hints-only mode, whatever the derivation behind it. It also collided with
VeriPB's RUP antecedent hints, which really are part of the proof, and which
`veripb-facts.md` and the code already call a **hinted RUP**; that name now has
its own row, and means only that. The
annotation goes in a rule's **Hint** field; it is what a reconstructor reads to
choose a procedure, and the derivation is only one way of reaching the same
conclusion.

## Appendix B: consistency level vocabulary

Two lists, and they are not interchangeable. The first is what a rule or a
propagator **achieves**, and is what the **Strength** field takes. The second
is what a model may **request**, and is what [Options](#options) takes.

### Levels achieved

| Name | Meaning |
|---|---|
| `GAC` | generalised arc consistency on the whole constraint |
| `bounds(D)` | each variable's two bounds have a support in which every other variable takes a value **from its domain** |
| `bounds(Z)` | each variable's two bounds have a support in which every other variable takes an **integer between its bounds**, holes ignored |
| `bounds(R)` | each variable's two bounds have a support in which every other variable takes a **real number between its bounds** |
| `range` | range consistency: every value has a support of the `bounds(Z)` kind |
| `partial` | a named subset of the above — say which, and on which variables |
| `checker` | detects violation of a full assignment only |
| `decomposition` | whatever the posted children achieve, which is weaker than GAC on the conjunction |

GAC on two constraints separately is not GAC on their conjunction; a family
implemented by decomposition says `decomposition`, not `GAC`.

**The three bounds levels are Choi, Harvey, Lee and Stuckey's** (*Finite
Domain Bounds Consistency Revisited*, arXiv cs/0412021, Definitions 3 to 5), and each
implies the next: `bounds(D)` ⇒ `bounds(Z)` ⇒ `bounds(R)`. The difference
between the last two is the one that is easy to get wrong. Interval arithmetic
on a linear sum or a single product, over distinct variables, reaches
`bounds(R)`, and it reaches `bounds(Z)` only when the relation happens to take
every integer in between. A general linear equality
does not: `2x + 3y + 3z = 4` with `x ∈ 0..2` and `y, z ∈ 0..1` is a fixed point
of the bounds sweep, but its one solution is `(2, 0, 0)`, so `x = 0`, `y = 1`
and `z = 1` have real supports and no integer ones. A product does not either:
with `x, y ∈ 2..4` and `z ∈ 5..15`, the box is a fixed point of `x·y = z`, but
the integer products in it are 6, 8, 9 and 12, so neither 5 nor 15 has an
integer support. So **check a `bounds(Z)` claim against a brute-force enumeration** of
small instances before making it, not against the algorithm's description.

None of the three is `consistency::BC`. That tag, below, names what a model
asks for, and a rule under it still says which of these it achieves.

### Levels requestable

The tags in `gcs/consistency.hh`, which a family exposes as a `std::variant`
through `with_consistency()`. Name the tag, `consistency::`-qualified, so that
the two lists cannot be confused in a table.

| Tag | What it selects |
|---|---|
| `consistency::GAC` | a genuine algorithm reaching GAC, whose cost is under that algorithm's control |
| `consistency::Tabulated` | GAC reached by enumerating every satisfying assignment — a different tag precisely because the set-up and the proof grow with the product of the domain sizes |
| `consistency::BC` | bounds consistency |
| `consistency::VC` | value consistency: a fixed variable's immediate consequences and nothing more |
| `consistency::Auto` | **a policy, not a level** — the solver chooses, once and before search |
| `consistency::Dynamic` | **a fixed rule, not a level** — GAC where the GAC algorithm is cheap on the current domains, re-decided at every call |

The bottom two never appear as a **Strength**. They say how a level is chosen,
and the answer can differ per model (`Auto`) or per call (`Dynamic`), so the
rule under one of them states what its own arm achieves and
[Options](#options) explains the choosing. The distinction between them is
*when the choice is made*, and it is worth keeping because it decides what a
reader can conclude from a benchmark: `Auto`'s answer is fixed for a whole
search and visible on the stats channel, `Dynamic`'s is not.

Requesting a level a family does not list is a compile-time error, so a
family's variant is the closed list of what it supports — and adding an
alternative is an API change, where adding a row to the first table is not.

## Appendix C: reconstructibility verdicts

For the **Offline reconstructibility** field. This is the field Matthew's tool
is read off, so it is worth being strict about.

**What a reconstructor starts with.** Every verdict is relative to one baseline:

- the original model, meaning the `.opb` and the `.scp` it came from;
- the proof so far, including every derived line the trimmed proof keeps;
- the assertion's clause and its hint;
- any definitions the reconstructor introduces itself: extension variables,
  reified bounds, flags.

The question is whether a **sufficient** derivation of the asserted clause can
be built from that context. Any sufficient derivation will do. The solver's own
derivation is one sufficient derivation, and a reconstructor does not have to
reproduce it.

| Verdict | Meaning |
|---|---|
| `offline` | the assertion and the baseline context lead directly to a sufficient derivation; the procedure is fixed by the rule and needs nothing chosen |
| `hinted` | as `offline`, once the hint payload is read: the hint names the row, or carries a witness, that makes the procedure direct |
| `search` | a sufficient derivation exists in the baseline context, but nothing in the assertion or hint points at it, so the reconstructor has to search: which model row licenses an unattributed clause, or which combination of rows eliminates to the conclusion. **Name the search, its cost and its assumptions.** A hint would turn it into `hinted`; whether that is worth carrying is an engineering question, not an information one |
| `solver-side` | a sufficient derivation needs information that is **not in the baseline context at all**. **Name the information, and argue that it is needed** |

**Failing to recover what the solver chose is not, by itself, `solver-side`.**
The exact Hall set, the order a DP visited its states, which of several
equally valid explanation subsets was taken, which rows a presolver gathered:
if the baseline context supports a different sufficient derivation, the rule is
`search` (or better). Say what that derivation is. A rule is `solver-side` only
when no derivation from the context will do; the argument for that is part of
the entry. A derivation that exists but is expensive to find, even one whose
only known route is to re-run the solver's own search, is `search`, with that
cost named. Hard-to-find is `search`; impossible-without-help is `solver-side`.

The `solver-side` rules are exactly the list of things the external tool cannot
rebuild, and therefore exactly what a hints-only GCS mode has to carry. The
`search` rules are the list of places where a hint would save work, and are
candidates for one on cost grounds, to be settled against the justifier as it
develops. Getting this field wrong is more expensive than leaving it blank.

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
template with the propagation sections deleted. A presolver's own pass runs
once, before search, and infers nothing during it. The differences:

**Dropped, conditionally.** Propagator inventory, mutable state and
incrementality, idempotence, consistency level, and interior values and
optional pruning — **for the presolver's own pass**, which has none of them.
They are not dropped for what the pass **installs**. Every presolver in the tree
today installs runtime machinery directly, as a propagator under
`CurrentlyUnnamedConstraint` rather than as a posted constraint, and two of them
can also disable their donors' propagators:

| Presolver | Installs | Can disable donors | Runtime machinery documented in |
|---|---|---|---|
| `auto_table` | an extensional propagator (`propagate_extensional`) over a table it builds | no | `table.md` |
| `cumulative_strengthening` | a derived cumulative (`install_derived_cumulative`) | no | `cumulative.md` |
| `difference_logic` | a difference-graph propagator (`install_difference_propagator`) | yes | `difference.md` |
| `inferred_cumulative` | a derived cumulative | no | `cumulative.md` |
| `inferred_disjunctive` | a derived cumulative | no | `cumulative.md` |
| `parity_system_gathering` | a GF(2) system propagator (`install_parity_system_propagator`) | yes | `parity.md` |

So a presolver document either covers that machinery — its proof rules, its
state, its idempotence and its hole sensitivity — or links to the family
document that does and says so. Where neither happens, the machinery falls
between the rewrite catalogue and the family catalogue and nobody documents it.
Hole sensitivity matters here because presolvers run **before** the choice
is made: `gcs::solve_with()` calls `choose_optional_interior_pruning()` after
the last presolver, precisely so that what a presolver installs is counted.
What the installed propagators observe is therefore part of what a presolver
contributes to someone else's choice.

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
interval efficiency, tests, benchmarks, both performance sections, gaps, next
steps, prior art — carries over unchanged. **Interval efficiency** carries over
because a donor scan is exactly the shape that walks values without looking
like a propagator: it runs once, over the whole model, and a scan proportional
to a domain's width is the same hazard wherever it sits.

---

# Provisional family list

The work plan, and the definition of "family". Provisional: the groupings
marked *candidate merge* should be settled as the documents get written, and
this table moves to `dev_docs/constraints/README.md` once it is stable.

| Document | Covers | Notes |
|---|---|---|
| `all_different.md` | `all_different/` | **written**. GAC, BC and VC arms, `AllDifferentExcept`, `ExceptZero`, and `SymmetricAllDifferent`, which lives here and shares the encoding and the GAC propagator |
| `all_equal.md` | `all_equal/` | |
| `arithmetic.md` | `multiply/`, `divide_modulus/`, `plus_minus/`, `power/`, and the `plus.hh` / `minus.hh` / `divide.hh` / `modulus.hh` headers | one family over several directories; existing note is `arithmetic-proofs.md` |
| `abs.md` | `abs/` | **written**. The candidate merge into `arithmetic`, settled: separate. The view-proof gap that first kept it apart has closed; it shares no code or encoding with the product family |
| `at_most_one.md` | `at_most_one/` | |
| `bin_packing.md` | `bin_packing/` | existing note `bin-packing.md` |
| `circuit.md` | `circuit/` | includes subcircuit |
| `counting.md` | `count/`, `among/`, `global_cardinality/`, `n_value/` | **written**. The candidate merge, settled: four classes (`Count`, `Among`, `NValue`, `GlobalCardinality` at `BC` and `GAC`), no shared propagation code and four encodings, so one document and no code merge |
| `comparison.md` | `comparison/` | **written**. Twelve classes over `ReifiedCompareLessThanOrMaybeEqual`; **not** merged with `equals` — same reified-dispatcher pattern, no shared code, separate encodings |
| `equals.md` | `equals/` | **written** — the pilot. `Equals`, `NotEquals` and the four reified forms |
| `cumulative.md` | `cumulative/` | the largest family, including the derived cumulative (`derived_cumulative.hh`) that three presolvers install; notes `cumulative-proof-logging.md`, `certified-makespan-bounds.md`, `rule-counters.md` |
| `difference.md` | `difference/` | difference constraints; note `difference-logic.md`, whose presolver half belongs under `dev_docs/presolvers/` |
| `dag.md` | `dag/` | `Dag`; shares `connectivity-proofs.md` with `reachable` |
| `disjunctive.md` | `disjunctive/`, `disjunctive_2d/` | one family, two dimensions; note `disjunctive-proof-logging.md` |
| `element.md` | `element/` | **written**. `Element`, `Element2D` |
| `in.md` | `in/` | note `range_literals_spec.md` |
| `increasing.md` | `increasing/` | `Increasing`, `Decreasing` |
| `inverse.md` | `inverse/` | **written**. One class; its propagator runs `all_different`'s generalised arc consistent algorithm on one array, and is documented there as well |
| `knapsack.md` | `knapsack/` | existing note `knapsack.md`; `decision-diagram-proof-strategies.md` |
| `lex.md` | `lex/`, `lex_smart_table.hh` | |
| `linear.md` | `linear/` | **written**. Note `linear-slack-waking.md` is cross-referenced and due to be folded in; `subset-sum-strengthening.md` is not this family's (an `innards/proofs` helper for `knapsack` and `cumulative`) |
| `logical.md` | `logical/` | |
| `mdd.md` | `mdd/` | `decision-diagram-proof-strategies.md` |
| `min_distance.md` | `min_distance/` | note `min-distance-proofs.md` |
| `min_max.md` | `min_max/` | |
| `nogoods.md` | `nogoods/` | search machinery rather than a posted constraint; notes `restarts-nogoods-weighting.md`, `refined-triggers.md` |
| `parity.md` | `parity/` | `ParityOdd`, and the GF(2) system propagator in `gf2_system.{hh,cc}` that the `parity_system_gathering` presolver installs; note `parity-system.md` |
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
`inferred_disjunctive`, `parity_system_gathering`. Existing notes:
`cumulative-strengthening.md`, `inferred-cumulative.md`,
`inferred-disjunctive.md`, the presolver half of `difference-logic.md`, and the
gathering half of `parity-system.md`. What each one installs, and which family
document owns that machinery, is the table under [The presolver
variant](#the-presolver-variant).
