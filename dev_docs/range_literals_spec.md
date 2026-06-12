# Range ("in") literals: reimplementation design specification

**Status.** This spec supersedes the design narrative that lived in
`dev_docs/range_literals.md` and `dev_docs/range_literals_theory.md` on the
`range-literals` branch (PR #281). That branch is retained, unmerged, as the
archaeological record; its conclusions that survive are restated here, and its
conclusions that were wrong are listed in Appendix B with the test that
catches each. This branch (`range-literal-foundation`) carries the parts of
that work that the new design keeps unchanged; everything else is to be
implemented fresh, against this spec.

**Audience.** Someone implementing or reviewing the interval-literal layer of
the proof encoding. Familiarity with the McIlree thesis machinery (BinEnc,
order atoms `x≥v`, eq atoms `x=v`, Inv1/Inv2/Inv3, Theorems 2.7–2.9, 3.2–3.4)
is assumed.

---

## 1. Two ways a proof goes wrong — read this first

Throughout, "UP" means plain unit propagation from the empty assignment,
with no case-splitting: the propagation a RUP check performs after asserting
the negation of the line being checked. Everything that went wrong in the
first implementation attempt, three separate times, came from conflating two
failure modes that look identical on small tests:

- **P1.** A line we emit is not itself accepted by VeriPB. These failures
  are loud, immediate, and local: veripb rejects at the line, and the error
  points at the culprit.

- **P2.** Every line checks individually, but the clause set does not keep
  UP strong enough for **later** RUP checks — backtrack clauses, other
  constraints' inferences — to re-derive the solver facts they depend on.
  The root cause of the eventual proof failure is then nowhere near the line
  VeriPB takes issue with: the rejection lands on an unrelated later line
  (typically a backtrack clause), only under composition, only for
  particular search shapes, and the missing clause is the real culprit.

The trap: **a RUP check is strictly stronger than the single UP pass later
checks rely on, so every P2 clause looks deletable under P1 testing.** Any
linking clause can be removed and a local test stays green, because RUP
re-finds the derivation that UP would have needed the clause for. "This
clause was never load-bearing in my tests" is *always* observable for P2
clauses on small tests. It is not evidence. The only evidence that a P2
clause is unnecessary is passing the witness suite of §8, which was built so
that each clause family's removal fails within milliseconds.

Each clause family below is labelled with the failure mode it guards
against.

## 2. The objects

For a plain integer variable X (views and constants: see §9.1):

| object | meaning | definition |
|---|---|---|
| bits | BinEnc(X) | core OPB |
| `x≥v` (gevar) | order atom | reified on the bit sum; chained (Inv1) |
| `x=v` (eqvar) | direct atom | `⇔ (x≥v ∧ ¬x≥v+1)` |
| `[x in a..b]` (invar) | interval literal | `⇔ (x≥a ∧ ¬x≥b+1)`, `a < b` |

An interval literal is a *wide equality atom*: same shape of definition, two
cuts. **A width-1 interval IS the eq atom**: `need_invar(v, v)` must return
the eq atom itself, never a separate flag. A separate width-1 flag is an
unlinked doppelgänger of the eq atom (same boundary cuts, different Boolean,
nothing connects them) and is the subject of witness W1.

## 3. The invariant: always-covered partitions

The interval literals on each variable are maintained so that, at all times:

1. **Partition.** The minimal ("leaf cell") literals partition the variable's
   initial bound range. Cells are intervals; width-1 cells are eq atoms.
2. **Every requested interval is a union of adjacent cells.** A request whose
   endpoint falls strictly inside an existing cell *splits* that cell first
   (≤ 2 splits per request, one per endpoint).
3. **Covering (P2).** Every non-leaf literal carries one clause
   `F → C₁ ∨ … ∨ Cₖ` over a partition of itself into existing literals,
   emitted once when F is defined (or when F is split, for the two halves).
   Coverings compose through UP across refinements — to falsify a node,
   falsify its pieces, recursively — so a covering is never revisited or
   re-emitted after later splits.
4. **Root covering (P2).** Each variable with any interval literal carries
   one clause `C₁ ∨ … ∨ Cₖ ≥ 1` over its top-level partition (RUP from the
   lb/ub axioms). This is the flag-level analogue of the direct encoding's
   at-least-one clause, and gives wipeout detection (Theorem 3.2 analogue)
   without descending to the bits.

   *Decided (2026-06-11 review):* conceptually this is the covering of the
   whole-variable literal `[x in lb..ub]`, so the covering rule is uniform
   with no special root case — but that literal is **never materialised**.
   The clause over the top-level partition is emitted directly: it has the
   same propagation power given the root bound units, positively asserts the
   last surviving piece without a detour through a root reification (which is
   what feeds Theorem 2.8 value-crossing), and avoids introducing a literal
   nothing else references.
5. **Containment (P2).** Child → parent edges (`¬C ∨ F` for C immediately
   inside F), as in the current implementation. Needed so a *rejected*
   literal (`¬F` as a branching decision or derived fact) pushes down to the
   atoms a conflict is written over. Note requests may overlap (e.g.
   `[7,15]` after `[5,10]`): the family is a DAG, not a tree; cells remain a
   partition; multiple incomparable parents are fine (this already works).
6. **Reification (P1+P2).** The usual red pair per literal. The reverse
   direction `(F ∨ ¬x≥a ∨ x≥b+1)` is what lets a bound walk past a dead
   interval (hole-jump) and is also what falsifies F when a bound crosses it
   — bound-truncation needs no special clauses given (3).

All of these are **state-independent tautologies of the encoding, emitted at
`ProofLevel::Top`**. There is no search-state bookkeeping, nothing to undo on
backtrack, and emission order does not matter for soundness (each clause is
RUP at emission given the reifications and the chain). This is what makes the
invariant maintainable at definition time: the alternative ("emit a covering over
whatever facts currently witness the exclusion") is also sound but drags
search state into the tracker; it was considered and rejected — see
Appendix B7.

Lazy throughout: nothing is defined for a variable until the first interval
request, exactly as gevars are lazy today.

### 3.1 Worked example

X in 1..20. First request `[5,10]` (from any source — conclusion, reason, or
branch guess): define `[1,4]`, `[5,10]`, `[11,20]` (cells), the root covering
`[1,4] ∨ [5,10] ∨ [11,20]`, reifications, no containment yet (no nesting).
Next request `[7,15]`: split `[5,10]` into `[5,6]`,`[7,10]` (covering
`[5,10] → [5,6] ∨ [7,10]`), split `[11,20]` into `[11,15]`,`[16,20]`
(covering), define `[7,15]` with covering `[7,15] → [7,10] ∨ [11,15]` and
containment `[7,10] → [7,15]`, `[11,15] → [7,15]`. The root covering is not
touched: to falsify `[5,10]` later, UP goes through its own covering.

## 4. One vocabulary, end to end

Every solver-visible interval fact is expressed over these literals, by the
encoding layer, never by propagator authors:

- **Conclusions.** `infer_not_in_range(var, lo, hi)` defines `[lo,hi]` (with
  splits as needed) and emits the single conclusion `reason → ¬[lo,hi]`.
- **Reasons.** A reason says "var ∉ [lo,hi]" as the *first-class element*
  `¬[lo,hi]` (defined the same way). There is **no per-value reason loop and
  no after-the-fact coalescing pass**: the Stage-2 coalescer
  (`coalesce_holes_in_reason`, `GCS_RANGE_REASONS`) is deleted, not ported.
  It introduced flags that nothing could falsify (Appendix B4/B5); under this
  spec the covering makes any defined literal falsifiable, and the reason
  never materialises per-value eq atoms.
- **Branching.** Range guesses are ordinary range conditions, mapping to the
  same literals.
- **Per-value consumers** (Table-style reasons saying `x ≠ v`) keep working
  untouched: eq atoms are cells (or get created and linked into the partition
  as singleton splits), so `¬F` reaches them by containment and they reach
  `¬F` through coverings.

Propagator authors see exactly two things: `infer_not_in_range` and interval
reason elements. Everything in §3 happens inside `need_invar`.

*Decided (2026-06-12, Ciaran):* a reason a propagator constructs is never
rewritten — only `generic_reason`, which derives a reason from the current
domains rather than receiving one, chooses the interval spelling for hole
runs, because the representation of "the domains, as a reason" belongs to
it. Revisit only if a propagator's explicit scaffolding turns out to need
the per-value spelling (it can always construct its reason explicitly), or
if the small-interval overhead grows beyond the noise it currently is.

## 5. Why this is believed complete (and what still needs proving)

Intra-variable falsification induction: if interval F is truly excluded by
the facts UP has, then every piece of F's covering is excluded, each either
by a **bound** (its reverse reification fires via the chain), by a **derived
or asserted ¬ancestor** (containment pushes down; order-independent because
edges are emitted whenever either endpoint is created), or **recursively** by
its own covering — grounding out at cells, whose exclusions are exactly the
logged conclusions. Positive directions (assert F → bounds; sandwiched bounds
→ F; F ∧ ¬child → sibling) come from reification + chain + covering.

Cross-variable, nothing new is needed: reasons and conclusions are
single-literal interval facts; values cross bit-sum equalities by Theorem 2.8,
contradictions by 2.7/2.9, and the *backtracking* obligation (Inv2) reduces to
leaf-conflict replays (a parent backtrack clause is RUP from its two child
clauses), where the path's own inference clauses are live and fire over the
vocabulary above. **A lone bound still cannot cross a bit-sum equality — the
thesis Example 2.14 limit is real — but no replay obligation requires it once
the vocabulary is complete.** The 2026-06 experiments that seemed to show
otherwise were P2 gaps in disguise (Appendix B).

**Lemma obligations (to be formalised, not assumed):**

- **L1 (intra-variable).** With §3 maintained, the {gevar, eqvar, invar}
  layer is UP-complete with respect to the variable's possible
  values: every implied literal propagates, and an empty domain propagates to
  contradiction. (Induction over the partition DAG; extends Theorem 3.3.)
- **L2 (Inv2 restoration).** With L1, reasons/conclusions in interval
  vocabulary, and eager per-inference logging, every backtrack clause is RUP
  (leaf-replay induction over trail order + parent-from-children).

Empirical support, for calibration only (it is not a proof): 3,204,000
randomized instances with interval inference enabled and zero veripb
failures, once the only-then-known P2 gap (width-1) was closed; every
remaining failure class reproduced and then eliminated by exactly the clauses
this spec mandates, validated by hand-elaborating the failing proofs.

## 6. Cost model

Per distinct requested interval: ≤ 2 cell splits (≤ 4 new literals, of which
width-1 pieces are eq atoms) + the requested literal; 2 red lines per literal,
binary coverings per split, one covering for the request (width = number of
pieces it spans), O(immediate neighbours) containment edges. **Nothing is
O(domain width)** — that was the point of interval literals, and the first
implementation lost it twice by materialising per-value eq atoms through
reason naming and through `In`'s per-value root pruning.

Known growth mode: a wide request over a heavily fragmented region gets a
covering as wide as the number of prior boundaries inside it (bounded by
request count, not domain size). Acceptable; measure, don't pre-optimise.
Flag reuse is high in practice (measured ~40× per flag under interval
branching), so per-literal fixed costs amortise.

## 7. What this branch already contains (kept from PR #281)

Sound under this spec, and either already correct or a strict subset of §3:

- `need_invar` reification + idempotence; Inv1 chain threading (`need_gevar`).
- Laminar containment edges, immediate-parent/child (Phase A/B) — §3.5.
- The `BranchGuess` guess channel, `reject_random_interval` (width-1 → eq
  atom), backtrack clauses over range guesses; suite-default interval-reject
  branching as a standing regression net.
- `IntervalSet::erase_range`; `State::infer_not_in_range` /
  `change_state_for_not_in_range`; `InferenceTracker::infer_not_in_range`;
  `ProofLogger::infer_not_in_range` (single-line conclusion, simple vars).
- `justify_not_in_range_across_equality` — the Theorem-2.9 bound-lemma bridge
  for interval pruning across a bit-sum equality (P1 machinery; correct and
  validated). *Re-factored per the 2026-06-11 review (Matthew)* from
  flag-conditioned lemmas to pure ge-layer lemmas:

      pruned >= lo          ->  other >= other_lo
      other >= other_hi + 1 ->  pruned >= hi + 1

  Each is RUP via the opposing-bounds (2.9) configuration. The lemmas mention
  no flag, so they are reusable by any literal sharing those endpoints, and
  they make explicit that the bridge *is* the cross-variable Inv1 link at
  exactly the boundary values in play, materialised locally per inference —
  the corrected form of what the superseded analysis believed had to be a
  per-equality global covering. Caveat: this pairing is orientation-sensitive
  (same-sign links only, which is all current callers); a sign-flipped link
  (Abs) needs the mirrored pairing — see the header comment.
- The gated consumer in `enforce_equality` (`GCS_RANGE_INFERENCES`, default
  off) with the width-1 guard.

To be implemented fresh: partition + splits + coverings + root covering in
`need_invar` (§3.1–3.4), `need_invar(v,v)` returning the eq atom, first-class
interval reason elements (§4), retiring the env gates once §8 is in place.

*Status (2026-06-11, revised same day): all of the above implemented.
`need_invar` returns `ProofLiteralOrFlag` (the eq atom for width 1) and
maintains §3 in full; `need_direct_encoding_for` performs the singleton
splits; `In` over constants batches initial-domain gaps (§9.3);
`GCS_RANGE_INFERENCES` is retired and the Equals holes path is interval-based
unconditionally for simple variables.*

*The interval vocabulary is carried by ordinary variable conditions, not a
separate reason-element type: `VariableConditionOperator` gained `InRange` /
`NotInRange` (closed interval `[value, upper_value]`), constructed via
`in_range()` / `not_in_range()`, which canonicalise width-1 to the equality at
construction. A range condition's proof name IS the range literal — an
xliteral allocated and registered exactly like the eq and order atoms — so
conditions resolve in the same `need_all_proof_names_in` / `xliteral_for`
pipeline, and there is no separate resolution pass to forget (the §9.2
worry, structurally dissolved). `generic_reason` states hole runs as range
conditions; branching yields them as plain `IntegerVariableCondition`
guesses; conclusions are range conditions through the ordinary
`InferenceTracker::infer` path.*

*Revised after review (2026-06-12): requests are NOT clamped to the
definition bounds. A literal whose cuts stick out of the definition range is
defined over its own cuts, and the bound-axiom units falsify the
out-of-bounds part through the reification and the order chain; the
partition still spans only the definition range, so a partially-outside
literal's covering is over the cells of its in-bounds intersection, and an
entirely-outside literal needs no covering at all. Containment neighbours
are found through a per-variable interval tree over all range and eq
literals rather than by scanning them.*

## 8. The witness suite — the actual defence against re-simplification

Each clause family has a deterministic counterexample that fails veripb
within milliseconds if that family is removed or weakened. These MUST be
checked in as gate-on, veripb-verified tests alongside the reimplementation,
and any change to the clause set MUST run them. They are all tiny (2–3
variables, 2–3 bits, one scripted decision pair) and were each found the
expensive way.

- **W1 — width-1 unification** (else: first backtrack clause not RUP).
  `a∈{0,2,3}, b∈{0,1,3}, c∈{0,1,2,3}`; `Equals(a,b)`, `Equals(b,c)`,
  `NotEquals(a,c)`; branch `c≠0` then `c=0`. If width-1 removals make flags
  instead of using eq atoms, the replay stalls in 6 steps: "b lost 1" is
  locked inside `¬f[in_b_1_1]` with no link to `b=1`.
- **W2 — reason falsifiability, exact match** (else: first backtrack clause
  not RUP). `a∈0..4, b∈{0,4}`; `Equals(a,b)`, `NotEquals(a,b)`; branch
  `a≠0` then `a=0`. Two variables suffice: the reason names `¬[b in 1..3]`,
  and if that literal cannot be falsified by UP (no covering, hole concluded
  in a different vocabulary), the replay stalls in 5 steps. Kills the
  "two-variable isolation is safe" heuristic as well: safety claims made on
  one vocabulary mode do not transfer.
- **W3 — union coverage** (else: first backtrack clause not RUP).
  `a∈{0,1,2,3,7}, b∈{0,4,5,6,7}, c∈0..7`; `Equals(a,b)`, `Equals(b,c)`,
  `NotEquals(a,c)`; branch `c≠0` then `c=0`. b's combined hole [1,6] is
  concluded as [1,3] and [4,6] separately; the reason names `¬[b in 1..6]`.
  Containment points the wrong way; only the covering
  `[1,6] → [1,3] ∨ [4,6]` (one RUP line) lets the replay through. This is
  the partition invariant earning its keep: under §3, `[1,6]` is defined as a
  union of cells and gets that covering when defined.
- **W4 — containment** (else: backtrack clauses over interval-reject
  decisions not RUP). Regression net: the whole constraint suite runs under
  `reject_random_interval` by default and fails on Count/Among/Element
  within seconds if containment edges are dropped (this is how the need for
  them was discovered). Keep `range_branch_test` as the focused version.
- **W5 — root covering / wipeout** (to be written with the implementation):
  a variable whose cells are all excluded must reach contradiction by UP at
  the flag level.

### 8.1 Implementation notes (2026-06-11, first full implementation)

The suite is checked in as `range_witness_w{1,2,3,5}_test` (W4 = the existing
`range_branch_test` plus the suite-wide interval-reject branching), each
veripb-gated. Each was validated by temporary ablation knobs before the knobs
were removed:

- **W1 bites harder than predicted.** With width-1 flags defined instead of eq
  atoms, W1 fails *even with the coverings and containment intact* (the
  pre-implementation UP analysis predicted the covering `flag ↔ eq-atom` link
  would rescue it; it does not). A fresh confirmation of §1's warning that
  hand UP-analyses of P2 are unreliable in both directions.
- **W3 bites on two families**: removing either the request covering or the
  containment edges fails it within milliseconds.
- **W2 and W5 are currently structural**: no *single*-family ablation makes
  them fail. W2's failure mode needs per-value `In` conclusions *and* no
  covering simultaneously (under §3 the vocabulary always matches or grounds
  out); W5's wipeout is also derivable by the bound-axiom walk through
  reverse reifications and the order chain, independent of the root covering.
  They stay in the suite as composed end-to-end regression nets.
- **Observation, not a proposal**: the root covering (§3.4) appears
  UP-redundant given the bound-axiom units, the reverse reifications,
  and the Inv1 chain (the walk derives both wipeout and the positive "last
  surviving piece"). Per the change protocol this is recorded for review, not
  acted on — the W1 result above is exactly why such an analysis is not
  trusted as grounds for removal.
- **Known witness gap**: there is no deterministic witness yet for split
  coverings composing across refinements (a literal whose covering names a
  cell that is *later* split, with the cell's exclusion arriving only
  piecewise and no bound anchor). Constructing one needs a contrived
  propagation order; the W4 net covers the shape randomly. To be added if a
  natural trigger is found.

Testing doctrine learned at cost, for the suite around these: a capped or
gate-off green run certifies nothing about P2; two-variable instances
certify nothing about composition; `run_test_only.bash` registrations do not
invoke veripb; and "the suite passed" must always be qualified by which gates
and which branching were active.

## 9. Inventory of known edge cases (harvested from the first implementation)

1. **Views and constants** take the per-value fallback everywhere
   (`ProofLogger::infer_not_in_range` already branches; reasons likewise).
   Folding views in = deview the interval onto the underlying variable;
   deferred, do not block on it.
2. **Reasons are resolved at four sites** in `proof_logger.cc` (two `infer`
   paths, `emit_under_reason`, `reason_to_lits`). Any reason-vocabulary
   change must hit all four; missing one no-ops silently (cost a day, twice).
3. **`In` posts the initial domain**: `create_integer_variable(vector)`
   leaves State at the bound range and posts `In`, whose root propagation
   creates the holes. Under this spec its removals go through
   `infer_not_in_range` like everyone else's (this was the hidden per-value
   eq-atom factory the first time round).

   *Open decision (revisit alongside the CakePB OPB-conformance work):*
   whether initial-domain gaps may instead be stated as interval literals in
   the OPB itself (e.g. `~[b in 1..3] >= 1` as part of the domain
   definition). That formulation is equally definitional and slightly more
   direct, but requires model-phase `need_invar` support (currently throws)
   and changes the OPB encoding surface that the CakePB verified-encoding
   pipeline conforms against. Until that decision is made, gaps are
   root-derived in the proof as specified here, and the OPB encoding is
   unchanged.
4. **Proof-level discipline**: justification scaffolding (bridge lemmas) is
   `Temporary` and deleted immediately after the conclusion; conclusions are
   `Current` and live until their level is forgotten at backtrack; §3's
   linking is all `Top`. The backtrack clause is emitted *before*
   `forget_proof_level(depth+1)`, so the subtree's clauses are live for its
   own Bt check; sibling subtrees' are not — never rely on them.
5. **`Inference::NoChange` must mean no change** (existing project rule);
   `infer_not_in_range` on an already-absent range must not report progress.
6. **Duplicate/aliased operands**: `enforce_equality` with `v1 == v2` never
   reaches the holes path (equal domains), but keep the existing aliasing
   guards; do not add interval paths to reified variants without re-checking
   the dispatcher cases.
7. **clang-format** will reflow multi-line emission expressions; the
   codebase's `//` line-ending convention applies in cxxopts blocks only —
   write emission code so reformatting cannot reorder emission.

## Appendix A — glossary of the failure that motivated all of this

A backtrack clause `Bt = ¬d₁ ∨ … ∨ ¬dₖ` is checked by RUP: assert all
decisions, expect UP to re-reach the conflict. Every solver inference along
the path is logged as `reason → conclusion` and is live, so the replay
succeeds exactly when each reason's literals become UP-units in turn. The
moment any solver fact is held in a Boolean that UP cannot derive from the
others — a width-1 doppelgänger, an uncovered reason flag, a union literal —
the chain stops, veripb rejects Bt, and the trace (six lines long, in W1)
*looks like* "UP cannot thread a bound across the equality" because the
bound-crossing steps are the next thing the stalled trail would have needed.
That misdiagnosis cost two sessions and a theory document. The bound-crossing
limit is real (thesis Example 2.14); it just was never the binding
constraint.

## Appendix B — refuted designs and simplifications. Do not retry without new theory.

Each entry: the claim, why it looked right, what catches it now.

1. **"Reify to cuts + the order chain; no covering, no containment"**
   (Stage 0). Looked right: a falsification matrix of *derivations* all
   passed — P1 only. Caught by: W4 (containment), W2/W3/W5 (covering).
2. **"Containment yes, covering unnecessary — the chain gives those
   deductions"** (Phase A). True for RUP-derivability, false for UP.
   Caught by: W2, W3.
3. **"A range removal is one RUP line, per-value facts follow free"**
   (early Stage 3). False across bit-sum equalities; needs the 2.9 bridge
   lemmas (kept, in `justify_not_in_range_across_equality`). Caught by:
   `range_infer_test` with the bridge deleted.
4. **Coalescing per-value reasons into flags after the fact**
   (Stage 2, `GCS_RANGE_REASONS`). Mints literals that nothing concludes and
   nothing covers; un-falsifiable in replays; also materialises the eq atoms
   anyway via reason naming. Deleted. Caught by: W2, W3.
5. **Width-1 range flags** (Stage 3 consumer). Doppelgängers of eq atoms.
   Caught by: W1.
6. **"The composition failure is AllEqual-specific" / "2 vs ≥3 variables" /
   "UP can't thread a bound, so a global cross-variable covering
   `(x≥k)⇔(y≥k)` is required"** (the misdiagnosis era — pairwise OPB,
   durable Top lemmas, and star-funnel "fixes" all evaluated on
   width-1-contaminated populations). All artefacts of P2 gaps. W1–W3 are
   the corrected understanding; no cross-variable covering exists in this
   design and none is needed.
7. **Cover-on-use over the live witness set** (instead of the partition
   invariant). Sound, validated, but drags search state into the tracker
   (level-aware registry of live conclusions) and makes the completeness
   argument depend on what was live when. The partition invariant gets the
   same clauses as state-independent tautologies. Rejected for complexity,
   not soundness.

**Change protocol.** Any proposal to weaken or remove a clause family from §3
must (a) say which of W1–W5 it expects to remain green and why, (b) run the
full witness suite gate-on, and (c) account for the P1/P2 distinction
explicitly — a local green test is not evidence (§1). Three prior
simplifications passed every test their authors thought to run.
