# Range ("in") literals: implementation specification

**Theory.** The definitions, invariants and completeness proofs for this layer
now live in [literal-encodings.tex](literal-encodings.tex), a revised version of
§3.2 and §3.3 of Matthew's thesis covering interval literals and views. Read
that first, or [literals.md](literals.md) for the index. **This document is what
was built, in what order, and what to be careful of** — the API propagator
authors see, the witness suite as checked in, the status log, and the edge-case
inventory.

**Status.** This spec supersedes the design narrative that lived in
`dev_docs/range_literals.md` and `dev_docs/range_literals_theory.md` on the
`range-literals` branch (PR #281). That branch is retained, unmerged, as the
archaeological record; its conclusions that survive are restated here or in
`literal-encodings.tex`, and its conclusions that were wrong are listed, each
with the witness that catches it, in that document's Appendix C.

**Audience.** Someone implementing or reviewing the interval-literal layer of
the proof encoding.

---

## 1. Two ways a proof goes wrong — read this first

*Stated in full in the "Interlude" of
[literal-encodings](literal-encodings.tex).* The one-line version, which every
section below assumes:

> **A RUP check is strictly stronger than the single UP pass later checks rely
> on, so every P2 clause looks deletable under P1 testing.**

P1 is "a line we emit is rejected" — loud and local. P2 is "every line checks,
but unit propagation is no longer strong enough for a backtrack clause three
thousand lines later" — and the rejection lands nowhere near the cause. The only
evidence that a P2 clause is unnecessary is passing the witness suite of §8.

## 2. The objects

*Their PB definitions are §3.3.1 of
[literal-encodings](literal-encodings.tex).* This table is the mapping from
the code's names, which that document does not use:

| code | document | definition |
|---|---|---|
| gevar | order atom `x>=v` | reified on the bit sum; chained (`Inv-Chain`) |
| eqvar | equality atom `x=v` | `<=> (x>=v & ~x>=v+1)` |
| invar | interval literal `[x in a..b]` | `<=> (x>=a & ~x>=b+1)`, `a < b` |

`need_invar(v, v)` returns the eq atom itself, never a separate flag
(Definition 3.2 there; witness W1).

## 3. The invariant: always-covered partitions

*The invariants are `Inv-Part`, `Inv-Cover` and `Inv-Cont` of §3.3.1 of
[literal-encodings](literal-encodings.tex); [literals.md](literals.md) maps each
to the function that maintains it.* Two implementation facts that live here and
nowhere else:

- Everything is emitted at `ProofLevel::Top`. There is no search-state
  bookkeeping and nothing to undo on backtrack, which is what makes the
  invariant maintainable at definition time.
- Lazy throughout: nothing is defined for a variable until its first interval
  request, exactly as gevars are lazy today.

## 4. One vocabulary, end to end

Every solver-visible interval fact is expressed over these literals, by the
encoding layer, never by propagator authors:

- **Conclusions.** `infer_not_in_range(var, lo, hi)` defines `[lo,hi]` (with
  splits as needed) and emits the single conclusion `reason → ¬[lo,hi]`.
- **Reasons.** A reason says "var ∉ [lo,hi]" as the *first-class element*
  `¬[lo,hi]` (defined the same way). There is **no per-value reason loop and
  no after-the-fact coalescing pass**: the Stage-2 coalescer
  (`coalesce_holes_in_reason`, `GCS_RANGE_REASONS`) is deleted, not ported.
  It introduced flags that nothing could falsify (refuted designs 4 and 5 in
  Appendix C of `literal-encodings.tex`); under this
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

*Second consumer (2026-09, #867):* `ReifiedEquals`' no-overlap rule is the
first propagator to take the "construct it explicitly" route, and it is worth
recording what that looked like, because it was not just a spelling change.
Saying "these two domains are disjoint" per value costs one literal and one
lemma per value; saying it over runs needs a *walk* — an invariant (`v1 >= p`)
carried up the number line, one move per run, each move either a hole of v1
(free: the range literal's own reverse reification steps `p` over it) or a run
where v2 is empty (two bound-crossing lemmas, the reified analogue of
`justify_not_in_range_across_equality`). The witness and the reason come out of
the *same* walk, in the same order, because the lemmas exist precisely to let
unit propagation see that reason's literals through; writing them as two
independent functions is how they drift. A run whose variable is a view is
spelled per value, per §9.1 — one run, not the whole rule, and the witness does
not notice, because stepping over a run is internal to that variable either way.

## 5. Why this is complete

*Resolved and moved.* The lemma obligations this section used to record as L1
and L2 are proved as Theorems 3.3 / 3.3' and Theorem 3.5 of
[literal-encodings](literal-encodings.tex). Two of its results bear on this code
directly: wipeout detection does **not** need the coverings (Remark 3.2 — the
root covering is UP-redundant, and we keep it anyway), and the coverings and
containment edges exist for reason validity (Lemma 3.4).

## 6. Cost model

*Measured numbers, including what a view adds, are the "Cost" part of
[literal-encodings](literal-encodings.tex).* The rule to hold on to: **nothing
is O(domain width)** — that was the point of interval literals, and the first
implementation lost it twice, by materialising per-value eq atoms through reason
naming and through `In`'s per-value root pruning.

## 7. What this branch already contains (kept from PR #281)

Sound under this spec, and either already correct or a strict subset of §3:

- `need_invar` reification + idempotence; Inv1 chain threading (`need_gevar`).
- Laminar containment edges, immediate-parent/child (Phase A/B) — `Inv-Cont`.
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
  (Abs) is *outside* Theorem 2.9's hypotheses rather than a mirrored instance of
  it, and uses `pol` instead — see the Theorem 2.9 section of
  [large-domains.md](large-domains.md).
- The gated consumer in `enforce_equality` (`GCS_RANGE_INFERENCES`, default
  off) with the width-1 guard.

To be implemented fresh: partition + splits + coverings + root covering in
`need_invar` (the partition, the coverings and the root covering),
`need_invar(v,v)` returning the eq atom, first-class
interval reason elements (§4), retiring the env gates once §8 is in place.

*Status (2026-06-11, revised same day): all of the above implemented.
`need_invar` returns `ProofLiteral` (the eq atom for width 1) and
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

*What each witness guards, its shape, and the W6–W9 ablation matrix are the
"Interlude" of [literal-encodings](literal-encodings.tex). This section is the
operational record: which test, gated how, validated how.*

| | test | gate |
|---|---|---|
| W1 | `range_witness_w1_test.cc` | gate-on, veripb-verified |
| W2 | `range_witness_w2_test.cc` | gate-on, veripb-verified |
| W3 | `range_witness_w3_test.cc` | gate-on, veripb-verified |
| W4 | `range_branch_test.cc`, plus the suite-wide `reject_random_interval` branching | always on |
| W5 | `range_witness_w5_test.cc` | gate-on, veripb-verified |
| W6–W9 | `range_witness_w{6,7,8,9}_test.cc` | gate-on, veripb-verified |

They are all tiny — 2–3 variables, 2–3 bits, one scripted decision pair — and
each was found the expensive way. Registration is in `gcs/CMakeLists.txt`, which
points back at this section. Any change to the clause set MUST run them all.

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
- **Observation, not a proposal**: the root covering (`Inv-Cover`(iii)) appears
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

1. **Views and constants.** *Resolved (2026-09, issue #882); see
   `dev_docs/view-range-literals.md`, which supersedes this entry.* A registered
   view owns its range literals over its own bit vector, exactly as it already
   owned its eq and order atoms, and every interval request is mirrored onto the
   underlying variable and joined to it by a pair of rup clauses. Deviewing the
   interval onto the underlying variable — the option this entry proposed — was
   rejected: it would leave ranges as the one atom kind not in `V`-form, which
   breaks the pol-cancellation invariant the view design rests on. The deview
   arm still handles the *unregistered* view path, which has no encoded variable
   to be consistent with. Constants fold to `TrueLiteral` / `FalseLiteral` and
   never reach the literal layer. The remaining per-value fallback is for
   variables with no bits encoding, which is a property of the variable and not
   of views.

   *Priced (2026-09, #882):* eight sites now carry a view detour — three that
   throw and five that degrade, two of those being the same code written twice
   — and since the interval vocabulary became the ordinary one, the gap between
   them is a domain width rather than a constant. #882 has the inventory, and
   the two candidate designs: deview onto the underlying variable, or define
   range literals over a registered view's own bits and let the *cuts* cross
   the view's defining equality. The second is a live possibility because a
   range literal never crosses an equality — only its two order cuts do, one
   bound at a time (#867/#881) — but that is a hand UP analysis, so it is a
   reason to test it, not to adopt it (§1).
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

## Appendix — where the theory went

The P1/P2 glossary, the refuted-design list and the change protocol that used to
live here are all in [literal-encodings](literal-encodings.tex): the
"Interlude" and its Appendix C. That version also carries the two refutations
issue #882 produced, and the witness that catches each.
