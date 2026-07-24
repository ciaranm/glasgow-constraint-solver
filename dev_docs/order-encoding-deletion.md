# Order-encoding deletion via consolidate-then-delete branching

**Status: implemented behind a flag (`GCS_DELETE_ORDER_ENCODING=literals`),
measured on synthetic AND real instances; suite-safe; committed on this branch;
not default.** This note records the design for shrinking the integer
order-encoding that VeriPB carries, plus the measured outcome and what is and
isn't yet done. The full Brancher-API refactor (step 2, below) is now a
**decided design, recorded in [brancher-design.md](brancher-design.md)** but not
yet implemented; the current implementation wires deletion into the existing
branch/backtrack flow via hoisting, and the sketch of the refactor further down
this note is superseded by that decided design (see the note at "Design
overview").

## Results (measured)

Data home for everything below:
`/cluster/ciaran/claude/order-encoding-deletion-artifacts/real-instance-bench/`
(`campaign-report.md`, `results.tsv`, `scoping-report.md`). All numbers are from
the phase-2 campaign on the tuned node **fataepyc-10** (each timed run pinned to a
single physical core with `numactl`/`taskset`/`setarch -R`, turbo boost OFF,
governor `performance`, all timed proof I/O on tmpfs, `veripb` 3.0.2 verify time via
`hyperfine`, peak RSS via `/usr/bin/time -v`). Every measured row cleared the gate:
search statistics **IDENTICAL** OFF vs ON and both proofs VeriPB-**VERIFIED**.

> **Superseded.** The earlier hand-written table that used to sit here (domain
> 100…4000, "~+89 % larger", ~60× at d4000) came from a *pre-commit* iteration of
> the `order_deletion_bench` driver and is **not reproducible with the committed
> driver**: that driver's defaults and `--problem linear` root-refute in ≤3
> recursions and produce no search signal (scoping report §7). Those numbers are
> retired; use the campaign figures below.

### Synthetic win curve (committed driver)

Exact invocation, `--domain` and `--window` swept together:

    order_deletion_bench --problem pairwise --size 8 --domain D --window D \
        --tightness 90 --unsat

(`pairwise` is the only mode that searches deeply on this build; `--window D`
disables the per-variable windows, `--tightness 90` sits just inside UNSAT so the
tree must be searched.)

| D    | verify OFF | verify ON | speedup    | pbp growth |
|-----:|-----------:|----------:|-----------:|-----------:|
| 250  | 0.939 s    | 0.199 s   | **4.73×**  | +101 %     |
| 500  | 4.833 s    | 0.517 s   | **9.36×**  | +117 %     |
| 1000 | 27.415 s   | 1.528 s   | **17.94×** | +135 %     |
| 2000 | 194.76 s   | 5.692 s   | **34.22×** | +155 %     |

The speedup **grows monotonically with domain** (roughly doubling per domain
doubling). A depth point isolates search depth from domain: same domain 1000 but
`--tightness 95`, **72 341 recursions** (~30× deeper than the 2 397 at tightness 90),
gives **20.22×** — slightly *above* the tightness-90 d1000 point, so deeper search at
the same domain also wins; the effect is not merely a domain artefact.

ON proofs are **+101 %…+213 % larger** (the +213 % is the tightness-95 depth point)
yet verify far faster — the design's central claim confirmed: **resident chain
length, not proof line count, dominates VeriPB's cost.** The honest costs on the win
rows: solver-side proof-*writing* overhead is **+55 %…+140 %** (largest exactly where
the verify win is largest — a genuine trade, not free). Peak RSS is *smaller* for ON
on the modest-growth wins (−22 % d250, −20 % d500, −13 % d1000), directly confirming
the "resident DB is smaller" prediction; the sign **inverts once ON's proof grows
several-fold** (d2000 is the transition at +2 %; the tightness-95 row's 360 MB ON
proof vs 115 MB OFF pushes ON RSS well above OFF), because peak RSS = (proof veripb
must hold) + (resident order DB) and the proof-size term swamps the resident-DB
saving when growth is large.

### Real instances — the win did NOT generalise

On **no reachable real instance** did the synthetic win materialise.

- **seat-moving 2018** — the one deep-yet-verifiable real split case (15 610-node
  find-first, `indomain_split`, maxdom 901): **1.02× = neutral**. The del-count proxy
  explains it precisely: ON emits only **+0.55 %** more `del` lines (936 818 vs
  931 708) and the proof grows **+1.7 %** — deletion barely fires. Not because the
  model lacks long chains (it has maxdom-901 split variables) but because it is
  reif/element/view-heavy and its order encoding is **pinned resident by design**
  (viewed variables held by the always-at-Top view bridges, product/aux magnitudes by
  the product-justification caches — the "delete only when unreferenced" rule).

- **mrcpsp 2023** (eq scheduling, `indomain_max/min`): **1.00×**, del delta **exactly
  0** (1540→1540) — eq branching has no split frontier to advance, nothing is
  deletable. Clean no-op; the `tour` circuit example is likewise 1.00×.

- **Expected-bad, confirmed and bounded:** talent (eq enumeration) **0.98×**,
  +22.6 % proof; crystal_maze (eq enum) **0.92×**, +48.5 % proof (the worst *relative*
  growth, but tiny absolute times); sudoku_fixed (split but maxdom 16) **0.98×**, del
  delta 0. The downside is a low-single-digit-percent verify slowdown plus +20–50 %
  proof size on eq/small-domain models.

- **scp divide_sat control** (`--all`, 21 solutions): **0.97×**, +1.2 % — the
  divide/modulus in-proof aux magnitudes stay resident by design (product caches):
  correct, no win, no harm. A small-scale isolation of the same resident-by-design
  mechanism that makes seat-moving neutral.

- **Hunt for a tractable real win — none exists in the reachable set.** Screened
  radiation (2012/2013), on-call-rostering (2013/2018) and mspsp on top of the scoping
  set. Real challenge instances are either **shallow find-first**
  (static-encoding-dominated → neutral) or **intractably deep**: radiation *does*
  search deeply on proven optimality, but the smallest case (m06) blew past **3.98 GB
  of proof before completion**, far outside any verify budget. seat-moving stands as
  the lone deep-yet-verifiable real case, and it is neutral.

**Correctness gate (the whole point of a proof-only change):** all 12 measured rows
were search-**identical** OFF vs ON, both modes **VERIFIED** with identical
bounds/solution counts. No ON-only failure, no divergence anywhere.

### Pin apportionment (step 1b, measured) — the real reason the win does not generalise

The campaign's provisional read — that the view/product resident-by-design classes
block the real-instance win, motivating the bridge-lifetime redesign (step 3) — is
**overturned by measurement**. The `GCS_ORDER_ENCODING_STATS` diagnostic (below)
attributes every resident `ge` to the site that pinned it, first-cause-wins;
attribution is exact (recorded at the deciding call site, never inferred). Dumps in
`.../real-instance-bench/apportionment/`.

On **seat-moving** (the lone deep-yet-verifiable real case), of 4 617 proof-time ge
atoms, 4 442 end Top-resident:

- **view_pin + aux_pin (what step 3 would free): 0 — 0.0 %.** No view-underlying or
  aux-magnitude variable has *any* tracked ge. The same is true on mrcpsp and talent.
  (The attribution mechanism itself is validated: a view-wrapped comparison test shows
  view_pin up to 84.6 %, and scp divide_sat shows aux_pin > 0.)
- eq_hoist: 1 962 (44.2 %); structural (model_time 1 858 + boundary 622): 55.8 %.
- Churn: **22 857 deletions but 22 829 reintroductions — net 28**. Split branching
  constantly re-touches deleted thresholds; deletion does enormous work for zero net
  shrinkage. This churn *is* the +1.7 % proof and +5.6 % solver overhead.

And the deeper cause, measured directly from the proof (distinct `ge` thresholds
ever named, per variable): seat-moving's chains are **tiny** — median 12, p99 13,
max 98 (the objective), across 497 variables — despite maxdom 901. Strong
propagation means search never names more than ~a dozen thresholds per variable, so
**the long resident chains that dominate synthetic VeriPB cost never form on
propagation-strong real models at all**. Domain size is not chain length. No
deletion scheme of any kind — step 3, eq-unpinning, anything — can win where there
is nothing long to shorten; the win regime is characterised as *weak-propagation,
large-domain, bound-split search* (the synthetic driver's regime).

Consequences: **step 3 is deprioritised** (it frees 0 % on every real instance
measured; its win-recovery motivation is gone). A cheap, attractive follow-up
instead: a **chain-length gate** on deletion — only track/delete a variable's order
literals once its live chain exceeds some threshold (~tens) — which would eliminate
the real-model churn/overhead entirely (making the feature strictly-no-harm) while
preserving the full large-domain win, and might eventually justify default-on.

The diagnostic: set `GCS_ORDER_ENCODING_STATS` (any non-empty value) under
`GCS_DELETE_ORDER_ENCODING=literals`; a `%% oed-stats:` summary is printed to
stderr at proof end. Collection is gated on the mode + env var and emits no proof
bytes (verified byte-identical in all mode × env combinations).

### Baseline (non-feature) finding recorded in passing

mzn-challenge `2023/unit-commitment` is **REJECTED by veripb at `pbp:882`** ("not
implied by reverse unit propagation") — but in **both** OFF and ON modes
identically. It is a **pre-existing frontend/model proof-logging bug, out of this
feature's scope**, not a deletion regression, and was excluded from the campaign.
Repro kept at `real-instance-bench/fzn/2023_unit-commitment.fzn`; flag it to whoever
owns the MiniZinc frontend proofs.

## Implementation status

- **Done, suite-safe:** the full caps-off test suite passes with the flag on (0
  flag-induced VeriPB rejections; mode-off byte-identical; flag-off 525/525). The
  hoist primitive, guess/eq/partition-atom hoisting, and the aux/view dispositions
  below are all in `gcs/innards/proofs/{names_and_ids_tracker,proof_logger,proof_model}.*`.
- **Kept resident (not deletable), per the "delete only when unreferenced" rule,
  because their `ge`s are named by *permanent* Top constraints:**
  - divide/modulus in-proof-bit **aux-magnitude** variables (`register_state_variable_bits_in_proof`)
    — pinned by the product-justification caches;
  - **viewed** variables (underlying of a registered view) — pinned by the
    always-at-Top view-bridge `pol`s in `need_gevar`.
  These get no deletion win, but are correct. Making them deletable needs the
  bridge-lifetime redesign (Future work).
- **`soli` objective atom** is hoisted to Top when the objective-improvement
  constraint is emitted (latent optimisation-mode bug fixed defensively).
- **Not yet done:** the clean Brancher abstraction (below) — the current wiring
  hoists guess/eq/aux references directly; the abstraction generalises and tidies
  it. Also future: short-reason flag / deview-companion level-scoping (currently
  inert), and the bridge redesign.

## Next steps (prioritised)

**1. Real-instance benchmarking — DONE.** Completed as the phase-2 campaign (see
Results above; data under
`.../order-encoding-deletion-artifacts/real-instance-bench/`). Verdict:
- The **synthetic mechanism is validated**, **4.7×→34× across domain d250→d2000**
  (and 20× at the depth point), driven by resident-chain shrinkage — the design's
  central claim holds.
- The **real-instance win is unproven**: no reachable real instance triggered it. The
  one deep-yet-verifiable real case (seat-moving) is neutral because its chains are
  pinned resident by view/reif bridges, and the tractable-real-win hunt found nothing
  (real instances are either shallow-neutral or intractably deep).
- The **downside is bounded**: a few-percent verify slowdown and +20–50 % proof size
  on eq/small-domain models, +55–140 % solver-side proof-writing on the win rows.
- **Correctness is clean** (every row search-identical OFF vs ON, both VERIFIED).
- **Conclusion: keep the feature flag-gated; default-on is NOT justified by these
  numbers** (real win unproven, measurable overhead on eq/value-heavy models) — but
  the mechanism is sound and correctness is solid.
- Verification-only drivers `order_jump_check.cc` / `order_hoist_check.cc` and the raw
  hyperfine TSV are preserved (uncommitted) under the artifacts dir above; promote
  them to proper `gcs/` tests when convenient (they regression-check the two verified
  foundations).

**1b. Pin-apportionment instrumentation — DONE.** Implemented as the
`GCS_ORDER_ENCODING_STATS` diagnostic and measured (see "Pin apportionment" above).
The answer: **step 3 would free 0 % of the resident encoding on every real instance
measured**; the win is absent on real models because propagation-strong search never
builds long chains (seat-moving: median chain 12, max 98, despite maxdom 901), and
the deletion machinery churns (22 857 deletes / 22 829 reintroductions, net 28) for
nothing there.

**2. Brancher-API refactor — DESIGN DECIDED (see
[brancher-design.md](brancher-design.md)); not yet implemented.** The concrete,
decided step-2 design lives in that note; it generalises consolidate-then-delete,
tidies the current direct wiring, and is the natural home for the chain-gated
deletion policy, the objective-variable exemption (from 2b, below), and the
objective-improvement `delc` lifecycle. Five owner decisions are settled there:
the per-node object stays a `std::generator` (not a virtual class) until it shows
as a benchmark hotspot; the pre-0.1 public yield-type source break is accepted
(the implicit `IntegerVariableCondition → BranchDecision` conversion is the
bridge); the objective is handled by exemption for its ges *and* an unconditional
delete-all-but-the-most-recent improvement constraint; the value-order mapping is
final; and the eq-atom window ships default-off pending a stage-E measurement.

Crucially, the design adds an **eq-atom sliding window** (validated 8/8 in VeriPB
3.0.2) that moves the four contiguous in-order/eq value orders —
`smallest_first`, `largest_first`, `smallest_in`, `largest_in` — into the win
regime as *O(1)-resident* (evict each eq/ge once the frontier steps past it),
**superseding this note's earlier claim that only split wins**: split still wins
by the bound *jump*, but ascending/descending eq now wins too, by the window.

**2b. Chain-length-gated deletion — DONE (implemented + measured; default gate 16).**

Under `OrderEncodingDeletion::Literals`, a real variable's interior (non-boundary)
`ge` definition is only emitted deletable-at-`Current` once the variable has crossed
a chain-length gate: when the number of `ge` thresholds ever named for it (its
`gevars_that_exist[id]` count at decision time in `need_gevar` — model-time atoms
included) exceeds `min_chain`. At or below the gate the def stays resident at `Top`,
exactly like the boundary / view-pin / aux-pin paths. The gate is monotone (the
count only grows; once crossed, stays crossed; below-gate residents are never
revisited) — no flapping.

Parameter: `ProofOptions::order_encoding_deletion_min_chain` (+ fluent setter), env
override `GCS_DELETE_ORDER_ENCODING_MIN_CHAIN` (explicit-in-code wins). **`0` = gate
off = byte-identical to the pre-gate Literals behaviour — the aggressive-testing
mode: regression runs exercising the deletion machinery MUST set `MIN_CHAIN=0`,
because tiny test domains never cross a nonzero gate.** The suite passes caps-off
flag-ON at gate 0 and at 32 (525/525 each, 0 flag-induced failures). The stats dump
gains a `gate-held` cause and a per-variable chain-length distribution.

**Default 16, chosen from measurement** (full tables in
`.../real-instance-bench/chain-gate/gate-measurement.md`):

| min_chain | pairwise d250 | d1000 | crystal_maze proof/deletes | talent | seat-moving |
|--:|--:|--:|--|--|--|
| 0 | 4.70× | 17.87× | +48.5 % / 774 | +22.6 % | +1.7 % / 22.8 k |
| **16** | **2.97×** | **11.33×** | **+0.0 % / 0 (byte-identical to None)** | +5.8 % | +1.6 % / 20.8 k |
| 32 | 2.29× | 8.43× | +0.0 % / 0 | +1.6 % | +1.6 % / 20.7 k |
| 64 | 1.61× | 5.74× | +0.0 % / 0 | −0.0 % / 0 | +1.1 % / 13.1 k |
| 128 | 1.04× | 3.43× | — | — | — |

Search identical OFF vs ON at every gate; every proof VERIFIED. An infinite gate
reproduces the mode-None proof **byte-for-byte** (measured two anchors) — the
strongest strictly-no-harm form; crystal_maze reaches that already at gate 16 (its
longest chain is 16). The synthetic-win tables in Results above are the gate-off
(`MIN_CHAIN=0`) ceiling.

Two measured caveats, stated plainly:
- **Stitch explosion (proof-size only).** Under split branching the first ~L
  thresholds are named in binary-split order, so resident anchors are spread and
  fragment each deleted run into per-sub-run stitches (d1000 stitches triple at
  L=16; the proof is briefly *larger* than un-gated at L=16/32). Proof size is
  non-monotone in L; **verify time — the target — erodes cleanly**, so the gate is
  chosen from the verify curve, not size. See `chain-gate/stitch-explosion.md`.
- **A single long chain defeats the flat gate.** seat-moving's residual churn
  (~20.8 k delete/reintroduce at gate 16) is concentrated on its objective (chain
  98) and cost (76) variables, which any win-preserving gate leaves deletable. That
  churn is verify-neutral (OFF 305.9 s ≈ L16 298.3 s ≈ L64 299.4 s, all VERIFIED)
  and costs only +1.6 % proof / ~+5 % solve. Follow-up recorded for step 2: a
  **targeted objective-variable exemption** (never delete, or gate separately, the
  bound-tightened objective) would remove most remaining real-model churn at zero
  win cost — it belongs where the backtrack-constraint owner knows the bound
  frontier, not in the flat gate.

**3. Bridge-lifetime redesign — DEPRIORITISED.** Making viewed and divide/modulus
aux magnitudes deletable frees 0 % on every real instance measured (step 1b); its
win-recovery motivation is gone. Revisit only if a view/product-heavy
*weak-propagation large-domain bound-split* workload appears — the only regime where
freed chains would be long enough to matter.

**Ordering decided (2026-07): 2b first (done, above), then step 2.** Step 2 is the
next piece of work, and inherits the objective-variable-exemption follow-up from 2b;
3 stays parked.

**Also:** decide productionisation (keep flag-gated vs default-on — current verdict:
flag-gated), and — cleanup — the superseded dormant `Links` mode can be removed.

## The problem

Every integer variable is proof-encoded with order literals `ge(v)` ("x >= v"),
each defined by a reification against the variable's bits, plus **chain-link**
constraints `ge(v+1) -> ge(v)` between adjacent thresholds (see
[variable-encodings.md](variable-encodings.md)). Under the current (pre-this-work)
scheme all of this is emitted at `ProofLevel::Top` and kept for the entire search —
nothing is ever removed — so a large-domain variable accumulates a chain of every
threshold any subtree ever touched. Changing exactly that is the point of this note;
the rest of the document is about *when and how* the encoding can instead be deleted.

The chain links are 2-literal clauses, which VeriPB propagates first (2WL,
clausal priority) on every RUP check. Touching one end of a 1000-long chain makes
VeriPB chase the whole thing, and the bit<->order reifications fire more long
sequences. So the cost is **chain length**, and the lever is to **stop keeping the
entire order encoding of a large-domain variable resident when the proof is only
operating over a narrow range locally.** The goal is reduced VeriPB verification
time; proof size is a secondary signal.

## Why the obvious approaches don't work

Recorded so future work doesn't re-walk these.

- **Delete only the chain links, keep the literals.** Fails. It *fragments* the
  chain, and VeriPB RUPs rely on the chain being contiguous over the existing
  literals, including for closure-only reasoning about variables not named in the
  step. A fragmented chain breaks those RUPs. (The Ch.3 property of McIlree's
  thesis: at any point every integer literal must unit-propagate all known facts
  about its variable. A hole in the chain violates it.)

- **Delete literals and re-introduce on demand.** Deleting a literal and stitching
  its two chain links into one skip-link *coarsens* the chain (complete, fewer
  thresholds) rather than fragmenting it, which is sound. But re-introducing a
  literal later — re-emitting its `red` reification — **fails VeriPB** once the
  surrounding context has moved on: a live constraint pins the atom, and the
  reification's falsify-witness (`ge(v) := 0`) contradicts the pin, so the
  redundancy sub-goal can't be auto-proven. The dominant pins are **backtrack
  clauses**, which name the search's guess (branch-threshold) literals, so this
  bites in *every* searching proof, eq-free or not. An experimental
  `OrderEncodingDeletion::Literals` mode on this branch demonstrates the failure
  (see Provenance); it should be reworked into the design below.

The lesson: never delete-then-reintroduce. Advance a **monotone** frontier and
delete behind it, and when a surviving constraint still needs a literal, **hoist**
it rather than deleting-and-recreating.

## The verified foundation: guess-reasoned bound jumps

*Verified against VeriPB.* When a variable X has a lower bound `X >= L` and the
values `L .. H-1` have been eliminated as holes (each elimination derivable from
the current guesses), the bound can be jumped over the holes with a single RUP
whose reason is **just the conjunction of guesses**:

    rup <guesses> (X >= H) >= 1

This checks because RUP does full unit propagation: it re-derives every hole
`X != v` from the guesses over the (permanent) base constraints, then climbs
`X>=L -> X>=L+1 -> ... -> X>=H` through the eq-atom reverse-reifications. You do
**not** need the per-value reasons, nor "all reasons over all other variables" —
the guesses entail them and RUP rediscovers them. This is the same monotonicity
the final backtrack clause already relies on.

Checked at wide gaps (L,H differing in up to all 6 bits, e.g. 3->60, 17->46, 5->26)
with two controls that must fail and do: dropping a needed guess is rejected, and
over-jumping by one value is rejected. Small gaps can RUP by bit-coincidence, so
the wide-gap controls are what make the positive result trustworthy. (See
`order_jump_check` in Provenance.)

Two consequences that shape the design:

1. The jump climbs through the intermediate eq/ge atoms, so they must be **live at
   emit time**; afterwards they are deletable. That pins the ordering: **emit the
   jump, then delete behind it.**
2. The jump is one `.pbp` line but VeriPB does O(H-L) propagation to check it. So a
   jump doesn't make *that* check cheaper — the win is that after deletion the
   *resident* database is smaller, so every *other* RUP's closure shrinks.

## Design overview: consolidate -> hoist -> delete

> **Historical sketch — superseded by [brancher-design.md](brancher-design.md).**
> The sections from here through "Implementation staging" are the original
> user-approved *conceptual* sketch; the concrete, decided step-2 design (grounded
> in the real code, with the five owner decisions and the eq-atom window folded in)
> is [brancher-design.md](brancher-design.md). In particular the "Mapping the
> existing heuristics" table below is **wrong** and superseded: its in-order/eq rows
> claimed `smallest_first`/`smallest_in`/`largest_first`/`largest_in` win by an
> "O(1) pin" bound-jump, but eq branching has no gap to jump and an eq atom pins
> both ges — those orders instead win via the **eq-atom window** (evict behind a
> one-step frontier), while the bound-*jump* win is the `split_*` family only. The
> foundation above this note ("The verified foundation: guess-reasoned bound jumps")
> stands. The prose below is kept for provenance; do not treat it as current.

A brancher maintains a compact **backtrack constraint** — the "what we'll use to
backtrack" fact, i.e. the weakest constraint it has proven must hold given every
sibling tried so far is refuted, under the current guesses. It tightens
monotonically as siblings fail. On each refutation the framework:

1. asks the brancher for the tightened backtrack constraint;
2. emits the guess-reasoned RUP that advances it (a bound jump, for the common
   case);
3. **hoists** the literals the new constraint names to the level where it lives;
4. **deletes** the encoding the advance stepped over that nothing else names.

Consolidate, hoist the frontier, delete the rest. Because the frontier is
monotone, we never delete-then-reintroduce.

## The backtrack constraint

Three kinds, declarative and extensible:

- **Bound** (`LowerBound(v)` / `UpperBound(v)`) — for split / ascending /
  descending value orders. Advanced by the bound-jump RUP; names **one** literal
  (the frontier). Maximally deletable.
- **ExcludedSet** — the generic fallback, accumulating `X != v`. This is exactly
  today's `~(all guesses)` behaviour. Correct, but names a growing set, so nothing
  is deleted for that variable. Used by genuinely unstructured orders.
- **Custom** — an escape hatch: the brancher supplies its own backtrack constraint
  plus a proof callback. For exotic branchers; not fleshed out until a use case
  appears.

## The Brancher abstraction

Replace the bare `BranchValueGenerator` (which yields a
`generator<IntegerVariableCondition>` and touches no proof state) with a small
stateful object that owns *both* the decision sequence and the backtrack
constraint:

    struct BranchDecision {
        IntegerVariableCondition guess;      // what to branch on
        BacktrackAdvance         on_refuted; // how the backtrack constraint tightens if this fails
    };
    // BacktrackAdvance = variant<LowerBound, UpperBound, Exclude, Custom>

    struct Brancher {
        virtual auto next(const CurrentState &, const Propagators &)
            -> std::optional<BranchDecision> = 0;
        virtual auto initial_backtrack_constraint(...) -> BacktrackConstraint = 0;
    };

`solve.cc` drives it: `next()` -> guess -> recurse -> on refutation apply
`on_refuted` (framework emits the advance RUP, hoists, deletes) -> repeat; when
`next()` returns `nullopt` the standing backtrack constraint is the node's
backtrack lemma, replacing the generic `~guesses`. A brancher that only ever emits
`Exclude` advances reproduces today's behaviour byte-for-byte.

Owning decisions and their proof consequence in one object is deliberate: it is
what lets a new brancher be written *correctly* without the caller having to keep a
separate "value order" and "consolidation strategy" mutually consistent.

## The hoist primitive

A general `ProofLogger` operation, foundational to the whole scheme:

    hoist_literal_to_level(lit, target_level)
    hoist_literal_to_top(lit)                 // = hoist to level 0, permanent

It is a **bookkeeping move**: it reassigns the literal's definition from its
current (deep) level bucket to a shallower one, so a later `forget` deletes it
later, or never. **It re-emits nothing.** That is precisely why it succeeds where
delete-then-reintroduce fails — there is no re-asserted reification and therefore
no witness to collide with a pin.

Caveat, load-bearing: hoisting a literal so it stays *referenceable* is not enough;
for it to keep unit-propagating (the Ch.3 invariant) at its new level it must be
chain-linked to its neighbours *at that level*. So hoisting is two steps — move the
definition **and** stitch the literal into the target level's chain (for
hoist-to-top, into the permanent boundary chain). This is the existing stitch
machinery run in the hoist direction. Doing only the first step reintroduces a
subtler version of the chain-fragmentation bug.

## The deletion rule

Stated once, cleanly:

> Delete a literal only when no surviving constraint names it. If a surviving
> constraint at level L names a literal currently at a deeper level, **hoist** the
> literal to L instead of deleting it.

The brancher's backtrack constraint and any live nogoods are the "surviving
constraints" that trigger hoists. A compact bound backtrack constraint names one
literal, so one is hoisted and the rest of the stepped-over range is deleted (the
win). An excluded-set constraint names many, so many are hoisted (no win, but
correct). Retention is therefore automatic and exactly as tight as the brancher's
backtrack constraint — there is no separate "retained set" to maintain.

## Mapping the existing heuristics

Helpers make each existing `value_order::` a one-liner:

| value_order                                   | backtrack constraint       | deletable        |
|-----------------------------------------------|----------------------------|------------------|
| `smallest_first`, `smallest_in`               | ascending `LowerBound`     | yes, O(1) pin    |
| `largest_first`, `largest_in`                 | descending `UpperBound`    | yes              |
| `split_smallest_first` / `split_largest_first`| `LowerBound`/`UpperBound`  | yes              |
| `median`, `random`, `random_out`, `reject_random_interval` | `ExcludedSet` | no (unchanged)   |

The orders people use for large domains (in-order, split) get the win; the
deliberately-random ones keep working unchanged.

## Restarts

Backtrack constraints and advance RUPs live at `Current` levels, so a restart's
`forget` wipes them and the next pass simply re-runs the brancher and re-emits
them — no special handling. The coupling is with learned nogoods: they are at
`Top` and name the decision (branch-threshold) literals, so those literals must
survive. They **hoist to Top**. Since nogoods are the reduced positive-decision
prefix, this hoists O(nogoods) literals, not O(domain).

## Last-value / phase saving

Falls out for free, and in fact motivates the hole-jumping. Trying a remembered
value `X==42` first: if it is refuted it becomes a hole `X != 42`; when the
ascending frontier later reaches 42 it jumps over it with the verified
guess-reasoned RUP. The backtrack constraint stays a clean bound; the saved value
is just a hole in its path. The d-way "last sibling is free" case is subsumed too:
the frontier reaching `ub+1` *is* the at-least-one closure, so there is no separate
last-value special case to carry.

(There is no in-tree phase-saving today; if one is added it slots in here as a
first decision that may become a hole.)

## Parallel search (future)

Planned parallel search runs independent search processes that sometimes share
restart-nogoods. A shared nogood is only usable by a receiving process if the
literals it names are stably, identically defined there — which is exactly what
**hoist-to-top** guarantees. So this design does not solve parallel *proof-logging*,
but the hoist-to-top hook is the thing that future work will want, and nothing here
precludes it. Restart nogoods hoisting to Top (above) is the same mechanism.

## Extensibility

A new brancher is: pick a variable, yield decisions, tag each with a backtrack
advance — or, for the common case, call `frontier_ascending()` / `bisect()` and get
the consolidation, hoisting and deletion for free. Unstructured branchers use
`excluded_set()` (correct, no win). `Custom` is the escape hatch, and even it never
writes raw VeriPB — it hands back a backtrack constraint and the framework emits the
RUP. Per the "don't design ourselves into a corner, but don't over-commit" steer, we
ship the internal helpers plus `Custom` and leave a polished power-user surface until
a real use case lands.

## Implementation staging

1. **Hoist primitive first.** It is foundational, independently testable, and needed
   by everything downstream. Build `hoist_literal_to_level` / `hoist_literal_to_top`
   (definition move + stitch into the target chain) and verify with VeriPB that a
   deep literal hoisted to Top / to a level still checks and the chain stays intact.
2. **Brancher abstraction.** Introduce `Brancher` + `BacktrackConstraint` +
   `BacktrackAdvance`, port the existing `value_order::` heuristics onto it via
   helpers (default `Exclude` = today's behaviour, byte-identical), keep `branch_with`
   working.
3. **Wire deletion.** Drive deletion from backtrack-constraint advances (consolidate ->
   hoist -> delete), replacing the experimental `OrderEncodingDeletion::Literals`
   mode. Gate behind the existing flag until it verifies across the suite.
4. **Benchmark.** Re-run the eq-free large-domain sweep (split branching, UNSAT) that
   the earlier attempt could not measure because its proofs did not verify.

Each stage gates on: VeriPB accepts, and recursions/propagations/solutions are
unchanged mode-off vs mode-on (a proof-only change must not perturb search).

## Open questions

- Backtrack-constraint expressiveness beyond bound/excluded-set/custom — deferred;
  revisit if a disjunctive (interval) brancher wants a first-class kind.
- Exactly how much chain context a hoist must carry to preserve the Ch.3 invariant
  cheaply (splice a single skip-link vs. rebuild a span).
- Whether hoist-to-top of nogood literals wants the full definition or a lighter
  "nameable at Top" form, once parallel proof-logging is designed.

## Provenance and artifacts

- Journey and findings: see the `gcs-order-encoding-deletion` project memory.
- Branch `delete-order-links-on-backtrack`: experimental `OrderEncodingDeletion`
  flag (`GCS_DELETE_ORDER_ENCODING=literals`) demonstrating the delete-then-reintroduce
  failure — to be reworked per this design.
- `examples/order_deletion_bench/` — scalable eq-free linear/cumulative driver
  (split branching, `--unsat`) for the benchmark.
- `order_jump_check` — the VeriPB verification of the guess-reasoned bound jump and
  its two controls.
- Background: McIlree PhD thesis, Chapter 3 (integer-literal propagation properties);
  [variable-encodings.md](variable-encodings.md); [reasons-improvement.md](reasons-improvement.md).
