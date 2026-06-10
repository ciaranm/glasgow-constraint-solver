# Range / interval literals — design and status

Status: foundation **done and green** (reasons + `reject_random_interval` branching; full suite
verifies). Stage-3 **`infer_not_in_range` primitives built and committed** (green, unused by
default); the single-line range *inference* itself is behind `GCS_RANGE_INFERENCES` (default
off) pending productionisation — see "Stage 3" below for the key finding (interval inferences
across a bit-sum equality need an explicit bridge proof, not RUP). The bridge now lives in a
reusable free helper `justify_not_in_range_across_equality`
(`gcs/constraints/innards/justify_not_in_range.{hh,cc}`) and is wired into `enforce_equality`,
so **`Equals` and `Element` (index-fixed) both verify it gate-on**. Attempting to extend it to
**`AllEqual` surfaced an axis-1/axis-2 coupling**: the bridge *inference* is sound, but
coalescing a multi-variable chain's per-value removals into one range flag breaks *backtrack-
clause* reconstruction (n≥3 fails; n==2 works) — see "Generalising across the family" below.
Branch `range-literals`, draft PR #281.

This document is the authoritative current-state summary. The git history and PR have the
blow-by-blow; this is the settled picture so we don't re-derive it.

## What a range literal is

A range ("in") literal `[x in a..b]` is a fresh proof-only `ProofFlag`, **reified to the
variable's two order cuts**:

    [x in a..b]  <=>  (x >= a) AND NOT (x >= b+1)

It is a "wide equality literal" — an equality atom `x = v` is exactly the singleton `[v,v]`.
Created lazily, in one place: `NamesAndIDsTracker::need_invar(id, lo, hi)`. All consumers
(reasons, inferences, branching) go through it, so they all inherit its linking.

## The two-axis model (the key idea)

There are two independent linking needs. Conflating them is what caused several false starts;
keep them separate.

1. **Bound / inference axis — the order chain (Inv1) is sufficient. No covering.**
   Every range<->range and range<->order *deduction*, and every *inference* of a range
   literal (or of `x != v` from `~[lo,hi]`), is RUP from the boundary-EO reification + the
   existing gevar order chain. This is because a `rup` check asserts the negation of its
   conclusion, which hands UP a bound that walks the chain. `need_gevar` already maintains the
   chain. Nothing extra is needed here.

2. **Hole / backtrack axis — needs laminar containment.**
   An interval *reject decision* `~[a,b]` (branching, or a removed-but-now-load-bearing hole)
   has no conclusion to hand UP a bound, so the chain does **not** forward-propagate it. A
   backtrack clause whose conflict is written over the `eq`/sub-range atoms inside `[a,b]` is
   then not RUP. Fix: **laminar containment edges `child -> parent`** for every nested literal
   — sub-ranges down to `eq` singletons at the leaves — so `~[a,b] -> ~child -> ... -> ~eq[v]`
   propagates transitively. Each edge is itself RUP from the boundary-EO + chain, so emitted as
   a `rup` line at `ProofLevel::Top`. Overlapping (non-nested) ranges need no edge; they
   connect via shared leaves.

## What is implemented

- **`need_invar` + reification + containment** — `gcs/innards/proofs/names_and_ids_tracker.cc`.
  Containment is maintained by `link_immediate_containment` (private), which emits only
  immediate-parent/child (Hasse) edges; bidirectional with `need_direct_encoding_for` (a new
  `eq` atom links to its containing ranges). Width-1 branch picks use the `eq` atom directly
  (no singleton flag).
- **Range literals in reasons** — `ProofLogger::reason_to_lits` and the other reason sites
  coalesce a run of `var != v` into one `~need_invar` literal, env-gated by `GCS_RANGE_REASONS`
  (off by default). `gcs/innards/proofs/proof_logger.cc`.
- **Interval branching** — `BranchGuess = variant<Literal, IntegerVariableRangeGuess>`
  (`gcs/branch_guess.hh`) threaded through the *guess channel only* (`State::guess/guesses`,
  `solve.cc` recurse/backtrack, `Propagators::propagate`, `auto_table`). A range guess maps to
  one `need_invar` flag in the backtrack clause. `value_order::reject_random_interval`.
- **Test default** — `constraints_test_utils.hh` branches with `reject_random_interval`, so the
  suite stress-tests this on every constraint.
- Proof tests: `invar_test`, `range_reason_test`, `range_branch_test`
  (`gcs/innards/proofs/`).

## Stage 3 — `infer_not_in_range` (issue #144): status and the key finding

**Built and committed (general, view-safe, green; unused by default):**

- **`IntervalSet::erase_range(lo, hi)`** — closed-range removal in one merge-walk pass, with
  unit tests. (`gcs/innards/interval_set.hh`, `interval_set_test.cc`.)
- **`State::infer_not_in_range` + `change_state_for_not_in_range`** — view-aware single-pass
  domain mutation, returns the right `Inference`. A genuine win on the **non-proof** solve
  path (one `erase_range` instead of N `erase`s). (`state.hh/.cc`.)
- **`InferenceTracker::infer_not_in_range` + `track_range_impl`** (both tracker classes) and
  **`ProofLogger::infer_not_in_range`** — proof-side plumbing for a *range-flag* inference
  (a `~need_invar` conclusion, not a standard `Literal` infer). Plain simple vars get the
  single-line conclusion; views/constants fall back to per-value. (`inference_tracker.hh`,
  `proof_logger.hh/.cc`.)

### THE KEY FINDING: inferring an interval needs its *own* proof — RUP alone is not enough

The Stage-3 plan above (now corrected) claimed a range removal is ONE proof line `~[lo,hi]`
**by RUP**, the per-value `x != v` following free from the chain. **This is false for the
constraints that actually do interval removals.** Empirically (VeriPB `--trace-failed`) and
from McIlree's thesis:

- A range flag `[X in lo..hi]` asserts only X's **order atoms** (`X>=lo ∧ ¬(X>=hi+1)`). With
  `lo<hi`, **Theorem 2.8 never fires** (it pins bits only for `sum=A ∧ sum<=A`, a single
  value), so a range assertion **never pins X's bits**.
- Constraints that prune an interval do so *across a cross-variable link*. If that link is a
  **bit-sum equality** `X−Y==0`, the range flag's order atoms can't cross it (UP can't do the
  cross-variable linear step), so `~[X in lo..hi]` is **not RUP**. The per-value version works
  only because asserting `X=v` (an *eq* atom) pins X's bits via Thm 2.8, which then channel to Y.

**Audit of scope (who is affected).** The break is exactly: *constraints that prune an interior
interval across a primary bit-sum equality.* These are:

| Constraint | Link | Bridge status (gate-on) |
|---|---|---|
| `Equals` / `ReifiedEquals` | `v1−v2==0` (via `enforce_equality`) | **works, verified** (the canonical case) |
| `Element` (index fixed) | `result−array_var==0` (via `enforce_equality`) | **works, verified** (var/const/const2d/var2d, 61 instances) — shares `enforce_equality` |
| `AllEqual` | `vars[i]−vars[i+1]==0` chain (witness) | **n==2 works; n≥3 breaks** on the axis-2 wall below |
| `Abs` | `v2∓v1==0` reified on sign | not yet wired; needs a sign case-split + (image direction) two-sided exclusion — `justify_abs_hole` is the per-value form |

Everything else is fine: constraints that channel via **eq-atoms / selectors** (Table, Regular,
GCC, Count, Among, In, Inverse, MinMax, AtMostOne, ValuePrecede, Circuit, AllDifferent) have
reasons that *forward-propagate* `X≠v`, so their interval removals **are** RUP as a single line
(consistent with thesis Justification Procedure 3.3). The bit-*arithmetic* constraints that
can't channel cheaply (Linear, Comparison, Plus, …) are bounds-consistent and never do interior
removals, so the question doesn't arise. (Note: `Abs` *does* do interior removal — earlier audit
said otherwise and was wrong; ArgSort/SmartTable have bit-sum equalities but reified *behind
selectors*, so they forward-propagate and are fine.)

### The fix that works: an explicit bridge (case-split, each case RUP)

RUP-as-a-single-*line* was the wrong bar. A short **explicit** justification collapses the
interval into one conclusion, on the **unmodified** bit-sum model — no re-encoding. To remove
`[lo,hi]` from `v1` because `v2` lacks it (`v1=v2`):

```
flag := [v1 in lo..hi]
1)  ~flag ∨ (v2 ≥ lo)        # RUP: ¬ gives flag ∧ v2≤lo−1; with v1=v2 this is the
2)  ~flag ∨ ¬(v2 ≥ hi+1)     #      Theorem 2.9 (contradictory binary sums) configuration
⇒  ~flag                     # RUP from (1),(2) + the disjunctive reason ~[v2 in lo..hi]
```

The case-split is the point: the *disjunctive* reason never hands UP an opposing bound, but each
lemma's negation does, triggering Thm 2.9. This is literally Justification Procedure 3.2
(Comparison) materialising each bound across the equality; `justify_abs_hole` is the per-value
sign-split form of the same idea. **Verified** end-to-end with VeriPB: full `equals_test` (plain
+ reified) passes with the bridge wired in.

This is exercised behind an env flag, **`GCS_RANGE_INFERENCES` (default off)**, in
`enforce_equality` (simple vars only; views/constants stay per-value), with a dedicated proof
test `range_infer_test`. Default behaviour is byte-identical to before (the bridge lambda is
only reached when the gate is on).

The two bound-lemmas are now a reusable free helper,
`gcs::innards::justify_not_in_range_across_equality`
(`gcs/constraints/innards/justify_not_in_range.{hh,cc}`): `ProofLogger &` first, matching the
`abs/justify`, `linear/justify`, … convention, so it travels with the scoopable proof-pattern
layer rather than baking into `ProofLogger`. It takes `(pruned, lo, hi, other, other_lo,
other_hi)` so a sign-flipped link passes `[-hi, -lo]` — ready for `Abs`.

### Generalising across the family: where it holds, and the axis-2 wall

The bridge lives in `enforce_equality`, so **`Equals` and `Element` (index-fixed) both inherit
it** and both verify gate-on (`Element`: var/const/const2d/var2d, 61 proof instances). Note the
constraint tests are registered with `run_test_only.bash` — they do **not** run VeriPB in
`ctest` — so gate-on verification is done by hand per constraint (`<test> <mode> --prove` with
`GCS_RANGE_INFERENCES=1`); the green 324/324 `ctest` run is the gate-**off** default.

Extending to **`AllEqual` does not just work**, and the reason is instructive. The bridge
*inference* (axis 1) is sound: with the chain reduced to a single equality (n==2) it verifies
(0/40 stress runs). But for **n≥3 it fails intermittently** (random domains; reproduced on
`domains=[(1,5),(2,6),(3,7)]`). The failing line is **not** the inference — it is a later
**backtrack clause** (`i₃==4 ∨ i₂==5`). Its RUP needs unit propagation to chain a bound across
the chain equalities (here `i₂≤4 ⟹ i₃≤4` across `i₂−i₃==0`). VeriPB's UP does **not** cross a
bit-sum equality for free; it only does so via explicit binary channelling clauses. The
gate-off per-value path leaves enough of those clauses behind (each `vars[i] != v ← witness != v`
survives at `Current`); coalescing N removals into **one** range-flag conclusion plus
**`Temporary`** bridge lemmas (deleted on backtrack) removes exactly the channelling the
backtrack reconstruction relied on. `Equals`/`Element`/n==2-`AllEqual` survive because the
pruned↔witness link is a **single direct equality** in the OPB, always available to RUP; a
multi-hop chain's link is not.

**The criterion, refined.** The bridge generalises wherever the interval removal crosses a
*single direct equality* to the witness. It does **not** generalise for free across a *multi-hop
equality chain*, because the coalesced inference (axis 1) starves the backtrack/hole machinery
(axis 2) of the per-value channelling it implicitly used. This **couples** the two axes that the
"two independent axes" model (above) treats as separate: independence holds for plain RUP
inferences, but coalescing an inference can change which clauses survive into axis-2
reconstruction. Making AllEqual (n≥3) work would need that cross-chain channelling preserved
durably (e.g. emit the needed bound-implication clauses at a surviving level, or fall back to
per-value when the witness is non-adjacent) — left as future work, not a quick recipe.

### Proof-size: width-independent inference, win for *wide* intervals (with caveats)

The inference is 3 lines (2 lemmas + conclusion) regardless of interval width. Measured
(VeriPB line counts, `Equals` with a hole):

- narrow ranges (widths 1–7, `equals_test`): **1306 vs 1269** — slight *loss*.
- one wide hole (width 21): **445 vs 582** — ~24% *win*.

The catch is a per-flag fixed cost: `need_invar` emits the reification + **O(width) laminar
containment edges** (the axis-2 backtrack machinery). So it's break-even for narrow intervals,
a win for wide ones. **But** that fixed cost amortises: in the `equals_test` proof, 23 distinct
range flags carry **932 references (~40× reuse each)** — mostly from `reject_random_interval`
branching, which mints and reuses the same flags. So the realistic marginal cost of a range
removal (reusing an existing flag) is ~3 lines vs O(width) per-value. The one-shot probe above
is the un-amortised worst case. **Not yet measured:** a realistic instance with recurring *wide*
removals; the effect of hoisting the bridge lemmas to `Top` (they are search-independent facts,
so they would amortise too, dropping the marginal cost toward 1 line); and **verify time** (a
larger constraint DB vs faster RUP — entirely unmeasured).

### What is left to productionise

1. **Generalise the bridge.** *Done:* home decided (free helper
   `justify_not_in_range_across_equality` in `constraints/innards/`), wired via
   `enforce_equality`, so `Equals` and `Element` (index-fixed) verify gate-on. *Blocked:*
   `AllEqual` n≥3 hits the axis-2 wall (see "Generalising across the family") — needs durable
   cross-chain channelling or a per-value fallback for non-adjacent witnesses. *Not started:*
   `Abs` — the helper is sign-flip-ready (pass `[-hi, -lo]`), but Abs needs (a) the v2→v1
   direction conditioned on the sign reification (only one of `v2=v1` / `v2=-v1` holds per
   branch, like `justify_abs_hole`), and (b) the v1→v2 image direction's *two-sided* exclusion
   (`v2∈[lo,hi]` ⟹ `v1∈[lo,hi]∪[-hi,-lo]`, so two bridge applications across the two preimages).
2. **Views.** `infer_not_in_range`'s single-line path is simple-var only; generalise (deview
   the range, or fall back cleanly). Relates to Stage 6.
3. **Cost policy (Stage 5).** A width threshold (cf. `min_run_to_coalesce` for reasons) to pick
   range-vs-per-value, since narrow ranges are break-even. Then the gate can come off.
4. **Hoist the bridge lemmas to `Top`** so they amortise across reuse; measure proof-size AND
   verify-time on a structured benchmark.
5. **Reason side is also an interval.** The reason `v2 != lo..hi` is the symmetric half; the
   Stage-2 `coalesce_holes_in_reason` already rewrites it to `~[v2 in lo..hi]` (gated by
   `GCS_RANGE_REASONS`). Building it as a native range literal (no loop, no coalescing pass)
   is the Stage-6 generality.
6. **`infer_in_range`** (issue #144's companion) — two bound infers; deferred, no clean caller
   after line drift. Add only when a real consumer appears.

## Stage 6 — generality

Fold ranges into `IntegerVariableCondition` / make them user-facing, retiring the dev-time
`BranchGuess`-only scope. This is the unifying step: one range-literal abstraction shared by
reasons, inferences, AND branching (today reasons and branching use it; inferences are the new
`GCS_RANGE_INFERENCES` path).

## Dead ends / corrected claims — do NOT revisit

- "The order chain alone is enough, no covering needed." True only for axis 1. The hole/
  backtrack axis genuinely needs containment; proven by `reject_random_interval` failing on
  Count/among/element before containment was added.
- For the branching wall, none of these is the fix: per-propagator explicit conflict
  justification; a bound-touching branching discipline; "it's a fundamental UP limitation".
  The fix is the containment edges (axis 2).
- Covering edges *between range literals* (`parent -> OR children`) are unnecessary — the chain
  gives those deductions. Only *containment* (`child -> parent`) is needed, and only on axis 2.
- **CORRECTED:** the old claim "a range *inference* is ONE line by RUP, overturning #144" is
  **wrong** for the bit-sum-equality family (Equals/AllEqual/Abs/Element-index-fixed). RUP
  suffices only when the constraint's link forward-propagates `X≠v` (eq-atom/selector channelled
  constraints). For the equality family, the single line needs the **explicit bridge** above.
  #144's "the proof is per-value" instinct was right for those constraints, but the proof can
  still be made width-independent (constant lines) with the bridge — just not pure RUP.
- **CORRECTED:** "the bridge generalises to the whole equality family by sharing
  `enforce_equality`." Only the **single-direct-equality** members do (Equals, Element-index-
  fixed, n==2 AllEqual). `AllEqual` n≥3 breaks — not in the inference, but because coalescing
  couples axis 1 and axis 2 (see "Generalising across the family"). Do not assume a constraint
  with interval-removal-across-equality is bridge-ready without checking its *backtrack* clauses
  gate-on, not just the inference.
- **CORRECTED:** "the constraint suite (324/324) verifies the bridge." The constraint tests use
  `run_test_only.bash` (no VeriPB) and the suite default is gate-**off**; gate-on bridge
  verification is manual per constraint. An earlier note that Element was "proven by the suite"
  was unsubstantiated until checked directly (it does pass: `element_test <mode> --prove` with
  `GCS_RANGE_INFERENCES=1`).
