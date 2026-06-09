# Range / interval literals — design and status

Status: foundation **done and green**. The whole constraint test suite (225 tests) verifies
under `reject_random_interval` branching. Branch `range-literals`, draft PR #281.

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

## What is left (productionization, no unknowns)

- **Stage 3 — `infer_not_in_range` / `infer_in_range` (issue #144).** A range removal is ONE
  emitted proof line `~[lo,hi]` (the per-value `x != v` follow by RUP, free) — overturning
  #144's "must emit per-value", which assumed an *unreified* range Boolean. Plan: add
  `IntervalSet::erase_range`; `State::infer_not_in_range` (erase + emit one `~need_invar` step
  via `emit_rup_proof_line_under_reason` — needs InferenceTracker support for a range-flag
  inference, which is not a standard `Literal` infer); trivial `infer_in_range` (two bound
  infers); apply at `equals.cc:65`, `min_max.cc:179`, `element.cc:477` (at equals the per-value
  reason `(v2 != val)` coalesces to `~[v2 in lo..hi]`, a range-to-range inference); bench proof
  size. Soundness in search relies on the containment from axis 2.
- **Stage 6 — generality.** Fold ranges into `IntegerVariableCondition` / make them
  user-facing, retiring the dev-time `BranchGuess`-only scope.

## Dead ends — do NOT revisit

- "The order chain alone is enough, no covering needed." True only for axis 1. The hole/
  backtrack axis genuinely needs containment; this was proven by `reject_random_interval`
  failing on Count/among/element before containment was added.
- For the branching wall, none of these is the fix: per-propagator explicit conflict
  justification; a bound-touching branching discipline; "it's a fundamental UP limitation".
  The fix is the containment edges (axis 2).
- Covering edges *between range literals* (`parent -> OR children`) are unnecessary — the chain
  gives those deductions. Only *containment* (`child -> parent`) is needed, and only on axis 2.
- The #144 overturn is delivered by the **reification + chain**, not by the containment.
