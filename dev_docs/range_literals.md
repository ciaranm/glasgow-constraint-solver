# Range / interval literals — design and status

Status: foundation **done and green** (reasons + `reject_random_interval` branching; full suite
verifies). Stage-3 **`infer_not_in_range` primitives built and committed** (green, unused by
default); the single-line range *inference* itself is behind `GCS_RANGE_INFERENCES` (default
off) pending productionisation — see "Stage 3" below for the key finding (interval inferences
across a bit-sum equality need an explicit bridge proof, not RUP). The bridge now lives in a
reusable free helper `justify_not_in_range_across_equality`
(`gcs/constraints/innards/justify_not_in_range.{hh,cc}`) and is wired into `enforce_equality`,
so `Equals` and `Element` (index-fixed) verify it gate-on **in isolation**. **CORRECTED (and
the headline): this does NOT compose.** A star of plain `Equals` over three transitively-linked
variables — no `AllEqual` involved — breaks gate-on identically. So interval *inference* across
a bit-sum equality is a **general** limitation of the equality family, not an `AllEqual` bug:
the moment ≥3 variables share an equality class, the backtracking invariant needs a *bound*
threaded across the equality, which unit propagation cannot do. The two-variable tests pass only
because two variables in isolation never raise that obligation. The full thesis-grounded
explanation (which thesis properties we preserve vs lose, and why) is in
**[`range_literals_theory.md`](range_literals_theory.md)** — read that first. Branch
`range-literals`, draft PR #281.

This document is the authoritative current-state summary. The git history and PR have the
blow-by-blow; this is the settled picture so we don't re-derive it. For the *theory* of why the
equality family breaks, see [`range_literals_theory.md`](range_literals_theory.md).

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
| `Equals` / `ReifiedEquals` | `v1−v2==0` (via `enforce_equality`) | verifies gate-on **in isolation only** (2 vars); breaks once 3+ vars are transitively linked (see [`range_literals_theory.md`](range_literals_theory.md)) |
| `Element` (index fixed) | `result−array_var==0` (via `enforce_equality`) | same — verifies in isolation (61 instances), composes no better than `Equals` |
| `AllEqual` | star `vars[0]−vars[i]==0` (via `enforce_equality`) | breaks gate-on for ≥3 vars — but this is the **general** equality-family limitation, *not* `AllEqual`-specific (a star of plain `Equals` breaks identically) |
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

### Why interval inference does not compose across the equality family

> The full, thesis-grounded version of this is **[`range_literals_theory.md`](range_literals_theory.md)**.
> This is the short operational summary.

The bridge lives in `enforce_equality`, so `Equals` and `Element` (index-fixed) inherit it and
both verify gate-on **when posted in isolation** (`Element`: var/const/const2d/var2d, 61 proof
instances). Note the constraint tests are registered with `run_test_only.bash` — they do **not**
run VeriPB in `ctest` — so gate-on verification is by hand per constraint; the green 324/324
`ctest` run is the gate-**off** default.

**That isolation is load-bearing, and it was a trap.** Earlier drafts of this section concluded
the break was `AllEqual`-specific (a "multi-hop chain" vs "single direct equality" distinction).
That is **wrong**, and the experiments that disproved it:

- Reducing `AllEqual` to a star of single-edge `enforce_equality` calls (every inference one
  direct equality, exactly the `Equals` case) — still breaks gate-on.
- Posting a **star of plain `Equals` constraints** over three transitively-linked variables, with
  no `AllEqual` anywhere — breaks gate-on identically (same rate, same instances).

So the limitation is **general to the equality family**: as soon as ≥3 variables share an
equality class (via `AllEqual`, a chain/star of `Equals`, or `Equals`+`Element`), the solver's
**backtracking justification** needs unit propagation to thread a *bound* from one variable to
another across a bit-sum equality (e.g. `i₃≥3 ⟹ i₂≥3`). Unit propagation across a bit-sum
equality moves **values** (Thm 2.8, bit-pinning) and **contradictions** (Thm 2.7/2.9), but
**never a lone bound** — there is no theorem for it. The per-value world never needs the step
(every obligation is a single value → 2.8); a wide interval literal asserts only order atoms,
never pins bits, so its obligation is a bound and the step is required and missing. Two variables
in isolation never raise it, which is the *only* reason `Equals`/`Element` pass their tests.

In thesis terms (see the theory doc): we **preserve** Theorem 3.3 (intra-variable completeness,
extended to interval literals) but **lose** Inv2 / Theorem 3.4 (the backtracking-RUP invariant)
for any constraint that channels across a bit-sum equality. Restoring it needs a cross-variable
Inv1 — `(x≥k) ⇔ (y≥k)` logged per equality at the boundary values in play — i.e. a *covering*,
the per-value work interval literals exist to avoid, now needed globally across the family.

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

1. **The equality family does not compose — design decision required, not a code task.** The
   bridge helper is built and wired (`Equals`/`Element` verify in isolation), but interval
   inference across a bit-sum equality is **unsafe for the whole equality family** once ≥3
   variables share an equality class (general, not `AllEqual`-specific — see
   [`range_literals_theory.md`](range_literals_theory.md)). The only known fix is a cross-variable
   Inv1 (`(x≥k) ⇔ (y≥k)` per equality at boundary values) — a covering applied globally to the
   family, the cost interval literals were meant to avoid. Until that's decided, `Equals` /
   `Element` / `AllEqual` should keep `GCS_RANGE_INFERENCES` **off**, and interval inference
   should target only the **eq-atom/selector-channelled** family (Table, Regular, GCC, Count, …),
   where every cross-variable obligation stays a single value (2.8) and the problem never arises.
   (`Abs` was the would-be next equality-family member; it is moot until this is resolved.)
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
- **CORRECTED (twice — note the trajectory, it's a cautionary tale):** first we thought "the
  bridge generalises to the whole equality family"; then, after `AllEqual` n≥3 broke, we thought
  it was a *single-direct-equality vs multi-hop-chain* distinction (Equals/Element/n==2 fine,
  longer chains not). **Both wrong.** A star of single-edge `Equals` calls breaks; a star of
  *plain `Equals` constraints* with no `AllEqual` breaks identically. The real boundary is
  **2 variables vs ≥3 in an equality class**, and it is a *general* property of interval
  inference across a bit-sum equality, not a chain/witness/coalescing artifact. The earlier
  "axis-2 coupling" / "multi-hop" framing was a wrong turn — the cause is that UP cannot thread
  a bound across a bit-sum equality (Thms 2.7/2.8/2.9 give value-crossings and contradictions,
  not bound propagation), so the backtracking invariant (Inv2 / Thm 3.4) cannot hold. See
  [`range_literals_theory.md`](range_literals_theory.md). **Lesson:** an interval inference that
  verifies for an isolated 2-variable constraint tells you *nothing* about composition; check ≥3
  variables in one equality class.
- **CORRECTED:** "the constraint suite (324/324) verifies the bridge." The constraint tests use
  `run_test_only.bash` (no VeriPB) and the suite default is gate-**off**; gate-on bridge
  verification is manual per constraint. An earlier note that Element was "proven by the suite"
  was unsubstantiated until checked directly (it does pass: `element_test <mode> --prove` with
  `GCS_RANGE_INFERENCES=1`).
- **Two refuted "more elaborate proof" attempts for AllEqual n≥3** (the OPB is a *line* of n-1
  consecutive `vars[i]=vars[i+1]`, not a star):
  1. **Full pairwise (n²/2) OPB instead of the line** — *does not help* (10/40 still fail). The
     failing backtrack step (`i₂≤4 ⟹ i₃≤4`) is across an equality that is *already adjacent* in
     the line; UP can't cross it, and adding the other pairs doesn't change that. Not a
     connectivity problem.
  2. **Bridge lemmas durable at `Top` (unconditional) instead of `Temporary`** — *necessary but
     insufficient* (13/40 still fail). They fire and resolve flags (the trail gets much further),
     and are RUP-derivable at `Top` for a direct equality, but the residual failures are raw
     var-to-var bound propagations *not mediated by any flag* (the solver's backtrack clauses,
     e.g. `i₂==5 ∨ i₃==3`).
  3. **Star OPB + funnel every inference single-hop through the hub** (`AllEqual` rewritten as
     n−1 single-edge `enforce_equality` calls, cost-neutral on the default path) — *does not help*
     (9/40 still fail), and crucially it reduces `AllEqual` to *literally* the `Equals` code, so
     it proved the inference justification was never the problem.
  All three confirm the same thing the theory doc explains: it is not connectivity, not durability,
  not how the inference is justified. UP cannot thread a bound across a bit-sum equality at all
  (Thms 2.7/2.8/2.9 give value-crossings and contradictions, never a lone bound), so the
  backtracking invariant cannot hold once ≥3 variables share an equality class. The only known fix
  is the cross-variable covering `(vᵢ≥k) ⟺ (vⱼ≥k)` — applied across the whole equality family, not
  just `AllEqual`.
