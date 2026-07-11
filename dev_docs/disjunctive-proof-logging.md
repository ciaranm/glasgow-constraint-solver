# Proof logging for `Disjunctive`

This document explains how the `Disjunctive` propagator's proofs are
backed by VeriPB. The propagator is time-table consistency specialised
to `h_i = 1`, `capacity = 1`
(see [`cumulative-proof-logging.md`](cumulative-proof-logging.md) for
the general time-table proof machinery), but the *proofs* do not use
the time-indexed vocabulary at all: at unit heights and capacity,
every inference the propagator makes is a statement about one **pair**
of tasks, and is justified directly against the declarative pairwise
OPB encoding. There is no per-(task, time) scaffolding anywhere — no
flags, no proof-only variables, no prefix emitted before search (a
previous design bridged to cumulative-style time-indexed flags at
`O(n × horizon)` cost; #495 has the measurements from removing it).

For the constraint itself — semantics, propagator, the strict / non-strict
flag — read `gcs/constraints/disjunctive/disjunctive.{hh,cc}`.

## The declarative OPB encoding

`define_proof_model` emits exactly one shape: for every unordered pair
of participating tasks `(i, j)`,

```
before_{i,j}  <->  s_i + l_i <= s_j     (i finishes at-or-before j starts)
before_{j,i}  <->  s_j + l_j <= s_i
before_{i,j}  v   before_{j,i}          (one of them must finish first)
```

That's the whole OPB contribution, and it is also all the proof
scaffolding there is. It directly mirrors the constraint's spec: "for
every pair, one task finishes before the other starts". A human
reading the OPB recognises the disjunctive constraint without knowing
how Glasgow's propagator works, and the encoding matches `cake_pb_cp`
(flags `x[id][i_j][bf]`, halves `[r]`/`[f]`, clauses
`@c[id][i_jsepal1]`), so the proofs chain-verify.

For a constant duration the flag's inequality folds to
`s_i − s_j ≤ −l_i`; for a variable duration the `l_i` term stays on
the left-hand side. Non-strict mode adds a reified `l_i ≤ 0` escape
flag (`x[id][i][zw]`) per variable-duration task to the separation
clause — a zero-length task does not constrain.

## The pairwise justification vocabulary

Every justification is built from one pol shape over a before flag's
`[r]` half (`flag → s_a + l_a ≤ s_b`, i.e. in normalised form
`M·¬flag + s_b − s_a − l_a ≥ 0`): add one **bound-literal definition
row** per integer operand, and the integer terms cancel exactly,
leaving a clause over the flag's negation and the residual order
literals. `emit_before_pol(a, b, cond_a, cond_b)` in
`disjunctive.cc` packages this:

```
pol  @x[id][a_b][bf][r]        M·¬bf + s_b − s_a − l_a ≥ 0
  +  rowa of [s_a ≥ lo]        s_a + lo·¬[s_a ≥ lo] ≥ lo
  +  rowa of [l_a ≥ llo]       l_a + llo·¬[l_a ≥ llo] ≥ llo    (variable duration)
  +  rowb of [s_b < hi+1]      −s_b + c·[s_b ≥ hi+1] ≥ −hi
  s
  =  ¬bf ∨ ¬[s_a ≥ lo] ∨ ¬[l_a ≥ llo] ∨ [s_b ≥ hi+1]   (degree lo + llo − hi)
```

The rows are obtained through
`NamesAndIDsTracker::need_pol_item_defining_literal`, which mints the
order-literal atoms on demand (the reason materialisation uses the
same atoms, so the residuals are exactly the literals the closing
reason-wrapped RUP assumes). Three details matter:

- **The pol is load-bearing.** Bare RUP is *not* sufficient in
  general: when the ordering margin is smaller than the residual
  bit-encoding range above a bound, unit propagation cannot transfer
  a bound row's cap into the reification row's slack (VeriPB's
  cross-variable linear-deduction limit). The pol does the linear
  combination explicitly; the closing RUP then only has to
  unit-propagate single-literal steps.
- **Bit-mapped literals add nothing.** When a bound literal maps
  directly onto a single encoding bit (a one-bit domain, or a
  threshold aligned with the top bit), the tracker returns the
  literal itself rather than a definition row. There is nothing to
  add in that case: the operand's raw term in the `[r]` row already
  normalises to exactly that residual literal (and the bit alignment
  bounds the remaining low-bit residual by the bound's slack).
  Adding the literal *axiom* instead would cancel the term outright
  and lose the bound — this is why `emit_before_pol` dispatches on
  the `variant<ProofLine, XLiteral>` and skips the `XLiteral` arm,
  rather than calling `PolBuilder::add_for_literal`.
- **The pushed variable's bounds are captured, not re-read.** By the
  time a `JustifyExplicitly` callback runs, the inference has already
  landed in the state, so `state.bounds()` on the pushed variable
  would return the *post-push* bound, which the reason does not
  support. Bounds of the other operands (blockers, durations) are
  unchanged by the inference and may be read at justification time.

Statically-true bound literals (a root bound, or a threshold past the
encoding maximum) degrade gracefully: `need_gevar` emits trivial
halves and pins the boundary atom at `ProofLevel::Top`, so the same
uniform pol works at domain edges and on domain-wiping pushes.

## The three inferences

- **Mandatory-overflow contradiction.** Two tasks `i`, `j` whose
  mandatory parts overlap at some time. Then neither can finish
  before the other starts: `lb(s_i) + lb(l_i) > ub(s_j)` and
  vice versa, so two pols (one per direction) force both before
  flags false under the reason, and the separation clause unit-fails
  in the framework's closing reason-wrapped RUP. Two pols, no `t`.

- **lb-push.** The propagator scans for the smallest fitting start
  `new_lb` for task `j`; the justification is a chain with **one
  dichotomy step per blocker** (not per blocked time — a step
  advances past a blocker's whole mandatory part, however long).
  At running bound `B` (established by the reason for the first
  step, by the previous step's deposit after), the window
  `[B, B + lb(l_j))` reaches into blocker `k`'s mandatory part
  `[lst_k, eet_k)`:

  - *left branch*: `before_{j,k}` would need
    `s_j ≤ ub(s_k) − lb(l_j) < B` — refuted by a pol citing the
    running bound, `lb(l_j)`, and `ub(s_k)`;
  - *right branch*: `before_{k,j}` gives
    `s_j ≥ lb(s_k) + lb(l_k) = eet_k` — folded onto the target order
    literal's definition row (`bf_{k,j} → [s_j ≥ target]`).

  Intermediate steps deposit `[s_j ≥ target]` under the reason (one
  RUP line) so the next step's left branch can unit-propagate from
  it. Targets are clipped to `new_lb`: the chain reads current
  bounds, which may be tighter than the profile the propagator
  scanned (mandatory parts only grow within a pass), and the final
  step must land exactly on the inferred literal, which the
  framework's closing RUP concludes. Cost: two pols plus at most one
  deposit per blocker.

- **ub-push.** The mirror image: at running bound `U`,
  `before_{k,j}` would put `s_j ≥ eet_k > U` (refuted), and
  `before_{j,k}` caps `s_j ≤ lst_k − lb(l_j)` (folded onto the
  target). Steps drop the bound to
  `max(lst_k − lb(l_j), new_ub)` per blocker.

Blocker selection is greedy (deepest mandatory end for an lb-push,
leftmost mandatory start for a ub-push); every non-fitting start is
blocked, so a blocker always exists while the chain has ground to
cover, and each step strictly advances.

### Variable durations

No extra machinery at all: the duration term stays on the before
flag's left-hand side and cancels against the duration's lower-bound
definition row *in the same pol* (see the shape above). Mandatory
parts and footprints use `lb(l_i)`, and every variable duration joins
the reason. In particular there is **no** proof-only `end = s + l`
variable — the in-proof end introduction
(`ProofLogger::introduce_bits_of`) exists for Cumulative's
time-indexed `after` flags, which Disjunctive's proofs no longer use.

### Non-strict zero-length escapes

Whenever an inference fires, every involved task has a positive
guaranteed duration, so its `zw` escape flag is false. The
justification pins the involved escapes false first (one RUP under
reason each, from `lb(l) ≥ 1`), and the separation clauses reduce to
their before-flag disjunctions for the rest of the derivation.

## Strict-mode zero-length tasks

Strict mode forbids a zero-length task from sitting strictly inside
another task's open active interval. The TT machinery doesn't help
here because zero-length tasks have empty mandatory parts and never
enter the profile. A separate all-fixed pairwise check covers them,
and the proof is straightforward: at the all-fixed leaf, the
declarative pairwise encoding alone is RUP-closable. With `s_z` and
`s_k` fixed at `vz`, `vk` satisfying `vk < vz < vk + l_k`,
`before_{z,k}` and `before_{k,z}` both UP to 0 from the unit
assignments and the encoded clause `before_{z,k} + before_{k,z} ≥ 1`
unit-fails. So this contradiction is pure RUP — `JustifyUsingRUP{hints::Disjunctive{owner}}`
(the typed hint is inert in proofs-off mode; the justification is still a bare RUP).

## 2D non-overlap (`Disjunctive2D` / `diffn`)

The same recipe lifts one dimension up to non-overlapping rectangles
(`gcs/constraints/disjunctive_2d/disjunctive_2d.{hh,cc}`). The
declarative OPB is the `diffn` definition: for each pair and axis `d`,
`before_{i,j,d} ⇔ pos_{i,d} + size_{i,d} ≤ pos_{j,d}`, plus a single
**4-way separation clause** per pair
`before_{i,j,x} + before_{j,i,x} + before_{i,j,y} + before_{j,i,y} ≥ 1`.
Again this is all the scaffolding there is; the justifications are the
same `emit_before_pol` shape per axis:

- **Contradiction** (mandatory-box overlap on both axes): four pols —
  one per axis and direction — force all four flags false under the
  reason; the 4-way clause unit-fails in the closing RUP.
- **Bound push** (a forced overlap on one axis pushes the other):
  the pair overlaps on the *forced* axis, so two pols refute both
  forced-axis flags exactly as in the contradiction; the *free* axis
  is then a single-blocker 1D dichotomy — one pol refutes the
  impossible free direction from the pushed rectangle's captured
  bound, one folds the surviving direction onto the target order
  literal. Six pols per push, one step regardless of the blocker's
  size (per-pair pushing means there is never a multi-blocker
  chain). The push target is capped to the rectangle's own domain
  (`cur_hi + 1` / `cur_lo − 1`), and zero-size rectangles are
  skipped on the axis where they span no cells.

Variable sizes work exactly like 1D variable durations (the size term
cancels in the pol; no proof-only `end = pos + size`), non-strict
zero-area escapes (`zw`/`zh`) are pinned false under reason before
the clause is used, and strict-mode zero-area conflicts are caught by
an all-fixed pure-RUP leaf check.

## Reusable ideas

[`cumulative-proof-logging.md`](cumulative-proof-logging.md) ends with
reusable patterns for time-indexed proofs. The disjunctive rewrite
adds a complementary one:

**Justify directly against the declarative encoding.** When the
propagator's inference is expressible as a statement about the
encoding's own reified constraints (here: every `h = 1`, `c = 1`
time-table inference is a two-task ordering statement), skip the
propagator-vocabulary scaffolding entirely: pol the encoding's
reification halves with the operands' bound-literal definition rows so
the integer terms cancel, and let the closing reason-wrapped RUP
unit-propagate over flags and order literals only. The justifications
become search-state-local (all `ProofLevel::Temporary`; nothing
accumulates at `Top` beyond the order-literal atoms every proof mints
anyway), duration-magnitude invariant, and — because hint-free RUP
costs `O(live database)` — everything *else* in the proof verifies
faster too, since no scaffolding sits in the live database.

Cumulative proper genuinely needs its time-indexed `C_t` occupancy
sums — heights make the profile argument irreducibly time-indexed —
which is why this document no longer shares machinery with it: the
right framing is that `Disjunctive` stops inheriting cumulative's
proof *strategy* along with its parameters.

## Open follow-ups

- **Optional tasks (`*_opt`).** A presence flag per task gates the
  encoded pairwise clauses; the pairwise pols would carry the
  presence literals as extra residuals.

<!-- vim: set tw=72 spell spelllang=en : -->
