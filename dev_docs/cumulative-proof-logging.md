# Proof logging for `Cumulative`

This document explains how the `Cumulative` propagator's three inferences
are backed by VeriPB proofs. The technique generalises beyond cumulative
to any constraint whose propagator reasons about a *load profile* over a
set of integer variables with constant coefficients (binPacking,
disjunctive, energetic-time-table extensions).

For the constraint itself — the basic case, the OPB encoding, the
time-table algorithm — read `gcs/constraints/cumulative.{hh,cc}`. For
the broader proof-logging framework (justifications, the OPB scaffold,
`emit_rup_proof_line_under_reason`), read [`constraints.md`](constraints.md).

## What's hard about it

The TT propagator on its own is textbook. The proof-logging is not: the
inference "task `j` cannot start at any `s ∈ [cur_lb, new_lb−1]`" hinges
on a *disjunctive* fact

```
∀ blocked t.    s_j > t   ∨   s_j ≤ t − l_j
```

— and that disjunction is exactly the shape memory flags as a hazard
(`X ∉ [a, b]` as one Boolean breaks RUP-closure under backtrack-from-guess).
So we can't reify the blocked-time fact as a single flag.

The way out is *chained bound pushes under extended reason*: at each
blocked time `t_i` in turn, we use the lower-bound work the previous
chain step did to close the disjunction's lower branch, leaving only
the upper branch `s_j > t_i` to derive.

## The OPB scaffolding (recap)

For every task `i` and every time `t` in its possible-active window,
`define_proof_model` emits three fully-reified flags:

| Flag                  | Reification                                                  |
|-----------------------|--------------------------------------------------------------|
| `before_{i,t}`        | `s_i ≤ t`                                                    |
| `after_{i,t}`         | `s_i ≥ t − l_i + 1`                                          |
| `active_{i,t}`        | `before_{i,t} ∧ after_{i,t}` (AND-gate over the two)         |

and, for each `t` in the union of possible-active windows, a single
time-table constraint

```
C_t :    Σ_i  h_i · active_{i,t}   ≤   capacity .
```

All three inferences below cite these flags and `C_t` lines by handle —
the `Cumulative` class stores them as private members (`_before_flags`,
`_after_flags`, `_active_flags`, `_capacity_lines`) so `install_propagators`
can capture them in the propagator closure.

## Inference 1 — `mand_load[t] > capacity ⇒ contradiction`

### Semantics

For each task `i`, the *mandatory part* is the half-open interval
`[lst_i, eet_i) = [ub(s_i), lb(s_i) + l_i)`. It's non-empty iff
`l_i > ub(s_i) − lb(s_i)`. Any feasible `s_i` puts the task active
at every `t ∈ [lst_i, eet_i)`, so `active_{i,t}` is forced to 1 by
unit propagation from the bound literals `s_i ≥ lb(s_i)` and
`s_i ≤ ub(s_i)`.

If `mand_load[t] = Σ_{i mandatory at t} h_i > capacity`, then `C_t`
can't be satisfied: the mandatory tasks alone already overflow.

### Proof emission

In the `JustifyExplicitlyThenRUP` callback:

1. For each task `i` mandatory at `t`, emit three RUPs under the
   bounds reason:
   ```cpp
   rup before_{i,t} >= 1   ;
   rup after_{i,t}  >= 1   ;
   rup active_{i,t} >= 1   ;
   ```
   The intermediate `before`/`after` lines are necessary because
   VeriPB UP cannot chase through the AND-gate of `active`'s
   reverse-half in one step.

2. Emit a single `pol`:
   ```
   pol  C_t  L_1 h_1 * +  L_2 h_2 * +  ...  ;
   ```
   where each `L_i` is the line ID returned by the active-pinning
   RUP. The result, evaluated against the bounds reason, is a
   trivially-false PB constraint (max LHS `< Σ h_i − capacity + Σ h_j`
   for non-mandatory `j`). The framework's wrapping RUP step closes
   the contradiction.

This is the "vanilla" shape: one blocked time, no chaining, no
extended reasons. The other two inferences are built on top of it.

## Inferences 2 & 3 — bound pushes

### Setup

After the mandatory-overflow check passes, the propagator scans, for
each unfixed task `j` and each candidate start `s`, whether
*"placing `j` at `s` is feasible"*. Concretely, `fits_at(s)` is false
iff there's some `t ∈ [s, s + l_j − 1]` with

```
mand_load[t] − h_j · [t ∈ mand_j] + h_j   >   capacity .
```

Call such a `t` **blocked for `j`**. The propagator sweeps `s` upward
(for `lb`-push) or downward (for `ub`-push) until `fits_at(s)` holds,
and pushes `s_j`'s bound to that fitting value.

For each blocked `t`, the underlying fact is

```
s_j ∉ [t − l_j + 1, t]      ⇔      s_j > t   ∨   s_j ≤ t − l_j .
```

Both branches are needed; neither alone gets us anywhere generic.

### The chain idea

Walk the bound one blocked-time at a time. At step `i`, we hold a
*running bound* `B_{i−1}` already established by previous steps
(initially the original bound from the reason). For the step's `t_i`:

- If `t_i − l_j + 1 ≤ B_{i−1}` (the *precondition*), then the lower
  branch `s_j ≤ t_i − l_j` is incompatible with `s_j ≥ B_{i−1}`,
  closing it. The remaining branch gives `s_j ≥ t_i + 1`.
- Symmetrically for `ub`-push, with `B_{i−1}` an upper bound and the
  precondition `t_i ≥ B_{i−1}` closing the *upper* branch
  `s_j ≥ t_i + 1`, leaving the lower one `s_j ≤ t_i − l_j`.

So the proof advances the bound exactly one blocked-time per step,
threading the previous step's intermediate fact into the next step's
preconditions. The chain terminates at `new_lb` (or `new_ub`).

### Step structure (shared)

The per-step proof emission is the same shape for both `lb`-push and
`ub`-push, with only the *extended-reason literal* and the *intermediate
fact* differing:

| Push     | Extended literal `ext_lit`            | Intermediate fact deposited |
|----------|---------------------------------------|------------------------------|
| `lb`     | `s_j ≥ t + 1`                          | same                         |
| `ub`     | `s_j < t − l_j + 1` (= `s_j ≤ t − l_j`) | same                         |

`ext_lit` is the *negation* of the literal we want to add to the
reason ("task `j` is active at `t` given its bounds-so-far") — it's
what appears as an extra disjunct in PB-form reified lines.

A single helper `emit_chain_step` in `cumulative.cc` emits the four
sub-pieces below, parameterised by `j`, `t`, the contributing tasks,
`ext_lit`, and whether this is the last step.

**(a) Mandatory tasks at `t` (other than `j`):** the same three RUPs
as inference 1, under the bounds reason. Each pins `active_{i,t} = 1`.

**(b) Task `j` itself, under the EXTENDED reason `{bounds ∪ ¬ext_lit}`:**
three RUPs of the same shape, but each line has `ext_lit` appended as
an extra disjunct:

```cpp
rup  1·before_{j,t}  + 1·ext_lit  >= 1  [reified under bounds reason] ;
rup  1·after_{j,t}   + 1·ext_lit  >= 1  ;
rup  1·active_{j,t}  + 1·ext_lit  >= 1  ;
```

PB-form: "if the bounds reason holds AND `¬ext_lit` holds, then the
flag is 1". VeriPB checks each RUP by negating the goal — including
`ext_lit = 0` — which together with the bounds reason brings it back
into the same UP chain as inference 1.

**(c) A `pol` combining `C_t` with the scaled `active = 1` lines for
every task in `(M_t ∪ {j})`:**

```
pol  C_t  L_1 h_1 * +  ...  L_k h_k * +  L_j h_j * +  ;
```

Critically, the `j`-line carries the `ext_lit` baggage from step (b),
so after cancellation against `C_t` the `pol` result is dominated by
the term `(M_t + h_j − capacity) · ext_lit` plus negated-reason terms.
Under the bounds reason, the negated-reason terms vanish, leaving a
unit-strength constraint that forces `ext_lit = 1` — i.e., the new
bound.

**(d) If this isn't the last step**, deposit `ext_lit = 1` as an
explicit RUP under reason. This is the *intermediate fact* that
subsequent steps' (b)-lines depend on for their preconditions to
close.

### Why this works mechanically

The pol-derived constraint at step `i` has the form
```
(M_{t_i} + h_j) · ext_lit + Σ h_? · ¬active_{l,t_i}  +  K · [¬reason-block]  ≥  S
```
with `S − max(LHS_under_reason) > 0`. Under the bounds reason,
`[¬reason-block] = 0`. So:
- If `step + 1 < chain.size()`: a separate RUP for `ext_lit ≥ 1`
  under reason closes via UP (`ext_lit = 0` would force the LHS
  below `S`).
- If this is the last step: the framework's wrapping RUP for the
  inference negates the target literal (which is exactly `ext_lit`,
  since `ext_lit` *is* the new-bound literal), gets `ext_lit = 0`
  under reason, and the same pol-derived constraint produces the
  conflict via UP.

### Chain construction (asymmetric)

The two chains pick different `t`s at each step to advance as far as
possible:

| Push    | Window scanned                                | Pick                  |
|---------|-----------------------------------------------|-----------------------|
| `lb`    | `[B_{i−1}, B_{i−1} + l_j − 1]`                | largest blocked `t`   |
| `ub`    | `[U_{i−1}, U_{i−1} + l_j − 1]`                | smallest blocked `t`  |

(Both windows are the same shape — the active window of `j` placed at
the running boundary — but "largest first" / "smallest first" matches
which end of `s_j` we're tightening.)

### Edge case: `j` is itself mandatory at some `t`

The blocked-time condition `mand_load[t] + h_j > capacity` requires
`t ∉ mand_j` (otherwise it reduces to `mand_load[t] > capacity`, which
inference 1 would already have caught). So blocked `t`'s for `j`
never include `j`'s own mandatory part; the contributing list never
mentions `j`; no aliasing in the pol.

## The general pattern

Two reusable ideas crystallise out of the above:

1. **`pol` over `active = 1` reified flags.** When a constraint
   ships a per-time-point sum `Σ h_i · active_{i,t} ≤ capacity` and
   the propagator detects "the load already exceeds capacity here",
   the proof is a `pol` summing scaled unit-active lines into the
   time-table constraint. VeriPB cannot do this via RUP alone:
   unit-propagating the flags to 1 is fine, but combining their
   *coefficients* with the time-table constraint's coefficients is a
   linear arithmetic step that RUP's UP loop won't perform. `pol`
   materialises the coefficient-sum directly. See
   [`constraints.md`](constraints.md#when-rup-isnt-enough-explicit-pol)
   for the generic shape.

2. **Extended-reason pinning for hypothetical literals.** When the
   inference depends on a fact that's *not* in the reason (here:
   "task `j` is also active at `t`, assuming `s_j` is in its active
   window"), pin that fact in the proof database as
   `flag + ext_lit ≥ 1` (reified under the actual reason). VeriPB
   treats it as "given the reason and `¬ext_lit`, the flag holds";
   the closing RUP supplies `¬ext_lit` from its negated goal.

Both ideas are likely to apply to `Disjunctive` (#146) and
`BinPacking` (#148) when those land — see
[`frontend-support-matrix.md`](frontend-support-matrix.md).

## Open follow-ups

- **Variable lengths / heights / capacity.** Out of scope for stage 1.
  Adding them needs new reifications for `before` / `after` over
  variable expressions; the chain logic should carry through.
- **Edge-finding.** A *set* of tasks blocks an interval, not a single
  task at a single time. The pol arithmetic would need to sum across
  the set; the chain idea no longer fits directly.
- **Energetic reasoning.** Even more set-of-tasks, set-of-intervals.
  No clean OPB witness exists in the current encoding; the proof
  scaffold would need extra auxiliary flags.

The current scaffolding (`_before_flags`, `_after_flags`,
`_active_flags`, `_capacity_lines`) is enough for time-table-strength
reasoning and not much more.

<!-- vim: set tw=72 spell spelllang=en : -->
