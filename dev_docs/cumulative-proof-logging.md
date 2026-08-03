# Proof logging for `Cumulative`

This document explains how the `Cumulative` propagator's three inferences
are backed by VeriPB proofs. The technique generalises beyond cumulative
to any constraint whose propagator reasons about a *load profile* over a
set of integer variables with constant coefficients (binPacking,
disjunctive, energetic-time-table extensions).

For the constraint itself — the basic case, the OPB encoding, the
time-table algorithm — read `gcs/constraints/cumulative/cumulative.{hh,cc}`. For
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

In the `JustifyExplicitly{…, ThenRUP::Yes}` emit callback:

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

A single helper `emit_chain_step` in `cumulative/cumulative.cc` emits the four
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

Both ideas are likely to apply to `BinPacking` (#148) when it lands —
see [`frontend-support-matrix.md`](frontend-support-matrix.md).
`Disjunctive` is the instructive counter-example: at `h = 1`,
`capacity = 1` every time-table inference is a two-task ordering
statement, so its proofs skip the time-indexed vocabulary entirely and
justify pairwise against the declarative encoding instead (#495) — see
[`disjunctive-proof-logging.md`](disjunctive-proof-logging.md). The
patterns above are for constraints whose profile argument is
irreducibly time-indexed, which heights make cumulative's.

## Variable durations, heights, and capacity

The basic case (constant `d`/`r`/`b`) generalises to full
`cumulative(var s, var d, var r, var b)` while staying time-table
strength. The propagator reasons over *bounds*: a task's mandatory part
and its guaranteed footprint when placed use `lb(l_i)`, the
possible-active flag window uses `ub(l_i)`, the guaranteed demand uses
`lb(h_i)`, and the overflow/blocked threshold uses `ub(capacity)`. Every
non-constant `d`/`r`/`b` joins the reason. Each extension touches the OPB
and the pol differently:

- **Variable capacity** is nearly free: `C_t` becomes
  `Σ h_i·active_{i,t} − capacity ≤ 0` (the bound moves left as a single
  linear term). The existing pol closes unchanged because the wrapping
  RUP now has `capacity ≤ ub(capacity)` in the reason.

- **Variable heights** linearise the nonlinear product `h_i·active_{i,t}`
  over `cake_pb_cp`'s per-bit contribution flags `cc_k = v[id][i_t_k][cc]`
  (weight `2^k`): `contrib_{i,t} = Σ 2^k·cc_k`, half-reified
  `active ⇒ contrib = h_i` and `¬active ⇒ contrib = 0` (the flags carry no
  domain bound of their own — `cle`/`cz` constrain them, exactly as cake
  does). `C_t` sums `contrib` for variable heights (and `h_i·active` for
  constant ones, so the all-constant proof is byte-identical). The pol pins
  `contrib_{i,t} ≥ lb(h_i)` (coeff 1) instead of an `active = 1` line
  scaled by the constant height; for the pushed task it deposits
  `contrib_j + lb(h_j)·ext_lit ≥ lb(h_j)`. This is **variable × Boolean**,
  which is linear — *not* the multiplication frontier. Because the `cc`
  flags are exactly cake's contribution encoding (to VeriPB they are
  ordinary Booleans, just as the solver's were), the variable-height load
  reasoning **chain-verifies** (`scp_chain_cumulative_var_height_sat`).

- **Variable durations** rewrite `after_{i,t} ⇔ s_i + l_i ≥ t+1`. The
  pinning `after = 1` then needs the *cross-variable* fact
  `s_i + l_i ≥ B`, which RUP cannot derive from the operands' bounds
  alone (the VeriPB linear-combination limit). `after` stays reified on
  `s_i + l_i` directly (matching `cake_pb_cp`, which has no `end`
  variable). To recover a single-variable pin when **both** `s_i` and
  `l_i` vary, a proof-only `end_i = s_i + l_i` is introduced **inside the
  proof** as a conservative extension (`ProofLogger::introduce_bits_of`,
  no OPB encoding: `cake_pb_cp` has no such variable, so keeping it out
  of the OPB is what makes the proof chain-portable) by the install
  initialiser, which also emits, per `(i,t)`, the **bridge lemma**
  `end_i ≥ t+1 → after_{i,t}`:

  ```
  pol  @v[id][i_t][ca][f]  ( ¬after → s+l ≤ t )  +  end_le ( end ≤ s+l )
     = M·after − end_i + t ≥ 0
  ```

  The `s+l` bits cancel exactly, leaving a single-variable-in-`end`
  handle. The pin then materialises `end_i ≥ s_lo + lb(l_i)` with a `pol`
  over `end`'s in-proof `end ≥ s + l` line plus the two operand
  order-literal defining lines, and the `after = 1` RUP closes
  single-variable in `end_i` against the bridge lemma — exactly like the
  constant-duration case. `s_lo` is the chain running bound (lb-push),
  `t − lb(l_j) + 1` (ub-push, i.e. `¬ext_lit`), or `lb(s_i)` (a mandatory
  task). If either operand is constant it folds into the OPB and `after`
  is already single-variable — no `end`, no pol. Because `end`'s
  definition and the bridge lemma both live in the proof, the
  variable-duration encoding **chain-verifies** against `cake_pb_cp`
  (`scp_chain_cumulative_var_duration_sat`).

  **The proxy is signed when a start can precede time 0.** Its range must
  cover `s + l` in full, or `introduce_bits_of`'s redundancy goals are
  unprovable — so its lower bound is `min(0, lb(s_i) + lb(l_i))`, not a
  hard-coded `0`, and it carries a sign bit whenever that is negative.
  This was issue #553: mznc2023 `unison` parks its inactive tasks at
  `s = -1, l = 0`, and with a `0` lower bound the first `le` step's
  proofgoal `s + l ≥ 0` is simply false, so veripb rejected the proof
  there. Zero stays the lower bound otherwise, because `end ≥ 0` is then
  the one boundary pin that is a tautology.

  `introduce_bits_of` grew the signed path to match: the same
  construction shifted by `2^S`, with `¬sign` as the top bit of the
  unsigned sum `BinEnc + 2^S`, so after veripb's literal normalisation
  the emitted lines *are* the unsigned lines of the shifted form. It also
  now derives the form's own bound lines by `pol` over the operands' OPB
  bound rows before the top step, so the two top-step redundancy goals
  discharge by veripb's implication check for any operand shape. Leaning
  on unit propagation for those, as it used to, stalls whenever an
  operand's bit encoding overhangs the target's — a start in `[-17, -16]`
  spanning `[-32, 31]` against a proxy spanning `[-8, 7]`, say — which
  was a latent failure in the unsigned case too.

The `pin_contributor` / `pin_pushed` helpers in
`cumulative/cumulative.cc` package the (a)/(b) emission so the overflow
and both push inferences share one shape across all constant/variable
combinations.

## Inference 4 — the overload check, and the window-energy lemma

Time-tabling only ever looks at one time point at a time. The overload
check (Cloutier & Quimper, CP 2026, rule `(OC')`, strengthened by the
mandatory-part profile to their `(TTOC)`) looks at a *window*: if the
tasks that must run entirely inside `[a, b)` carry more energy than the
window can supply, the constraint is infeasible. It is conflict-only —
no bound moves — and it lives behind `CumulativeRules::overload` /
`::profile_overload`.

### What the propagator computes

For each pair `(a, b)` with `a` an earliest start time and `b` a latest
completion time, let `I(a, b)` be the tasks with `est ≥ a` and
`lct ≤ b`. The conflict condition is

```
    Σ_{i ∈ I(a,b)} p_i·h_i   +   F(a, b)   >   capacity · slots(a, b)
```

where `F(a, b)` is the mandatory-part load inside the window of the
tasks *not* in `I(a, b)`, and `slots(a, b)` counts the time points in
`[a, b)` that some task can occupy at all.

Two things make this quadratic rather than cubic. A task in `I(a, b)`
has its mandatory part inside the window too, so `F` is the window's
total mandatory load minus `I(a, b)`'s — both terms then accumulate as
`b` grows over the tasks sorted by `lct`. And `slots` comes from a
prefix count of the per-task windows, built once in `prepare()`.

`slots` rather than `b − a` because a time point no task can occupy
supplies nothing to the window's tasks — and has no `C_t` line to cite,
since `define_proof_model` writes one only where some task can be
active. Counting it would claim capacity the proof cannot produce.

### The window-energy lemma

The proof needs, for each `i ∈ I(a, b)`, a derived line saying task `i`
really does spend `p_i` time active inside the window:

```
    Σ_{t ∈ [a,b)} active_{i,t}  ≥  p_i .
```

That is `derive_window_energy` in
[`gcs/constraints/innards/window_energy.hh`](../gcs/constraints/innards/window_energy.hh),
and it is the reusable piece: issues #549 and #550 consume it, in its
clipped form (a task only partly inside the window), so it derives the
general bound rather than just the contained case.

Per time point `t`, three `pol` lines:

```
    before_{i,t} \/ [s_i ≥ t+1]                  @v[..][cb][f]  +  Def([s_i < t+1])   , saturate
    after_{i,t}  \/ ~[s_i ≥ t-p+1]               @v[..][ca][f]  +  Def([s_i ≥ t-p+1]) , saturate
    active_{i,t} \/ [s_i ≥ t+1] \/ ~[s_i ≥ t-p+1]        @v[..][cact][f]  +  the two above
```

The first two are order bridges of exactly the shape
`product_justify::add_order_bridge_hints` uses: a flag's `[f]` half and
an order literal's defining row share the `s_i` bits, which cancel, and
saturation turns what is left into a two-literal clause. The third adds
`active`'s `[f]` half — the AND-gate clause
`active \/ ¬before \/ ¬after` — whose `before` and `after` terms cancel
against the bridges, each pair contributing a constant to the degree.

Summing those over `t ∈ [a, b)` gives

```
    Σ active_{i,t}  +  Σ_{v ∈ (a, b]} [s_i ≥ v]  +  Σ_{u ∈ (a-p, b-p]} ~[s_i ≥ u]   ≥   b − a
```

and this is where the telescoping happens: every value in both ranges
contributes `[s_i ≥ w]` and its negation, which is a constant, so it
cancels inside the pol. What survives is `min(p, b−a)` literals at each
end, and each is resolved against the start bounds:

- `~[s_i ≥ u]` with `u ≤ lb(s_i)`: RUP `[s_i ≥ u]` under the reason —
  the terms cancel and the degree is unchanged;
- `[s_i ≥ v]` with `v > ub(s_i)`: RUP `[s_i < v]` under the reason —
  likewise;
- anything the bounds do not decide: push the literal itself onto the
  `pol` stack (VeriPB reads a bare literal as the trivial constraint
  `lit ≥ 0`), which cancels the term at the cost of one unit of the
  bound.

So a fully contained task yields exactly `p_i`, and a task hanging out
of the window yields its guaranteed overlap. `window_energy_bound()`
computes the same number without emitting anything, and the emitter
cross-checks against it: a disagreement would otherwise only show up as
a rejected proof much later.

### The conflict

One `pol`: every `C_t` for `t ∈ [a, b)` that exists, each contained
task's window-energy line scaled by its height, and — for `(TTOC)` —
the outside tasks' compulsory contributions via the existing
`pin_contributor`. Each contained task's `active` terms cancel exactly
against its terms in the capacity lines, and what is left is a
constraint with nothing but negative coefficients on the left and a
positive right hand side. The framework's wrapping RUP closes it.

### Restrictions, and why they are only weakenings

The energy set takes only tasks with a constant length and height (a
variable height enters `C_t` as the bit-linearised `contrib`, not as
`h·active`, so the cancellation would not be exact) and a start that is
a plain variable with an order encoding (the bridges need order
literals; a `{0,1}` domain is direct-only encoded, and a view's atoms
would need deview-mode arithmetic). The whole check is skipped when the
capacity is a variable: a `(b−a)·capacity` term would survive into the
conflict line for the wrapping RUP to dispose of over the capacity's
bits, which it cannot do in general.

None of these lose soundness or solutions: a task the energy set will
not take still counts through `F(a, b)`, and a check not made is a
conflict found later.

## Derived Cumulatives: an implied constraint that adds nothing to the model

A presolver that spots an implied `Cumulative` — a strengthened capacity, a
lifted resource, a disjunctive clique — needs its propagator's inferences to be
justifiable, and the obvious way to do that is the wrong one. Writing the
implied constraint's rows into the OPB changes the statement being verified:
VeriPB would check the proof against a model containing an assertion nobody
proved, accept it, and mean nothing by it. The whole point of #541's plan is
that everything inferred enters as a *derivation*.

`install_derived_cumulative`
([`derived_cumulative.hh`](../gcs/constraints/cumulative/derived_cumulative.hh))
is the mechanism. A derived Cumulative covers a donor's tasks, with its own
heights and capacity, and creates no flags and no rows of its own: it pins the
donor's flags, and its per-time capacity rows are derived in the proof from the
donor's by a recipe the caller supplies.

### Reaching the donor

Two halves, both following the discipline #603 set for citing another
constraint's model output — the constraint *publishes* what is citable, and the
tracker says whether it is there:

| what | published as | resolved by |
|---|---|---|
| `Σ h_i·active_{i,t} ≤ C` for a time `t` | `ConstraintProofModelData<Cumulative>::capacity_row_role(t)` | `NamesAndIDsTracker::constraint_row_label` |
| the `before` / `after` / `active` flags for `(i, t)` | `...::before_flag_key(i, t)` and friends | `NamesAndIDsTracker::find_proof_flag_values` |

The flag half is new. A flag's name is a pure function of
`(ConstraintID, values, annotation)` — the same function
`create_proof_flag_values` applies — so the tracker can answer "did a flag go
out under this key?" exactly as it answers the question for rows. Holding the
returned `ProofFlag` is then the permission to cite its reification rows by
name, as the constraint that made it does; those rows live in the `v[...]`
namespace, which `claim_constraint_row_labels` deliberately leaves out of the
row-label set.

Reconstructing either name as a string would work and is what not to do: the
citer would be hard-coding another constraint's naming scheme, with nothing to
tell the constraint's author they had broken somebody.

The lookup also does the windowing check for free. The donor's flags exist only
over the windows it encoded, so a derived constraint whose tasks run longer asks
for a key that has no flag — and declines to install, rather than inventing one
and finding out at verification time.

### Where the derivation happens

Inline, in `install_derived_cumulative`, at `ProofLevel::Top` — not from an
`install_initialiser`. Initialisers have already run by the time a presolver is
called (`solve.cc` runs them, then the presolvers), so one installed from there
never fires, and the propagator would spend the whole search citing rows that
were never written. Top level is what makes the rows survive backtracking,
which the propagator needs at every node.

### The recipe

```cpp
std::function<auto(ProofLogger &, ProofLine donor_row, Integer t)->ProofLine>
```

Called once per time point with the donor's row, returning the derived one. It
has a `ProofLogger` and no `ProofModel`, so a recipe cannot write to the OPB
even by mistake. The two in `derived_cumulative_test` are the shapes to copy: a
one-line `pol` that copies the donor's row, and
[subset-sum strengthening](subset-sum-strengthening.md) over the row's own
terms, which takes its divisibility fast path and rounds a capacity of eight
down to six when every height is a multiple of three.

That second one is worth a note, because it is easy to expect the wrong thing
from it. Rounding the capacity down by integrality is **invisible to
time-tabling**: a load is a sum of heights, so it clears eight exactly when it
clears six. What it changes is the *energy* argument, where a window's supply is
the capacity times its width, and that is not a multiple of three. Seven
unit-length tasks of height three need 21 units in `[0, 3)`, which eight
supplies and six does not.

### Multi-donor, for later

Issues #548 and #549 infer a Cumulative over tasks drawn from *several* donors,
each with its own flag copies for the same `(task, time)` semantics. Two ways to
make one derivation speak about all of them:

1. **Bridge lemmas.** Pick one donor's flags as canonical and derive
   `active^{(r)}_{i,t} ↔ active^{(1)}_{i,t}` per `(i, t)`, by `pol` over the two
   reification halves — the start variable's bits cancel, exactly as in the
   window-energy bridges above. O(tasks × times) extra Top lines per extra
   donor, and it needs no new API: both donors' rows are citable by name.
2. **Rewrite each donor's row.** One `pol` pass per row, over the flag-defining
   rows directly, landing on the canonical flags without ever stating the
   bridge.

Neither is implemented here. The first is the safer starting point (each lemma
is checkable on its own); the second is smaller if it works. Whichever lands
should measure the proof size, since that is the whole difference between them.

## Open follow-ups

- **Edge-finding.** A *set* of tasks blocks an interval, not a single
  task at a single time. The pol arithmetic would need to sum across
  the set; the chain idea no longer fits directly.
- **Energetic reasoning.** The window-energy lemma above is the first
  piece of it: horizontally elastic and knapsack-augmented checking
  (#550) build on the clipped form, and the lifted-constraint
  presolvers (#549) on the contained one.
- **Variable lengths, heights and capacity in the energy set.** Staged
  deliberately; the extensions are sketched in #542.
The current scaffolding (`_before_flags`, `_after_flags`,
`_active_flags`, `_contrib_flags`, `_end`, `_capacity_lines`) is
enough for time-table-strength reasoning over variable `d`/`r`/`b` and not
much more. Variable durations and variable heights both chain-verify
against `cake_pb_cp`; the only remaining divergence is the start/size bit
*variable* encoding (#358), which is orthogonal.

<!-- vim: set tw=72 spell spelllang=en : -->
