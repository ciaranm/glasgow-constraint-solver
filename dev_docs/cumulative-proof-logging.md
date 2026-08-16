#Proof logging for `Cumulative`

This document explains how the `Cumulative` propagator's three inferences are backed by VeriPB proofs
    .The technique generalises beyond cumulative to any constraint whose propagator reasons about a *load profile *
        over a set of integer variables with constant
        coefficients(binPacking, disjunctive, energetic - time - table extensions)
    .

    For the constraint itself — the basic case,
    the OPB encoding,
    the time - table algorithm — read `gcs / constraints / cumulative / cumulative.{hh, cc}`.For the broader proof
    - logging framework(justifications, the OPB scaffold,
`emit_rup_proof_line_under_reason`),
    read[`constraints.md`](constraints.md)
        .

    ##What is and is not covered

    Worth stating plainly,
    because "we can certify cumulative scheduling" is an easy thing to write and a wrong thing to claim.Certified here:
**time - tabling **(the overflow check and both bound pushes), the ** overload check **and the window - energy lemma under it,
    **derived - constraint inference **(capacity strengthening, conflict cliques, lifted cover cuts),
    and**makespan lower bounds ** — over optional tasks and over variable durations,
    heights and capacities.

    Also certified,
    off by default : **edge - finding **
    , in both directions
    , under
`CumulativeRules::edge_finding`
    , **time - table extended edge - finding **(TTEF)under `CumulativeRules::time_table_edge_finding`
    , and**not -first / not -last *
    *under `CumulativeRules::not_first_not_last`.See the sections below.

     Not here : **KAOC
    * *(#550)
    , and energetic reasoning in general.The claim to make is "a wide range of commonly used techniques"
    , not completeness.The Open follow -
        ups section at the end says what each would take
            .

        ##What's hard about it

        The TT propagator on its own is textbook.The proof
        -
        logging is not
    : the inference "task `j` cannot start at any `s ∈ [cur_lb, new_lb−1]`" hinges on a
      *
      disjunctive *
      fact

```
∀ blocked t.s_j
    > t   ∨ s_j ≤ t − l_j
```

— and that disjunction is exactly the shape memory flags as a hazard(`X ∉ [a, b]` as one Boolean breaks RUP - closure under backtrack - from - guess)
          .So we can't reify the blocked-time fact as a single flag.

      The way out is * chained bound pushes under extended reason * : at each blocked time `t_i` in turn
    , we use the lower - bound work the previous chain step did to close the disjunction's lower branch, leaving only the upper branch `s_j
    > t_i` to derive.

      ##The OPB scaffolding(recap)

For every task `i` and every time `t` in its possible - active window,
`define_proof_model` emits three fully - reified flags :

    | Flag | Reification | | -- -- -- -- -- -- -- -- -- -- -- -|
    -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --| | `before_
{
    i, t
}
` | `s_i ≤ t` | | `after_
{
    i, t
}
` | `s_i ≥ t − l_i + 1` | | `active_
{
    i, t
}
` | `before_
{
    i, t
}
∧ after_
{
    i, t
}` (AND-gate over the two)         |

and, for each `t` in the union of possible-active windows, a single
time-table constraint

```
C_t :    Σ_i  h_i · active_
{
    i, t
}   ≤   capacity .
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
at every `t ∈ [lst_i, eet_i)`, so `active_{
    i, t}` is forced to 1 by
unit propagation from the bound literals `s_i ≥ lb(s_i)` and
`s_i ≤ ub(s_i)`.

If `mand_load[t] = Σ_{i mandatory at t} h_i > capacity`, then `C_t`
can't be satisfied: the mandatory tasks alone already overflow.

### Proof emission

In the `JustifyExplicitly{
    …, ThenRUP::Yes}` emit callback:

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
*running bound* `B_{
    i−1}` already established by previous steps
(initially the original bound from the reason). For the step's `t_i`:

- If `t_i − l_j + 1 ≤ B_{
    i−1}` (the *precondition*), then the lower
  branch `s_j ≤ t_i − l_j` is incompatible with `s_j ≥ B_{
    i−1}`,
  closing it. The remaining branch gives `s_j ≥ t_i + 1`.
- Symmetrically for `ub`-push, with `B_{
    i−1}` an upper bound and the
  precondition `t_i ≥ B_{
    i−1}` closing the *upper* branch
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

**(b) Task `j` itself, under the EXTENDED reason `{
    bounds ∪ ¬ext_lit}`:**
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
   ships a per-time-point sum `Σ h_i · active_{
    i, t} ≤ capacity` and
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
  `Σ h_i·active_{
    i, t} − capacity ≤ 0` (the bound moves left as a single
  linear term). The existing pol closes unchanged because the wrapping
  RUP now has `capacity ≤ ub(capacity)` in the reason.

- **Variable heights** linearise the nonlinear product `h_i·active_{
    i, t}`
  over `cake_pb_cp`'s per-bit contribution flags `cc_k = v[id][i_t_k][cc]`
  (weight `2^k`): `contrib_{i,t} = Σ 2^k·cc_k`, half-reified
  `active ⇒ contrib = h_i` and `¬active ⇒ contrib = 0` (the flags carry no
  domain bound of their own — `cle`/`cz` constrain them, exactly as cake
  does). `C_t` sums `contrib` for variable heights (and `h_i·active` for
  constant ones, so the all-constant proof is byte-identical). The pol pins
  `contrib_{
    i, t} ≥ lb(h_i)` (coeff 1) instead of an `active = 1` line
  scaled by the constant height; for the pushed task it deposits
  `contrib_j + lb(h_j)·ext_lit ≥ lb(h_j)`. This is **variable × Boolean**,
  which is linear — *not* the multiplication frontier. Because the `cc`
  flags are exactly cake's contribution encoding (to VeriPB they are
  ordinary Booleans, just as the solver's were), the variable-height load
  reasoning **chain-verifies** (`scp_chain_cumulative_var_height_sat`).

- **Variable durations** rewrite `after_{
    i, t} ⇔ s_i + l_i ≥ t+1`. The
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
  `end_i ≥ t+1 → after_{
    i, t}`:

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
    Σ_{t ∈ [a,b)} active_{
    i, t}  ≥  p_i .
```

That is `derive_window_energy` in
[`gcs/constraints/innards/window_energy.hh`](../gcs/constraints/innards/window_energy.hh),
and it is the reusable piece: issues #549 and #550 consume it, in its
clipped form (a task only partly inside the window), so it derives the
general bound rather than just the contained case.

Per time point `t`, three `pol` lines:

```
    before_{
    i, t} \/ [s_i ≥ t+1]                  @v[..][cb][f]  +  Def([s_i < t+1])   , saturate
    after_{
    i, t}  \/ ~[s_i ≥ t-p+1]               @v[..][ca][f]  +  Def([s_i ≥ t-p+1]) , saturate
    active_{
    i, t} \/ [s_i ≥ t+1] \/ ~[s_i ≥ t-p+1]        @v[..][cact][f]  +  the two above
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
| `Σ h_i·active_{
    i, t} ≤ C` for a time `t` | `ConstraintProofModelData<Cumulative>::capacity_row_role(t)` | `NamesAndIDsTracker::constraint_row_label` |
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
`install_initialiser`. That was originally forced: initialisers had already run
by the time a presolver was called, so one installed from there never fired and
the propagator spent the search citing rows that were never written. #658 fixed
that ordering, and this stays inline anyway for a better reason — the caller is
told whether the constraint could be set up at all, and that answer has to be
known while not installing the propagator is still an option.

Top level is what makes the rows survive backtracking, which the propagator
needs at every node.

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

The real presolver built on that recipe is `CumulativeStrengthening` — see
[cumulative-strengthening.md](cumulative-strengthening.md), which turns the
invisibility above into an automated soundness tripwire rather than a caveat.

### Multi-donor

Issues #548 and #549 infer a Cumulative over tasks drawn from *several* donors,
each with its own flag copies for the same `(task, time)` semantics. Two things
make that work, and both are now here.

**The spec is per task.** `DerivedCumulativeTask` names the donor and the
position within it for each task separately, so a constraint whose members come
from different donors needs nothing special — `derived_cumulative_tasks_from`
builds the all-of-one-donor case, which is still the common one. `row_donors`
is separate from the tasks' donors, because a pairwise conflict is witnessed by
whichever resource cannot hold both tasks, and that need not be where either
task's flags are taken from. The recipe is handed the rows those donors wrote
for that time point, by donor, and may return nullopt to decline a time point it
cannot derive — which declines the whole constraint, since the propagator cites
a row at every time it covers.

**The bridge is one `pol`.** `recover_flag_bridge`
([`flag_bridge.hh`](../gcs/innards/proofs/flag_bridge.hh)) turns one donor's
flag into another's. A fully reified flag emits `g → ineq` under `[r]` and
`ineq → g` under `[f]`; adding one flag's `[r]` to another's `[f]` puts the two
inequalities in with opposite signs, so their terms cancel — every bit of every
variable they mention — and saturation leaves the two-literal clause. The
sketch this replaces assumed order literals and bit reasoning would be needed;
they are not.

`active ⇔ before ∧ after` needs one more step, since two `active` flags are
reified over *different* flags and so do not cancel against each other.
`recover_conjunction_flag_bridge` bridges the conjuncts first, after which each
appears with both signs and drops out. Three `pol`s per `(task, time, donor
pair)`.

What the derivation needs is not that the conditions match but that the
constants leave something behind: for `e ≤ p` and `e ≤ q` the sum has degree
`q − p + 1`, so it goes through exactly when the implication is true. Identical
conditions are the case this is for; a weaker target also works, a stronger one
correctly does not.

Two traps, both guarded. The halves are labelled from the flag's **full PB
rendering**, not `name_of`, whose plain-flag form is the bare stem — the
window-energy bridges get away with `name_of` only because `Cumulative`'s flags
are values-named. And a negated flag has no halves of its own, so bridging one
is refused rather than silently naming the positive flag's rows.

`recover_bridged_row` composes the bridges with the row itself, which is what
[#549's lifted cover cuts](inferred-cumulative.md) need: weaken a donor's row
down to the members of a cut, add each member's bridge as many times as its
coefficient, and the same inequality comes back over another donor's flags. The
result is pinned, since a bridge pointing the wrong way is otherwise a mistake
that only shows up thousands of lines later.

Proof size is the thing to watch: the bridges are O(tasks × times) lines per
extra donor. #548's are emitted at `Top`, where none of them ever dies, which is
[#666](https://github.com/ciaranm/glasgow-constraint-solver/issues/666). A recipe
that raises the level around its own working before bridging does not have that
problem --- `InferredCumulative`'s does, and only the row it hands back
survives.
## Optional tasks (issue #543)

The optional-task constructor gives each task a `{0, 1}` presence
variable, and an absent task consumes nothing. That is the *one*
sanctioned change to the OPB in the whole #541 plan, and it is a single
extra conjunct:

```
active_{
    i, t}  ⇔  before_{
    i, t} ∧ after_{
    i, t} ∧ (presences[i] = 1)
```

`C_t` keeps its shape. A `{0, 1}` variable is direct-only encoded as one
PB literal (`i[name][b0]`, with `= 0` its negation — see
[`variable-encodings.md`](variable-encodings.md)), so the three-way AND
costs one term in the same two reification halves, and nothing else in
the encoding has to know the task is optional.

A task posted with the *constant* 1 as its presence keeps the two-way
AND, and one posted with the constant 0 is dropped from the constraint
altogether. Only constants resolve away like this: a variable that
happens to be fixed when `prepare()` runs keeps its conjunct, because the
OPB has to say what it means without appealing to a domain the OPB does
not record. `cumulative_optional_test enumerate` asserts the degeneracy
by diffing the two forms' OPB constraint lines.

### Presence in reasons

Presence enters a reason as an explicit `presences[i] = 1` literal per
task known present, *not* by putting the variable in the `generic_reason`
scope. An undecided presence has no fact to record — a task not known
present is simply not in the profile, and staying out of it is monotone
as the domain shrinks — and `generic_reason` would otherwise contribute
the pair of trivial bounds `0 ≤ p ≤ 1`, which says nothing and costs an
order atom on a variable whose whole encoding is one literal.

### Presence falsification

The new inference is the mirror image of an lb-push: when an undecided
task has no start position left that fits under the profile, its presence
is 0. The proof is the lb-push chain run over the task's *whole* domain
with `present_j = 0` carried as an extra disjunct on every line, so each
step reads "either `j` starts later than this, or `j` is not here at
all". `ExtLits` generalises `emit_chain_step`'s single extension literal
to the (at most two) disjuncts this needs.

The last step drops the start-side disjunct. Its blocked time is at or
beyond `ub(s_j)` — that is what makes it the last, since the chain stops
when the running bound passes `ub(s_j)` — so `before_{
    j, t}` follows from
the task's own upper bound in the reason, and the proof never asks for an
order literal above the domain, which need not exist.

### Why the chain is load-bearing, and what a mutation can catch

The wrapping RUP (`ThenRUP::Yes`) cannot close on its own: the order
atoms `[s_j ≥ v]` for the interior of the domain are created lazily, and
it is the chain that creates them. The `EmitNothing` mutation is the
control for exactly this, and VeriPB rejects it.

What VeriPB will *not* reject is a mutation that merely shortens the
chain — omitting a step, or stopping one step early. This is worth
understanding, because it looks like a gap and is not one. Once the chain
has narrowed `s_j` far enough, the reason context extended with
`present_j = 1` is *contradictory*, and every subsequent RUP under it is
vacuously valid. A shortened chain is therefore still a sound (if
differently shaped) derivation, and VeriPB is right to accept it. This is
the same trap as #656's contradictory micro-model, one level in: there
the whole OPB was unsatisfiable, here it is the reason context.

So the mutations that bite are the ones producing a statement that is
*not* implied:

- `WrongTask` — carry a different optional task's presence literal
  through the chain. The pinned activity is then about a task nothing has
  cornered, and the pin fails to RUP.
- `ClaimOneTooFar` — fire on the twin instance where exactly one
  placement still fits. The conclusion is wrong rather than the route to
  it, the chain runs out of blocked times, and the wrapping RUP has
  nothing to close on. This is the plan's "bound + 1 must fail" check for
  this rule.

The general lesson for the rest of #541: for a *conflict-shaped* rule —
one whose content is "this assignment is impossible" — corrupting the
route is not a test, because the destination makes every route valid.
Corrupt the destination.

### Interaction with the overload check

The overload check (issue 01, above) is guarded the same way the profile
is, and it has to be: its energy set counts each contained task's
`length x height` as *guaranteed*, which an optional task's is not until
its presence is fixed to 1. Counting an undecided task's energy would
manufacture a conflict that is not there. So `propagate_cumulative`
filters the candidate list by the same `is_present`. That one is
load-bearing and cheap to check: remove it and the enumeration tests lose
solutions immediately, because two optional unit-height tasks over one
capacity-1 window carry enough combined "energy" to overload it when in
truth both may simply be absent.

The (TTOC) strengthening's pinned outside-the-window tasks are filtered
too, and that one is *not* checkable, which is worth knowing before
someone deletes it as untested. Pinning a task the arithmetic never
counted would be accepted by VeriPB, not rejected: by the point the pins
are emitted the reason context is contradictory, so every RUP under it is
vacuously valid --- the same phenomenon as the mutation finding below,
one rule over. The filter keeps the `pol`'s inputs matched to the
arithmetic that decided the conflict, and it has to be argued rather than
tested.

Both then need the presence literals in the reason, which they get for
free: `reason_with_presence()` carries every known-present task's
literal, and the energy set is a subset of the profile's tasks. The
eligibility resolved once in `prepare_cumulative_overload_check` is
unchanged --- it cannot know a runtime presence, so the filtering belongs
at the point of use.

Falsifying a presence *by* an energy argument, rather than by the
profile, is issue 09's extension and is not here.

### Deriving over a donor that is not all constants

Everything a derived constraint's recipe does is an argument about rows of the
form `Σ h_i·active_{
    i, t} ≤ C`, and a donor only writes those when its arguments
are constants. `CumulativeDonorView`
([`donor_view.hh`](../gcs/constraints/cumulative/donor_view.hh)) is what reduces
a donor to the part of itself that is, and the reduction is per **task**: one
task with a variable height no longer costs a whole donor its strengthening, it
costs that task its term.

A variable **length** is not a reduction at all, and the difference is worth
being clear about. No length appears in a capacity row, so the rows are the same
rows and a recipe reads them identically. What a variable length costs is the
`after` pin, and that is bought back rather than given up — see *A task whose
length is a variable*, below.

A variable **height** is a restriction, but a payable one — see *A task whose
height is a variable*, below. What is left as a genuine set-aside is a height
that cannot be argued about at all: a view, or one whose lower bound is zero.

`recover_constant_argument_row` does the proof half, and it is one `pol`:

- **A set-aside task** is weakened out of the row with `w`. For a constant
  height that is one `w` on its activity flag; for a variable height the row's
  terms for it are the bits of the linearised contribution, so every one of them
  goes, which is what
  `ConstraintProofModelData<Cumulative>::contribution_flag_key` is published for.
  How many bits there are is not published: ask for bit zero, one, two and so on
  until the tracker has none, the same "is it there?" question a citer asks of
  every other key.

  Only the variable-height half is a tripwire. Remove the constant-height `w` and
  every proof still verifies, because a recipe pins what it returns with an `ia`
  and dropping a non-negative term from the left of a `≤` is a valid implication
  — the pin weakens it away for free. It is written anyway so that the row a
  recipe argues over is the row it claims. **Do not delete it as untested.**

- **A variable capacity** is replaced by a number. The row has `− capacity` on
  its left, so the bits have to cancel against something, and the something is
  the *order literal* for the bound the capacity has now:
  `need_pol_item_defining_literal` hands back the definition of
  `[capacity ≥ b+1]`, whose bits cancel exactly and which leaves the atom behind
  with a coefficient of its own. Going through the literal rather than citing the
  capacity's OPB bound row is what lets this use the bound the capacity has *now*
  — a presolver reads a live `State`, and the declared bound is a weaker number
  the moment anything has tightened it.

  What is left is paid off in the same `pol`, by the unit line saying the atom is
  false, added as many times as its coefficient. That coefficient is
  `(everything the encoding could reach) − b`, worked out with
  `get_bits_encoding_coeffs` over the range `tracked_bounds` says the variable
  was encoded over — the same primitive the encoding is built with, rather than
  anything this file assumes about its shape. Get it wrong and the recipe's `ia`
  refuses the row immediately, which is what
  `cumulative_strengthening_var_capacity` checks.

  The unit line holds *permanently*: the bound it denies is the one the capacity
  had before the search started. So what comes back is an unconditional row, not
  one carrying a condition into every reason — which it has to be, since the
  propagator's `pol`s cancel against it term by term.

With nothing to do — the all-constant case, and so the common one — the row is
handed back untouched: no `pol`, no line, and a proof byte-identical to the one
written before any of this existed.

What stays declined is a capacity that is a **view**, whose bits are not the ones
the row mentions, so there is no order literal whose definition would cancel
them.

### A task whose length is a variable

Nothing in a capacity row mentions a length, so a derived constraint over such a
task derives exactly the row it would otherwise. What breaks is the pin.
`after_{
    i, t}` for a constant length is `s_i ≥ t − l + 1`, single-variable and
RUP-closable from the start's bounds; for a variable one it is reified on
`s_i + l_i ≥ t+1`, which no RUP reaches from the operands' bounds separately —
the VeriPB linear-combination limit.

`Cumulative` already solves that for itself, with a proof-only
`end = s_i + l_i` introduced by `ProofLogger::introduce_bits_of` and a
per-`(i, t)` bridge lemma `end ≥ t+1 → after`. Almost all of it was already
reachable by a citer:

- **The bridge lemmas need no publishing.** They go out at `ProofLevel::Top` for
  every `(i, t)` in the donor's window, unit propagation finds them, and a
  derived constraint's flag lookups have already established that its window is
  inside the donor's — `find_proof_flag_values` declines otherwise.
- **`materialise_after_sum` reads one line**, `end ≥ s + l`, plus two order
  literals any citer makes for itself. So the whole publication requirement is
  **one `ProofLine` per task**.

That line is a **third kind of citable thing**. A labelled OPB row is found by
`NamesAndIDsTracker::constraint_row_label` and a flag by `find_proof_flag_values`;
a line an install initialiser *derived* has no row to label and no reification to
key. `publish_derived_line` / `find_derived_line` is the pair for it, under a
role `ConstraintProofModelData<Cumulative>::end_lower_bound_role` publishes like
any other, and it hands back a line number because that is all there is to hand
back — per-solve state, exactly as `boundary_pin_line` already keeps.

It could not have been a getter on `Cumulative`. A presolver sees the constraint
`Problem` stored, and `create_propagators` installs a *clone*; the clone is what
ran the initialiser and the clone is what the tracker heard from. Everything a
citer reaches goes through the tracker keyed by `ConstraintID`, and this is no
exception.

What a citer then does:

- widen the task's length to an `IntegerVariableID` and window with `ub(l)`, as
  the donor did, or the flag lookups do not line up;
- ask `find_derived_line` for a task whose start *and* length both vary, and
  decline if it comes back empty. Empty means the donor had a constant somewhere
  after all, or the proof is being written with assertions on, which omits
  definitions. Either way there is no pin to be had.

`CumulativeDonorView` sets such a task aside when the answer is empty, and keeps
it otherwise. It asks "can this task load the resource at all?" *first*: a task
the donor gave no window — a zero height on this resource — published no proxy
either, and would otherwise be counted as set aside for the wrong reason.

The energy rules need no thought. `prepare_cumulative_overload_check` keeps only
constant-length tasks, a window-energy lemma needing a task's energy to be a
number, so a variable-duration task takes part in the rows and the time-tabling
and stays out of the lemma. Where it *does* earn its place in a presolver that
runs the energy rules alone is the (TTOC) profile term, which counts a task's
mandatory part whether or not the lemma can speak for it — and those pins are the
ones that go through the proxy. `cumulative_strengthening_var_length` is that
case: four tasks of energy six fill a window of four at the strengthened capacity
exactly, and one compulsory time point of a fifth, variable-duration task is the
whole of the overshoot.

**A tripwire.** No fixture in the tree catches the *wrong* line being published.
Publish `end ≤ s + l` in place of `end ≥ s + l` and every proof still verifies:
VeriPB's unit propagation reaches these `after` pins without the `pol` at all,
the reasons instantiating the lengths and an eq atom pinning the bits the
reification row wants. That the `pol` is load-bearing in general is pinned by
`cumulative`'s own `len_wide` case, which fails without it. What does catch a
broken citation here is the install declining, and nothing else.

### A task whose height is a variable

A variable height is the one that touches the rows. A donor's capacity row does
not contain `height × active` for such a task; it contains the bits of a
linearised contribution:

```
C_t :   Σ_{i const} h_i·active_{i,t}  +  Σ_{i var} Σ_k 2^k·cc_{
    i, t, k}   ≤   capacity
```

so a subset sum of the heights is not a subset sum of the row's coefficients,
and nothing a recipe says about that row is a statement about that task. What
takes it back is the row saying the contribution is *at least* the height, which
turns those bits into a coefficient on the activity flag again — at the height's
lower bound, which is the demand the task is guaranteed to make.

**The rows are citable, with cake's names.** `cake_pb_cp` already labels all
three halves of the contribution definition, as `@c[id][<i>_<t>_cge]`,
`[<i>_<t>_cle]` and `[<i>_<t>_cz]`, over the same terms and keyed by absolute
`(task, time)` exactly as the flags are. Ours went out unlabelled, which is what
made them uncitable; labelling them with cake's names is therefore a conformance
improvement rather than a divergence, and
`ConstraintProofModelData<Cumulative>::contribution_ge_row_role` and its two
siblings publish them.

**The conversion is one hinted RUP** per (variable-height task, time), with `L`
the height's lower bound:

```
rup  Σ_k 2^k·cc_{i,t,k} + L·¬active_{i,t} >= L   :  @c[id][<i>_<t>_cge]  <the height's lower-bound line> ;
```

added to the capacity row with coefficient one, so the bits cancel exactly and
what is left on that task is `L·active_{
    i, t}`.

It closes for a reason, which is worth writing down because the alternative is
believing a pass rate. Negating the target forces `¬active` to zero — its
coefficient `L` exceeds the slack `L−1` — leaving
`{
    Σ2 ^ k·cc_k ≤ L−1, Σ2 ^ k·cc_k ≥ Σ2 ^ j·hb_j, Σ2 ^ j·hb_j ≥ L}` over two
power-of-two bit counters. Induct on the top bit `2^s`: if `L ≤ 2^s` the negated
target zeroes `cc_s`, the `cge` row then zeroes `hb_s`, and the same system
recurs one bit narrower; if `L > 2^s` the bound row forces `hb_s = 1`, `cge`
forces `cc_s = 1`, and it recurs with `L' = L − 2^s`. Every step is
single-constraint slack propagation, so any unit-propagation fixpoint finds it
whatever the order — which is also why the hint order does not matter, and why
the negated target does not need to be named in the hints.

Swept over several thousand `(L, ub(h), bit width)` shapes before being believed,
including contribution bits narrower than the height's, which is what happens
when the install-time upper bound is tighter than the declared one. The negative
controls fail: a target one stronger than justified is refused, and so is one
with the bound line withheld from the hints.

The `pol` this replaces is the `cge` row plus the bound, then a **saturate** to
cap the reification constant down to the degree, then a literal axiom
`(2^k − min(2^k, L))·cc_k ≥ 0` per bit to put the coefficients back. It works —
and needs less than it looks, since `ia`'s implication check performs the
saturate-and-restore itself, so `pol <cge> <lb> + ;` with an `ia` pin is enough.
It is three times the code and O(bits) more addends than the RUP.

**Which bound.** The one the height has *now*, through
`need_pol_item_defining_literal`, exactly as the capacity's reduction does and
for the same reason: the declared bound is a weaker number the moment anything
has tightened it, and a declared zero would give the conversion up altogether on
models that reach a height through an `Element` over a mode variable. The unit
saying the atom holds is what makes the resulting row unconditional, permanently,
the bound having been reached before the search started.

**What stays set aside** is a height that cannot be argued about at all: a
**view**, whose reification is emitted over its own bit vector so the height's
bound rows have nothing to cancel against — and which `bound_rows` cannot even be
asked about — or a lower bound of zero, which guarantees nothing.

**Converting is not always a gain**, which is the one thing here that is
arithmetic rather than proof. `kappa` is the largest subset sum of the heights
the capacity allows, so adding a task can only push it up: heights `{3, 3}` under
a capacity of eight give six, and converting a task at a guaranteed demand of two
gives `{3, 3, 2}`, whose largest subset sum at most eight is eight — no
strengthening where there used to be two units of one. Against that, the
converted task's energy joins the overload check. `CumulativeStrengthening`
therefore assesses the donor both ways and keeps the bigger reduction;
`CumulativeDonorView::with_converted_heights_set_aside` is the other candidate.
The two multi-donor presolvers need no such choice: a converted task can only add
a conflict edge or a column.

Unlike the end-proxy publication of the length half, this one has a tripwire. A
recipe pins what `recover_constant_argument_row` returns with an `ia`, whose
implication check is syntactic, so a conversion landing on the wrong row is
refused immediately — which is what `cumulative_strengthening_var_capacity`
already checks for the capacity half, and what two deliberate corruptions of the
conversion (claiming one more than the demand, and using `ub(h)` in place of
`lb(h)`) are caught by in all three presolvers' fixtures.

### Deriving over an optional donor

A *derived* Cumulative (issue 04) works over an optional donor, and the
striking thing is how little it takes. The rows are the argument, and an
optional task's presence is a conjunct *inside* its activity flag rather
than a term beside it, so `Σ h_i·active_{
    i, t} ≤ C` is the same row either
way. Every recipe built on one — subset sums, at-most-ones, coefficient
raising, cover cuts — reads it identically, and none of them changes at
all.

What does change is what the derived propagator may *say*. Pinning
`active_{i,t} = 1` now needs `presences[i] = 1` too, so
`DerivedCumulativeTask` carries the donor's presence argument and
`install_derived_cumulative` resolves it through
`cumulative_task_presence` — the same function `Cumulative::prepare`
resolves its own with, shared precisely so that the two cannot come to
different verdicts about which flags carry a literal. From there
`propagate_cumulative` is the code that already knew how to do this, and
`reason_with_presence()` supplies the literals.

The window-energy lemma then comes out right without being asked. Its
per-time step adds `active`'s `[f]` half, which for an optional task *is*
`active ∨ ¬before ∨ ¬after ∨ ¬p`, so summing the window's worth of them
gives

```
Σ_{t∈[a,b)} active_{i,t}  +  activity·¬p_i  ≥  activity
```

— the conditional form, for free. That leftover `activity·¬p` rides
through the consuming `pol`, which therefore does not reach a
contradiction on its own; the wrapping RUP disposes of it, because
`p_i = 1` is in the reason. Which is exactly why the rule may only speak
for tasks that are *known* present, and why both consumers filter on
`is_present` before counting anything.

At the root usually nothing is known present, so a presolver's energy
bound counts an optional task as absent. That is weaker, not wrong. What
it gives up is the conditional bound

```
capacity × window  ≥  Σ_i energy_i · p_i
```

which is an implied linear constraint over the presences rather than
anything a makespan variable's lower bound can hold, and so belongs with
the conditional-bounds follow-up below rather than here.

The multi-donor case is *not* covered, and that is where the remaining
work is: `recover_conjunction_flag_bridge` cancels two donors' conjuncts
against each other, and a presence conjunct cancels only when both donors
carry the same literal. Mixed arities change the degree arithmetic
outright. The presolvers of issues 07 and 08 bridge between donors, so
they still decline an optional one; issue 06's does not, and does not.

Variable arguments they *do* take, by the same route: each reduces the row
it is about to argue over before doing so --- `InferredDisjunctive` its
witness's, before recovering the pairwise at-most-one from it;
`InferredCumulative` each row of the lifting programme, before lifting
anything out of it. Both then weaken over the donor's **usable** positions
only, since a set-aside task's terms went out with the reduction and `w`
on a variable the constraint no longer mentions is refused.

A variable **height** they take by converting it, not by setting it aside:
its bits become `lb(h) x active` before anything is lifted or recovered,
so the task keeps a column in the matrix and an edge in the conflict
graph. Neither presolver has a choice to make about it --- a converted
task can only add one of those --- which is what separates them from
issue 06's, whose argument is a subset sum and can be made worse by one.

A variable duration they take too, and it costs them nothing but a choice
of bound. A window takes `ub(l)`, which is what the donor encoded its
flags over and so the only thing that finds them; an energy sum or a
ranking takes `lb(l)`, which is the work every solution has to contain.
Tasks are matched across donors by the length *variable*, since the same
variable is the same duration whatever its bounds come to, and two
different ones are not even where their bounds agree today.

`constraint_type()` is `cumulative_optional` for the optional form, so
the verified-encoding chain does not silently match it against
`cake_pb_cp`'s `cumulative` encoder, which would re-derive a strictly
weaker set of capacity rows. cake has no optional cumulative encoder, and
that gap is now named rather than hidden.

## Edge-finding, and the reason-free window-energy row

The rule (#733): at a window `[a, b)` with `Theta` the tasks contained in it,
`energy = sum p_i h_i` over `Theta` and `width` the window's occupiable slots, a
task `j` with one end inside the window and one outside is pushed away from it.
Writing `rest = energy - (capacity - h_j) * width` for the contained energy that
exceeds what could be there if `j` ran at full height throughout, a `j` starting
inside cannot start before `a + ceil(rest / h_j)`, and a `j` ending inside
cannot start after `b - p_j - ceil(rest / h_j)`.

**The certificate is the overload check's, emitted under the negated
conclusion.** Over the same window: the contained tasks' energy by the
window-energy lemma, plus what `j` must still occupy if the conclusion were
false, against the same `C_t` rows. That overflows the window, so the `pol` is
contradictory and the framework's wrapping RUP turns it into the push. One
window, no chain — which is what the follow-up below used to say could not be
done.

What makes it affordable is that the energy lines are made **reason-free**.
`derive_window_energy` resolves the order literals its sum leaves over against
the current bounds, which is good for exactly one inference.
`derive_guarded_window_energy` weakens them onto two guard literals instead,
along the order encoding's own monotonicity, giving

```
sum_{t in [a,b)} active_{i,t} + low_coeff·~[s_i ≥ low_guard] + bound·[s_i ≥ high_guard] ≥ bound
```

which holds for every value of `s_i`. That lives at `ProofLevel::Top` and is
cited by every later firing over the same window; a citing firing discharges
whichever guards its reason refutes and leaves the one the conclusion is about
standing. Measured over the Pack instances, a row is cited between 322 and 3455
times for each time it is derived, because a window is a pair of an earliest
start and a latest completion time and those repeat constantly.

Three things worth knowing before touching it.

- **The clipping is not a separate mechanism.** A guard the ladder cannot reach
  — because it sits the wrong side of a survivor — is discharged by that
  survivor's own literal axiom, at a unit of the bound each. That count *is* the
  difference between a contained task's whole `p_i` and a pushed task's clipped
  contribution.
- **Both guards must be stated against the clipped window.** A window can run
  past the last time a task could be active, and the lemma clips there. A guard
  outside that leaves survivors nothing can weaken onto, and on a task whose
  flags start after the window does it discharged the only survivor there was.
- **The propagator asks `window_energy_bound` for exactly the bounds the
  derivation will be given**, not for the state's. The row is a model fact; the
  state is the looser of the two in one direction and the tighter in the other,
  and either way the rule would then fire on energy the certificate does not
  establish. There is no mutation lane that can catch this, because citing a row
  at the wrong threshold usually yields a *stronger* row that verifies happily.

Testing is `cumulative_edge_finding_test`, whose fixtures are a window packed to
capacity by tasks with **empty mandatory parts** — without that, time-tabling
makes the same push and unit propagation closes the conclusion's RUP whatever
the derivation above it says, so the fixture measures nothing. Six mutation
lanes, all rejected.

## TTEF: the same certificate, with the profile added (#696)

Time-table extended edge-finding is to edge-finding what `(TTOC)` is to the
overload check. The tasks a window does not contain still put their
mandatory-part load into it, so `rest` is computed against

```
window_total = energy + (profile_within(a, b) - inside_mandatory)
```

with the pushed task's own mandatory load taken back out, since its clipped
energy already covers those time points and each time point has one `C_t` row
to cancel against. `CumulativeRules::time_table_edge_finding`, off by default.

**The certificate is edge-finding's, plus the pins `(TTOC)` already emits.**
Same window, same guarded rows, same `pol`; the profile term is the same
`pin_contributor` line per mandatory `(task, time)` pair that the overload check
uses. Nothing new was needed, which is the answer to the question #696 asked.

Two things are worth knowing.

- **The pins are read from the live bounds, not from the `mand_load` snapshot
  the sweep was set up from.** A mandatory part only grows as the sweep pushes
  bounds around, so the pins claim at least what the firing's arithmetic
  counted, and a `pol` carrying more energy than it needs closes just the same.
- **The pins are usually not load-bearing at all.** Without them the `pol`
  leaves the non-contained tasks' `active` terms uncancelled, and unit
  propagation assigns those from the reason's own bound literals — so the
  wrapping RUP closes anyway. Dropping *every* pin is rejected on only 13 of 248
  searched instances. They are emitted because those 13 exist, not because the
  common case needs them.

That second point is what makes the fixtures hard. A fixture has to make the
pins matter *and* land its push somewhere a solution actually sits — where the
push is merely valid rather than tight, "one too far" is valid too and VeriPB
verifies the corrupted proof. `cumulative_ttef_test --search` generates random
instances and keeps the ones satisfying both, `--describe` prints what one does,
and `--instance=` runs a mutation against a candidate; the two `sharp` fixtures
came out of that, and the two `profile_push` ones are hand-built to *explain*
the rule rather than to test it. Seven mutation lanes, all rejected.

`OmitCapacityLine` is not among them: it is accepted on every TTEF fixture
searched, for the same reason dropping the pins usually is.

**Measured, 175 instances at 60 s** (`data_bl`, `data_pack`, `data_la_x`), over
the 36 that every arm closed:

| arm | recursions | vs ef | propagations | vs ef |
|---|---|---|---|---|
| no edge-finding | 7,227,100 | 3.062x | 72,057,194 | 2.450x |
| edge-finding | 2,359,885 | 1.000x | 29,411,592 | 1.000x |
| TTEF | 1,768,271 | **0.749x** | 23,452,325 | 0.797x |
| energetic | 1,573,267 | **0.667x** | 21,566,293 | 0.733x |

TTEF has fewer recursions on 35 of the 36 and more on none. Do not read the
wall times from that sweep: the arms differ in per-node cost, and `data_la_x`
closes nothing at 60 s in any arm.

What it costs: over `data_bl`, 67.1M firings, of which **72.6% are ones
edge-finding would not make at all**, carrying **2.93 pins per firing** (most 21)
against 4.54 contained energy rows. So the pins roughly double a firing's proof
lines. They are also **15,037x reused** — 13,065 distinct `(task, time)` pairs
across 196M citations — so a guarded, cached pin in the shape of
`derive_guarded_window_energy` over `[t, t+1)` would amortise them away, exactly
as the contained rows already are. Not done: the guards of a one-time-point row
are fixed by `(task, time)` alone, which is why the reuse is so high.

`CumulativeRules::energetic_edge_finding` is the same rule with every task's
*guaranteed* energy in the window in place of contained-energy-plus-profile.
That is what `window_energy_bound` computes anyway, so it needs no pins at all,
and it is stronger. It is **not certified** — `define_proof_model` refuses a
logger while it is set — and it is in the tree to be measured, not to be used:
the row above is what it buys, and the propagation cost of recomputing the sum
per window is not paid for on this family.

## Not-first / not-last: the same certificate, different thresholds (#732)

A task that cannot start before every task the window contains has ended must
start after the earliest of those ends; and a task that cannot end after every
one of them has started must end before the latest of those starts. So the
thresholds are the contained set's own `min ect` and `max lst`, not a figure
computed from the leftover energy --- which is what makes this a different rule
rather than a weaker edge-finding.
`CumulativeRules::not_first_not_last`, off by default.

**The certificate is edge-finding's, unchanged.** Same window, same guarded
rows, same `pol`; what differs is the threshold and which guard carries the
negated conclusion, and `derive_guarded_window_energy` already takes both as
parameters. Nothing was added to the proof vocabulary, and the first proof
generated verified.

**What is new is which tasks it can speak about.** Where a task has one end
inside the window, edge-finding's threshold is the furthest an energy argument
over that window can reach --- `step = ceil(rest / h_j)` is exactly the largest
`v` for which `energy + h_j * minoverlap(a, b, est_j, v-1) > supply` --- so its
push subsumes this rule's and the live-bound test drops the duplicate. Measured
over `data_bl`, **every one of 6,316,773 firings is on a task that SPANS the
window**, which is the case the edge-finding section documents as one where
nothing can be said. A spanning task's guaranteed energy is a hump in its start:
it rises until the task is fully inside the window and falls after, so no
closed form pushes it, and restricting the start to one side of a threshold is
what makes the hump's *minimum* say something.

One wrinkle in the guards. A spanning task's lower bound is to the left of the
window, so the low guard cannot be `clipped_window_start`, which would not be
dischargeable. It is `min(lb(s_j), clipped_window_start(j, a))`: any guard at or
past the window's start already discharges every survivor the ladder has, so
where the bound is inside the window the window's own start does just as well
--- and being a fact about the window rather than about the search, the row it
derives is the one edge-finding already keeps, rather than one keyed on a bound
that moves.

**Measured, `data_bl` + `data_pack` at 60 s**, over the 37 instances every arm
closed:

| arm | recursions | vs baseline | propagations |
|---|---|---|---|
| edge-finding | 3,852,140 | 1.000x | 45,917,542 |
| + not-first / not-last | 3,846,036 | 0.998x | 45,847,449 |
| TTEF | 2,244,499 | 1.000x | 30,271,109 |
| + not-first / not-last | 2,238,267 | 0.997x | 30,071,983 |

It changes the search on 5 of 37 over edge-finding and 8 of 37 over TTEF, never
for the worse, and no arm disagrees about an optimum. But it fires in the
millions to buy that 0.3%, and at 60 s it **closes fewer instances than leaving
it off** (37 against 39, and 38 against 39 alongside TTEF) --- the scan costs
more than the pruning returns. Hence off by default, and hence the honest
summary: certifiable for nothing, and worth nearly nothing.

**What is certified here is a weakening of the published rule (#746).** The
conclusions are the published ones, and the propagator reproduces Schutt &
Wolf's (CP 2010) worked example number for number. Their *detection* condition,
and Kameugne et al.'s (CPAIOR 2018), take the pushed task's overlap at **one
end** of the negated conclusion's start range; this takes `window_energy_bound`
over the whole range, i.e. the minimum over both, because that is exactly what
`derive_guarded_window_energy` can derive and the certificate then cites. Where
each paper's setting makes the overlap monotone across that range the two
coincide; where it does not, we fire less --- 3535 published-only firings
against 7 of ours on one seed. #746 has the measurements and the open question,
which is whether the divergence is a standing assumption on the task set that
the transcription drops, or a genuine argument the window-energy lemma cannot
make.

Testing is `cumulative_nfnl_test`, whose fixtures were searched the same way
TTEF's were and against the same two conditions --- the rule must move a bound
that time-tabling, the overload check, edge-finding and TTEF together do not,
and the bound must be one a solution sits on. Its mutation harness differs in
one way from the other two, and deliberately: it does **not** insist the root
was reached. A push corrupted one step too far can empty a domain outright,
leaving no root to report, and the proof of that emptying is exactly the
corrupted step. Where a mutation is a no-op the root *is* reached and veripb
accepts, which fails the lane, so the verdict is veripb's either way.

`PushOneTooFar` had to be wired into this rule's own pushes. Until it was, the
lane was corrupting an edge-finding firing on the same instance and reporting a
rejection that said nothing about not-first / not-last.

## The overload ladder: one certificate, a tighter line per time point (#550)

`(TTOC)` charges a window `capacity x width` in bulk and subtracts the profile.
Two published rules improve on the same comparison by capping what each
*individual* time point supplies:

* **(TTHE-OC)**, the time-table horizontally elastic overload check (Kameugne,
  Fetgo Betmbe, Noulamo & Tayou Djamegni, C&OR 172 (2024); the formulation used
  here is Cloutier & Quimper's equivalent one, CP 2026 SS2.2.5). A time point no
  task can reach with more than its own tasks' heights does not supply the whole
  capacity: resource nobody can use is not available.
  `CumulativeRules::elastic_overload`.
* **(KAOC)**, the knapsack-augmented overload check (Cloutier & Quimper, CP
  2026). The tasks that could run at a time point have integer heights, so what
  they can between them consume is the largest *subset sum* of those heights
  fitting under what the profile leaves --- not that figure itself.
  `CumulativeRules::knapsack_overload`, which implies the rule above and
  dominates it.

### The three rungs are one comparison

Charge the window each contained task's energy less whatever its compulsory part
already accounts for, and supply it one time point at a time:

    required = e_Theta - sum_i h_i * |comp_i ^ window|
    supplied = sum over t in [a, b) of A_t

With `A_t = capacity - f(I, t)` this **is** `(TTOC)`: each contained task's
compulsory load comes off the required side and goes back on as the supply the
profile removes, and the two rearrange into `e + F > C(b-a)` term for term. Cap
`A_t` by the optional heights at `t` and it is (TTHE-OC); cap it by the largest
total they can reach and it is (KAOC). Nothing else changes --- so this is one
certificate with a tighter line at some time points, not three certificates.

### The certificate

Per time point, a line saying what the contained tasks can take there:

* where the optional heights **exceed** what the profile leaves, start from the
  capacity row `C_t`, pin every compulsory contribution off it
  (`pin_contributor`, which `(TTOC)` already uses) and `weaken` away every term
  that is not a contained task's optional one. What is left is a statement over
  exactly the heights the knapsack reasons about, with right hand side
  `capacity - f(I, t)`. For (KAOC), put it through
  `derive_subset_sum_strengthening` (#544);
* where they **do not**, the capacity row is not the binding fact and citing it
  would supply the window with resource nobody can take. The binding fact is
  each task's own literal axiom, and their sum is the whole cap --- no capacity
  row, no pins, and nothing for the knapsack to improve on, since the entire set
  already fits.

Against those, each contained task's `derive_window_energy` line scaled by its
height, over the task's **own** `[est, lct)` rather than over the window, with
its compulsory times weakened back out --- those charged the availability side,
and counting them twice would leave the pol open.

`weaken` is what makes the item set exact. VeriPB's `w` drops a term and lowers
the degree by its coefficient, which is precisely "remove this from the left of
a `<=`"; without it the knapsack would run over the wrong coefficients and the
cap would be too weak to fire.

### Strengthen only where the conflict needs it

The dynamic programme costs a layer of proof flags per reachable partial sum, at
every time point it is applied to. The certificate sorts the time points by what
the cap buys, applies it biggest-gain first, and stops as soon as the comparison
tips; the marker comment records `strengthened=k/w`. This falls out of the
per-time-point shape rather than needing machinery, and it means a conflict the
elastic cap alone can carry pays nothing for the knapsack at all --- which is
what the `ttheoc` marker means.

### Measured, `data_bl` + `data_pack` at 60 s, over the 36 instances every arm closed

| arm | recursions | vs baseline | propagations | closed |
|---|---|---|---|---|
| time-tabling + `(OC')` + `(TTOC)` | 7,227,100 | 1.000x | 72,057,194 | 38 / 95 |
| + (TTHE-OC) | 5,008,908 | 0.693x | 51,145,525 | 36 / 95 |
| + (KAOC) | 2,832,478 | 0.392x | 29,227,548 | 48 / 95 |

Fewer recursions on 30 of 36 and more on none, and no arm disagrees about an
optimum. **The knapsack cap is what pays**: it more than halves the search and
closes ten more instances at the same wall time. **The elastic cap alone does
not**: 0.693x of the search, but it closes *fewer* instances than leaving it off,
because its per-time-point scan costs more than the pruning returns --- the same
verdict not-first / not-last got, and for the same reason.

And on top of the edge-finding family, which is the question that decides
whether it is worth having at all --- over the 39 instances both arms closed:

| arm | recursions | vs TTEF | propagations | closed | wall |
|---|---|---|---|---|---|
| TTEF | 7,250,390 | 1.000x | 74,388,179 | 39 / 95 | 98.2 s |
| + (KAOC) | 2,342,923 | 0.323x | 29,856,904 | 49 / 95 | 76.0 s |

Fewer recursions on 26 of 39 and more on none, ten more instances closed, and
**faster in wall time as well** --- so the rule pays for its own O(n^2 * horizon)
scan and then some. It is not subsumed by the energetic family: edge-finding and
TTEF move bounds from a window's total energy, and this refutes windows where
the *shape* of the heights is what does not fit, which no amount of aggregate
energy reasoning sees.

Soundness: 600 generated instances enumerated exhaustively at sizes 8 and 10,
zero solution-count differences against the rules off.

### What the fixtures could not catch

Both bugs found in this rule were the same mistake --- a quantity the check
computed that the certificate never derived --- and **every fixture verified
through both of them**. 11 of 60 proofs on generated instances did not.

* The elastic cap was computed and not derived (above). Every published fixture
  has every task able to run at every time point, so none of them ever reaches
  the branch where the cap binds.
* The energy lines ran over the window rather than over the task, leaving a
  negative coefficient on every `(task, time)` the task cannot reach. Unit
  propagation finishes that from the reason's bound literals often enough to
  hide it, and all four fixtures have every task spanning the whole window, so
  the residue was zero there anyway.

Both are now cross-checked in the justification, which adds up what the pol
actually charges and throws if it disagrees with what the rule fired on. The two
figures come from opposite sides of the propagator --- the incremental
per-time-point arrays against the lines as they are emitted --- so agreeing is
worth something.

The general lesson is the one #696 recorded from the other side: a fixture built
to *demonstrate* a rule is symmetric and generous, and the asymmetric cases are
exactly where a certificate and a check drift apart. Generated instances are not
an optional extra here.

### Mutations

`claim_one_better` (claim one better than the largest reachable total),
`strengthen_one_fewer` and `capacity` are rejected on all three fixtures, so the
integrality argument is load-bearing on both of the strengthening's paths --- the
divisibility one `cloutier_ex2` takes and the layered programme `dp_path` takes.

There is no lane for the compulsory-time weakening. Leaving it out is a real
corruption and VeriPB accepts it anyway: the terms it would have cancelled are
the ones unit propagation assigns from the reason's own bound literals, the same
way `(TTOC)`'s pins are droppable on 235 of 248 instances. The step stays, since
it is what makes the pol itself contradictory rather than only close, but nothing
can test it.

### Restrictions

Constant heights only: a variable height puts bit-linearised contribution terms
in the capacity row, which neither the knapsack's item list nor the term-dropping
can read, so v1 declines rather than approximates and the plain rules still run.
A capacity above 4096 falls back to the elastic cap, since the bitset is
`capacity + 1` bits at every time point (scheduling capacities are nothing like
that --- Cloutier & Quimper report `C <= 122` across their benchmarks).

Propagation is `O(n^2 * horizon)` rather than Cloutier & Quimper's `O(Cn^2)`:
their doubly linked Profile collapses the runs where the profile is constant, and
this keeps a flat array plus the incremental bitset (their Algorithm 3 shift-or)
per time point. Same trade as #742 for edge-finding's scan, and the same answer
--- what is missing is propagation performance, not proof content.

## Open follow-ups
- **Cloutier & Quimper's Profile.** The doubly linked list over time points,
  which collapses the runs where the profile is constant and takes the sweep
  from `O(n^2 * horizon)` to `O(Cn^2)`. Propagation performance only; the
  certificate is unchanged.
- **Guarded pins for the profile term.** TTEF's pins are reason-backed and
  re-derived per firing, at 2.93 lines' worth per firing and 15,037x repetition.
  A one-time-point `derive_guarded_window_energy` row is keyed by `(task, time)`
  alone, so it would cache the way the contained rows do --- and the same row
  would amortise `(TTOC)`'s pins, which the merged overload check also
  re-derives every firing.
- **Certifying the energetic form.** `energetic_edge_finding` measures better
  than TTEF and needs *no* pins, since every task's contribution is a guarded
  window-energy row. What is unresolved is the cache key: a contained task's
  guards come from the window, a non-contained one's from its current bounds, so
  the rows would repeat far less. Weakening the guards deliberately, to buy
  reuse at the price of a looser bound, is the experiment.
- **Edge-finding's scan (#742).** The rule is certified and its inferences cost
  nothing measurable, but the window x task sweep that finds them is O(n^3) and
  taxes the solve about 1.5x at identical search. Propagation performance, not
  proof logging.
- **A variable duration in the energy set (#689).** The window-energy
  lemma's eligibility filter turns away a task whose length or height is
  not a constant, and those two halves are now in different states. The
  **height** one has resolved itself: a task #686 converted arrives at the
  filter as a constant and passes, which
  `cumulative_strengthening_all_var_heights` demonstrates by refuting at
  the root through the energy check. The **length** one still binds, since
# 685 passes a length through as the variable it was posted with — so a
  multi-mode RCPSP task gets its demand counted and its energy discarded,
  and it is the duration that discards it. Loosening it is not free: the
  lemma telescopes order literals over ranges fixed by a constant length,
  and a variable-duration task's `after` is reified on `start + length`
  instead. #689 has the sketch. The rest of #542's staging is unchanged.
- **Conditional bounds for optional tasks.** An undecided task's start
  bounds are never pruned, because there is no conditional-bounds store
  and an unconditional prune would be unsound if the task turns out
  absent. The propagation that is being left on the table is real:
  "if present, `j` cannot start before `b`" is derivable by exactly the
  chain above, stopped early.
- **A `cake_pb_cp` encoder for `cumulative_optional`.** Until there is
  one, the optional form is outside the verified-encoding chain.
The current scaffolding (`_before_flags`, `_after_flags`,
`_active_flags`, `_contrib_flags`, `_end`, `_capacity_lines`) is
enough for time-table-strength reasoning over variable `d`/`r`/`b` and not
much more. Variable durations and variable heights both chain-verify
against `cake_pb_cp`; the only remaining divergence is the start/size bit
*variable* encoding (#358), which is orthogonal.

<!-- vim: set tw=72 spell spelllang=en : -->
