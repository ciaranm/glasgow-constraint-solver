# Proof logging for `Disjunctive`

This document explains how the `Disjunctive` propagator's proofs are
backed by VeriPB. The propagator runs time-table consistency
specialised to `h_i = 1`, `capacity = 1`
(see [`cumulative-proof-logging.md`](cumulative-proof-logging.md) for
the general time-table proof machinery) plus **detectable
precedences**, and behind flags an **overload check** (#730, #737–#741)
and **edge-finding** (#751).

**The declarative OPB encoding is the same whatever the rules say**, and
it is purely pairwise: no per-(task, time) rows, no proof-only variables,
no prefix emitted before search. What differs between the rules is the
*justification*, and that splits in two.

The pairwise rules — every `h = 1`, `c = 1` time-table inference, and
detectable precedences — do not use a time index at all: each is a
statement about one **pair** of tasks, justified directly against the
encoding's own reified rows. That is what #495 measured and what the
rewrite bought (a previous design bridged to cumulative-style
time-indexed flags at `O(n × horizon)` cost *in the model*, before
search, whether or not anything used them).

The energetic rules cannot be pairwise — a *set* of tasks blocks an
interval — so they re-encode time **inside the proof**, per firing: an
activity flag per (task, time) minted by `red` over order literals the
encoding already has, and the pairwise separation rows folded into a
per-time at-most-one. The distinction that matters is not
"time-indexed or not" but **where the time index lives**: in the model
and paid for unconditionally, or in the proof and paid for only by the
firings that want it. The OPB is genuinely untouched, which is the
interesting part.

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
clause — a zero-length task does not constrain. Optional tasks add
their presence literals to the same clause, and nothing else (see
below).

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

## The inferences

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

- **Detectable precedences** (issue #731, step 2 of #729). The
  precedence `k ≪ j` is *detectable* when `j` cannot finish before
  `k` starts on bounds alone, `lb(s_j) + lb(l_j) > ub(s_k)`. Then
  `before_{j,k}` is false, the separation clause forces
  `before_{k,j}`, and reading that both ways round gives

  ```
  s_j ≥ lb(s_k) + lb(l_k)      pushing the successor up
  s_k ≤ ub(s_j) − lb(l_k)      pushing the predecessor down
  ```

  Each detected precedence justifies its own push, so a push cites
  only the *best* detected predecessor (latest earliest-end) or
  successor (earliest latest-start): no set, and no chain. Vilím's
  O(n log n) form keeps the detected predecessors in a Θ-tree and
  pushes to the whole set's earliest completion time, which is
  stronger and needs an energy argument (see the follow-ups).

  **The proof is exactly one step of the push chain above**, with
  `final = true` and no deposit: one pol refuting the reverse
  precedence from the running bound, one folding the surviving
  precedence onto the target order literal. Nothing new was needed
  for it, which is the point — the detection condition
  `lb(s_j) + lb(l_j) > ub(s_k)` is *precisely* the condition under
  which the refuting pol's degree comes out positive, and it is also
  the condition a chain step's blocker satisfies. Where the two rules
  differ is only in what the propagator has to notice: a chain step's
  blocker is found by scanning the profile, so it must have a
  non-empty mandatory part, while the pol arithmetic never cared
  whether it did. A detected predecessor with an empty mandatory part
  is invisible to time-tabling and prunes here.

  Two guards, both inherited from the pushes above: a task with no
  guaranteed duration is skipped (there is no positive `lb(l)` to pin
  its zero-length escape false with), and so is a task whose start is
  already fixed. The second loses nothing: a precedence detected
  between a fixed task and an unfixed one is the same precedence read
  the other way round, so it pushes the unfixed one and fails there
  if it must, and two fixed tasks that collide both have mandatory
  parts, which is the overflow contradiction.

  Each push writes one `%` comment naming the pair and the direction,
  which is what lets a test count what fired rather than only that the
  rule compiled. It is also the only thing this rule adds to a proof
  beyond its two pols: a 2 GB RCPSP proof over a unary machine carried
  982,065 of them, about 2% of the file, alongside the per-node
  comments every proof already writes.

### Rule selection, and what always runs

`DisjunctiveRules` switches time-tabling's pushes and detectable
precedences on and off independently (both default on). It selects
propagation strength only: same solutions, same OPB. Presence
falsification reads time-tabling's own placement scan, so it is under
`time_table` with the pushes.

The **mandatory-overlap contradiction is not switchable**. At an
all-fixed leaf every task's mandatory part is its whole active
interval, so that scan is what makes the propagator a *checker*; a
selection that stopped it running would not be weaker propagation but
a solver reporting assignments that violate the constraint.
`disjunctive_precedences_test` enumerates its fixture under
`{time_table = false}` for exactly this reason — the extra solutions
would show up there.

### Which of the two pols is load-bearing

Both are emitted, and on some instances either one alone suffices:
the closing RUP can sometimes get the other's content by unit
propagation over the operands' bit encodings. That depends on the
particular arithmetic, not on the rule, and the propagator cannot
cheaply tell which case it is in — so it always emits both, as the
push chains do. The mutation lanes therefore run on a fixture where
each half is needed (`disjunctive_precedences_test`'s `tight`), which
is not the fixture that best *demonstrates* the rule; a fixture
chosen for one job does not do the other, and both are in the test.

### Variable durations

No extra machinery at all: the duration term stays on the before
flag's left-hand side and cancels against the duration's lower-bound
definition row *in the same pol* (see the shape above). Mandatory
parts and footprints use `lb(l_i)`, and every variable duration joins
the reason. In particular there is **no** proof-only `end = s + l`
variable — the in-proof end introduction
(`ProofLogger::introduce_bits_of`) exists for Cumulative's
time-indexed `after` flags, which Disjunctive's proofs no longer use.

### Optional tasks

An optional task carries a `{0, 1}` presence variable. It reaches the
encoding in exactly one place — two more disjuncts on the separation
clause the pair already had:

```
before_{i,j} + before_{j,i} [+ zw_i + zw_j] + ¬p_i + ¬p_j  ≥ 1
```

The before-flag reifications stay **unconditional**:
`before_{i,j} ⇔ s_i + l_i ≤ s_j` whatever the presences. That is the
design, not an economy. Every justification in this document is a pol
over those reification rows and the operands' bound-literal definition
rows, so leaving them alone means **the pols do not change at all**:
presence surfaces only where the *separation clause* is used, which is
always the framework's closing reason-wrapped RUP. Each such RUP just
has two more literals available in its reason. A presence posted as
the constant 1 resolves to nothing at all (`innards::task_presence`,
shared with `Cumulative`), so a non-optional model's OPB is unchanged
byte for byte, and a constant 0 drops the task from the constraint
entirely.

Propagation follows `Cumulative`'s rules and for its reasons: an
absent task is dropped; an **undecided** task contributes no mandatory
part, is in nobody's blocker set, is not a detected predecessor or
successor, and — the load-bearing part — **its own start bounds are
never pruned**, because there is no conditional-bounds store and a
prune valid only if the task is present would be unsound. Reasons
carry `p_i = 1` as an explicit literal per task known present, rather
than putting the variable in the reason's variable list: an undecided
presence has no fact to record, and `generic_reason` would spend an
order atom saying `0 ≤ p ≤ 1`.

**Presence falsification.** When no start in `dom(s_j)` escapes the
mandatory parts of the present tasks, `p_j = 0`. The derivation is the
lb-push chain above, replayed over the *whole* domain, with "or task
`j` is not here at all" carried as an extra disjunct on every deposit:

```
[s_j ≥ target] ∨ ¬p_j                (one RUP under reason per step)
```

so each step reads "either `j` starts later than this, or `j` is not
here". The last step deposits nothing, exactly as the last step of a
push does: its target is one past `j`'s upper bound, which the reason
already refutes, so the closing RUP concludes the presence. The two
pols per step are the ordinary ones — `emit_lb_chain_step` takes the
extra disjunct as an argument and changes nothing else.

Falsification is **conflict-shaped**, and that constrains what can
test it. Once the chain has cornered the task, the reason context
extended with "the task is present" is contradictory and every RUP
under it is vacuously valid, so a mutation that merely *shortens* the
chain is still sound and VeriPB is right to accept it. Corrupting the
route is not a test; corrupt the destination. Hence the three lanes in
`innards/disjunctive_mutations.hh`: `WrongTask` (argue about a task
nothing has cornered), `ClaimOneTooFar` (draw the conclusion where it
is false, on a fixture with exactly one placement left), and
`EmitNothing` as the control. `cumulative_mutations.hh` records the
same finding from the constraint this rule is modelled on.

The strict-mode zero-length check below is where optional tasks meet
#731's trap in its second form. That check and the mandatory-overlap
scan are what make the propagator a *checker*, so both use the same
`is_present` test as the profile: an undecided task that slipped past
the leaf check would be one whose presence never got fixed, and the
solver would report it as a solution.

### Non-strict zero-length escapes

Whenever an inference fires, every involved task has a positive
guaranteed duration, so its `zw` escape flag is false. The
justification pins the involved escapes false first (one RUP under
reason each, from `lb(l) ≥ 1`), and the separation clauses reduce to
their before-flag disjunctions for the rest of the derivation.

## Edge-finding, and the guarded window-energy row (#751)

The rule: for a window `[a, b)` and the set `Θ` of tasks it contains
(`est_i ≥ a`, `lct_i ≤ b`), a task `j` with **one** end inside that
cannot fit alongside `Θ` is pushed out of the window:

```
est(Θ ∪ {j}) + p(Θ) + p_j > lct(Θ)      detection

lb(s_j) ← a + p(Θ)                      j starts inside, ends after
ub(s_j) ← b − p_j − p(Θ)                j ends inside, starts before
```

This is the capacity-one case of `CumulativeRules::edge_finding`, where
`rest = energy − (capacity − h_j)·width` collapses to `p(Θ)`. A task with
*neither* end inside spans the window and no closed form pushes it: its
guaranteed energy is a hump in its start rather than monotone, which is
what [not-first / not-last](#not-first--not-last-752) is for, below.
`DisjunctiveRules::edge_finding`, off by default —
the sweep is cubic, so a solve that never fires it still pays, which is
the trade #742 records on the cumulative side.

**The certificate is the overload check's, emitted under the negated
conclusion.** Same window, same activity flags, same bridge, same fold.
One step differs, and it is the whole of what a *pruning* rule needs
that a conflict-only one does not.

### Why `energy_pol` cannot serve

The overload check's `energy_pol` sums a task's backward rows and
resolves the order literals the telescope leaves over **against the
current bounds**, one reason-wrapped RUP each. That is exactly right for
a conflict: a conflict-only rule never has to keep a row past the
firing. It is no use here for two reasons — a pruning rule has to carry
the *negated conclusion* into the row, and a row good for one node is
not worth deriving at all when the same window recurs.

So the survivors are weakened onto **two guards** instead, along the
order encoding's own monotonicity, giving

```
Σ_{t∈[a,b)} act_{i,t} + c_lo·¬[s_i ≥ L] + c_hi·[s_i ≥ Hg]  ≥  p_i
```

which holds for every value of `s_i`. It cites nothing but the flags'
own backward `red`s and rows of the form `[s ≥ u] → [s ≥ v]`, both facts
about the model, so it lives at `overload_vocabulary_at` with the rest
of the vocabulary and is cited rather than re-derived.

**That is `derive_guarded_window_energy`, the same lemma the cumulative
energy rules cite** (`gcs/constraints/innards/window_energy.hh`). The
two encodings reach it differently and share everything after: there,
three bridges over fully reified `before` / `after` / `active` flags;
here, the reverse half of an activity flag reified straight onto the two
order literals, which *is* the statement those bridges are built to
produce. `WindowRows` is the seam. Sharing it is not tidiness — the
telescope's guard arithmetic is easy to get subtly wrong in a way that
still verifies (see below), and one copy is one thing to get right.

### The conclusion is derived, not assumed

A firing discharges whichever guards its reason refutes. A contained
task is inside the window whichever way the push goes, so both of its
guards fall. The pushed task's are asymmetric: one is refuted by the
reason, and **the other is the negated conclusion and is left standing**.
What the summed `pol` lands on is therefore

```
bound·[s_j ≥ push]  ≥  p(Θ) + bound − (b − a)      > 0
```

so the `pol` *derives* the pushed literal and the framework's wrapping
RUP only reads it off. The negated conclusion never enters the proof as
an assumption.

### Clipping is not a separate mechanism

`j` has one end outside, so it is guaranteed less than `p_j` inside the
window. That falls out with nothing added: the guard sits past
`b − p_j + 1`, so the leftover thresholds between the two cannot be
weakened onto it — the implication runs the wrong way — and each is
discharged by its own literal axiom at a unit of the bound. The count is
exactly `p_j − (b − push + 1)`.

The invariant that keeps this honest: **the propagator asks
`window_energy_bound` for exactly the guards the derivation will be
given**, not for the state's bounds. The row is a model fact; the state
is looser in one direction and tighter in the other, and either way the
rule would fire on energy the certificate does not establish. There is
no mutation lane that catches this — citing a row at a threshold the
reason still entails yields a *stronger* row, which verifies happily —
so it has to be read rather than tested. `disjunctive_mutations.hh`
records the lane that was written for it and why it was removed.

### What it costs, and what caches

Per firing: the fold, one guard-discharge RUP per guard, and one `pol`.
Everything else is cited. Per (task, window), measured on the standalone
simulation (`~/claude/tmp/disj-ef-751/`, and the comment on #751):

| row | derivation | cache key | stable? |
|---|---|---|---|
| contained task `i` | 5–7 lines | `(i, a, b)` — its guards are `(a, b − p_i + 1)`, a function of task and window | yes |
| pushed task `j` | `p_j + 3` lines | `(j, a, b, push)`, and `push = a + p(Θ)` moves with the contained set | no |

So `|Θ|` of the `|Θ| + 1` rows are keyed exactly as the bridge is and
cache on the same terms; only the pushed task's guard moves. Deferring
its ladder walk to the citation would buy a stable key for about one
proof line, which is why there is one code path and not two.

### What it is worth, and which half is worth it

Generated RCPSP with a unary machine (`--machine-fraction 0.8`, without
which hardly any resource has capacity one and the rule never fires),
sizes 8–30, 68 instances at a 60 s timeout. Ratios are over the 36
instances **every arm closed** that needed at least a hundred
recursions — an arm that timed out contributes a lower bound rather
than a count, and a ratio of 98/98 is not evidence.

| arm | summed | median | geomean | better than off |
|---|---|---|---|---|
| off | 1.000x | 1.000x | 1.000x | — |
| lb push only | 0.655x | 0.758x | 0.418x | 34/36 |
| ub push only | 0.273x | 0.242x | 0.172x | 35/36 |
| **both** | **0.169x** | **0.127x** | **0.099x** | **36/36** |

and 46 of the 68 close within the timeout against 41 with the rule off,
so unlike cumulative not-first/not-last this pays for itself rather than
being a table row. Three statistics rather than one because the summed
ratio is a division and not a sample: the largest instance carries 37%
of the summed recursions on its own, and dropping it moves the summed
figure (0.169x to 0.129x) far more than the median (0.127x to 0.123x).

**The two halves are not worth the same, and by a factor of three.**
That is the whole reason both are separately switchable and both are in
the table: a run measuring only the lb push would have reported 0.758x
and concluded the rule was marginal. Which half dominates is a property
of the instance family rather than of the rule — the cumulative side
found the same asymmetry with the roles reversed — so the number to
quote for a new family is one measured on it.

Adding the lb half to the ub half is a small loss on exactly one of the
36 (233 recursions against 286). It is worth knowing that a stronger
rule can cost search, and not worth acting on.

Across every instance more than one arm closed, all arms proved the
**same optimum**. That is the check the proof lanes cannot make: a rule
that removed a solution would still emit perfectly valid proofs of the
pushes it did make.

### Testing

`disjunctive_edge_finding_test`, and the shape of it is decided by the
rule being a *push*: once the reason context extended with the negated
conclusion has gone contradictory, every RUP under it is vacuously
valid, so **a corruption that merely shortens the derivation verifies**.
The `+1` on the conclusion is the signature test, and the fixtures put
exactly one unit between a valid push and a false one. Five lanes, all
rejected; `sharp` measures the lb push and `mirror` the ub push, because
measuring one half of a symmetric rule tells you almost nothing. Each
fixture carries a control with the rule off — no task has a mandatory
part and no pair's ordering is bounds-forced, so time-tabling and
detectable precedences are both silent, and the control is what keeps
that true as the rest of the propagator changes.

`--search` generates instances and verifies a proof per instance, which
is the lane that matters: hand-built fixtures are symmetric and generous
and verify straight through certificate bugs.

## Not-first / not-last (#752)

The rule: for the same window `[a, b)` and contained set `Θ`, and a task
`j ∉ Θ`,

```
lb(s_j) ← min_{i∈Θ} ect_i        j cannot start before all of Θ has ended
ub(s_j) ← max_{i∈Θ} lst_i − p_j  j cannot end after all of Θ has started
```

`DisjunctiveRules::not_first_not_last`, off by default, with
`not_first` and `not_last` separately switchable.

**The certificate is edge-finding's, unchanged.** Not a rewrite of it, not
a variation on it: `edge_finding_justification` already takes the pushed
task's two guards and a flag saying which of them the reason discharges,
which is the entire difference. Not-first puts the negated conclusion on
the high guard at `min ect` and lets the reason discharge the low one;
not-last is the mirror, with the negated conclusion on the low guard at
`max lst − p_j + 1` and `ub(s_j) + 1` as the high one. The first generated
proof verified, and the five mutation lanes are edge-finding's own with
nothing added.

So this section is about the *firing set*, which is the only part that is
new.

### The `continue` this rule exists for

Edge-finding's sweep carries

```cpp
if (starts_inside == (j.lct <= b))
    continue;
```

— a task with **neither** end inside the window spans it, its guaranteed
energy inside is a hump in its start rather than monotone, and no closed
form pushes it. Restricting the start to one side of a threshold is what
makes a hump's minimum say something, and that is exactly what these two
thresholds do. So the rule shares the sweep rather than adding one, and
turning it on turns that sweep on whether or not edge-finding is set.

Where `j` has one end inside, the two rules overlap and edge-finding's
threshold is the furthest an energy argument over that window can reach,
so its push subsumes this one and the live-bound tests drop the
duplicate. The rule is still run over those tasks, because it is
separately switchable and has to be worth measuring on its own.

### What the lemma gives, which is not the overlap

The propagator asks `window_energy_bound` for the pushed task's
contribution rather than computing an overlap, and the two are **not the
same number**. The guarded row states one bound uniformly over the whole
negation range using only its two guard literals: it keeps the "ends by
`t`" survivors the low guard decides and concedes a unit for every "starts
after `t`" survivor the high guard does not. Those are two worst cases
that need not occur at the same start value, so where the true minimum
overlap sits in the middle of the range the row is strictly weaker than
it.

A propagator that fired on the overlap would be firing on energy its own
certificate does not establish, and would emit a *rejected proof* rather
than an unsound push. This is the same invariant edge-finding records, and
it bites harder here, because not-first's range runs from outside the
window to inside it and so straddles the hump.

### Two facts about the rule, and what they cost the test

Both came out of scanning random unary instances, and both are worth
knowing before writing a fixture:

- **Where the rule adds a push, the push is never tight.** Of 800,000
  random instances, 615,263 survive time-tabling and detectable
  precedences; those carry 35,189 firings that push past them, and **not
  one** has a target equal to the bound enumeration gives.
- **At one contained task the push is exactly a detectable precedence's**,
  to that task's earliest end, under a weaker detection condition. Which
  is the same fact from the other side: the exact pushes are the ones the
  pairwise rule already makes.

So a fixture cannot be both load-bearing and exact. `disjunctive_nfnl_test`
splits the difference: `sharp` and `mirror` push a spanning task where
nothing else does (and their controls say so), while `tight_nf` and
`tight_nl` land on the enumerated bound with the pairwise rules turned
off.

The mutation lanes needed a third kind of fixture again, and a
**generated** one. On every hand-built fixture at least one route
corruption still verified — the instances are small enough that the
closing RUP finishes from whatever the corrupted derivation left, which is
sound and VeriPB is right to accept. Scanning found 222 generated
instances that fired the rule and exactly one that rejected all five
lanes. `drop_contained` (35 of 222) and `drop_pushed` (20) are the fragile
ones, and the reason is this rule's own: `min ect` and `max lst` are
quantities pairwise reasoning can often reach by itself, where
edge-finding's `a + p(Θ)` is not. That is a sharper form of a finding
#731 left behind: the fixture that best *demonstrates* a rule is not the
fixture that makes its mutations bite.

### What it is worth: it fires everywhere and buys nothing

The same generated RCPSP as edge-finding's table above, and deliberately the
same 68 instances and the same 60 s timeout, so the two are read together. Six
arms, because "against nothing" is not the question a reader has: this rule
shares edge-finding's sweep and its firing sets overlap, so what matters is what
it adds *on top of* edge-finding.

| arm | against | summed | median | geomean | better | closed |
|---|---|---|---|---|---|---|
| off | — | 1.000x | 1.000x | 1.000x | — | 41/68 |
| not-first only | off | 0.893x | 0.884x | 0.760x | 34/36 | 41/68 |
| not-last only | off | 0.712x | 0.796x | 0.644x | 33/36 | 41/68 |
| **both** | off | **0.676x** | **0.668x** | **0.536x** | 36/36 | 42/68 |
| edge-finding | off | 0.169x | 0.127x | 0.099x | 36/36 | 46/68 |
| **edge-finding + both** | **edge-finding** | **1.024x** | **1.000x** | **1.001x** | **1/36** | **46/68** |

Edge-finding's row reproduces the table above exactly — same 36 of 68 in the
common set, same three ratios — which is the check that the two measurements are
comparable and that #752 changed nothing about #751.

**On its own the rule is worth real search**: two thirds of the recursions,
better on 36 of 36, and one more instance closed. Both halves pay, with not-last
the stronger — the same direction edge-finding's asymmetry runs on this family,
which is a small piece of evidence that the asymmetry belongs to the instances
rather than to either rule.

**On top of edge-finding it is worth nothing at all.** The median is exactly
1.000x and it is better on 1 of 36. It changes the search on **4** of the 36:
two by a handful of recursions in either direction, and two for the worse, by
0.7% and by 4.7%. That last one is the 1.024x summed figure on its own — it
carries 37% of the summed recursions, and dropping it takes the summed ratio to
1.000x. Neither arm closes a different set of instances.

**And it is not that the rule does not fire.** Propagation counts differ on 57
of the 68, so it fires nearly everywhere and reaches the same fixpoint by a
different route — sometimes in fewer propagator invocations, sometimes more.
Every bound it moves is a bound edge-finding was going to move.

That is a sharper verdict than the cumulative side's 0.997x, and the same one:
**certifiable for nothing, and worth nothing once the stronger rule is on.**
Hence off by default, and hence a table row rather than a recommendation. A rung
that is free to certify and measurably not worth running is a better row than a
gap, which is the whole reason it is here.

Across every instance more than one arm closed, all six arms proved the same
optimum — the check no proof lane can make.

### The published detection, and what it is worth: 37% more firings, 0.6% less search (#757)

What the section above certifies is a **strict weakening** of the rule as
published (Baptiste, Le Pape and Nuijten; Vilím's Θ-tree presentation).
The published conditions do not ask about the enumerated window at all:

```
p(Θ) > lct(Θ) − ect_j            not-first
p(Θ) > ub(s_j) − est(Θ)          not-last
```

Under the negated conclusion `s_j < min ect(Θ)`, every `i ∈ Θ` has
`s_j < ect_i`, so `j` cannot be *after* `i`, so `j` is *before* it — and
then all of `Θ` has to fit in `[ect_j, lct(Θ))`, a **narrower** window
than `[a, b)`, whose left edge the negated conclusion *derives* rather
than the reason carrying it. `DisjunctiveRules::not_first_not_last_published`
is that detection, over the same sweep, the same contained sets and the
same thresholds — the condition is the only thing that differs, which is
what makes the two comparable.

**Ours is a subset of it, and not by luck.** The window-energy figure
over `[a, b)` at `s_j = lb(s_j)` is at most `ect_j − a`, so
`p(Θ) + clipped > b − a` implies `p(Θ) > b − ect_j`: every firing of ours
is one of theirs, by arithmetic rather than by observation. Counting them
over the same transcribed sweep, and checking every published firing
against a full enumeration of its instance's solutions:

| draw | ours | published | only ours | firings that removed a solution |
|---|---|---|---|---|
| 20,000 instances, 4 tasks | 44,720 | 75,806 | **0** | **0** |
| 20,000 instances, 5 tasks | 89,039 | 143,525 | **0** | **0** |

So the published condition detects **1.7×** as much. The question #757
exists to answer is whether that is worth a certificate, and the
certificate is not free: `[ect_j, lct(Θ))` is keyed on `j`'s own lower
bound, so its activity flags, bridge rows, folds and guarded rows share
with nothing the sweep already derives — #737's caching result is about
windows the *instance* gives, and these move with the search.

**It is not worth it.** The same 68 instances and the same 60 s timeout
as the two tables above, so all three read together:

| arm | against | summed | median | geomean | better | closed |
|---|---|---|---|---|---|---|
| nfnl | off | 0.676x | 0.668x | 0.536x | 36/36 | 42/68 |
| **nfnl published** | **nfnl** | **0.994x** | **1.000x** | **1.002x** | 9/36 | 42/68 |
| ef | off | 0.169x | 0.127x | 0.099x | 36/36 | 46/68 |
| ef + nfnl | ef | 1.024x | 1.000x | 1.001x | 1/36 | 46/68 |
| **ef + nfnl published** | **ef** | **1.026x** | **1.000x** | **1.036x** | 4/36 | 46/68 |

Three of those rows reproduce the earlier tables to the digit, which is
the check that the runs are comparable. **The 37% detection gap buys
0.6% of the summed recursions and nothing at all at the median.** It is
not that the stronger detection sits idle — propagation counts differ on
**64 of 68** instances, and it changes the search on 21 of the 36 — but
every change is small and they run both ways: the best instance goes to
0.965x and the worst to 1.060x. On top of edge-finding it is a small
loss, and the 1.026x is one instance at 4.05x carrying it.

So the certificate is **not built**, and the switch is here as the record
of why. It throws rather than propagating under `--prove`: a rule that
quietly weakened itself when proof logging came on would confound exactly
the comparison it exists to make.

The result is worth more than the propagator would have been. #746 asks,
on the cumulative side, whether certifying a weaker detection than the
literature states costs anything real, and could not answer it. **This is
that answer, on the encoding where the gap is cleanest**: the weakening
is strict, it is 37% of the firings, and it is worth 0.6% of the search.
What is certifiable here is not what the rule can detect but what
detection is *worth* — and a rule that fires 1.7× as often reaching the
same fixpoint is the same finding as not-first/not-last reaching
edge-finding's fixpoint by a different route, one rung further down.

It also prices #754. Set-based detectable precedences want the same
derived-window mechanism, and their stage zero found `ect(Ω)` reaching
past everything else running on 2.9% of nodes — a *smaller* gap than the
one measured here to be worth nothing. That is not a reason to close
#754, whose gap is against a different rule's fixpoint rather than a
weaker form of its own, but it is the number to beat before building it.

## The set-based detectable precedence, measured before it is certified (#754)

#734 pushes `lb(s_j)` to `max_{k∈Ω} ect_k` over the detected
predecessors — the latest *single* predecessor's earliest end. Vilím's
rule pushes to the **set's** earliest completion time,

```
ect(Ω) = max_{Ω' ⊆ Ω} ( est(Ω') + p(Ω') )        lb(s_j) ← ect(Ω)
lst(Ω) = min_{Ω' ⊆ Ω} ( lct(Ω') − p(Ω') )        ub(s_j) ← lst(Ω) − p_j
```

which is larger exactly when the predecessors **cannot all fit** before
that point. `DisjunctiveRules::detectable_precedences_set`, off by
default, computed by a left-cut scan rather than a Θ-tree: the maximum
over subsets is attained at a cut, since taking every predecessor with
`est ≥ a` never lowers `est(Ω')` below `a` and only adds duration, so
one pass over the ests sorted descending gives it.

Measured before it was certified, which is #757's discipline: a stronger
rule ships as a switch first, because the certificate is the expensive
part and a detection gap need not be a search gap. Unlike #757 the answer
came back yes, so it **is** certified — see below.

### It is sound, checked against enumeration

A rule that removed a solution would measure as a large win, so the
sweep cannot make this check. Both left-cut scans were transcribed back
out of the propagator and every push reaching past the pairwise target
checked against a **full enumeration** of its instance's solutions:

| draw | pushes | past the pairwise target | removed a solution |
|---|---|---|---|
| 30,000 instances, 4 tasks | 125,060 | 33,307 | **0** |
| 20,000 instances, 5 tasks | 114,500 | 41,566 | **0** |
| 12,000 instances, 6 tasks | 87,214 | 37,710 | **0** |

### And unlike #757 it is worth building

The same 68 instances and 60 s timeout as the tables above:

| arm | against | summed | median | geomean | better | closed |
|---|---|---|---|---|---|---|
| **set-based** | pairwise | **0.547x** | **0.386x** | **0.289x** | 34/36 | **44/68** |
| ef | pairwise | 0.169x | 0.127x | 0.099x | 36/36 | 46/68 |
| **ef + set-based** | ef | **0.820x** | **0.941x** | **0.824x** | **23/36** | **47/68** |
| ef + nfnl | ef | 1.024x | 1.000x | 1.001x | 1/36 | 46/68 |
| ef + nfnl + set-based | ef + nfnl | 0.807x | 0.955x | 0.827x | 23/36 | 46/68 |

`ef` and `ef + nfnl` reproduce their earlier rows to the digit.

**On its own it is worth nearly half the search** and closes three more
instances, which is a lot for a rule that adds a linear scan rather than
edge-finding's cubic one.

**On top of edge-finding it is the first rung here that adds anything.**
Better on **23 of 36**, worse on 6, unchanged on 7, and it closes one
more instance — including `--size 18 --seed 5`, which *no other arm
closes at all*. Set that against not-first/not-last's 1 of 36 and the
published detection's 4 of 36, both at a median of exactly 1.000x.

Quote the median and the geomean, not the summed figure: the largest
instance carries **52%** of the summed total by itself, and dropping it
takes 0.820x to 0.971x. The rule's real size is 0.941x at the median
with a long tail — the best instance goes to 0.128x.

### The certificate, settled in simulation

Not edge-finding's at another threshold: **#757's shape, mirrored**.
That window has its *left* edge derived from the negated conclusion;
this one has its **right** edge derived, and is one unit too narrow for
`Ω'` exactly when the rule fires. So the guard the reason cannot
discharge is the **high** one rather than the low one, and everything
else is inherited — the simulation's `SetPrecedence` subclasses #751's
`Certificate` and adds two methods, as #757's `DerivedWindow` added one.

Writing `Ω'` for the maximising left cut and `T = est(Ω') + p(Ω')`:

1. Each `i ∈ Ω'` is a detected predecessor, so `before_{i,j}` follows
   from the reason by #734's own refutation pol, giving `s_i + l_i ≤ s_j`.
2. Under the negated conclusion `s_j ≤ T − 1` that gives
   `s_i ≤ T − 1 − p_i`, i.e. the two-literal clause
   `[s_j ≥ T] ∨ ¬[s_i ≥ T − p_i]` — and `T − p_i` is exactly the **high
   guard** of `i`'s guarded window-energy row over `[est(Ω'), T − 1)`.
3. Cite `guarded_energy(i, est(Ω'), T − 1, est(Ω'), T − p_i)` per
   `i ∈ Ω'`; the low guard falls to the reason (`est_i ≥ est(Ω')` is what
   a left cut means) and the high guard to step 2's clause, which leaves
   `[s_j ≥ T]` standing at that row's coefficient; fold the per-time
   at-most-ones over the window and sum.

The window is `p(Ω') − 1` wide and `Ω'` needs `p(Ω')` of it, so the pol
lands on `(Σ coeffs)·[s_j ≥ T] ≥ 1` and **derives** the conclusion rather
than assuming it.

Simulated standalone before any C++, as #730, #751 and #757 all were:
126 lines, veripb exit 0, every load-bearing row on its predicted shape,
and **all seven mutation lanes rejected** on a generated four-predecessor
fixture. Then built, and `disjunctive_set_precedences_test` carries the
same battery in the solver — six lanes (`emit_nothing`, `skip_fold`,
`drop_energy`, `drop_clause`, `rup_clause`, `one_too_far`), all
rejected — plus a `--search` lane that generated 60 instances, verified a
proof for each, and found the rule firing on 51.

`drop_clause` and `rup_clause` are the two aimed at what is actually new.
The first leaves out the derived clause, so the guard is never discharged
and the conclusion never enters the sum; the second asks whether unit
propagation can reach that clause on its own, and it cannot — the same
cross-variable limit `RupOverloadBridge` finds for the bridge.

As #731, #752 and #757 all found, the demonstration fixture is not the
one the lanes bite on: on `sharp` only four of the six do, because with
two tasks in the derived window the fold is a single bridge row the
closing RUP reconstructs. **`|Ω'| ≥ 3` is the threshold**, the same one
the simulation found, and the mutation fixture is a generated instance
with a cut of three.

**Steps 1 and 2 are not load-bearing, and step 3 is.** Replacing the
detection pol and the separation clause with a bare `rup b_ij ≥ 1`
verifies on **27 of 27** generated firings — which is not a corruption
surviving but the same fact reached another way: `before_{i,j}` is
RUP-available from the bounds the reason carries, because #734's
detection condition and its refuting pol's positive degree are the same
statement. Asking the same question of the *clause* (`rup_clause`) is
rejected, so the arithmetic in step 3 does need its pol. A propagator
should still emit all of it, for the reason #734 records about its own
two pols: it cannot cheaply tell which case it is in, and the cost is two
lines.

Unlike #757 the final division is **not** load-bearing here — the
surplus is exactly one, so the propagator leaves the closing RUP to read
the pol off, exactly as edge-finding's does.

### The trap the build hit, which no sweep would have caught

The first version read the bounds its arithmetic needed back out of
`state` inside the justification, and **every generated proof above a
handful of tasks was rejected**. By the time a justification runs, an
earlier push in the same propagation has landed, so the state holds a
bound the reason does not support — and a `pol` built on it is arithmetic
about a fact nothing has established. The ub push already carried a
comment recording exactly this for #734's own certificate.

The fix is that every bound the arithmetic reads is captured at
*detection* time and carried into the closure, which is why `SetTask`
holds `lb` and `ub` beside the edge its cut is sorted by. Worth stating
as a rule: **a justification may read the reason and the model, and
nothing else.** Anything else it reads out of `state` is a bound that has
since moved.

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

With optional tasks the clause carries the pair's presence disjuncts
too, so both tasks have to be *known present* for it to unit-fail —
which is also the semantics, since an absent task sits wherever it
likes. This is the only certified route to a strict optional
disjunctive: a task consuming nothing for no time is invisible to a
resource profile, so nothing built on `Cumulative` can express it, and
MiniZinc's `fzn_disjunctive_strict_opt` had no solver redefinition at
all before #735.

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

The standard suite's remaining rungs are tracked by #729. What each
would take from *this* encoding:

- **The set-based form of detectable precedences.** The rule above
  pushes to `max_k eet_k` over the detected predecessors; Vilím's
  pushes to `ect(Ω)`, the *set's* earliest completion time, which is
  larger when the predecessors cannot all fit before it. That is an
  energy statement about a set, so it is the same obstacle as the
  overload check below, not a variation on the pairwise proof.
- ~~**An overload check** (#730)~~ — done, #737–#741, and
  ~~**edge-finding** (#733)~~ — done, #751. Kept here in outline because
  the shape of the obstacle is what the two sections above are answers
  to. The conclusion,
  `Σ_{i∈Ω} p_i > lct(Ω) − est(Ω)`, is already in this document's
  vocabulary; the derivation is the problem, and giving `Disjunctive`
  per-time `active_{i,t}` flags to reach it would reintroduce exactly
  the scaffolding #495 removed. #730 records a machine-checked
  construction that avoids them — a proof-only comparator network over
  bit-encoded wires — verified for `k = 3 … 8` at equal durations, and
  a refutation rather than a propagator so far.
- ~~**Not-first / not-last** (#752)~~ — done, and its own section
  above. It did inherit #746's weakening, deliberately: the guarded row
  is what the detection may use, and at capacity one that turns out to
  cost more than it does on `Cumulative`, since the negation range
  straddles the hump. What the published unary rule detects instead, and
  whether the pairwise encoding can certify *that*, is #757.
- **Optional tasks for `Disjunctive2D`.** The 1D form has them
  (#735, above); the 2D 4-way separation clause would take the same
  two disjuncts per pair, but nothing asks for it yet.
- **A `cake_pb_cp` encoder for the optional form.** The pairwise
  encoding matches cake's for the non-optional constraint, which is
  why disjunctive proofs chain-verify, and the optional form differs
  from it by two literals per separation clause. Until cake has that,
  `disjunctive_optional` / `disjunctive_strict_optional` are outside
  the chain, which is what those names are for.
- **Conditional pruning for an undecided task.** Its own bounds are
  never pruned, because there is no conditional-bounds store and an
  unconditional prune would be unsound if the task turns out absent.
  The same applies to a precedence conditional on a presence, which
  would need the presence literals *inside* the pols rather than only
  in the reason. Both are real propagation left on the table, and
  `Cumulative` leaves the same amount for the same reason.

<!-- vim: set tw=72 spell spelllang=en : -->
