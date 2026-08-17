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
what #752 exists for. `DisjunctiveRules::edge_finding`, off by default —
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
- **Not-first / not-last** (#752). The thresholds are the contained
  set's own `min ect` and `max lst` rather than a figure computed from
  the leftover energy. On the cumulative side this was edge-finding's
  certificate *unchanged* — a different threshold and a different guard,
  both already parameters of the guarded lemma — so expect the same
  here, and expect it not to be worth its scan (0.997x there, closing
  fewer instances). Do not inherit #746's weakening silently: at
  capacity one the papers' standing assumption may be easier to
  discharge, which would be a result rather than a caveat.
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
