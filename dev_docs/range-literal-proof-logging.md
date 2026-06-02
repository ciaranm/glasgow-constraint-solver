# Range-literal proof logging (design note)

**Status: design note, not implemented.** This documents an *approach* for
logging a whole-interval domain removal (`X ∉ [a,b]`) as a compact proof
object instead of one RUP line per removed value, together with the VeriPB
experiments that establish it is sound at the checker level. It is the
proof-logging half of issue #144 (`infer_not_in_range`). Nothing here is
wired into the solver yet; the remaining metatheory is listed at the end.

Read [`view-proof-logging.md`](view-proof-logging.md) first if you want the
template for "an idea on top of chapter 3, then what it means in practice" —
this doc follows the same shape, and reuses the same foundations (order/equality
atoms over a `BinEnc(X)` bit-vector, RUP / `pol` / `red`, an inference logged as
the clause `¬R ∨ ℓ`).

## The problem

A propagator that removes a contiguous block `[a,b]` from `X`'s domain today
logs one `infer_not_equal` per value, i.e. `b − a + 1` RUP lines. For a wide
interior hole that is the dominant proof cost at that site. The question is
whether the *interval* can be a first-class proof object: introduce a single
literal `r = [X ∈ [a,b]]` and log a single inference `¬r`.

## Why the naive single-Boolean fails

Mint `r ⇔ ([X ≥ a] ∧ ¬[X ≥ b+1])` and infer `¬r`. This is *sound* (you may
introduce `r` by `red`) but **inert**, and it breaks the backtracking-proof
invariant from chapter 3 §3.3.

Recall (Inv3): for a correct backtracking proof, the atom literals that
unit-propagate under `F_t ∪ {¬B_t}` must keep `domL(X) ⊆ dom_t(X)` — the
verifier's picture of `X` must stay at least as strong as the solver's. Now
assert `¬r`. The two forward clauses (`r → [X≥a]`, `r → ¬[X≥b+1]`) are
satisfied and dormant; the backward clause reduces to the **binary clause**
`¬[X≥a] ∨ [X≥b+1]`, which has two unassigned literals and therefore
unit-propagates **nothing**. So:

- `domL(X)` still contains all of `[a,b]` while the solver's domain doesn't —
  Inv3 violated.
- `r` is not an atom, so it cannot appear in a reason (reasons are sets of
  atoms, §3.3.2 / Lemma 3.4), and RUP cannot case-split the disjunction to
  recover any `[X ≠ v]`.

This is the disjunctive-reification trap, and it is the same wall the chapter-3
encoding is built to avoid. A naive `r` is a disjunction wearing an atom's
clothing.

## The encoding that works

Treat a range exclusion as a **guarded long-range link on the order-encoding
chain**. Ordinary order linking is `[X ≥ v+1] → [X ≥ v]`; the range's backward
reification clause is the same kind of link, just conditioned on `¬r`.

Three ingredients:

1. **Fully reify the range literal — do not half-reify it.** The backward
   clause `r ⇐ ([X≥a] ∧ ¬[X≥b+1])` *is* the guarded shortcut. Under `¬r` it
   delivers, from one 3-literal clause, **both** bound jumps:

   ```
   ¬r ⇒ ( [X≥a]      ⇒ [X≥b+1] )    lower bound jumps the dead block
   ¬r ⇒ ( ¬[X≥b+1]   ⇒ ¬[X≥a]   )    upper bound drops below it
   ```

   No second clause is needed for "the other side"; the single backward clause
   propagates either way depending on which bound is already known.

2. **Lazy per-value link.** When an equality atom `[X = v]` is *defined* and `v`
   lies inside a defined range `r`, also emit the clause

   ```
   r ∨ [X ≠ v]          ("¬r ⇒ X ≠ v")
   ```

   This is RUP (proof below), globally valid (true in every solution:
   `X=v ⇒ r`; `X≠v ⇒ [X≠v]`), and never retracted. It is what restores the
   "any valid literal is a reason / don't care *how* a value was excluded"
   property for interior values you actually touch — once it is present,
   `[X ≠ v]` unit-propagates from `¬r` like any ordinary excluded value.

3. **Hole-aware `domL`.** The verifier-side definition of `domL` must let a true
   `¬r` subtract the whole block `[a,b]`, so Inv3 holds for the values you
   *don't* mint an atom for. This is notation, not a proof step.

The division of labour is exactly: ingredient 2 (lazy clauses) restores
reason-usability + Theorem 3.3 for *touched* values; ingredient 3 (hole-aware
`domL`) restores Inv3 for everything else.

### Why `r ∨ [X≠v]` is RUP

Assume the negation `¬r ∧ [X=v]` with `a ≤ v ≤ b`:

1. `[X=v]` → `[X≥v]`, `¬[X≥v+1]` (its definition);
2. `[X≥v] ⇒ [X≥a]` (order chain / bit layer) → `[X≥a]`;
3. `¬[X≥v+1] ⇒ ¬[X≥b+1]` (order chain) → `¬[X≥b+1]`;
4. `[X≥a] ∧ ¬[X≥b+1]` fires the backward clause → `r`;
5. `r ∧ ¬r` → conflict. ∎

## What VeriPB confirms

Probes were run against **VeriPB 3.0.2** (the scratch harness lives outside the
tree; see issue #144 for the scripts). The encoding uses a two's-complement
`BinEnc` with a sign bit, and constants spaced with gaps **≫ 2 bits** so that
RUP cannot succeed by a small-value coincidence in the bit layout. Two harness
gotchas worth recording: VeriPB's OPB parser **rejects single-character
variable names** (use ≥2 chars), and a proof needs the
`output NONE; conclusion …;` trailer or it is a parse error.

Decisive results, all as predicted:

| check | verdict |
|---|---|
| per-value link `r ∨ [X≠v]` derivable by RUP — pinned **and** sign-crossing range | VERIFIED |
| mixed-vocabulary empty-domain sweep (bound + equality + range holes tiling a domain) → conflict | VERIFIED UNSATISFIABLE |
| bound-jump across a dead range, **both** bounds, **both** signs, value *unpinned* (only a bound known) | VERIFIED |
| bogus claims (`r ∨ [X≠v]` for `v ∉ [a,b]`; assert a refuted `r`) | correctly REJECTED |

The empty-domain sweep is the Theorem 3.2 analogue for the *mixed* vocabulary:
bound, equality, and range literals together tile a domain to empty and unit
propagation reaches conflict by a single left-to-right walk that jumps across
range blocks and steps over individual equality holes.

### The ablation (what is actually load-bearing)

`--elaborate` shows a *sufficient* propagation path, but unit propagation is
confluent, so a single elaboration is not evidence a constraint is *necessary*.
To get necessity, an exhaustive single-constraint ablation was run on a
downstream inference (`¬r ⇒ [X≠v] ⇒ z`): delete each formula constraint in
turn, re-check whether `z` still derives. **9 of 16 constraints are individually
necessary**, and the necessary set traces exactly one chain:

```
¬z → [X=v] → BinEnc=v → {[X≥a], ¬[X≥b+1]} → [backward reif clause] → r → ⊥
```

The sharp finding: the **backward reification clause is necessary**, while
**both forward `r` clauses are redundant** for this inference. That is the
formal content of "a range exclusion is specifically a *backward* long-range
link" — half-reifying the range (forward only) makes the downstream inference
correctly fail to verify, because with only forward reif `¬r` constrains
nothing about `X` and `[X≠v]` is genuinely not entailed.

### A surprise about the order-encoding chain

The explicit chain-link constraints (`[X≥u] → [X≥w]`, Inv1) turned out **not**
to be load-bearing for any of these *RUP derivations*. VeriPB unit-propagates
straight through the `BinEnc` bit layer, and two contradictory bounds on the
same two's-complement bit-vector already conflict (chapter 3 Lemma 3.2 /
Theorem 2.7). So for *derivability* the chains are an efficiency aid, not a
correctness requirement — the bit layer does the linking the chains would.
**This is a statement about Theorem 3.2 (empty domain → conflict) only.** It
does *not* transfer to forward propagation: for Theorem 3.3 (next section) the
per-value links are strictly load-bearing, as the failure example there shows.
The two theorems have different load-bearing constraint sets; do not read
"chains are cheap for the conflict" as "linking is cheap in general."

## The central obligation VeriPB cannot witness: forward propagation (Theorem 3.3)

VeriPB only ever checks RUP **derivability** — that a claimed clause *follows*.
It says nothing about which literals a solver's unit propagation will *reach*.
The empty-domain sweep and the ablation above are both about Theorem 3.2 (a set
of literals defining an empty domain unit-propagates to conflict). The harder
theorem — and the one that is actually *central* to making `infer_not_in_range`
usable — is **Theorem 3.3**:

> if a set of literals `L` defines a domain `D`, then unit propagation of `L`
> propagates **every defined literal implied by `D`**.

This is where a naive `¬r` silently fails *as a reason source for other
propagators*, even though the `¬r` inference itself is fine. The example is
Matthew's. A propagator logs `reason_1 ⇒ ¬r` for `r = [X ∈ [10,20]]`, so the
solver now knows `X ≠ 15`. A *different* propagator — `X = Y`, or `Abs(X,Y)` —
carries the reason clause

```
[X ≠ 15] ⇒ [Y ≠ 15]        i.e.   [X=15] ∨ [Y≠15]
```

and `15` is the last value left for `Y`. We expect to backtrack now with the
clause `[guesses] ⇒ 0 ≥ 1`. For that to be RUP, unit propagation under
`[guesses]` must reach the conflict:

- `[guesses]` propagates `reason_1`, which propagates `¬r`. So far so good.
- But `¬r` is the **inert disjunction** again (`¬[X≥10] ∨ [X≥21]`, two
  unassigned literals): on its own it propagates **nothing** about `[X=15]`. The
  reif clauses are all satisfied or dormant under `¬r` (§"Why the naive
  single-Boolean fails"). So `[X=15] ∨ [Y≠15]` never fires, `[Y≠15]` never
  propagates, `Y=15` is never refuted — **no conflict, and the backtracking
  clause is not RUP.**

The fix is exactly ingredient 2, the per-value link `r ∨ [X≠v]`. With
`r ∨ [X≠15]` present, `¬r` unit-propagates `[X≠15]`, the downstream clause fires,
`Y=15` conflicts, and the backtracking clause closes. So the per-value link is
**load-bearing for forward propagation** — in direct contrast to the order
chains, which the ablation found redundant for the Theorem 3.2 derivation.
"This clause causes that forward propagation" is a framework property, not a
checkable RUP step, so it cannot be probed; it has to be argued in the
metatheory, and that argument *is* Theorem 3.3 for the extended vocabulary.

### What the closure actually costs

Theorem 3.3 ranges over *every* defined literal implied by `D`, so the
obligation is not "one clause" but a **closure** maintained incrementally on
*both* atom-introduction paths:

- a new range `r` over `X` ⇒ emit `r ∨ [X≠k]` for every already-defined `[X=k]`
  with `k ∈ r`;
- a new equality `[X=k]` ⇒ emit `r ∨ [X≠k]` for every already-defined range
  `r ∋ k`.

In the worst case that is **O(#defined equalities × #defined ranges)** clauses
per variable — a cross-product. Better than the O(width) per-value loop we set
out to avoid, but not the O(1) the order chain gives for bounds. It plausibly
extends to **range–range** pairs: if `[X ∈ [12,18]]` is itself a defined literal
then `¬r` for `r = [X∈[10,20]] ⊇ [12,18]` implies `¬[X∈[12,18]]`, so a propagator
using *that* as a reason needs `r ∨ ¬[X∈[12,18]]` for the same forward-propagation
reason. The one bound that survives: a link is only ever needed for a literal
that *exists in the vocabulary*. Nobody can use `[X≠15]` as a reason unless
`[X=15]` was defined, so the closure is over the lazy/defined set, not the
domain — for a handful of holes and ranges it is small. It is just not free, and
the bookkeeping must be correct on every introduction event.

### Recovering near-linear: a containment chain

There is an order-chain analogue that collapses the cross-product back toward
linear for the common case. Link each defined range to its **tightest enclosing**
defined range (`r_outer ∨ ¬r_inner`), and link each equality only to its tightest
enclosing range (`r_tightest ∨ [X≠k]`). Unit propagation then **composes down the
containment chain**: `¬r_outer → ¬r_inner → [X≠k]`. For range families that
**nest or are disjoint** — exactly what repeated `infer_not_in_range` on a
shrinking domain tends to produce — this is O(#defined literals) with
composition, just as Inv1 collapses the bound pairs.

It degrades under **arbitrary overlaps**: `[10,20]` and `[15,25]` do not nest,
"tightest enclosing" is not unique, and an equality at `17` (in both) deriving
from `¬[10,20]` *alone* will not propagate if `17` was linked only to `[15,25]`.
Under heavy overlap you are pushed back toward the cross-product. Not fatal, but
the clean cost depends on the range family's shape — worth measuring before
preferring ranges to per-value lines at a given propagator.

## What is still owed before implementing

1. **Theorem 3.3 (propagation completeness) for the extended vocabulary — the
   central deliverable.** Prove that, with the link closure maintained, unit
   propagation of any literal set propagates *every defined* bound / equality /
   range literal implied by the resulting domain. This is the subtle,
   bookkeeping-driven induction the forward-propagation example turns on, and
   the one most prone to a plausible-but-wrong paper proof — a good candidate
   for the proof-assistant formalisation we have been discussing separately.
2. **Inv3 for the whole block** via the hole-aware `domL` (covers untouched
   values).
3. **Lemma 3.4 (valid reason) re-proved** admitting range literals into the
   reason vocabulary. The mixed-vocabulary conflict sweep above essentially is
   this argument; it needs writing up against the thesis definitions.
4. **Inv1′ + the introduction-path wiring.** Maintain the link closure
   (`r ∨ [X≠v]`, and range–range links, in containment-chain form where the
   family nests) on *both* atom-introduction paths — new range and new equality.
   It is globally valid and never retracted, so no epoch bookkeeping, but the
   introduction hooks must fire at atom-definition time, symmetric with how
   order/equality atoms are introduced today.

## Practical takeaways for when this is built

- **Solver-side `infer_not_in_range` is a clean win regardless** of the proof
  story — it collapses per-value loops at the four Pattern-A sites in issue
  #144 into one call.
- **The compact proof object only pays off for persistent interior holes.** A
  block flush against a current bound is already a single bound move
  (`infer_greater_than_or_equal` / `infer_less_than`); don't encode those as
  ranges. The win is one RUP step per *touched* `(equality atom, containing
  range)` pair — **not** per value in the range — plus the `¬r` inference
  itself.
- **The forward-propagation closure is the real cost, not the bound chain.**
  Each range introduces endpoint bound atoms (`[X≥a]`, `[X≥b+1]`) linked into the
  order chain — that part is O(#ranges). The bookkeeping that actually bites is
  the per-value (and range–range) link closure that Theorem 3.3 needs: worst case
  O(#defined equalities × #defined ranges) per variable, collapsing to
  O(#defined literals) only when the ranges nest or are disjoint (containment
  chain). Heavy overlap degrades it back toward the cross-product. Measure the
  range family's shape before preferring ranges to per-value lines.
- **Never half-reify a range literal.** The ablation shows the backward clause
  is the load-bearing one; emit the full `red`-introduced biconditional.

## Related

- Issue #144 — `infer_not_in_range` / `infer_in_range` / `IntervalSet::erase_range`,
  and the discussion thread with the probe scripts and ablation harness.
- [`view-proof-logging.md`](view-proof-logging.md) — same "RUP cannot compose
  across constraints; pre-derive atom-level links so UP can" theme, in a
  different setting.
- [`reification.md`](reification.md) — the full-vs-half reification machinery a
  range literal would be built on.
- Chapter 3 of Matthew McIlree's thesis — §3.3.1 (atomic-literal properties,
  Inv1, Theorems 3.2/3.3), §3.3.2 (backtracking proofs, Inv2/Inv3, Lemma 3.4).
