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
(They still matter for keeping the *up-front* order encoding compact and for
forward propagation; see the next section.)

## The one obligation VeriPB cannot witness

VeriPB only ever checks RUP **derivability**. The remaining hole is about
forward **unit-propagation**: that `[X≠v]` actually *propagates* from `¬r`
(so it lands in the propagated set `L`, keeping `domL ⊆ dom_t` and making the
literal reason-valid per Lemma 3.4). That is exactly what the standing
per-value link `r ∨ [X≠v]` is *for* — but "this clause causes that forward
propagation" is a framework property, not a checkable proof step, so it cannot
be probed here. It has to be argued in the metatheory.

## What is still owed before implementing

1. **Inv3 for the whole block** via the hole-aware `domL` (covers untouched
   values).
2. **Lemma 3.4 (valid reason) re-proved** admitting range literals into the
   reason vocabulary. The mixed-vocabulary conflict sweep above essentially is
   this argument; it needs writing up against the thesis definitions.
3. **Inv1′:** maintain `r ∨ [X≠v]` whenever `[X=v]` is defined inside a defined
   range. It is globally valid and never retracted, so no epoch bookkeeping —
   but the introduction path has to fire at atom-definition time, symmetric with
   how order/equality atoms are introduced today.

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
- **Cost of overlapping / splitting / merging ranges.** Each range introduces
  endpoint bound atoms (`[X≥a]`, `[X≥b+1]`) that must be linked into the order
  chain. With many ranges on one variable the Inv1 bookkeeping goes from O(1) to
  O(#ranges) per variable; weigh that against the per-value lines saved.
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
