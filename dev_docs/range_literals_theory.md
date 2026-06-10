# Interval ("in") literals and the proof framework: what we preserve and what we lose

**Audience.** This is written for someone who knows McIlree's thesis — the binary
encoding `BinEnc(X)`, atomic literals `x≥v` / `x=v` and their definition constraints
(3.23)–(3.26), the intra-variable invariant **Inv1** and Theorems **3.2**/**3.3**, the
cross-variable Theorems **2.7**/**2.8**/**2.9**, and the backtracking invariants
**Inv2**/**Inv3** with **Theorem 3.4** — but *not* the range-literal work built on top of
it. It explains (1) the extra object we added to the encoding, (2) which thesis properties
that object preserves, (3) the one it does not, and (4) why that single gap breaks interval
*inference* for `Equals`, and hence for `Element` and `AllEqual`, while leaving reasons and
branching untouched.

The short version: **we preserve everything *intra-variable* — Theorem 3.3 generalises
cleanly to interval literals — but the framework's *cross-variable* propagation is governed
entirely by Theorems 2.7/2.8/2.9, and those give us value-crossings and two-bound
contradictions, never one-sided bound propagation. The per-value world never needs that
missing step; interval literals do, and so they cannot keep the backtracking invariant
(Inv2 / Theorem 3.4) for a constraint that prunes across a bit-sum equality.**

---

## 1. Recap of the machinery we build on

Two layers of the thesis matter here.

**Intra-variable (one CP variable's atoms).** For a single variable `X`, the order atoms
`x≥v` form a chain maintained by **Inv1** (Corollary 3.1: `x≥v ⇒ x≥w` is RUP for `v ≥ w`).
Given Inv1, Theorem **3.3** ("complete propagation of implied atomic literals") says: for any
restriction `R` of `X`'s atoms, if `F↾R` does not unit-propagate to contradiction, then *every*
literal in `ImpLits(dom_R(X))` propagates by UP or is already in `R`. Theorem **3.2** is the
companion: if `dom_R(X) = ∅`, `F↾R` unit-propagates to contradiction. Both are statements
about **one variable in isolation**; the eq atom `x=v` is the special case where `dom_R(X)`
is the singleton `{v}`.

**Cross-variable (between two binary sums).** Everything that crosses from one variable to
another goes through exactly three theorems:

- **2.7** — *contradictory bounds on one binary sum* (`Σ2ⁱℓᵢ ≥ A` and `Σ2ⁱℓᵢ ≤ B`, `A > B`)
  unit-propagate to contradiction.
- **2.8** — *equality of a binary sum to a single value* (`Σ2ⁱℓᵢ ≥ A` and `Σ2ⁱℓᵢ ≤ A`)
  unit-propagates to a **fixed assignment of all the bits** with `Σ2ⁱρ(ℓᵢ) = A`. This is
  bit-pinning: knowing the value pins every bit.
- **2.9** — a *contradictory cross-variable configuration* of two binary sums
  unit-propagates to contradiction.

A constraint justifies a propagation by combining intra-variable 3.3 on each variable with
its own cross-variable channelling. For an **equality** `X = Y` encoded as the bit-sum
`BinEnc(X) − BinEnc(Y) == 0`, the *only* cross-variable channelling available is 2.8 (a value
crosses) and 2.7/2.9 (a contradiction crosses). The thesis is explicit (Example 2.14, "Generalised
versions of Theorem 2.9 do not always hold") that this is the frontier — there is no general
rule for propagating an arbitrary linear fact across a binary-sum equality.

**Backtracking.** Whenever the solver backtracks it logs a *backtracking justification*
`Bt := Σ dᵢ ≥ 1` (3.40), the negation of the decisions on the current path. For these to be
checkable they must be RUP, and the thesis guarantees this via **Inv2/Inv3** and **Theorem
3.4**, summarised by the Gocht invariant the thesis quotes:

> *any variable-value deletion that is known to the CP solver … must be visible to the proof
> verifier either through unit propagation, or through reverse unit propagation of the
> backtrack clause.*

Concretely (Inv2): if the solver reached a conflict, `Ft ∪ {¬Bt}` must unit-propagate to
contradiction. This is the load-bearing requirement below.

---

## 2. The new object: interval ("in") literals

We add one kind of literal. An **interval literal** `[x in a..b]` is a fresh proof variable,
**reified to the variable's two boundary cuts** ("boundary-EO"):

    [x in a..b]  ⇔  (x≥a) ∧ ¬(x≥b+1)

with both directions logged as definition constraints, exactly analogous to (3.23)–(3.26) for
`x≥v` and `x=v`. It is a **generalised equality atom**: the eq atom `x=v` is precisely the
singleton `[x in v..v]`, whose boundary cuts are `(x≥v) ∧ ¬(x≥v+1)`.

We also maintain a **laminar containment** invariant between interval literals on the same
variable — for nested intervals (down to the eq atoms at the leaves), `child ⇒ parent` is
logged by RUP. This is the inter-literal analogue of Inv1: it lets a restriction that forces
`x` into a sub-interval propagate up to the containing intervals, and lets the negation of an
interval propagate down to the eq atoms it covers.

That is the entire addition: a wider class of "implied atomic literals" for each variable,
reified onto the existing order atoms, with an Inv1-style chain to keep them linked.

---

## 3. What is preserved — everything intra-variable

Because an interval literal is reified onto order atoms and linked by containment, it is a
genuine **implied atomic literal in the sense of Theorem 3.3**, and that theorem generalises
without change:

- **Inv1, Corollary 3.1, Lemma 3.2, Lemma 3.3, Theorem 3.2** are untouched — they are
  statements about the order atoms `x≥v`, which interval literals only reify, never alter.
- **Theorem 3.3 extends to interval literals.** With boundary-EO and containment maintained
  as invariants (the way Inv1 is maintained for the order chain), for a single variable `X`
  and any restriction `R` (which may now mention interval literals), every implied atomic
  literal — *including* the implied interval literals — propagates by UP or conflicts. The
  forward direction `(x≥a) ∧ ¬(x≥b+1) ⇒ [x in a..b]` and the reverse
  `[x in a..b] ⇒ (x≥a) ∧ ¬(x≥b+1)` are exactly the Def⇐/Def⇒ pair, and containment supplies
  the nesting.

This preserved property is precisely why the parts of the system that live **on one variable
at a time** all verify:

- **Reasons** — coalescing a run of `x ≠ v` in a reason into a single `¬[x in lo..hi]` is sound
  and RUP because it is an intra-variable restatement (Theorem 3.3 on `x`).
- **Interval branching** — a decision/`reject` of `[x in a..b]` and the backtrack clause over it
  are intra-variable; the containment chain gives the needed propagation (this is the
  hole/backtrack "axis" of the design, fixed by containment).
- **Single-variable inference of an interval literal** is RUP for the same reason.

Nothing in §§1–3 is in question.

---

## 4. What is **not** preserved — cross-variable bound propagation

The gap is entirely cross-variable, and it is a gap that *already exists* in the thesis
framework — interval literals merely stop us from dodging it.

Across a bit-sum equality `X = Y`, the thesis gives us:

| have | theorem | what crosses |
|---|---|---|
| `X = v` (a single value) | 2.8 | the value: `Y`'s bits get pinned to `v` |
| `X ≥ v` **and** `Y ≤ v−1` (two opposing bounds) | 2.7 / 2.9 | a *contradiction* |

What we do **not** have is the forward step:

> from `X ≥ k` alone, derive `Y ≥ k`.

This is not an oversight to be patched — there is no theorem for it, and (Example 2.14) the
obvious generalisation of 2.9 is false. A single bound `X ≥ k` does **not** pin `X`'s bits
(2.8 needs a value, not a bound), so the equality constraint has nothing to propagate from;
2.7/2.9 only fire once the *opposing* bound is also present, and then only to produce `0 ≥ 1`.
Unit propagation across a binary-sum equality moves **values and contradictions, never a lone
bound.**

The per-value world never has to make that move. Every cross-variable obligation it raises is
of the form `X = v` or `X ≠ v` — a single value — and so it is always a 2.8 crossing. **An
interval literal `[x in a..b]` with `a < b` asserts only the order atoms `x≥a`, `¬x≥b+1`; it
never pins bits** (2.8 fires only when `a = b`). So the instant a cross-variable obligation has
to pass through a wide interval literal, it becomes a *bound* obligation, the missing forward
step is required, UP stalls, and the obligation is not visible to the verifier.

In thesis terms: **interval literals preserve Theorem 3.3 but cannot preserve Inv2 (Theorem
3.4) for a constraint that channels across a bit-sum equality**, because Inv2 demands that the
solver's deletions be reconstructible by UP under `¬Bt`, and reconstructing a bound across the
equality is exactly the step 2.7/2.8/2.9 do not provide.

---

## 5. Why this breaks Equals — and hence Element and AllEqual

Take `Equals(X, Y)`, encoded as `BinEnc(X) − BinEnc(Y) == 0`. Its propagator removes from `X`
any value `Y` lacks. There are two distinct proof obligations, and only the first is fine.

**(a) The forward inference is fine.** Removing the interval `[lo,hi]` from `X` because `Y`
lacks it is logged with an explicit *bridge*: two bound-lemmas
`¬[x in lo..hi] ∨ (y ≥ lo)` and `¬[x in lo..hi] ∨ ¬(y ≥ hi+1)`, each RUP because its negation
supplies *both* opposing bounds and so triggers 2.9, followed by the conclusion
`¬[x in lo..hi]` by RUP. This is just Justification Procedure 3.2 (Comparison) materialising
each bound as a 2.9 contradiction. It verifies. The single-line interval inference is real.

**(b) The backtracking obligation is not.** The framework (Theorem 3.4 / Inv2) requires that at
every backtrack, `Ft ∪ {¬Bt}` unit-propagate to contradiction — every deletion the solver used
to reach the conflict must be visible under `¬Bt`. Whether this holds depends on whether those
deletions are *values* (2.8-visible) or *bounds* (need the missing forward step):

- With **two variables in isolation**, a conflict is reached by pinning or excluding values on
  `X` and `Y`; every obligation is a value, 2.8 carries it across the single equality, Inv2
  holds. This is why `equals_test` and `element_test` pass gate-on — they only ever post a
  single equality over two variables.

- With **three or more variables in one equality class** — `AllEqual`, a chain/star of `Equals`,
  or `Equals` composed with `Element` — the backtrack clauses range over several variables, and
  reconstructing the conflict requires a **bound to be threaded from one variable to another
  through a shared variable** (empirically: "`i₃ ≥ 3`, therefore `i₂ ≥ 3`" across `i₃ = hub = i₂`).
  In the per-value world this still decomposes into value-crossings (2.8) and Inv2 holds; once an
  interval literal is in play the obligation is a bound, the forward step has no theorem, UP
  stalls, `Ft ∪ {¬Bt}` does not reach contradiction, Inv2 fails, and the backtrack clause is not
  RUP. VeriPB rejects it.

So the failure is **not** specific to `AllEqual` and **not** a defect in any propagator's
justification. It is a property of the encoding: interval literals are order-atom-only, hence
2.8-invisible, and the moment three variables share a bit-sum equality the backtracking
invariant needs the one cross-variable step the framework does not have. `Element`
(index-fixed: `result − array_var == 0`) and `AllEqual` (a class of equalities) "do similar
things" to `Equals` and inherit the same fate. The two-variable tests give false confidence:
the property holds *in isolation* and is lost *under composition*.

---

## 6. Summary

| Property (thesis) | Status with interval literals | Why |
|---|---|---|
| Inv1, Cor 3.1, Lemma 3.2/3.3, Thm 3.2 | **preserved** | unchanged statements about order atoms |
| Thm 3.3 (intra-variable completeness) | **preserved, extended** | interval literals are implied atomic literals via boundary-EO + containment |
| 2.8 value-crossing of an equality | **preserved for eq atoms** | singletons `[x in v..v]` still pin bits |
| 2.8 crossing for a *wide* interval | **n/a — never held** | `[x in a..b]`, `a<b`, asserts bounds only; no bit-pinning |
| forward bound propagation across `X=Y` | **never held; now needed** | not implied by 2.7/2.8/2.9 (cf. Example 2.14) |
| Inv2 / Thm 3.4 backtracking-RUP, equality family, ≥3 vars | **lost** | conflict reconstruction needs the missing forward step |
| Inv2 / Thm 3.4, eq-atom/selector-channelled constraints | **preserved** | their channelling delivers per-value (2.8-visible) literals for 3.3 to reassemble |

**Consequence.** Interval *inference* is sound to enable only where every cross-variable
obligation stays a single value — i.e. for constraints whose channelling is per-value
(eq-atom / selector channelled: Table, Regular, GCC, Count, …), where Theorem 3.3 reassembles
the per-value literals and no bound is ever threaded across a bit-sum equality. For the
**equality family** (`Equals` / `Element` / `AllEqual`, all built on `BinEnc(X) − BinEnc(Y) ==
0`), interval removals do **not** compose past two variables, because the backtracking invariant
requires forward bound propagation across the equality and the framework provides only
value-crossing (2.8) and contradiction (2.7/2.9). Interval **reasons** and interval **branching**
are unaffected — they are intra-variable, and §3 covers them.

Restoring the equality family would mean supplying the missing cross-variable step explicitly:
a cross-variable analogue of Inv1, `(x≥k) ⇔ (y≥k)` logged for every equality at the boundary
values in play. That is a "covering" — exactly the per-value work interval literals were
introduced to avoid — now required globally across the equality family rather than locally.
Whether that trade is worth making is a design decision, not a bug fix.
