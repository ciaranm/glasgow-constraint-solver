# Justification techniques: why our proof steps are RUP

Every rule in a [constraint family document](constraints/TEMPLATE.md) carries a
**Proof technique** field, and for most rules in most families that field says
`RUP`. On its own that is a claim, not an argument: reverse unit propagation
succeeds only for particular shapes of constraint over particular encodings,
and "we emit `rup` and VeriPB accepts it" is evidence about one instance rather
than a reason it will always work.

This document is what licenses those names. It collects the small number of
unit-propagation facts the whole solver leans on, says which published result
proves each, and maps them onto the justification procedures our families
actually use. **A family document should cite a procedure and a theorem from
here rather than restating the argument** — and, where a family departs from a
published procedure, say so, because that is exactly where an external
justifier cannot replay a known recipe.

The results are Matthew McIlree's, *Pseudo-Boolean Proof Logging for Constraint
Propagation Algorithms* (University of Glasgow, 2026;
<https://theses.gla.ac.uk/86049/>). **Cite the final accepted version's
numbering**, which is what this document uses: Chapter 2's theorems and
Chapter 3's Encoding and Justification Procedures are unchanged from the
pre-examination draft, but the Chapter 2 examples and the Chapter 3 equation
numbers both shifted, so a number copied out of the draft may be wrong by one.

## What the arguments rest on

Chapter 3 is the authoritative treatment of our integer encoding; read it
before theorising about either the encoding or the proof framework. Three
things from it are load-bearing here.

**Two kinds of atomic variable, and only two.** A CP variable `X` gets *bound*
variables `x≥v` and *equality* variables `x=v`, the latter **defined on the
bound variables** rather than being their peer. Everything a propagator states
is a literal over those, so every question in this document is "does unit
propagation get from these atomic literals to that one".

**A binary backbone underneath.** `BinEnc(X)` is the bit-sum encoding of `X`
(two's complement when the lower bound is negative), O(log domain) variables,
and the linking constraints tie the atomic literals to it. This is what makes
the encoding logarithmic instead of per-value, and it is also why the facts
below are all about sums of the form `Σ 2ⁱ ℓᵢ`.

**The linking invariant `Inv1`.** Between any two defined bound literals on the
same variable there must be either an intervening defined bound or an explicit
implication between them. Maintaining it costs two RUP steps per bound literal
used, and it buys **Theorem 3.3 (complete propagation of implied atomic
literals)**: given any set of atomic literals on one variable, unit propagation
derives every atomic literal they imply. That is what "our careful literal
setup" means in practice, and it is the reason a propagator can state a bound
or an equality and expect the encoding to do the rest *within* that variable.
Getting from one variable to another is what the next section is for.

The framework-level results are **Theorems 3.4 and 3.5** with invariants `Inv2`
and `Inv3`: a solver that logs a propagation justification `R ⇒ ℓ ≥ 1` and a
conflict justification `R ⇒ 0 ≥ 1` for every inference, and maintains the
invariants, produces a checkable proof. Those are the reason the *shape* of
what we emit is right; the facts below are the reason each individual step goes
through.

## The five facts

| Fact | Result | Statement | What it licenses |
|---|---|---|---|
| Opposing bounds on one bit sum | **Thm 2.7** | `Σ2ⁱℓᵢ ≥ A` together with `Σ2ⁱℓᵢ ≤ B`, for `A > B`, always unit propagates to contradiction | any contradiction from two bounds on the same variable |
| An equality on a bit sum fixes every bit | **Thm 2.8** | `Σ2ⁱℓᵢ ≥ A` together with `Σ2ⁱℓᵢ ≤ A`, for `0 ≤ A < 2ᵏ`, always unit propagates to a complete assignment of the bits summing to `A` | a *value* crossing an equality — the fact behind `[x = v] ⊢ [y = v]` |
| A bound, a difference row, a bound | **Thm 2.9** | for `A + B − C > 0` and **`B ∈ {0,1}`**, a lower bound on one bit sum, a row `BinEnc(X) − BinEnc(Y) ≥ B`, and an upper bound on the other always unit propagate to contradiction | a *bound* crossing an equality half or a comparison row |
| A reified step reduces to its consequent | **Thm 2.6** | for `C := ρ ⇒ D`, `¬C` propagates every literal of `ρ`, so `C` is RUP with respect to `F` exactly when `D` is RUP with respect to `F↾ρ` | every reified verdict, and every justification stated under a reason |
| An emptied domain is a conflict | **Thm 3.2** | if `domR(Xi)` is empty for some set `R` of atomic literals on `Xi`, unit propagation on `F↾R` must conflict | the **collapse** step of every rule that rules out a variable's values one at a time and then concludes |

Theorem 2.6 is why a reason costs nothing structurally: stating an inference
under a conjunction of literals reduces to the unreified question with those
literals assumed. Theorems 2.7 to 2.9 are, in the thesis's own words, relied on
implicitly in several published works and had not been written down anywhere
before it.

Theorem 3.2 is the one to reach for when a derivation has the shape *"rule out
each value in turn, then conclude"*, which is what most of the non-binary
families do. The per-value lines establish that no value of some variable
survives; 3.2 turns that into the conflict the conclusion is RUP against. It
sits in Chapter 3 rather than 2 because it is about the *defined domain* of an
encoded CP variable, not about bit sums.

### Where the third one stops

**Theorem 2.9's `B ∈ {0,1}` precondition is load-bearing, and the boundary is
sharp.** It is tempting to assume the same triple propagates for any
`A + B − C > 0`; it does not. **Example 2.15** is a concrete counterexample
over two's-complement four-bit sums with a middle row of degree 3, and the
slack computation showing why unit propagation stalls.

What this means for us in practice:

- **An equality is covered.** Our equality encoding is two rows,
  `BinEnc(X) − BinEnc(Y) ≥ 0` and `≤ 0`, so each half has `B = 0` and a bound
  crosses it.
- **A comparison is covered.** `X ≤ Y` is `Y − X ≥ 0` and `X < Y` is
  `Y − X ≥ 1`, which is the whole of the `B ∈ {0,1}` range and the whole of the
  comparison family's encoding.
- **A general linear row is not.** A two-term inequality with a constant
  outside `{0,1}` is outside the theorem, which is why the linear family
  justifies its bound pushes through its own procedure (JP 3.15) rather than by
  appeal to 2.9.

That boundary also shows up empirically, which is worth knowing because it
makes fixtures misleading. The `equals` mutation lane that removes the bridge
lemmas is *accepted* by VeriPB at two domain widths out of thirteen tried —
both of them putting an interval endpoint on a bit boundary, where the bound is
a single literal rather than a sum and propagation crosses unaided. A narrow
fixture would have concluded the lemmas were unnecessary.

## The procedures we use

Chapter 3 §3.4 sets out a ladder of justification procedures — single-RUP,
multiple-RUP, cutting-planes, reified — and gives named procedures with
correctness proofs for the common constraints. These are the ones our audited
families land on:

| Procedure | Shape | Licensed by | Used by |
|---|---|---|---|
| **JP 3.1** (Not-Equals) | `rup x=v ∧ y=v ⇒ 0 ≥ 1` | Thm 2.8 | `equals`'s not-equal-to-fixed-operand rule |
| **JP 3.2** (Comparison) | `rup y≥v ∧ x≥u ⇒ 0 ≥ 1`, precondition `B ∈ {0,1}` | Thm 2.9 | every bound transfer in `comparison`, and `equals`'s bounds-intersection and interval-bridge rules |
| **JP 3.9** (Empty intersection for Element) | per `w` in the entry's domain, `rup R ⇒ y=v + xv=w ≥ 1`; then `rup R ⇒ y=v ≥ 1` | Thm 2.8 per line, Thm 3.2 for the collapse | `element`'s index-support rule |
| **JP 3.10** (Missing value for Element) | per index value `i`, `rup R ⇒ z=v + y=i ≥ 1`; then collapse | as JP 3.9 | `element`'s per-value result-union rule |
| **JP 3.11** (Single value for Element) | one step, `rup R ⇒ xi=v ≥ 1`, with the index a singleton | Thm 2.8 | `element`'s selected-entry rule, in the entry-pruning direction |
| **JP 3.12** (Equality propagation) | `rup y=v ⇒ x=v ≥ 1` | Thm 2.8, twice | `equals`'s equal-to-fixed-operand rule, and its per-value symmetric-difference fallback |
| **JP 3.13** (Equality infeasibility) | a per-value RUP for each surviving value, then a generic-reason contradiction | JP 3.12 for each line | **nothing any more** — see below |

JP 3.2's correctness proof is worth reading rather than taking on trust,
because it is careful about a case our encoding hits: if either operand is
*not* two's-complement encoded, the three constraints are not literally
Theorem 2.9's, but are in the state 2.9's own proof reaches after propagating
the most significant bit, so the argument still applies.

A transfer and an infeasibility are the same clause written two ways. JP 3.2 is
stated as a contradiction from two reason literals; a propagator that pushes a
bound emits the same clause with one literal moved to the conclusion, which is
the reified form Theorem 2.6 reduces back to the stated one.

### Where we depart from a published procedure

Two families have a rule that no procedure covers.

**`equals`'s disjointness witness no longer follows JP 3.13.** The published
procedure states "these two domains do not overlap" one value at a time: a RUP
line per surviving value, then a contradiction against the generic reason. That
is what gcs did until #881, and it is O(domain width) in both proof size and
reason length. The witness now used is an **interval walk** — an invariant
`v1 ≥ p` carried up the number line, one move per maximal run, at most two
lines per run — which is not in the thesis and is argued from scratch in
[`constraints/equals.md`](constraints/equals.md).

**`element`'s interval result-union rule has no published form either.** JP 3.10
states "this result value is supported by no entry" one value at a time. When
the result and every entry it considers are bare variables, `element` states the
same thing over an *interval* — which costs two extra bound lemmas per index
tuple to carry a range literal across the model's half-reified equality, and is
then independent of how wide the interval is. The per-value form is kept as the
fallback, and is JP 3.10 exactly. See
[`constraints/element.md`](constraints/element.md).

`element`'s bounds-consistency arm is a third case, and a milder one: its
derivation is JP 3.10's tuple walk with a bound as the conclusion instead of a
value. The procedure is not stated for that conclusion, but nothing in the
argument depends on which literal is concluded, so this is a gap in the
published list rather than a new technique.

That distinction is the one an external justifier most needs. Everywhere a
family cites a procedure number, a tool that knows the procedure can rebuild
the derivation from the assertion. Where a family says it departs, the tool
cannot, and the family document owes it a full argument instead. **So a rule
whose technique is a published procedure and a rule whose technique is ours are
different kinds of entry, and the field should say which.**

## How to cite this from a family document

In a rule's **Proof technique** field, give the technique name from
[Appendix A](constraints/TEMPLATE.md#appendix-a-proof-technique-vocabulary),
then the licence:

```
- **Proof technique** — `RUP`, by JP 3.12 (equality propagation), which is
  Theorem 2.8 applied twice; the condition literal comes along by Theorem 2.6.
```

and where there is no published procedure:

```
- **Proof technique** — `RUP+hints`. **No published procedure**: JP 3.13 states
  this per value, and the interval witness below is ours. Argued in full under
  *Why it is true*.
```

Two rules about scope, both learned the hard way:

- **Do not restate an argument that is proved somewhere.** A citation plus one
  sentence saying which literals play which role is more useful than a
  paraphrase, and cannot drift out of step with the source.
- **Do state the preconditions**, because they are what a reader needs in order
  to know whether the citation still applies after a change. `B ∈ {0,1}` is the
  example: a family whose row degree could grow past 1 has lost its licence and
  needs a different one.
