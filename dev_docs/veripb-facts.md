# What VeriPB checks, and what it does not

The rest of `dev_docs/` is about how to write a proof for a propagator. This
document is about the checker at the other end: what `veripb` actually does with
what we emit, where its cost goes, and what it can and cannot be asked to
establish.

Everything here was established empirically, against the Rust VeriPB that CI
installs — Cargo version `3.0.2`, built from a fresh `--depth 1` clone of
upstream `main` (see [building.md](building.md), which also explains why that
clone is deliberately unpinned). That makes these observations about a moving
target: they were each re-checked at the date given, and if the checker
surprises you, re-check rather than assume. Every one of them cost somebody a
session to learn.

Read this when a proof verifies and you are not sure it should, when a proof is
slow to check, or when you are deciding whether a derivation can be certified at
all.

## A green exit status is not a checked proof

There are two independent ways for `veripb` to exit 0 on a proof that
establishes less than you meant it to. Neither is a bug in the checker.

### The `s` line, not the exit code

A proof containing unchecked assertions (VeriPB's `a` rule, which the solver
emits for `AssertRatherThanJustifying`) verifies with exit status 0 and prints
`s UNDER ASSERTIONS …` instead of `s VERIFIED …`. Since `run_veripb` in
`constraints_test_utils.hh` reads only the exit status, a full green `ctest` is
exactly as green with cheats in it as without.

[constraints.md](constraints.md) ("Bringing up a new constraint", stages 3–5)
covers the staged bring-up this enables and the never-merge-an-assertion rule.
Two things to add to what it says: `--elaborate` is **not** a second gate —
3.0.2 takes `-e/--elaborate [<PATH>]` and, on an asserted proof, merely warns
that unchecked assertions have been written to the elaborated proof, exit 0
(re-checked 2026-09-10; the older hard refusal was a behaviour of the
`CP2026-enumeration` tag of the development checker, not of anything shipped).
And there is no `--force-…` flag for assertions the way there is for deletions,
so the burn-down count on a preserved proof is the only mechanical check there
is.

### A valid proof is not the proof you meant

A hand-built certificate for disjunctive edge-finding verified end to end —
`s VERIFIED UNSATISFIABLE` — while **every** order-ladder row in it had the
wrong coefficients.

The mechanism: a `pol` that ends `+ s` where the running degree is `d > 1`
saturates to `d·l₁ + d·l₂ ≥ d`, not to the unit clause, because saturation caps
a coefficient *at the degree*. Every row downstream of that is then correct but
slack, and a proof full of slack rows still closes whenever the wrapping
reason-carrying RUP can finish the job. Nothing in the exit code distinguishes
"the certificate did the work" from "the RUP did".

So for any hand-generated proof — a prototype, a simulation of a rule you have
not implemented yet, anything you are about to take a measurement off — run
`veripb --trace` and check every load-bearing row against a written-down
expected shape before believing conclusions drawn from it. The line counts of a
mangled certificate are not the line counts of the real one, so a cost model
taken from it is wrong too. [constraints.md](constraints.md) (Mutation testing)
is the complementary check for a proof the solver emits.

## What RUP can and cannot do

RUP unit-propagates one constraint at a time, including bit-level propagation
through bit-encoded integers — enough to fix individual bits of `a` when
`result` and `b` are known. It does **not** perform the cross-variable linear
combination "`a + b = result`, plus `b ≤ b_ub`, plus `result = v`, therefore
`a ≥ v - b_ub`". Combining several PB constraints into a tighter one is `pol`'s
job.

So when designing a stronger-than-bounds proof for an arithmetic constraint,
assume that any "narrow `X` using `Y` and `Z`'s bounds" deduction needs an
explicit `pol` step, and that the trailing RUP can only close *after* the bound
has been materialised. `Plus`'s bound inferences are the worked example
(`gcs/constraints/plus_minus/plus.cc`, which builds the `pol` and hands it to a
`JustifyExplicitly`); issue #192 is the case study where missing this made
per-value `result ≠ v` proofs fail verification. A
per-pair lemma like `(a ≠ a_v) ∨ (b = v - a_v) ∨ (result ≠ v)` *is* RUP-derivable
and useful, but it does not substitute for the bound-materialisation step.

The converse trap is real too, so check before reaching for `pol`. Converting a
`Cumulative`'s `cge` row plus a height's lower bound into
`Σ 2ᵏ cc_k + L·~active ≥ L` closes as a plain **hinted RUP**, always: negating it
forces `~active` to zero, leaving two power-of-two bit counters that unit
propagation walks down one bit at a time, every step single-constraint. Two
sweeps (1504 and 968 shapes, including contribution bits narrower than the
height's and non-power-of-two upper bounds), with negative controls that do fail,
confirmed it (#686). That is one line instead of O(bits) addends, and unlike a
`pol` it can carry hints. Before writing a saturate-and-restore `pol`, try the
RUP.

### A `pol` only has to get close

**The `pol` is not the certificate; the wrapping RUP is.** A firing emits a `pol`
and then RUPs its conclusion under the reason, so the `pol`'s result is just
another line in the database when that RUP runs. It only has to get close enough
that unit propagation can finish — not all the way to a contradiction.

Concretely, in `Cumulative`'s energy `pol`s, leaving a task's `active_{i,t}` terms
uncancelled produces a valid but weaker line, and UP then assigns those flags
from the reason's own bound literals (the reifications are full) and the line
goes violated. TTEF's certificate pins the non-contained tasks' mandatory load
for exactly that cancellation, and **dropping every one of those pins still
verifies on 235 of 248 searched instances**.

Two consequences, and the second is the more interesting one.

1. **A mutation that only removes energy from a `pol` is usually not a test.** It
   is a corruption VeriPB is right to accept. What bites instead is corrupting
   the *claim*, and only where the claim is **tight** — where some solution sits
   exactly on the bound being pushed to. Where a push is merely valid,
   one-too-far is valid too. A fixture therefore has to satisfy two conditions at
   once, and a hand-built one usually satisfies at most one.

   There is a second absorber, found on #746's published not-first/not-last
   (PR #772): **the detection's own margin**. Dropping a contiguity row costs the
   `pol` `lb(h_k)` units of degree, and a rule that fires at `> supply` has at
   least one to spare and usually many. Dropping those rows — the rows carrying
   the whole of what makes that rule stronger than window energy — could not be
   made to fail in either a one-row or an every-row form on any of ~1,700 firing
   instances, while `emit_nothing` was rejected on 171 of 238. A mutation lane
   for such a row needs a fixture whose margin is narrower than the smallest
   height involved, which for unit heights is impossible. When that happens, say
   so in the mutations header as *deliberately absent* rather than shipping a lane
   that always passes — and **keep the rows**: a `pol` that stops short of its own
   claim is not a certificate of the rule, however VeriPB finishes it.

2. **A cheaper certificate may be available by deliberately leaving work to UP.**
   Every term a `pol` cancels costs lines; the ones UP can reach from the reason
   are free. Nobody has measured how far this goes — the 13 of 248 above say it
   does not go all the way, and there is no cheap test for which firing needs
   what, so TTEF emits its pins unconditionally. "Which `pol` terms are
   load-bearing" is an open question about proof size, not just about mutation
   lanes.

### What a RUP step costs

A **hinted** `rup` unit-propagates over only the cited lines: cost O(|hints|). A
**hint-free** `rup` propagates over the entire live constraint database: cost
O(standing constraints). That asymmetry drives both hint emission and what may
be left living at `ProofLevel::Top`.

Two symmetric traps follow from it:

- **Hints must cover the whole conflict path.** Hints *restrict* propagation;
  there is no fallback to a full-database search when they turn out to be
  incomplete. `RUPProofRule{}` with an engaged-but-empty vector renders `: ;`,
  which restricts propagation to nothing. (One exception, found later: an empty
  hint vector does check when the negated claim is contradictory on its face,
  i.e. degree > Σ coefficients.)
- **Lines that never leave the database tax every later hint-free RUP.** A
  value-keyed cache that pushed ~45k lines to `Top` made a modulus proof check
  **9× slower** while being 7× smaller.

**How much hinting is worth is set by what is standing, not by what you are
emitting.** Hinting the lifted cover cut replay against a bare model — one
capacity row per time point, all scaffolding deleted — bought 25% of checking
time. The same change against a real RCPSP model, where the standing database is
the whole model, bought **6–14×** (`pack043`, 17.69 s → 1.24 s; #676 / PR #681).
Deleting your own scaffolding cannot touch the model underneath it. So a
derivation benchmarked in isolation and found not to need hints may well need
them inside a real proof, and a scaling harness built on a toy model will tell
you the opposite.

When choosing a proof level for a cache, go by key churn: keys that repeat
heavily across the search (a few hundred distinct values) can live at `Top`;
churning keys such as per-node bounds belong in a per-pass cache at `Current`,
where backtracking cleans them up.

Debugging aids, in rough order of usefulness:

- To tell an incomplete hint set from a wrong claim, `sed`-strip the hints and
  re-verify: if it then passes, the hints were incomplete; if it still fails, the
  claim is wrong.
- Claims emitted under a reason render `>= K:` with no space before the colon,
  which matters when grepping a proof.
- Unit propagation cannot cross `[v ≥ 5] → [v ≥ 1]` via the bit definitions.
  Derive the ladder clause from the two atoms' definition rows with a `pol` and
  hint that; the tracker's own ladder lines are not recorded as citable.
- `ia`'s implication check is itself "literal axioms, one saturation, literal
  axioms", so pinning with `ia` gets a saturate-and-restore for free.

[decision-diagram-proof-strategies.md](decision-diagram-proof-strategies.md)
turns this cost model into the `displacement × DB-tax` rule for deciding between
upfront and per-call scaffolding.

## Deletion is checked by where the target lives

The natural reading of "`del` is the unchecked rule, `delc` is the checked one"
is wrong. `DeletionChecker::check` enters the checked path according to whether
the deleted **IDs are in the core set**; `DeletionOrigin` only decides which
origins are *permitted*. So a `del` aimed at a core constraint is checked exactly
as a `delc` is, and rejects under `--force-checked-deletion` if the autoproof
fails.

What `delc` buys is therefore the **origin assertion**, not the check: `delc` on
a derived constraint is rejected outright ("Deletion of derived constraint ID N
using deletion from core set"). That is worth having for an emitter that deletes
by remembered line number, because getting the two the wrong way round then fails
loudly instead of silently. Relative (negative) ids work in `delc` and resolve
exactly — confirmed by aiming one a line further on and watching the autoproof
reject.

For a gcs `soli`, the `soli` line itself produces the objective-improvement
constraint in **core**, while a `rup` line — including the `~ge(v) >= 1` unit
emitted right after it — is **derived**.

[solution-clause-deletion.md](solution-clause-deletion.md) covers what happens
when a deletion check fails (a warning and a downgrade, not a rejection) and why
the suite passes `--force-checked-deletion` everywhere. The flag is a
**diagnostic, not a soundness requirement**: without it the downgrade is still
enforced at the conclusions that need it, but the error arrives at a distant
conclusion instead of at the deletion that caused it.

One more asymmetry to know about: **VeriPB polices the order encoding only at a
point of use, not at deletion.** Deleting definitions out from under a
still-resident line that names them also verifies. Eviction ordering is a
solver-side invariant, and a green proof is not evidence that the discipline
held.

## What the proof system can express

Background rather than day-to-day practice, but it settles a class of question
that keeps coming up — "can this be logged at all?" — and it has already stopped
one bad idea.

**Strength.** The redundance rule (substitution redundancy — the `red` lines
that `emit_red_proof_lines_reifying` writes behind
`create_proof_flag_reifying`; `create_proof_flag` alone only mints a name and
emits nothing) is *equivalent to extended resolution*. Dominance
lifts that to G₁, one level above, plausibly but **not provably** strictly
stronger; the hierarchy is not known to be strict. A single symmetry is
ER-simulable; multiple symmetries need the full rule. (Kołodziejczyk & Thapen,
"The Strength of the Dominance Rule", SAT 2024, Theorems 4 and 5.)

**Essentially no superpolynomial lower bounds are known** for anything at this
strength. So when we say we cannot log something, that almost always means *no
compact construction has been found yet*, not *it is proven hard*. The frontier
is constructive, not complexity-theoretic, and treating it as the latter talks
us out of things that are merely unbuilt.

**There is no general "derive once, cite many times" facility, and there cannot
be one here.** Cutting planes + such a facility is sound, and cutting planes +
dominance is sound, but cutting planes + dominance + it is **unsound**. Since we
rely on dominance, the facility is off the table in general, and the fallback is
to re-derive the fact per use and pay for it. (This is why "derive `v` is in no
`k`-clique once, then reuse it across pattern vertices" cannot be a generic move
in subgraph-isomorphism proofs.) The loophole, if anyone wants to chase it: the
unsoundness argument needs *strengthening inside the body* of the reusable step,
so inferences that never strengthen there may be a safe special case. That is an
open question, not a known construction.

Two corrections worth not relapsing into:

- **Parity / XOR is not a wall.** Gocht & Nordström certify XOR reasoning and
  Gaussian elimination efficiently: reify each XOR with a fresh variable via the
  redundance rule, then combine by cutting planes. It is a known construction,
  merely unimplemented here. (The barrier that does exist is for *plain* cutting
  planes without redundance, which is a different system from ours.)
- **Multiplication is the current frontier, not a proven barrier.** Bit
  decomposition gives a polynomial-size encoding, but bounds reasoning over it
  blows up. Whether a compact certificate exists is open — the same epistemic
  status as everything else above. [view-proof-logging.md](view-proof-logging.md)
  records the one case where a suspected "bit-composition wall" turned out to
  have an ordinary cause.

## Names and labels

VeriPB 3.0.2 allows `-` in **both** variable names and `@labels`. Earlier
versions allowed it in names only, and because the solver derives labels from
names, a negative value leaking into a label was illegal — which is why the tree
once spelled negatives `minusN`. PR #367 switched to rendering `-N` everywhere a
value goes into a proof name: `eq`/`ge` literals, interval literals, and
value-indexed flags. The old "must spell minus" rule is gone; do not reintroduce
it.

## See also

- [constraints.md](constraints.md) — justifications, mutation testing, and the
  staged bring-up that the `a` rule exists for.
- [decision-diagram-proof-strategies.md](decision-diagram-proof-strategies.md) —
  the upfront-vs-per-call cost model built on the RUP cost facts above.
- [solution-clause-deletion.md](solution-clause-deletion.md) — deletion in
  practice, and the core-set check from the solver's side.
- [variable-encodings.md](variable-encodings.md) — which encodings exist to be
  reasoned over in the first place.
