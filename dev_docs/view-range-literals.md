# Range ("in") literals on views

How the two mechanisms in `dev_docs/range_literals_spec.md` and
`dev_docs/view-proof-logging.md` combine. Neither document covered this, because
until issue #882 they did not combine: a `ViewOfIntegerVariableID` had no range
literal at all, and every part of the solver that wanted to say something
interval-shaped about a view carried its own detour — three that threw, and five,
later seven, that silently degraded to one literal per value.

**Theory.** The general account — what these literals are, what the invariants
are, and why the design is complete — is
[literal-encodings.tex](literal-encodings.tex), which subsumes the argument that
used to be §5 here. This document is the issue-#882 implementation record: the
sites that changed, the trigger that is easy to get wrong, the ablation table,
and what was measured.

**Audience.** Anyone touching `need_invar`, `simplify_literal`, the view
machinery in `NamesAndIDsTracker`, or a propagator that emits explicit `pol`
over a range literal. Read both of the documents above first; this one assumes
the partition/covering/containment apparatus of §3 of the range spec and the
three view invariants of the view document.

## 1. The design in one paragraph

A registered view `V = sX + c` already owns its own bit vector `BinEnc(V)`, its
own order atoms and its own equality atoms, joined to `X` by a single
definitional link axiom plus lazily emitted atom-level biconditionals. Range
literals join that list: `[V in a..b]` is an ordinary range literal over `V`,
reified against `V`'s own two order cuts, with `V`'s own partition, coverings
and containment edges. Every interval named on either side is mirrored onto the
other — *named*, not requested, which §3 is entirely about — and the two
literals are joined by **two** rup clauses. Nothing
above the encoding layer knows any of this happened: a propagator says
`infer_not_in_range(operand, lo, hi)` and states hole runs as range conditions
over the operand, whether or not the operand is a view.

The alternative — rewriting a view's range conditions onto `X`, as
`simplify_literal`'s deview arm does for the four scalar operators — was
rejected. It would make ranges the one atom kind that is *not* in `V`-form,
and a `pol` step resolving a range literal against a `V`-form constraint body
would then strand (view invariant 1). The deview arm still handles range
conditions, but only on the path it already handled the others: an
*unregistered* view, seen for the first time during proof logging, which has no
encoded variable to be consistent with.

## 2. The link pair

For a registered view `V = sX + c` the interval `[a, b]` on `V`'s value scale
corresponds to

    s = +1:  [a - c,  b - c]
    s = -1:  [c - b,  c - a]

on `X`'s — the endpoints swap for a negated view, and the map is its own
inverse. `interval_on_underlying` and `interval_on_view` are the two directions.
Width is preserved either way, which is why a width-1 request is the eq atom on
both sides and never reaches this machinery.

Writing `F_V` for `[V in a..b]` and `F_X` for its image, the two clauses emitted
are `~F_V | F_X` and `~F_X | F_V`. **Both are needed, each for its
contrapositive rather than its implication** — as implications both directions
are already derivable by unit propagation, which is what issue #882 observed, and
is true but beside the point. *The argument is the remark "Both in-link clauses
are needed, and neither for its implication" in
[literal-encodings.tex](literal-encodings.tex).*

Why the negative directions come up at all is the part specific to this code:
search branches on real variables only (`reject_random_interval` requires a
`SimpleIntegerVariableID`), while `generic_reason` states hole runs over the
*operand*, which under a wrap is the view. So a range decision on `X` routinely
has to reach a reason literal on `V`, and a conclusion on `V` a reason stated
over `X`.

## 3. Linking is triggered by *naming*, not by requesting and not by defining

This is the part that is easy to get wrong, and getting it wrong is silent.
*Why naming is the right trigger is the remark "Why naming, not requesting, is
the trigger" in [literal-encodings.tex](literal-encodings.tex);* what follows is
where it lives in the code.

A range literal comes into existence two ways. Either a caller asks for it — a
conclusion, a reason element, a branching guess — reaching `need_invar`; or the
partition machinery creates it as a **cell**, from `ensure_partition_cut` or
`init_interval_partition`, straight through `define_plain_invar`, never going
near `need_invar`. A cell is therefore never "requested", and both
`need_proof_name` and `xliteral_for_ensuring` short-circuit on a condition that
already has a proof name. So "link the literals that are requested" leaves every
cell unlinked.

`mirror_invar_across_view_link` is therefore called from two places: from
`need_invar`, *outside* the "already defined" guard, and from
`xliteral_for_ensuring` whenever a range condition that already has a name
reaches a proof line. It is idempotent, and a set probe after the first time.
`ProofLogger::emit` and `emit_under_reason` render with `EnsureNames::Yes`, so
every `rup` / `a` / `ia` line takes each range condition through
`xliteral_for_ensuring`; only the `red` reifications bypass it.

**The invariant to preserve is that every non-`red` emission names its
literals.** A path that rendered a range literal without going through
`need_all_proof_names_in` or `xliteral_for_ensuring` would leave a cell
unlinked, and nothing would notice.

*Correction (2026-09-09).* An earlier version of this section claimed there is
no such thing as an unnamed range literal. That is false: a literal whose
in-bounds part is empty is defined by `define_invar_with_covering`'s
`span_lo > span_hi` branch with no partition, no covering and no containment
edge, and nothing names it. `Inv-View` survives because such a literal can only
arise from a request, and `need_invar` mirrors unconditionally — but the
"everything is named" form of the argument does not hold, and the invariant in
`literal-encodings.tex` is stated over cells for exactly this reason.

One consequence worth knowing: `need_invar` is genuinely re-entrant, because
resolving a literal while emitting a covering can re-enter it.
`ensure_partition_cut` publishes a partition boundary *before* defining the two
halves it creates, so for that window the partition claims a cell that does not
exist yet. `define_invar_with_covering`'s single-cell path defines it in that
case, and `define_plain_invar` is idempotent so the split does not define it
twice.

## 4. The two sides hold the same literals, but not in the same roles

The two sides end up holding the same set of literals up to the affine map.
Measured on `equals_test --view-position=mixed`, 258 proofs, every registered
(variable, view) pair whose view appears in the proof: 300 pairs, 300 matches,
no exceptions.

What does *not* correspond is a literal's **role**. `need_direct_encoding_for`'s
eq-atom backfill re-enters `ensure_partition_cut` on the far side before the
request's own second cut arrives, so the two sides reach the same set by
different routes, and the same interval can be a cell on one side and a request
with its own covering on the other. Measured over 400 sweep proofs: 66 contained
such a difference, 297 literals in all, every proof verifying. So the split
coverings and the containment DAGs genuinely differ.

*Why that does not matter — argue per side, never by isomorphism — is Theorem
3.3' and the paragraph after it in
[literal-encodings.tex](literal-encodings.tex).*

## 5. Why this is complete

*Resolved and moved.* The argument — mirror closure, unit transport, per-side
UP-completeness — is proved over a whole view family in §3.3.1 of
[literal-encodings.tex](literal-encodings.tex), as `Inv-View`, Lemma 3.E and
Theorem 3.3. What it depends on, and so what would break it: that every non-`red`
emission names its literals (§3); that every domain change is logged eagerly; and
that in-bounds endpoints are partition boundaries, which is why
`need_direct_encoding_for` cuts at `v` and `v+1` when a partition exists.

## 6. The coincidence trap — read this before believing a green test

The negative crossing succeeds **with no linking clause at all** in about 80% of
small random configurations, and over 987 conflict-reaching instances, ablating
the links makes only 37 notice. A green `--view-wrap` sweep is therefore close to
no evidence. *The four mechanisms that make it pass by coincidence, with the
measurements, are "The coincidence trap" in
[literal-encodings.tex](literal-encodings.tex).* W6–W9 are constructed against
them.

## 7. The witnesses

`range_witness_w{6,7,8,9}_test.cc`, all gate-on and veripb-verified. *What each
one guards, and the ablation matrix showing every clause and rule separately
load-bearing, are in the "Interlude" of
[literal-encodings.tex](literal-encodings.tex).*

`invar_view_test.cc` sits alongside them and covers something different: the
`need_pol_item_defining_literal` range arms, which no propagator reaches, and the
sign arithmetic of the endpoint map in both directions — checked with
`find_xliteral_for`, which does not introduce what it fails to find, so "the
mirror exists at exactly these bounds and not at the neighbouring ones" is a real
assertion. Both an off-by-one and a dropped endpoint-swap mutant are killed by
it. It deliberately does **not** witness the link clauses, and says so.

Two notes for anyone adding to this set. A witness stated as a RUP line of the
fact you care about tests nothing at all, because RUP is strictly stronger than
the single unit-propagation pass the links exist for. And a decision naming a
literal that is not a **cell** on both sides is not discriminating either:
containment carries the negation down to the cells, the cells' own link pairs
cross, and the far side's covering lifts it back, so no single clause is
load-bearing there. Ablate before claiming a witness bites.

## 8. Cost

Per interval literal per registered view: the mirrored literal on the other side
(with its own partition maintenance) plus two rup lines — the same constant
factor the eq and ge atoms already pay for a wrapped variable, and nothing
proportional to a domain width. *The measured table, including the `17 + 71w`
per-value fallback this replaced and where it stopped being writable at all, is
the "Cost" part of [literal-encodings.tex](literal-encodings.tex).*

VeriPB checks every `after` row in about 0.012 s. The `before` row at 10^3 takes
42 s, and the one at 10^4 — ten times the lines — was still going after an hour,
when it was stopped. So writability is the generous half of the `before`
column's problem: the widths that can still be written are already past the
widths that can be checked.

## 9. The one residue

Range literals need a bit-vector representation; `need_invar` throws without one.
The gate is `has_bit_representation` (membership of
`integer_variable_bits_to_size_and_proof_vars`), and the throwing case is a
direct-only variable whose domain is **not** `{0,1}` — a `{0,1}` one is
registered with a one-element bit vector by
`set_up_direct_only_variable_encoding` and works. See Appendix B item 1 of
[literal-encodings.tex](literal-encodings.tex), which also records that two
earlier versions of this section named the wrong case.

This is a property of the variable, not of views:
`can_represent_range_literal_for` resolves a view to its underlying variable, so
a view never asks for a mirror the underlying cannot hold, and
`ProofLogger::infer` / `infer_explicitly` fall back to per-value. It is the
bits-less fallback bare variables have too, and it is the only detour left.
