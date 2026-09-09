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

on `X`'s — the endpoints swap for a negated view, because it reverses the
order, and the map is then its own inverse. Width is preserved either way, which
is why a width-1 request is the eq atom on both sides and never reaches this
machinery at all. `interval_on_underlying` and `interval_on_view` are the two
directions.

Writing `F_V` for `[V in a..b]` and `F_X` for its image, the link is

    L1:  ~F_V | F_X
    L2:  ~F_X | F_V

Each is RUP at emission: assert one and the negation of the other, and the
forward reification gives that side's two cuts, the ge-links carry each cut
across (for `s = -1` the two cuts swap roles, which is exactly the endpoint
swap above), and the far side's reverse reification fires.

**Both clauses are needed, and each for its contrapositive rather than for its
implication.** As implications, both directions are already derivable by unit
propagation — one forward reification, two ge-links, one reverse reification,
no new clauses. That is what issue #882 observed, and it is true; it is also
beside the point, because the directions unit propagation actually needs are the
negative ones, and neither of those is derivable without its clause. The
argument is Remark 3.1 of [literal-encodings.tex](literal-encodings.tex); the
one-line version is that a negated interval literal is a *disjunction* of two
bounds, not a conjunction, and unit propagation cannot carry a disjunction
across one disjunct at a time.

Both negative directions are ordinary rather than exotic. Search branches on
real variables only — `reject_random_interval` requires a
`SimpleIntegerVariableID` — while `generic_reason` states hole runs over the
*operand*, which under a wrap is the view. So a range decision on `X` routinely
has to reach a reason literal on `V`, and a conclusion on `V` routinely has to
reach a reason stated over `X`.

## 3. Linking is triggered by *naming*, not by requesting and not by defining

This is the part that is easy to get wrong, and getting it wrong is silent.

A range literal can come into existence two ways. Either some caller asks for it
— a conclusion, a reason element, a branching guess — which reaches
`need_invar`; or the partition machinery creates it as a **cell**, from
`ensure_partition_cut` or `init_interval_partition`, straight through
`define_plain_invar`, without going anywhere near `need_invar`. A cell is
therefore never "requested", and:

- `need_proof_name` short-circuits on a condition that already has a proof name;
- `xliteral_for_ensuring`, which is where the emission path actually resolves
  literals, does the same.

So "link the literals that are requested" leaves every cell unlinked, and a
later decision, reason or conclusion that happens to name one of those cells
gets no link — a unit-propagation dead end with nothing to see at the point of
failure. `mirror_invar_across_view_link` is therefore called from `need_invar`
*outside* the "already defined" guard, and again from `xliteral_for_ensuring`
whenever a range condition that already has a name reaches a proof line. It is
idempotent, and after the first time it is a set probe.

**In a definitions-on proof there is in fact no such thing as an unnamed range
literal**, which is what makes the rule complete rather than merely better than
the alternative. `ProofLogger::emit` and `emit_under_reason` render with
`EnsureNames::Yes`, so every `rup` / `a` / `ia` line takes each range condition
through `xliteral_for_ensuring`. Every creation path writes such a line about the
literal it has just created, in the same call: `ensure_partition_cut` writes the
split covering, `init_interval_partition` the root covering,
`define_invar_with_covering` the request covering, `link_immediate_containment`
the containment edges. Only the `red` reifications go out through the ostream
overload with `EnsureNames::No`. So a cell is linked when its own covering is
written, not when some later solver fact happens to mention it.

That is the invariant to preserve: **every non-`red` emission names its
literals**. A future path that rendered a range literal without going through
`need_all_proof_names_in` or `xliteral_for_ensuring` could leave one unlinked,
and nothing would notice.

One consequence worth knowing about: `need_invar` is now genuinely re-entrant,
because resolving a literal while emitting a covering can re-enter it.
`ensure_partition_cut` publishes a partition boundary *before* defining the two
halves that boundary creates, so during that window the partition claims a cell
that does not exist yet. `define_invar_with_covering`'s single-cell path defines
it in that case, and `define_plain_invar` is idempotent so that
`ensure_partition_cut` does not then define it a second time.

## 4. The two sides hold the same literals, but not in the same roles

Because every literal is linked at creation (§3), and linking creates the mirror
on the far side, the two sides end up holding **the same set of literals** up to
the affine map. Measured on `equals_test --view-position=mixed`, 258 proofs, every
registered (variable, view) pair whose view appears in the proof: 300 pairs, 300
matches, no exceptions.

What does *not* correspond is a literal's **role**. `need_direct_encoding_for`'s
eq-atom backfill re-enters `ensure_partition_cut` on the far side before the
request's own second cut arrives, so the two sides reach the same set by
different routes, and the same interval can be a root cell on one side and a
split half or a request with its own covering on the other. Measured over 400
sweep proofs: 66 contained such a difference, 297 literals in all, every proof
verifying. So the split coverings and the containment DAGs genuinely differ.

**Argue per side, never by isomorphism.** The correctness argument runs: every
fact is a unit on every side (bounds via the ge-links, equalities via the
eq-links, intervals via L1/L2), and then per-side UP-completeness derives every
implied literal on the side that needs it. That argument does not care which
role a literal plays, which is exactly why it survives the role differences. An
argument that appealed to the two sides having the same clauses would not. This
is Theorem 3.3' and the paragraph after it in
[literal-encodings.tex](literal-encodings.tex).

## 5. Why this is complete

*Resolved, and moved.* The argument is now written out and proved, over a whole
representation family and all three literal kinds, in §3.3.1 of
[literal-encodings.tex](literal-encodings.tex) — see Lemma 3.E (unit transport),
Theorems 3.2' and 3.3' (the family versions of wipeout and complete
propagation), and Lemma 3.4 (reason validity). The three parts this document
originally identified — mirror closure, unit transport, and per-side
UP-completeness — survive as `Inv-Rep`, Lemma 3.E, and Theorem 3.3
respectively.

Two things from that write-up bear on this code specifically.

- **Argue per side, never by isomorphism.** The correctness argument transports
  every fact to one representation and then works there, which is why the role
  differences of §4 do not matter. An argument that appealed to the two sides
  having corresponding clause sets would be unsound reasoning even in the runs
  where the correspondence holds, because nothing maintains it.
- **What it depends on**, and therefore what would break it: that every
  non-`red` emission names its literals (§3); that every domain change is logged
  eagerly, as the range spec already assumes; and that in-bounds endpoints are
  partition boundaries — which is why `need_direct_encoding_for` cuts at `v` and
  `v+1` when a partition exists, and dropping that would break the base case of
  the cell-exclusion lemma.

Corroboration, which is not the argument but is worth having: 3000 randomly
generated view proofs verified with zero mirror-closure violations, over Equals,
NotEquals, AllEqual, Min, Max, In, LessThan, LessThanEqual and AllDifferent with
holey domains, three-view bases, and intervals pushed outside the definition
bounds.

## 6. The coincidence trap — read this before believing a green test

The negative crossing is derivable *without any linking clause* in a large
fraction of small configurations, for four separate reasons:

- the range is the whole definition range, so asserting its negation is
  UP-inconsistent and the check passes vacuously;
- the range abuts or sticks out below (`a ≤ lb`): the boundary pin
  `need_gevar`'s `fix_bound` emits makes the reverse reification a unit, the
  ge-link carries it, and the far side's *forward* reification finishes the job;
- the range abuts or sticks out above (`b ≥ ub`): the mirror image;
- every cell inside the range is a singleton — and one well-placed eq atom
  shatters a width-2 cell on *both* sides, so any per-value activity anywhere
  near the range (Table reasons, equality holes, `x = v` branching, enumeration
  nogoods, width-1 `In` gaps) silently makes the case work.

Measured two ways, both damning for the sweep as evidence. Over domain widths
4–16 with 0–7 random requests per instance: **80% of instances cross successfully
with no linking clause at all** — abut-high 39%, abut-low 23%, whole-range 12%,
shattered 5.6% — and of the 20% that stall, a single wide cell accounts for 88%.
And over 987 randomly generated instances that actually reach a conflict, with
the link clauses ablated: only **37 of them notice**. The sweep is about 96%
coincidence.

A discriminating instance therefore needs *all* of: the range strictly inside
both variables' definition bounds; at least one interior cell of width ≥ 2 that
no per-value machinery touches; and a backtrack replay that has to reach the far
side's literal from the near side's negation rather than from a bound. This is
why the `--view-wrap` sweep passing is not by itself evidence, and why the
witnesses below are.

## 7. The witnesses

`dev_docs/range_literals_spec.md` §8 is the suite; these four are its view half,
all gate-on and veripb-verified.

- **W6** — an interval fact concluded on a plain variable reaching a reason
  literal on a view of it (`X → V`, so L1's contrapositive).
- **W7** — the mirror image (`V → X`, L2's contrapositive).
- **W8** — the *trigger*: the named literal is one the partition machinery
  already created as a cell, so it is invisible to a request-driven link rule.
- **W9** — W8's two-view form, where the fact composes `view1 → b → view2`, and
  where the unlinked literal is a conclusion rather than a decision.

Validated by ablation, with a temporary knob since removed:

| ablation                | W6     | W7     | W8     | W9     |
|-------------------------|--------|--------|--------|--------|
| none                    | passes | passes | passes | passes |
| both link clauses gone  | FAILS  | FAILS  | FAILS  | FAILS  |
| L1 removed              | FAILS  | passes | FAILS  | FAILS  |
| L2 removed              | passes | FAILS  | passes | FAILS  |
| link on request only    | passes | passes | FAILS  | FAILS  |

Each fails within milliseconds, on a backtrack clause. W6 and W7 separate the
two clauses cleanly, one each; W8 and W9 fail whenever linking is driven by
requests rather than by naming, whichever clauses are present; and W9, whose
fact has to compose `view1 → b → view2`, needs both clauses. Every clause and
every rule here is separately load-bearing, which is a stronger result than the
spec records for W2 and W5, both of which are structural.

`invar_view_test` sits alongside them and covers something different: the
`need_pol_item_defining_literal` range arms, which no propagator reaches, and the
sign arithmetic of the endpoint map in both directions — checked with
`find_xliteral_for`, which does not introduce what it fails to find, so "the
mirror exists at exactly these bounds and not at the neighbouring ones" is a real
assertion. Both an off-by-one and a dropped endpoint-swap mutant are killed by
it. It deliberately does **not** witness the link clauses, and says so: it states
the crossings as RUP lines, and every one of them still verifies with the link
pair deleted, because a RUP check is strictly stronger than the single
unit-propagation pass the links exist for. That is §1's P1/P2 distinction, and it
caught this document claiming otherwise in an earlier draft.

Two notes for anyone adding to this set. The obvious control for W8 — decide
`¬[b in 3..4]` instead of `¬[b in 3..5]`, so the decision names a fresh interval
rather than a cell — verifies with *either* link clause removed, because the
interval then sits at the bottom of a covering-forced block and the bound
crosses. And a witness stated as a RUP line of the fact you care about tests
nothing at all here. Ablate before claiming a witness bites.

## 8. Cost

Per interval literal per registered view: the mirrored literal on the other side
(with its own partition maintenance) plus two rup lines. That is the same
constant factor the eq and ge atoms already pay for a wrapped variable, and
nothing here is proportional to a domain width.

Measured on one `Equals` whose operands are a bare `0..w` and a two-value
`{0, w}`, so root propagation prunes exactly one wide interior run; proofs on,
root propagation only, `.pbp` lines, every `after` row VeriPB-verified with
`--force-checked-deletion`. `view` wraps both operands as `x + 10^6`, `negview`
as `-x + 10^6`, `mixed` as `x + 10^6` against `-y + 10^6 + w`.

| width | plain | view before | view after | negview after | mixed after |
|---|---|---|---|---|---|
| 10^3 | 68 | 71,017 | **200** | 200 | 200 |
| 10^4 | 68 | 710,017 | **200** | 200 | 200 |
| 10^5 | 68 | *timed out at 300 s* | **200** | 200 | 200 |
| 10^6 | 68 | *timed out at 300 s* | **200** | 200 | 200 |

The `before` column is `17 + 71·w` lines and stops being writable at all between
10^4 and 10^5. The `after` columns are flat, and 200 rather than 68 because the
view carries its own bit-vector encoding, its own order and equality atoms and
the link pairs — a constant, not a function of the width. That constant is the
price of the design; the slope was the point of the issue. `plain` is the
control that makes the two builds comparable: it is the same 68 on either side
of the change, as it should be, since nothing here touches a bare variable.

VeriPB checks every `after` row in about 0.012 s. The `before` row at 10^3 takes
42 s, and the one at 10^4 — ten times the lines — was still going after an hour,
when it was stopped. So writability is the generous half of the `before`
column's problem: the widths that can still be written are already past the
widths that can be checked.

The `mixed` offsets are not free to choose, and getting them wrong is quiet.
The two wraps have to put both operands over the *same* interval; otherwise they
stop overlapping, the instance is unsatisfiable at the root, and the row measures
a refutation rather than the hole prune. An earlier version of this probe paired
`x + 10^6` with `-y + 2·10^6`, which overlap only at `w = 10^6` — so three of the
four `mixed` rows were the wrong shape, and the fourth was the right one. The
only tell was a three-line step in a column that should have been flat.

These figures are against `main` at 7b582656, and are about twice the ones this
branch first reported. #914 puts each of the tracker's definition lines into
VeriPB's core set, which writes an extra `core id` line for each; both columns
grow by that factor. Flat against linear is unchanged, and so is everything the
table is used for.

## 9. The one residue

A variable with no bit-vector representation has no order cuts to reify against,
so `need_invar` throws for it. The gate is `has_bit_representation`, i.e.
whether the variable is in `integer_variable_bits_to_size_and_proof_vars` — not
what its domain looks like.

**Correction (2026-09-09).** An earlier version of this section said the case
was a real variable with `lower == 0 && upper == 1` and no explicit
representation. That is wrong. `set_up_direct_only_variable_encoding`'s `{0,1}`
branch calls `track_bits(id, 0, {{1, eqvar}})`, giving such a variable a
one-element bit vector, so `has_bit_representation` is true for it and
`need_invar` does *not* throw. Confirmed by probe: for a `{0,1}` direct-only
variable, `need_invar(b, 0, 1)` returns a literal and the resulting proof
verifies; for a width-6 direct-only variable, `has_bit_representation` is false
and `need_invar` throws `range literal requested for a variable without a bits
encoding`. So the throwing case is a **direct-only variable of width three or
more**, which is a property of the variable and not of views.

Either way this is not a view detour. `ProofLogger::infer` and `infer_explicitly`
fall back to per-value when `can_represent_range_literal_for` is false, and that
predicate resolves a view to its underlying variable, so a view of such a
variable never asks for a mirror the underlying cannot hold. It is the bits-less
fallback, which bare variables have too, and it is the only detour left.
