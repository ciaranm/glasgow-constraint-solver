# Range ("in") literals on views

How the two mechanisms in `dev_docs/range_literals_spec.md` and
`dev_docs/view-proof-logging.md` combine. Neither document covered this, because
until issue #882 they did not combine: a `ViewOfIntegerVariableID` had no range
literal at all, and every part of the solver that wanted to say something
interval-shaped about a view carried its own detour — three that threw, and five,
later seven, that silently degraded to one literal per value.

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
and containment edges. Every interval request on either side is mirrored onto
the other, and the two literals are joined by **two** rup clauses. Nothing
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

    L1:  ¬F_V ∨ F_X
    L2:  ¬F_X ∨ F_V

Each is RUP at emission: assert one and the negation of the other, and the
forward reification gives that side's two cuts, the ge-links carry each cut
across (for `s = -1` the two cuts swap roles, which is exactly the endpoint
swap above), and the far side's reverse reification fires.

**Both clauses are needed, and each for its contrapositive rather than for its
implication.** As implications, `F_V → F_X` and `F_X → F_V` are both already
derivable by unit propagation — one forward reification, two ge-links, one
reverse reification, no new clauses. That is what issue #882 observed, and it
is true. But UP uses a clause in whichever direction has a unit, and the
directions that matter are the negative ones:

    ¬F_X ⟹ ¬F_V   (L1's contrapositive)
    ¬F_V ⟹ ¬F_X   (L2's contrapositive)

and neither is derivable without the clause. A negated interval literal is a
unit on *neither* of its cuts — its reverse reification leaves only the binary
clause `¬(Y≥p) ∨ (Y≥q+1)` — so all it can do is descend its own variable's
containment edges, and it bottoms out at cells that are themselves unlinked
range literals unless they happen to be width 1. Descending to width 1 is
precisely the per-value shattering the interval vocabulary exists to avoid.
The issue's argument ("a range literal never has to cross an equality: it is
reified against its own two order cuts, so an interval fact decomposes into
cross one bound, move within one variable, cross back") decomposes a
*conjunction* of two bounds; a negated interval is a *disjunction* of two
bounds, and UP cannot carry a disjunction across one disjunct at a time.

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

Literals that are never named need nothing, and cost nothing: a fact only ever
enters a variable's literal family through a named literal or through a bound,
and both of those cross.

One consequence worth knowing about: `need_invar` is now genuinely re-entrant,
because resolving a literal while emitting a covering can re-enter it.
`ensure_partition_cut` publishes a partition boundary *before* defining the two
halves that boundary creates, so during that window the partition claims a cell
that does not exist yet. `define_invar_with_covering`'s single-cell path defines
it in that case, and `define_plain_invar` is idempotent so that
`ensure_partition_cut` does not then define it a second time.

## 4. Every cell gets named, so in practice everything is linked

A useful consequence of §3 that is worth stating explicitly, because it is not
obvious and because it is what makes the cost predictable: **coverings name their
cells.** `init_interval_partition` emits a root covering over every cell it
creates, and `ensure_partition_cut` emits a split covering over the two halves it
creates. Emitting either one renders those literals into a proof line, which
takes them through `xliteral_for_ensuring`, which links them. So although the
rule is "link on naming" rather than "link everything", nothing that exists ends
up unlinked, and the two sides' literal families do in fact end up as affine
images of each other.

Measured on `equals_test --view-position=mixed`, 258 proofs, every registered
(variable, view) pair whose view appears in the proof: **300 pairs, 300 matches,
no exceptions.**

**Do not turn that into the correctness argument.** Nothing maintains the
correspondence as an invariant — it is a downstream consequence of coverings
naming their pieces, and a future change that emitted a covering differently, or
that created a literal without a covering, would break it silently and without
breaking any test that checks for it, because there is no such test. The
load-bearing property is the one §3 actually enforces: *every named literal is
linked*, plus per-side UP-completeness (the range spec's Lemma L1). Argue through
those, not through the two sides having the same clauses.

## 5. The coincidence trap — read this before believing a green test

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

Measured over a sweep of domain widths 4–16 with 0–7 random requests per
instance: **80% of instances cross successfully with no linking clause at all**
— abut-high 39%, abut-low 23%, whole-range 12%, shattered 5.6% — and of the 20%
that stall, a single wide cell accounts for 88%.

A discriminating instance therefore needs *all* of: the range strictly inside
both variables' definition bounds; at least one interior cell of width ≥ 2 that
no per-value machinery touches; and a backtrack replay that has to reach the far
side's literal from the near side's negation rather than from a bound. This is
why the `--view-wrap` sweep passing is not by itself evidence, and why the
witnesses below are.

## 6. The witnesses

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

Note for anyone adding to this set: the obvious control for W8 — decide
`¬[b in 3..4]` instead of `¬[b in 3..5]`, so the decision names a fresh interval
rather than a cell — verifies with *either* link clause removed, because the
interval then sits at the bottom of a covering-forced block and the bound
crosses. Ablate before claiming a witness bites.

## 7. Cost

Per interval literal per registered view: the mirrored literal on the other side
(with its own partition maintenance) plus two rup lines. That is the same
constant factor the eq and ge atoms already pay for a wrapped variable, and
nothing here is proportional to a domain width.

Measured on one `Equals` whose operands are a bare `0..w` and a two-value
`{0, w}`, so root propagation prunes exactly one wide interior run; proofs on,
root propagation only, `.pbp` lines, every row VeriPB-verified. `view` wraps both
operands as `x + 10^6`, `negview` as `-x + 10^6`, `mixed` gives the two operands
different wraps of opposite sign.

| width | plain | view before | view after | negview after | mixed after |
|---|---|---|---|---|---|
| 10^3 | 40 | 36,012 | **106** | 106 | 109 |
| 10^4 | 40 | 360,012 | **106** | 106 | 109 |
| 10^5 | 40 | *timed out at 300 s* | **106** | 106 | 109 |
| 10^6 | 40 | *timed out at 300 s* | **106** | 106 | 106 |

The `before` column is `2 + 36·w` lines and stops being writable at all between
10^4 and 10^5. The `after` columns are flat, and 106 rather than 40 because the
view carries its own bit-vector encoding, its own order and equality atoms and
the link pairs — a constant, not a function of the width. That constant is the
price of the design; the slope was the point of the issue.

VeriPB checks every `after` row in 0.01–0.02 s, against 5.4 s for the largest
`before` row that finishes at all.

## 8. The one residue

A real variable with `lower == 0 && upper == 1` and no explicit representation
is `DirectOnly`, so it has no bit vector and no order cuts to reify against, and
`need_invar` throws for it. That is pre-existing and applies to bare variables
too. A view of such a variable *does* get bits, so its mirror would be the first
thing to ask `need_invar` for a bits-less variable.

It cannot arise — a two-value domain has no interior hole, `reject_random_interval`
needs three values, and `each_interval_minus` on a two-value domain yields only
width-1 intervals — but `ProofLogger::infer` and `infer_explicitly` fall back to
per-value when `can_represent_range_literal_for` is false, and that predicate
resolves a view to its underlying variable, so the case stays correct if it ever
does. That is the bits-less fallback, which bare variables have too. It is not a
view detour, and it is the only one left.
