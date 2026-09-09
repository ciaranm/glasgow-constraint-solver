# Constraint family documents

One document per constraint family, written to
[`TEMPLATE.md`](TEMPLATE.md) — which is also where the conventions, the closed
vocabularies, and the authoritative family list live. Read it before writing or
auditing one of these.

`dev_docs/constraints.md`, one directory up, stays the generic "how to
implement a constraint" guide. These documents are about particular
constraints and do not restate it.

## Written so far

- [`equals.md`](equals.md) — `Equals`, `NotEquals` and the four reified forms:
  one class and one propagator behind six posted constraints, a definitional
  bit-sum OPB encoding that stays logarithmic in domain width, nine inference
  rules under three wire hints, and the busiest propagator in the solver on
  clique-encoded models (71% of calls, 18% of propagation time). The pilot for
  this template, and now also the first **re-audit**: it filed seven issues,
  six are fixed, and four of the fixes changed what the document says rather
  than only what the code does.
- [`comparison.md`](comparison.md) — `LessThan`, `LessThanEqual`, their
  `Greater*` mirrors and their eight reified forms: twelve posted constraints
  over one propagator whose whole vocabulary is bounds, so one definitional OPB
  row, **no proof flags and no view detour anywhere**, seven inference rules
  each a single RUP, and 11.8% of its own proof. Nearly unreachable from the
  frontends, which turn a binary ordering into a two-term linear inequality;
  its real consumer is the difference-logic presolver. The audit's finding is a
  reason assembled on every call whether or not anything reads it — 43% of the
  cycles on a family-dominated benchmark.
- [`element.md`](element.md) — `Element`, `Element2D` and their constant-array
  forms: four posted classes over one templated implementation and **four**
  propagators, and the first family in the arc that is not binary. One
  half-reified equality **per array cell**, so its encoding is linear in the
  array and the slowest proof to verify in the curated set is its; the first with
  a real option (`with_consistency`), the first to claim idempotence, the first
  whose propagators are not all GAC, and the only one whose dominant wire hint
  belongs to another family — 93% of the assertions it is responsible for
  arrive labelled `equals`, because it reuses `enforce_equality`. Three of its
  six rules are published justification procedures; two are ours.

Everything else is still to write; the family list in
[`TEMPLATE.md`](TEMPLATE.md#provisional-family-list) is the work plan, and #871
is the tracker for the arc — including the method that produced the pilot, and
the decisions already settled.

The point of the arc is not a complete set of documents. It is that by the time
the audit is done, the solver is in a good state to write the
proof-logging-for-CP paper: each family gets read carefully, its problems get
filed and fixed, and the document is the record of that pass. Expect the fixing
to outweigh the writing, and expect the document to need rewriting afterwards:
the pilot filed seven issues, six of the fixes landed, and bringing the
document back into line with them touched the rule catalogue, the robustness
section, both performance tables and every measured figure. A family document
is the record of a pass, so a pass that changes the code changes the document.
