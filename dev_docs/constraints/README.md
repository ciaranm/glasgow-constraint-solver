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
  this template, and the only family so far with **four** audit dates: the
  first pass filed seven issues, six are fixed, and four of the fixes changed
  what the document says rather than only what the code does. The third pass is
  where a rule was **deleted** — #904 gave views their own range literals and
  the per-value fallback rule had nothing left to cover for — and it is the
  family whose interesting answer to `consistency::Auto` is about `NotEquals`:
  a disequality clique keeps nobody's interior pruning alive, where a real
  `AllDifferent` over the same variables does. The fourth pass records #1088,
  which made `NotEquals(x, x)` a root contradiction rather than a
  construction-time throw.
- [`comparison.md`](comparison.md) — `LessThan`, `LessThanEqual`, their
  `Greater*` mirrors and their eight reified forms: twelve posted constraints
  over one propagator whose whole vocabulary is bounds, so one definitional OPB
  row, **no proof flags and no view detour anywhere**, eight inference rules
  each a single RUP, and 11.8% of its own proof. Nearly unreachable from the
  frontends, which turn a binary ordering into a two-term linear inequality;
  its real consumer is the difference-logic presolver. The audit's two findings
  are both fixed — a reason assembled on every call whether or not anything
  reads it, 43% of the cycles on a family-dominated benchmark (#907 → #916),
  and two reification kinds that threw from `s_expr()` leaving a truncated
  `.scp` behind (#908 → #915). It is also the family that makes
  `consistency::Auto` pay: everything it reads is a bound, so **holes affect
  nothing here**, and a comparison in a model is not a reason for anybody
  else's interior pruning to stay on. Its third pass records #1088, which made
  `LessThan(x, x)` a root contradiction rather than a construction-time
  throw.
- [`element.md`](element.md) — `Element`, `Element2D` and their constant-array
  forms: four posted classes over one templated implementation and **four**
  propagators, and the first family in the arc that is not binary. One
  half-reified equality **per array cell**, so its encoding is linear in the
  array and the slowest proof to verify in the curated set is its; the first with
  a real option (`with_consistency`), the first to claim idempotence, the first
  whose propagators are not all GAC, and the only one whose dominant wire hint
  belongs to another family — 93% of the assertions it is responsible for
  arrive labelled `equals`, because it reuses `enforce_equality`. Three of its
  six rules are published justification procedures; two are ours. It is also
  **the first and so far only client of optional interior pruning**: under
  `consistency::Auto` its two result propagators are installed as a pair and
  the solver decides, once and per model, whether anything could observe the
  interior values the generalised arc consistent arm removes. Read it for the
  two promises a pair makes and for the shapes where they do not hold.
- [`all_different.md`](all_different.md) — `AllDifferent` at three consistency
  levels, `AllDifferentExcept` and `SymmetricAllDifferent`: one clique encoding,
  nine rules, and the thesis's own Hall set procedures (JP 3.16, 3.17) behind the
  generalised arc consistent arm. The first family whose code is not only its
  own — `Inverse`, `ArgSort`, `Circuit` and `SubCircuit` run its propagators —
  and the counterexample for `consistency::Auto`: a bounds consistent arm that
  cannot be paired, because a hole in one variable moves another's bound. The
  audit's headline is in the front end: MiniZinc's `symmetric_all_different`,
  and by the same sweep `inverse` and `arg_sort`, give wrong answers on arrays
  not indexed from 1, and the wrong `UNSATISFIABLE` verifies through the whole
  `cake_pb_cp` chain.
- [`counting.md`](counting.md) — `Count`, `Among`, `NValue` and
  `GlobalCardinality`, four directories and one document. The family list's
  candidate merge is settled as four classes with no shared propagation code
  and four encodings, three of them fixed by `cake_pb_cp`. The one thing to
  read it for is how they relate. `Count` with a constant value of interest is
  the counting constraint the MiniZinc Challenge models use: 1,464 of 1,816
  posts, and `Among` appears in none. It finds the same solutions as a
  one-value `GlobalCardinality`, which explores 1.4 to 3.7 times as many nodes
  per second, so the specialised constraint is the slow one (#1029).
  `GlobalCardinality`'s default bounds arm is likewise slower than its flow arm
  on covers of several values, by up to 3.6 times on real models at equal node
  counts and two orders of magnitude on a synthetic large cover, but its proofs
  have about an eighth as many lines (#1028); on a one-value cover it is the
  faster. The audit's headline is a
  wrong answer: the flow arm binary-searched a cover only the bounds arm
  sorted, so an open constraint with an unsorted cover lost solutions (#1026,
  fixed by #1030). Thirty rules, all justified, two of them unreachable. The
  `inverse` audit later found that a constant in `GlobalCardinality`'s array
  breaks its proofs (#1046).
- [`linear.md`](linear.md) — `LinearEquality`, `LinearNotEquals`,
  `LinearLessThanEqual`, `LinearGreaterThanEqual` and their reified forms:
  twelve named classes over two base classes and one bound sweep, and the
  family that reaches the most models (250 of 298). Its vocabulary is bounds,
  so every cost is in terms, never width. That includes the proof: every bound
  push names every term's bound, trivial ones included, and a 0.92 s
  `shortest_path` search writes 15 GB (#1035). Three wrong answers, all at the
  edges and none in the propagator: an XCSP3 `sum ≠` translation whose wrong
  `UNSATISFIABLE` verifies (#1032), constant-condition `If` forms (#1033), and a
  `gcspy` binding posting `≤` for `≥` (#1036). Its inequality's bound pushes are
  the only unhinted assertions any family document has recorded. The stateless and
  incremental sweeps give identical searches and each wins by up to 3× somewhere;
  the default loses 2.2× on one model to per-node heap copies of its fold state
  (#1034).

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
