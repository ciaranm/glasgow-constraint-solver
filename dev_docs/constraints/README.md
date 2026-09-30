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
  so one sweep costs terms, never width, but an equality can need a number of
  sweeps linear in the width to reach its fixpoint (#1091), and it reaches only
  `bounds(R)`. Every bound push names every term's bound, trivial ones
  included, and a 0.92 s `shortest_path` search writes 15 GB (#1035, fix open
  as #1055). Three wrong answers, all at the edges and none in the propagator,
  all now fixed: an XCSP3 `sum ≠` translation whose wrong `UNSATISFIABLE`
  verified (#1032), constant-condition `If` forms (#1033), and a `gcspy`
  binding posting `≤` for `≥` (#1036). Its inequality's bound pushes are the
  only unhinted assertions any family document has recorded. The stateless
  and incremental sweeps find the same solutions and each wins by up to 3×
  somewhere; the default loses 2.2× on one model to per-node heap copies of its
  fold state (#1034).
- [`inverse.md`](inverse.md) — `Inverse`: one class, one propagator that
  channels between two arrays and then runs `all_different`'s generalised arc
  consistent algorithm on one of them, which is `GAC` on the pair whenever every
  position is a different variable. So nearly a third of its assertions arrive
  named for `all_different`, and its Hall proofs derive each pairwise
  at-most-one through two channelling rows rather than reading it from a clique.
  Where it is the cost (`black-hole`) it searches the same number of nodes as
  Gecode, to the same first solution, and is 8–10 times slower, because every
  call rescans every pair (#1048). Re-audited 2026-09-25 after its two other
  issues were fixed. It builds its at-most-ones lazily now, where it used to
  write every value's at the root (#1049 → #1089). It answers a repeated
  variable with a root contradiction instead of an error, and it takes XCSP3's
  one-directional `channel` as an injection form with a Hall-set rule of its own,
  which `cake_pb_cp` cannot check (#1047 → #1088). Checking how it called a
  shared helper found a proof bug in `GlobalCardinality`: a constant in the
  array can make its proofs abort or fail (#1046, still open).
- [`abs.md`](abs.md) — `Abs`: one class, nine rules, one `pol` shape.
  Re-audited 2026-09-25, after all three of its issues were fixed. Its
  propagator is generalised arc consistent in a single call, and since #1076
  claims it: 18–21% on `celar`, where `Abs` is the largest share of the
  propagation. The encoding is the thesis's; the negative branch is a sum, not
  a difference, so its proofs resolve by `pol` rather than Theorem 2.9's RUP.
  A constant `v2` used to cost time and proof lines in proportion to the
  constant, 30% of `celar`'s proof; since #1080 its runs are plain RUP, at 86
  lines for any constant. Its audit also found the test harness's
  idempotence-claim checker off in 100 lanes (#1056, fixed by #1086). A
  constant operand, `v1` or `v2`, still fails the strict `opbdiff` oracle, in
  two different ways (#1101). Not merged into `arithmetic`: no shared code.
- [`logical.md`](logical.md) — `And`, `Or`, `AndIf` and `OrIf`: four classes
  over one template and two propagators, and after `equals` and `linear` the
  most posted family in the corpus (`bool_clause` alone is 391,679 posts in
  155 models). Every inference is one RUP against one of cake's two rows. The
  audit's one issue is fixed. Its scan did not disable a satisfied clause that
  still had two undecided literals, so one 2,774-literal clause was three
  quarters of `network_50_cstr`'s propagation (#1060). Since #1105 the scan
  stops at a satisfying literal if it meets one before a second undecided
  literal, and a clause of 128 literals or more watches two of them; that
  clause is now 0.03%. Three times as fast as Gecode on `grid-colouring`, in
  the same sitting. The half-reified forms reach
  only CPMpy and the `.scp`, and cannot chain through cake yet, which has no
  rule for them (#1100).
- [`parity.md`](parity.md) — `ParityOdd`, and the certified GF(2) system that
  `ParitySystem` and the `parity_system_gathering` presolver run over many XORs.
  No front end reaches the system (#983). On the one corpus model where parity
  dominates, `parity-learning`, gathering prunes nothing and costs four times as
  much: at every node, unit propagation has already done all elimination could.
  `ParityOdd` alone matches Gecode's node count and is 7.4 times slower.
- [`arithmetic.md`](arithmetic.md) — `Plus`, `Minus`, `Multiply`, `Power`,
  `Divide` and `Modulus`: six classes over four directories. `Plus` / `Minus`
  are GAC over interval lists by default; the other four are cake's
  bit-product encoding, every bound justified through the grid by McIlree's
  Chapter 7. `Multiply` costs under a microsecond a call and is rarely the
  bottleneck, but its derivations are over half of a proof's lines. Four
  findings: `Modulus`'s hints-only proofs fail the solution check (#1067),
  `Divide` could not prune a sign-open quotient (#1065, fixed by #1081), an
  aliased `Plus` converges one value per pass (#1068), and large operands
  overflowed rather than saturating (#1064, fixed by #1079; with proofs on,
  the encoding still stops at 62 bits). Re-audited 2026-09-25, which also
  corrected the product's strength on `z` from `bounds(Z)` to `bounds(R)`.
  Its audit also found the engine's per-node state copy costing 58% of
  `stable-goods` in page faults (#1063).
- [`table.md`](table.md) — `Table` and `NegativeTable`, and
  `propagate_extensional`, the helper that also propagates the `AutoTable`
  presolver's tables and the tabulated arithmetic and linear constraints.
  `Table` is generalised arc consistent and certified by the thesis's JP 3.3
  and 3.4. It runs a live set or, when `table::Auto` judges it worth it, a
  compact table. Its search is 1.1–1.3× Gecode's on Crossword and 1.4–4.2× on
  a synthetic matrix. End to end it is ahead on six of nine Renault
  instances, where Gecode's time goes on posting the model. `NegativeTable` watches two literals per forbidden
  tuple and is not generalised arc consistent. The audit's headline is a proof
  failure: a table whose rows overlap, which MiniZinc and XCSP3 both allow and
  `yumi-static` posts, writes proofs VeriPB rejects at the solution line,
  because GCS only half-reifies each tuple's selector value. The width trim that makes a
  wide domain cheap runs too late on two paths, and never runs on a column
  where a tuple has a wildcard, whose domain is then walked on every call
  while a wildcard row is live. A fully justified proof of an
  arity-5 benchmark takes about 830 times its solve to check. Not merged with
  `smart_table`: no shared code, different encodings.
- [`smart_table.md`](smart_table.md) — `SmartTable`: Mairy, Deville and
  Lecoutre's smart table, the engine under `LexSmartTable` and
  `AtMostOneSmartTable`, with McIlree and McCreesh's proof logging. No front end
  posts it; the `.scp` is its only way in from a file. It is generalised arc
  consistent, which a brute-force check over 5,000 random tables with views,
  holes and repeated variables confirms at every node. Each removal is a RUP
  per row after a lemma per tree-filtering step, and dropping those lemmas makes
  VeriPB refuse the thesis's Example 4.3. The audit's headline is the hints-only
  mode: at the `Definitions`, `Links` and `Inferences` levels every removal is
  asserted as a bare unit clause with no reason, and on one enumeration 184 of
  194 are contradicted by later solutions in the same proof. `Circuit` has the
  same defect from the same change. Also: an entry over a
  variable outside the scope aborts the solve, and the default short reasons
  define a flag on every call, taking one enumeration's checking time from
  0.8 s to 15.9 s. On identical trees it is 8–23 times slower than the native
  `Lex` and `AtMostOne`, about half of it in allocation, hash lookups and map
  helpers. Not merged with
  `table`: no shared code, and a different encoding.
- [`increasing.md`](increasing.md) — `Increasing`, `StrictlyIncreasing`,
  `Decreasing` and `StrictlyDecreasing`: four classes over one chain of
  comparisons and one two-sweep propagator, generalised arc consistent on
  distinct variables, holes included, and bounds-only, so holes affect nothing
  here. Each inference is one RUP by JP 3.2, and the family is 2 to 6% of its
  own enumeration proofs. On an identical enumeration it takes 2.5 to 2.7 times
  Gecode's chain propagator's time, and about 10% less than the `n − 1`
  `LessThan`s it replaces. Findings: MiniZinc's int `decreasing` and
  `strictly_decreasing` never reach it, because the standard library has no
  plain `var int` overload to select the solver's own `fzn_decreasing_int`, and
  all three of its `fzn_*decreasing*` files are dead; a chain that repeats a
  variable in an impossible order, such as `StrictlyIncreasing{x, x}`, is
  noticed only after up to W/2 calls on a domain of width W, where
  `LessThan(x, x)` has contradicted at once since #1088; and a repeat through an
  opposite-sign view is not even `bounds(Z)`. Not merged with `comparison`: the
  same row and theorem, but no shared code.
- [`value_precede.md`](value_precede.md) — `ValuePrecede`, a value chain
  whose each value first appears before the next: one propagator per
  consecutive pair over `cake_pb_cp`'s first-occurrence encoding, matched
  label for label, and quadratic in the array per chain value. It removes a
  later value wherever no earlier one can precede it, and nothing else: Law and
  Lee's forcing half is missing, so it is neither GAC nor `bounds(Z)`, and a
  backwards enumeration of restricted-growth strings meets 247,823 failures
  where Gecode's `precede` has none, at 8.0 times the time. Every removal's
  reason is the whole array. The proofs are one RUP per removal, by a
  procedure of our own through three of the thesis's theorems.
- [`seq_precede_chain.md`](seq_precede_chain.md) — `SeqPrecedeChain`, the
  chain `1, 2, 3, …` over positions: it clamps any variable whose declared
  bound exceeds the array length and installs a `ValuePrecede`, so it inherits
  that document's strength and costs, and is weaker again because the chain is
  propagated pair by pair. The clamp row is part of the encoding's definition,
  since the chain stops at the array length; `cake_pb_cp` writes one for every
  position. Everything is independent of width, because the chain is capped,
  checked by full enumerations up to `2⁶¹ − 1`. The encoding is `Θ(n²)` rows
  and `Θ(n³)` terms. Its class comment misstates the semantics, and MiniZinc's
  standard library wrongly rejects an all-negative array.
- [`lex.md`](lex.md) — the twelve `LexGreaterThan`, `LexGreaterEqual`,
  `LexLessThan` and `LexLessThanEqual` forms, plain, `If` and `Iff`, over one
  Frisch et al. propagator with a flag-per-position encoding matching
  `cake_pb_cp`'s; and `LexSmartTable`, a benchmarking reference. Generalised arc
  consistent on distinct variables, holes and unequal lengths included, at 4.2
  to 4.8 times Gecode's time on an identical tree. The headline is a proof
  failure: under the general constructor's `NotIf`, which the `.scp` reader also
  reaches, a correct inference of the condition's negation is justified under
  the wrong half of the condition, and VeriPB rejects 50 of 160 random proofs.
  Also: it materialises a whole-scope reason on every call, and deferring it
  gives 1.58 times the node throughput on `zephyrus` and 3.0 times on `mqueens`
  (the reason's content is unchanged; the builds' proofs and first solutions
  agree); its proofs are quadratic in the array per inference, 654 MB for 211
  inferences at 200; repeated variables, which lex-leader symmetry breaking
  produces in seven corpus models, lose generalised arc consistency, and one
  such shape takes W/2 calls to fail; and `LexSmartTable` ignores the lengths,
  losing solutions when the first array is the longer. The reified detection is
  incomplete.
- [`sort.md`](sort.md) — `Sort` and `ArgSort`: the Mehlhorn–Thiel propagator
  over `cake_pb_cp`'s stable-rank encoding, with every inference certified,
  Hall-interval ones included, by a pigeonhole on the rank line;
  [`sortedness.md`](../sortedness.md) stays as the long note. `Sort` is
  `bounds(Z)` on both arrays over distinct variables (GAC is NP-hard) and 2.9
  to 3.2 times Gecode's `sorted`; `ArgSort` is not `bounds(Z)` on `x` or `p`.
  No corpus model posts either. Findings:
  - with proofs off `Sort` still runs its proof's `O(n³)` Hall search, which
    makes a Hall-heavy benchmark 32 times slower at `n = 100`;
  - `ArgSort`'s rank propagator is up to cubic per call, and walks an
    element's domain value by value to find a proof-only threshold when ties
    leave a hole, 5.5 s at width 10⁹, where no current guard can see it;
  - the proof costs `Θ(n³)` lines at the root, 118 s to check at `n = 80`, plus
    `Θ(n²)` lines per order-statistic inference.
- [`all_equal.md`](all_equal.md) — `AllEqual`: one propagator that intersects
  every domain in a call, bounds first and then holes, over a chain of
  consecutive-pair equalities matching `cake_pb_cp`'s label for label. The
  headline is wrong answers: the propagator disables itself when `vars[0]` is
  single-valued after its own pruning, but `vars[0]` can become fixed during
  the call while another position is left unequal to it, so
  `AllEqual{x, y}` with `x ∈ {1, 3}`, `y ∈ {2, 4}` reports `(3, 2)`. It is
  reachable from the C++ API, the `.scp` reader, XCSP3 and, under search,
  MiniZinc. VeriPB rejects the proof, and a one-line fix is tested. With it,
  the family is generalised arc consistent on distinct variables, holes and
  views included, and holes affect every variable. A same-sign repeat with
  offsets (`{x, x + 1}`) takes W/2 calls to fail, and an opposite-sign one is
  not `bounds(Z)`; both need a view, which only the C++ API can post. On an
  identical enumeration it makes 4.0 to 15.0 times fewer calls than the
  `n − 1` `Equals` it replaces, but is no faster, and takes 4.6 to 10.5 times
  Gecode's time. Bounds and values are one RUP each, a removed interval three;
  a bound moved across more than one equality is checked, not argued.

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
