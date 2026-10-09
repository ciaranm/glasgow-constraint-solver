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
  fixed by #1030). Thirty rules, all justified, two of them unreachable. Five
  proof bugs found since, all at shapes the audit's tests did not post, are
  fixed: a constant in `GlobalCardinality`'s array (#1046, found by the
  `inverse` audit; #1187), aliasing in `GlobalCardinality` and `Count` (#1191,
  #1197, #1201) and a view registered by a later constraint (#1200).
  Re-audited 2026-10-08.
- [`linear.md`](linear.md) — `LinearEquality`, `LinearNotEquals`,
  `LinearLessThanEqual`, `LinearGreaterThanEqual` and their reified forms:
  twelve named classes over two base classes and one bound sweep, and the
  family that reaches the most models (250 of 298). Its vocabulary is bounds,
  so one sweep costs terms, never width, but an equality can need a number of
  sweeps linear in the width to reach its fixpoint (#1091), and it reaches only
  `bounds(R)`. Bound pushes used to name every term's bound, trivial ones
  included, so a 0.92 s `shortest_path` search wrote 15 GB (#1035); since
  #1055 they leave out bounds the bits imply or a pin states (or, above
  `Links`, would), and that proof is 617 MB. Three wrong answers, all at the
  edges and none in the propagator,
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
  array made its proofs abort or fail (#1046, fixed by #1187).
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
  the encoding still stops at 62 bits). Re-audited 2026-09-25 (which also
  corrected the product's strength on `z` from `bounds(Z)` to `bounds(R)`)
  and 2026-10-08. Its audit also found the engine's per-node state copy
  costing 58% of `stable-goods` in page faults (#1063), since fixed by #1113.
- [`table.md`](table.md) — `Table` and `NegativeTable`, and
  `propagate_extensional`, the helper that also propagates the `AutoTable`
  presolver's tables and the tabulated arithmetic and linear constraints.
  `Table` is generalised arc consistent and certified by the thesis's JP 3.3
  and 3.4. It runs a live set or, when `table::Auto` judges it worth it, a
  compact table. Its search is 1.1–1.3× Gecode's on Crossword and 1.4–4.2× on
  a synthetic matrix. End to end it is ahead on six of nine Renault
  instances, where Gecode's time goes on posting the model. `NegativeTable` watches two literals per forbidden
  tuple and is not generalised arc consistent. The audit's headline was a
  proof failure: a table whose rows overlap, which MiniZinc and XCSP3 both
  allow and `yumi-static` posts, wrote proofs VeriPB rejected at the solution
  line, because GCS only half-reified each tuple's selector value. #1202 fixed
  it by taking `cake_pb_cp`'s encoding, a proof flag per tuple reified both
  ways under an at-least-one; and since #1215 a tuple value outside the
  solver's integer range is refused at construction. The width trim that makes a
  wide domain cheap runs too late on two paths, and never runs on a column
  where a tuple has a wildcard, whose domain is then walked on every call
  while a wildcard row is live. A fully justified proof of an
  arity-5 benchmark takes about 800 times its solve to check. Not merged with
  `smart_table`: no shared code, and different entries.
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
  same defect from the same change. Also: the default short reasons
  define a flag on every call, taking one enumeration's checking time from
  0.8 s to 15.9 s. On identical trees it is 8–23 times slower than the native
  `Lex` and `AtMostOne`, about half of it in allocation, hash lookups and map
  helpers. Not merged with
  `table`: no shared code, and different entries.
- [`increasing.md`](increasing.md) — `Increasing`, `StrictlyIncreasing`,
  `Decreasing` and `StrictlyDecreasing`: four classes over one chain of
  comparisons and one two-sweep propagator, generalised arc consistent on
  distinct variables, holes included, and bounds-only, so holes affect nothing
  here. Each inference is one RUP by JP 3.2, and the family is 2 to 6% of its
  own enumeration proofs. Enumerating the same solutions under a different
  branching scheme, it takes 2.5 to 2.7 times Gecode's chain propagator's
  time, and about 10% less than the `n − 1`
  `LessThan`s it replaces. Findings: a chain that repeats a variable in an
  impossible order, such as `StrictlyIncreasing{x, x}`, is noticed only after
  up to W/2 calls on a domain of width W, where `LessThan(x, x)` has
  contradicted at once since #1088; and a repeat through an opposite-sign view
  is not even `bounds(Z)`. MiniZinc's int `decreasing` and
  `strictly_decreasing` never reached it, and all three `fzn_*decreasing*`
  files were dead, until #1178 routed them through `increasing` over the
  reversed array. Not merged with `comparison`: the same row and theorem, but
  no shared code.
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
  to 4.8 times Gecode's time on an identical tree. The headline is the cost of
  a call: it materialises a whole-scope reason on every call (#1141), and at
  `c9ceea25` deferring it gave 1.58 times the node throughput on `zephyrus`
  and 3.0 times on `mqueens` (the reason's content is unchanged; the builds'
  proofs and first solutions agreed). Also: its proofs are quadratic in the
  array per inference, 654 MB for 211 inferences at 200; repeated variables,
  which lex-leader symmetry breaking produces in seven corpus models, lose
  generalised arc consistency, and one such shape takes W/2 calls to fail;
  and the reified detection is incomplete. Fixed since the audit: under the general constructor's `NotIf`
  a correct inference was justified under the wrong half of the condition
  (VeriPB rejected 50 of 160 random proofs; #1179), and `LexSmartTable`
  ignored the lengths, losing solutions when the first array was the longer
  (#1183).
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
  consecutive-pair equalities matching `cake_pb_cp`'s label for label. It is
  generalised arc consistent on distinct variables, holes and views included,
  and holes affect every variable. The audit's headline, wrong answers, is
  fixed by #1180: the propagator disabled itself when `vars[0]` was
  single-valued after its own pruning, but `vars[0]` could become fixed during
  the call while another position was left unequal to it, so
  `AllEqual{x, y}` with `x ∈ {1, 3}`, `y ∈ {2, 4}` reported `(3, 2)`, from
  the C++ API, the `.scp` reader, XCSP3 and, under search, MiniZinc; it now
  disables only when the entry bounds meet. A same-sign repeat with offsets
  (`{x, x + 1}`) takes W/2 calls to fail, and an opposite-sign one is
  not `bounds(Z)`; both need a view, which only the C++ API can post. On an
  identical enumeration it makes 4.0 to 15.0 times fewer calls than the
  `n − 1` `Equals` it replaces, but is no faster, and takes 4.6 to 10.5 times
  Gecode's time. Bounds and values are one RUP each, a removed interval three;
  a bound moved across more than one equality is checked, not argued.
- [`at_most_one.md`](at_most_one.md) — `AtMostOne`, at most one position of an
  array equals a value that may itself be a variable, and
  `AtMostOneSmartTable`, its `SmartTable` baseline. Generalised arc consistent
  on distinct variables, holes and views included, by two rules that read only
  which variables are fixed; not even `bounds(Z)` on repeated ones. Only the
  C++ API and the `.scp` reader reach it: MiniZinc and XCSP3 post `Count`,
  which on an identical tree takes 1.5 to 1.8 times its time and writes 1.8
  times its proof lines. Findings, each with a tested patch: while the value
  variable is unfixed every call walks its whole domain, about 0.4 s a call at
  10⁷ values, where collecting the fixed values does the same in `O(n log n)`;
  its `on_change` triggers declare every variable's holes relevant, though
  none is; every reason is the whole scope where two literals suffice; and its
  encoding is `Count`'s from before `Count` was conformed to `cake_pb_cp`. Not
  merged with `counting`: no shared code, and it is the cheaper special case.
- [`in.md`](in.md) — `In`: a variable equals one of a list of constants or
  one of a list of variables, over `cake_pb_cp`'s at-least-one and flag-triple
  encoding, matched label for label. Generalised arc consistent on distinct
  variables, holes and views included, with every inference certified by our
  own derivations (guarded bound lemmas carry a range across a selected
  equality); interval-shaped throughout since #874. Gecode's `member` never
  prunes a candidate once posted; enumerating the same solutions without
  failures, under different branching, GCS takes 3.3 to 3.7 times its time.
  Every listed domain from C++ and XCSP3 is an `In`, and so
  is Python's `post_in`, which is where the findings are: carving `K` values
  costs Θ(K²) in the state layer's interval scans (12.1 s at 10⁵; 0.021 s with
  a binary search); the posted `In` stays live after its only useful call,
  idle on real instances (262,179 calls on XCSP3's `Dubois-015`, 1.6 million
  on the `all_equal` benchmark, whose time falls 27% with the fix); and its
  trigger marks the variable's holes as observed, which keeps other
  constraints' optional interior pruning on. Also: repeated or aliased
  candidates lose `bounds(Z)` and can take W/2 calls to fail; step 1 is
  quadratic in interval counts; and XCSP3's index-free `element` is
  unsupported. Since #1215 a constant outside the solver's integer range is
  refused at construction, so the 64-bit overflow the audit found with proofs
  on can no longer be reached.
- [`min_max.md`](min_max.md) — `ArrayMin`, `ArrayMax`, `Min` and `Max`: one
  propagator over a selector-per-entry encoding that matches `cake_pb_cp`'s row
  for row, though unlabelled and in another order. It is generalised arc
  consistent on distinct variables, holes included, but only because of a
  final per-value pass over the array that costs the width of the domains on
  every call. Without that pass the rules are already GAC on interval domains
  and `bounds(D)` with holes, almost exactly where Gecode's domain-consistent
  maximum stops.
  Because of the pass, three MiniZinc Challenge models make no progress in a
  minute, one overshoots its time limit by 44 s, and the audit row stays
  `KnownTrip`. Enumerating the same solutions as Gecode, under different
  branching, it takes 12 to 15 times Gecode's time. Other findings:
  - plainly repeated variables fall below `bounds(Z)`;
  - the single-support rule's reason and proof are per value of the result.

  Fixed since the audit, by #1181: a result that shares a variable with an
  entry through a view (only the C++ API and `gcspy` can post a harmful one)
  made it throw "missing support" instead of failing, and occasionally write
  a proof VeriPB rejected; it now fails in place and verifies.
- [`min_distance.md`](min_distance.md) — `MinDistance`, the smallest distance
  between any two of `p` selected sites, from Lagerkvist's p-dispersion
  propagators: one definitional encoding with a min-attained ladder, and five
  propagation modes from a checker to the conflict-matching bound, every
  inference certified; [`min-distance-proofs.md`](../min-distance-proofs.md)
  stays as the long note. Library and `.scp` only, and `cake_pb_cp` has no rule
  for it. Partial by design: forward checking or pairwise arc consistency on
  the sites, upper bounds only on `z`, whose lower bound nothing raises before
  every position is fixed. Findings: with proofs, building the ladder scans
  every site pair once per distinct distance, 26 s at 600 sites against 9 ms
  without; the matching bound concludes `z ≤ t − 1` where its own certificate,
  guarded one distance lower, proves `z ≤ t*`, which cuts the tree by 26 to
  52% on 20-site random instances with six positions and by up to 58% with
  eight; and its assertions carry no hint. Distances near `2⁶³` crashed the
  proof model when `z` could be negative, and through an offset view on `z`
  the propagators too; since #1215 and #1214 such distances and offsets are
  refused at construction.
- [`cumulative.md`](cumulative.md) — `Cumulative`, over optional tasks and
  variable lengths, heights and capacity. This is the largest family and the
  most heavily certified. One propagator carries the whole rule ladder:
  time-tabling, the overload check and its profile, elastic and knapsack
  strengthenings, edge-finding with its time-table and energetic forms, and
  not-first / not-last in our detection and the published one. Every
  inference is proved, under the one shipped encoding: start-checkpoint,
  `6n(n − 1) + n` rows and no time point in the model. The per-time capacity
  rows every rule but the time-table run steps argues over are recovered
  inside the proof the first time something cites them, since #1290 mostly
  by a quadratic chain step from the row below. The same propagator runs the
  derived Cumulatives that three presolvers install, and each axis of a
  `Disjunctive2D`, so this document also covers that runtime machinery.
  [`cumulative-proof-logging.md`](../cumulative-proof-logging.md) stays as the
  long note. Re-audited 2026-10-08 for #1271, #1273, #1278, #1284, #1285,
  #1290 and #1292.

  Findings:
  - at `Definitions`, `Inferences` and `Backtracking`, a derived Cumulative
    installed over a posted donor gets the proof rejected under the
    shipped start-checkpoint encoding, because the donor publishes its row
    deriver at every level but its flag definer only at `Off`. The test-only
    time-indexed encoding verifies. Over a `Disjunctive2D` donor, two
    presolvers decline and the proof verifies, and `CumulativeStrengthening`
    throws a `ProofError` where it has something to strengthen;
  - inputs within the integer range policy throw `IntegerOverflow` at four
    sites, three of them on feasible single-task instances. Since #1271 that
    is a clear error by decision (no 128-bit arithmetic), and
    `integer_ranges_test` pins each site. #1292's published not-first /
    not-last sweep adds a fifth when that detection runs, with a lower limit
    and no lane;
  - fixed since the audit: a push's certificate was linear in its distance
    (295,048 lines for a push of 5,000; one 63-line proof since #1285's run
    steps, though per-time steps remain for variable heights, views and
    derived constraints), and its chain was built even with proofs off
    (#1285 builds it only for a proof); no rule lowered a variable height (#1284); the
    elastic and knapsack conflicts were not counted (#1273); and the
    test-only encodings were public API (#1278, which keeps the environment
    variable as a diagnostic).

  On `data_bl` at the audit, edge-finding and TTEF halved the default's
  instruction count under the example's search. Against Gecode the default is
  the stronger propagator (7 to 34× fewer nodes), and with both solvers on
  the same decomposition (312,333 nodes each) ours was 3.6× slower per node.
  Proofs run to 1.03M lines and 221 s of VeriPB at 8,917 nodes (1.19M and 390
  to 510 s at the audit), about 96% of them this family's own.
- [`disjunctive.md`](disjunctive.md) — `Disjunctive`, the unary resource:
  tasks with variable starts, constant or variable durations and optional
  presences, strict or non-strict. The OPB encoding is purely pairwise, and
  sixteen rules are certified against those rows alone: time-tabling,
  detectable precedences in pairwise and set form, overload checking,
  edge-finding, and not-first / not-last in two detections. The energetic
  rules re-encode time inside the proof, and one overload certificate is a
  proof-only sorting network, `ComparatorNetwork`, which this document
  describes for `disjunctive_2d.md` too. Two energetic proofs (edge-finding
  alone, and the time-indexed overload, edge-finding, sweep not-first /
  not-last and set rule together) pass `cake_pb_cp`'s full verified chain.
  The audit's findings, all closed on 2026-10-08 (re-audited at `0a5b4ec6`):
  - time-tabling's pushes are subsumed by detectable precedences at the
    fixpoint; they stay by decision, and since #1279 their start scan jumps
    past blocked times rather than being quadratic in the duration. Turning
    them off now saves 4.7% of the instructions on `ft06`, not 10.7%;
  - the set rule skipped fixed tasks and edge-finding skipped overloaded
    windows while the overload check was off, so both depended on rule
    order. #1275 fixed both;
  - not-first / not-last never pushed a task its window contains, and only
    ever took Θ as a whole window's contents. #1288 and #1289 lifted both
    for the published detection only: with it and every rule on, the root
    is weaker than Gecode's `unary` on none of 20,000 random machines (452
    with the sweep detection), and `la01` at its optimum finds a schedule
    in 240 recursions;
  - the per-time folds are now kept (#1287), and a reason names only the
    tasks its certificate cites, except in the window rules (#1283).
- [`disjunctive_2d.md`](disjunctive_2d.md) — `Disjunctive2D` (`diffn`): one
  definitional encoding, a reified before flag per ordered pair and axis plus a
  separation clause per pair (five- or six-way with optional rectangles), and every
  inference justified against it. By default the propagation is a pairwise rule
  by forbidden regions. Off by default and reachable only from the C++ API is
  the cumulative relaxation, certified two ways. Route B is time-tabling with a
  per-firing comparator-network certificate. Route A adds the overload check,
  edge-finding and TTEF over a flagged capacity row per time point derived
  inside the proof. There is also a projection that runs `Cumulative`'s own
  propagator on each axis and publishes each axis as a presolver donor. No
  capacity row is in the model. Separated from `disjunctive.md` because the
  relaxation is as large as the 1-D family. Findings (re-audited at
  `0a5b4ec6`, after five fixes on 2026-10-08):
  - The pairwise rule asked for **both** rectangles' mandatory parts where its
    certificate needs only one's compulsory part against the other's bounds.
    #1276 widened it to forbidden regions, with no change to the proof code,
    which takes shikaku `human --autotable` from 312 recursions to 10.
  - Under one static branching, Gecode's `nooverlap` searches 2.6 to 22 times
    fewer nodes than the default rule. Under the same branching, the relaxation
    closes the refuted packings in 1 to 203 recursions, but no frontend can turn
    it on.
  - A size variable that is also a position gave proofs VeriPB rejected
    (fixed by #1269), and so did route B with a variable resource-axis size
    (fixed by #1270). Every inference is now justified.
  - At assertion levels above `Off`, two presolvers derive nothing from a
    projection donor, where they do with proofs off, and
    `CumulativeStrengthening` throws wherever it would strengthen something.
  - The projection did not wake when a presence was decided (fixed by
    #1276).
  - The projection inherits `Cumulative`'s per-call horizon arrays: 8.4 GB for
    four rectangles 2²⁸ wide side by side. The large-domain audit row cannot see this, because it
    runs default rules only.
  - MiniZinc `diffn` with a size that can go negative gets `=====ERROR=====`,
    by decision (#1272 documents it).
  - Route B's 630 MB enumeration proof checks faster than the projection's
    49 MB one, probably because cached `Top` rows slow every RUP (untested).
- [`cumulative_strengthening.md`](../presolvers/cumulative_strengthening.md) — the
  first of the three presolver documents, and the first written to the
  template's presolver variant. It covers Schulz's integrality strengthenings of
  each posted `Cumulative`, and of each `Disjunctive2D` projection.
  - **What it does.** It reduces the capacity to the largest load the tasks
    that can run beside something can actually reach, by gcd rounding or a
    knapsack programme. It sets the height of every task that can run beside
    nothing to that capacity, raising or lowering it. The result is installed as a derived `Cumulative` whose
    rows are proved from the donor's and pinned by `ia`, so the OPB and the
    `.scp` are untouched, and every rewrite is time-table neutral.
  - **Reachable only from the C++ API.** No front end or example adds it.
  - **Findings**, re-audited 2026-10-08 after #1280, #1281 and #1286 fixed
    the first three.
    - Its own pass walked every time point of the horizon, with proofs off
      too: 12 s and 5.6 GB at 10⁷. It is per stretch between window edges
      since #1281 (#1240), and the pass is no longer what a long horizon
      costs.
    - Its proof budgets applied only with proofs on, and their predictions
      grew with the horizon and the capacity's magnitude, not with the
      derivation: a fixture scaled by 20 was declined, and the proofs-on
      search took 182 nodes where the proofs-off one refuted at the root.
      #1280 and #1286 removed them (#1242, #1241), so at `Off` proofs on and
      off search identically, at the price of proofs of any size: 767,000
      lines on #1286's sixteen-task example.
    - Raising a height cost up to a `pol` per unit of the capacity. Since
      #1280 it is one proof by contradiction per raised task per row (#1242).
    - Wherever it installs something over a posted donor, like every derived
      `Cumulative` under the default encoding, its proofs are rejected at
      assertion levels above `Off`. Over a `Disjunctive2D` projection donor
      that it would strengthen it is worse: the other two presolvers decline
      there and their proofs verify, but this one throws and the solve
      aborts.
    - Its answer depends on presolver order: `DifferenceLogic`'s initialiser
      can tighten a start before it reads the windows.
- [`inferred_cumulative.md`](../presolvers/inferred_cumulative.md) — the
  `InferredCumulative` presolver. It is Sidorov's (CP 2026) cover-and-lift
  procedure over every posted `Cumulative` and every `Disjunctive2D`
  projection at once. Each lifted cut is posted as a derived `Cumulative`,
  and each per-time row is certified by replaying the knapsack dynamic
  programme that validates the whole cut, built by the same code that answers
  the lifting subproblems. That way no validated cut ever fails to
  certify: zero uncertifiable over 710 MiniZinc RCPSP and 1,999 PSPLib
  instances. Findings:
  - **No front end can run it** (#983). The audit answers what it would detect by
    building the MiniZinc and XCSP3 shapes by hand. A capacity-one resource
    posted as `Disjunctive` is invisible. Per-resource length variables
    break cross-resource lifting (`L` lower on 87 of 710 instances).
    Three spellings zero the certified bound on every instance:
    per-resource length variables, single-value length variables, and
    end-variable makespan rows. At the audit none of them said so; since
    #1282 (#1257) each gets a `General` note. Adding `InferredDisjunctive`
    first can zero it too, where that presolver's bound already reaches this
    one's, and the summary now says so.
  - **#943's single start-checkpoint encoding cost it heavily, and #1290 won
    most of it back** (#1254). One donor row's recovery was about 7,200
    lines, and the reference certificate 6.8 times the lines and 93 times
    the checking time of the time-indexed arm. Recovering each row from the
    one before it takes that certificate from 35.5 s of checking to 0.64 s,
    and the Pack_d certificates check again.
  - **With a makespan named, the root proof is linear in the makespan
    bound,** so in the task lengths, and its checking time worse than linear.
  - **The lifting programme's frontier sweep** cost up to minutes per PSPLib
    J90 or J120 instance with proofs off. #1277 and #1291 (#1255) took
    `J120_59_6` from 57 s to 12 s serially. `J120_19_1`, the slowest
    measured, now takes 33 s serially (3 to 4 minutes at the audit, partly
    beside other jobs). Its state budget still binds on at
    least 102 of them, changing cuts or dropping ones it could not afford to
    validate, and still counts states rather than comparisons (#1255,
    open).
  - **An `Important` note fired on 556 of the 710 instances** for the
    published procedure's own output budget. Since #1274 (#1256) a drop at
    the default budget is a `General` note.
  - **Assertion levels.** Above `Off`, under the default start-checkpoint
    encoding, a cut over posted donors gets the proof rejected
    (#1234). Over a `Disjunctive2D` projection donor every cut
    is declined instead, and the proof verifies at `Definitions`,
    `Inferences` and `Backtracking`. At `Links` every proof of a satisfiable
    model is rejected (#1210). The installed constraint's hints
    say `constraint_id unnamed`.
- [`inferred_disjunctive.md`](../presolvers/inferred_disjunctive.md) — the
  `InferredDisjunctive` presolver. It reads every posted
  `Cumulative`, and every `Disjunctive2D` axis projection, as a resource. It
  grows maximal cliques in the cross-resource conflict graph and installs each
  as a derived capacity-one `Cumulative`. Nothing reaches the OPB, and every
  per-time row is proved from the witnessing resources' rows: a pairwise
  at-most-one and its bridges, then a clique merge pinned by `ia`, at
  `(k² + 7k)/2` to `k(7k − 11)/2` lines per time point, depending on how
  many pairs need bridging. Sidorov's stage one, at unit
  coefficients. Findings:
  - **No front end reaches it** (#983).
  - **It cannot see a machine written as a `Disjunctive`** or as pairwise
    non-overlap. That halved the conflict graph on 30 generated instances.
  - **It has nothing to infer on job shops by construction.** At the audit
    it still raised an Important "search may be slower" note there (#1258).
    Since #1274 a drop by a budget at its default is a `General` note only.
  - **Its pass is quadratic in memory**: a 104-byte conflict entry per task
    pair, held about three times over at the peak, so 3.1 GiB at 3,200 tasks.
    With proofs on, each posted clique keeps one copy (#705).
  - **`dropped_subset` cannot fire on an honest run**, so #706 cannot have
    an honest fixture for it.
  - **No declines on 110 Pack and Pack_d instances**: install posts the same
    cliques with proofs on as with them off.
  - **Above `AssertionLevel::Off`**, a proof containing one of its
    constraints over a posted donor is rejected under the default
    start-checkpoint encoding, and over a `Disjunctive2D` projection nothing
    is installed under any encoding (#1234).
  - **Its certified makespan bound is fragile.** It disappears when the
    lengths are single-valued variables or the finish rows go through end
    variables (checked on 110 Pack instances), or when `InferredCumulative`
    runs first and certifies the same bound. Since #1282 (#1257) each of
    these is reported, by a `General` note or the summary.
  - **With proofs on, the bound's certificate grows with the span of the
    window**: a 133 MB root proof on Pack_d `pack008` that checks in 8 s,
    against 2.3 MB without it. At the audit, before #1290, it was 822 MB and
    did not check in 30 minutes.
- [`reachable.md`](reachable.md) — `Reachable` and `DReachable`, MiniZinc's
  `reachable` and `dreachable` and, through the stdlib's wrappers, `connected`
  and `dconnected`; also the child that `Tree` and `Path` post. One propagator
  over a breadth-first unfolding of reachability, `reach[v][k]`, against which
  every removal is a single RUP because unit propagation replays the
  propagator's own search. Generalised arc consistent on nodes, edges and root
  in both spellings with its cut-vertex and bridge forcing on (no unsupported
  value in 12,000 random root states per spelling); with it off, only the
  0-values lose support. The costs are on the proof side and in one algorithm:
  the encoding is `Θ(nodes × (nodes + edges))` rows, 136,395 for an 11-by-11 grid, and it
  taxes every proof line, this family's or not; a forcing made while the root
  is open pins a lemma per candidate root, 96.5% of `hitori` `h11-1`'s 673 MB
  proof, mostly each lemma's own piece's border (narrowing each lemma to its
  piece saves 23.5% and leaves them 95%; #1312); and the directed forcing searches once per candidate per
  node and per edge on every call, 3.3 ms a call at 400 nodes against 0.16 ms
  undirected (#1316). An empty node set is a solver error rather than unsatisfiable
  through MiniZinc's int spelling (#1305, shared with `tree` and `path`). The design note's "not implemented" section
  is stale.
- [`dag.md`](dag.md) — `Dag`, MiniZinc's `dag`: the selected part of a fixed
  digraph has no directed cycle and every selected edge has both endpoints
  selected. That is stricter than the stdlib decomposition, deliberately:
  six solutions to five on one edge, and Chuffed has four. One propagator,
  five rules, each **one RUP** against `Reachable`'s level unfolding with the
  root taken out and restricted to the input's strongly connected components.
  It is generalised arc consistent by downward closure, and 10,000 random
  graphs found no unsupported value. Repeated variables lose that, but no
  solutions. The audit's findings: through MiniZinc, an **empty node set is
  unsatisfiable**, because `fzn_dag.mzn` takes `min` of an empty index set,
  which its sibling files guard (#1303, and the four-argument `subgraph`
  has the same defect). The propagator rebuilds everything on every call and
  searches edges that cannot close a cycle; two changes that keep every
  inference cut 29% of the instructions on `maximum-dag` `25_04` (#1310).
  Installing any one-propagator constraint is quadratic in its trigger count,
  about 11 s at the root of a 100,000-node path (#1309, engine). The encoding costs
  nodes × (nodes + edges) per strongly connected component, so even one
  400-node cycle is 52 MB of OPB. `connectivity-proofs.md` stays as the design note, shared with
  `reachable.md`.
- [`subgraph.md`](subgraph.md) — `Subgraph`, MiniZinc's `subgraph`: a selected
  edge has both its endpoints selected. Two clause rows per edge, one
  propagator, two rules, each a one-line RUP against its row, and generalised
  arc consistent on the node and edge variables unless a variable appears in two
  positions with opposite signs, which only the C++ API can post (brute force
  on 24,000 random instances). Its rows and its propagation loop are copied,
  not shared, into `Reachable` and `Dag`; nothing calls this class, and no corpus
  model posts it. The audit found a wrong answer in the front end: the
  four-argument MiniZinc spelling over an empty node array computes the minimum
  of an empty index set and comes out unsatisfiable, as `fzn_dag.mzn` does
  (#1303). And the class costs more than the decomposition it stands in for:
  every call rescans every edge, so a 5×5 grid model through MiniZinc takes
  11.0 s against the stdlib clauses' 6.9 s on the same nodes, and a path of
  10,000 edges with 12 undecided is 9.4 times slower; a candidate with one
  propagator per edge, disabled once its edge is decided or entailed, is as fast as
  the decomposition or slightly faster, with fewer calls (#1311).
- [`tree.md`](tree.md) — `Tree` and `DTree`, MiniZinc's `tree` and `dtree`, and
  through the standard library's wrappers `steiner`, `dsteiner` and both
  `weighted_spanning_tree` spellings: a delegating family that posts a
  `Reachable` child and a `LinearEquality` count under its own ID, and only
  `DTree` adds rows of its own, an at-most-one per node over its entering arcs,
  through the `graph_rules` helper it shares with `Path`. Its cost is the
  reachability child's: on an 8 × 8 grid `Tree` owns 2 of the OPB's 37,208 rows.
  Not GAC, and the brute-force sweep says where: undirected, every missing
  removal at up to four nodes is an edge closing a cycle, and posting one row
  per cycle made `Tree` GAC on every sampled instance up to six nodes (#1315);
  directed, most of the rest is that nothing may enter the root, which `DPath`
  says of its start and for which `DTree` has no rule (#1314). Neither
  strengthening is a RUP against the encoding in general. A fixed cycle can
  leave the root fixpoint standing with no solution. 1,930 random instances (and
  a fact-check re-run that also catches solver errors) agree across both
  MiniZinc versions, both index conventions, the `.scp` reader and Gecode; the
  empty graph is a solver error through MiniZinc where the standard library says
  unsatisfiable (#1305).

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
