# Developer Documentation

This directory contains in-depth notes for developers (human or AI) working on
the Glasgow Constraint Solver. Each document covers one architectural area in
more detail than the top-level `README.md` does.

These docs are aimed at people changing the solver's code, not at users of the
library. For an introduction to *using* the solver, start with the top-level
`README.md`.

## Contents

- [State and variables](state-and-variables.md) — how variables and their
  state are represented inside the solver: the `IntegerVariableID` family,
  the `State` class, the `IntervalSet` domain representation, chronological
  backtracking via epochs, and the inference paths through which propagators
  modify domains. Read first when changing the solver internals.
- [Variable encodings: state, OPB, and proof](variable-encodings.md) — the map of
  the ways to bring a variable into existence, along two axes (does it have solver
  state, and is its encoding asserted in the OPB or introduced inside the proof).
  A table of every mechanism plus the `register_bits_variable_encoding` primitive
  they share, why "not in the OPB" is what makes an auxiliary chain-portable
  against `cake_pb_cp`, and the footguns of a state variable whose bits are
  introduced in-proof. Read when choosing how to create an auxiliary for a
  proof-logged constraint.
- [Implementing a constraint](constraints.md) — the structural pattern every
  constraint follows: class shape, the three install phases, the propagator
  framework, triggers, the inference and justification APIs, OPB encoding
  building blocks, and the testing pattern. Start here when adding any new
  constraint — and for the umbrella-header directory layout, which presolvers
  under `gcs/presolvers/` share.
- [Reification](reification.md) — additional machinery for *reified* constraints:
  the `ReificationCondition` static and `EvaluatedReificationCondition` runtime
  types, the `install_reified_dispatcher` helper, the OPB encoding pattern,
  and the conventions for writing new reified constraints. Read
  `constraints.md` first.
- [MiniZinc bindings](minizinc.md) — how the `minizinc/` directory plugs into
  the MiniZinc / FlatZinc ecosystem: `fzn-glasgow`, the `mznlib/` predicate
  overrides, `.msc` solver-config files, the cross-solver test harness, and
  the recipe for exposing an existing C++ constraint.
- [XCSP3 bindings](xcsp.md) — how the `xcsp/` directory consumes XCSP3
  instances: the `XCSPCallbacks` class, the intension tree walker, the
  cache-based test harness with ACE cross-checking, and the recipe for
  adding a new constraint binding.
- [Benchmarking](benchmarking.md) — the curated set of benchmarks for
  measuring the wall-time impact of a performance-sensitive change, the
  rationale for each pick, the harness pattern for comparing two builds,
  and what to capture. Use when quantifying a refactor's perf impact.
- [Proof benchmarks](proof-benchmarks.md) — the counterpart set for when
  the *proof* is what is being measured: proof-writing cost, proof size
  and VeriPB checking time. Groups instances by whether they stress
  writing or checking, records which candidates are too large to
  proof-log at all, and lists the argument-shape traps. Use when
  changing proof logging, scaffolding, encodings or hinting.
- [Frontend support matrix](frontend-support-matrix.md) — single source of
  truth for which gcs propagators each frontend (MiniZinc, XCSP3, CPMpy)
  exposes, plus where the solver-side gaps are tracked. Update when adding
  a propagator or a frontend binding.
- [Proof logging for `Cumulative`](cumulative-proof-logging.md) — concrete
  walk-through of the three-inference proof for the time-table propagator:
  the `pol`-over-`active=1`-flags idiom, the "extended-reason pinning"
  technique for hypothetical literals, and the chain-of-blocked-times
  structure that proves a bound push. The generic patterns are summarised
  in `constraints.md`; this doc spells them out for one concrete propagator
  and flags the bits that should carry across to `Disjunctive` and
  `BinPacking`.
- [`Regular`: design and proof scaffolding](regular.md) — working-design
  note for the upfront-DAG `Regular` propagator: layered-DAG view, OPB
  encoding, Top-level scaffolding (per-val backward chains + statically-
  dead-state lines), slim per-call propagator, and bench numbers vs
  `RegularLegacy`. Cross-references the broader unification path of
  issue #200.
- [Proof logging for `Disjunctive`](disjunctive-proof-logging.md) — companion
  to the cumulative writeup, focused on justifying directly against
  the declarative OPB encoding (pairwise non-overlap clauses only):
  every `h = 1`, `c = 1` time-table inference is a two-task ordering
  statement, backed by pols over the before-flag reification halves
  and the operands' bound-literal definition rows — no time-indexed
  scaffolding at all. Covers the per-blocker push chains, variable
  durations without in-proof end variables, and the same recipe one
  dimension up for `Disjunctive2D`.
- [Difference logic](difference-logic.md) — design note for
  `DifferenceConstraints`, the global propagator for systems of `x - y <= d`:
  the constraint-graph formulation, the two Bellman-Ford directions, why every
  operand is canonicalised to a bare variable before the OPB row is emitted
  (representation consistency, without which nothing cancels), the two proof
  shapes — a negative cycle refuted by one telescoping `pol`, a bound push
  justified per edge along the predecessor forest — the source paper's
  pseudocode defects, the measured order-independence and proof-size results,
  half-reified edges `b -> x - y <= d` (the one extra `saturate`, why the reason
  must name every conditional edge used, and why the round bound survives an
  edge set that changes between calls), the `DifferenceLogic` presolver that
  lifts an already-posted model into the same propagator (including why
  `DisableUntilBacktrack` could not be imposed from outside, and why a
  half-reified donor is never retired), the RCPSP/max benchmark tables
  (including where the non-incremental propagator loses, and why "detected at
  the root" belongs to the paper's root simplification stage rather than to its
  propagator), and what is deferred (incrementality, `IncImp`, root
  simplification).
- [Range ("in") literals](range_literals_spec.md) — the design specification
  for the interval-literal proof layer: reifying `[X∈[a,b]]` to its
  order-chain cuts, the always-covered partition invariant, interval-tree
  containment, and the P1/P2 (line-checkability vs replay-completeness)
  distinction that governs which linking clauses are load-bearing — with the
  W1–W5 witness suite as the regression defence against re-simplification.
  Read when touching range/interval reasons, branching, or `infer_not_in_range`.
- [View proof logging](view-proof-logging.md) — how the proof layer handles
- [arithmetic-proofs.md](arithmetic-proofs.md) — how Multiply/Divide/Modulus/Power propagate and justify against cake's encoding: the slot-keyed emitters, the ConditionalBound justification layer, the sign-case driver, and the hard-won RUP/pol rules.
- [Decision-diagram proof strategies](decision-diagram-proof-strategies.md) — for
  the layered/partial-sum propagators (`Regular`, `MDD`, `Knapsack`,
  `BinPacking`), the choice between "upfront" Top-level scaffolding and "per-call"
  RUP-driven proofs. The `veripb_time = displacement × DB-tax` cost model that
  explains why proof size and verification time diverge, the per-propagator
  measured verdicts and defaults, a predictive rule to apply before implementing,
  and why scaffold deletion is unsafe while hinting the propagator's own RUPs is
  the high-value lever. Read when adding or tuning a diagram-shaped constraint.
  views (`ViewOfIntegerVariableID`): the V↔X link constraints that tie a view's
  proof variable to its underlying variable, and how literals over views are
  deviewed for emission. Read when touching view handling in proofs.
- [Proof logging for `Sort` / `ArgSort`](sortedness.md) — the fully-certified
  Mehlhorn–Thiel sortedness propagator proof: the permutation/root argument and
  the Hall-band pigeonhole over ranks. A worked companion to `constraints.md`.
- [Reasons rework (design)](reasons-improvement.md) — the rationale for the
  declarative `Reason` variant and lazy `materialise()` that replaced the eager
  `ReasonFunction` thunks. Read alongside `infer-redesign.md`.
- [Infer rework (implementation notes)](infer-redesign.md) — the as-built
  justification layer: `JustifyExplicitly` / `JustifyUsingRUP`, the mandatory
  `ThenRUP` enum, the pay-for-use `SimpleInferenceTracker`, and the typed
  per-constraint assertion hints (`gcs::innards::hints`).
- [SCP s-expression migration](scp_s_expr_migration.md) — how constraints expose
  themselves to the sub-constraint-proof (SCP) writer via `s_expr`, and the
  status of the per-constraint migration.
- [Workflow-2 / SCP chain testing](workflow2_testing.md) — the
  `glasgow_scp_solver` binary and the SCP chain test harness
  (`run_scp_chain.bash`, `scp_cases/`) for verifying constraint encodings
  against an external checker.
- [`Knapsack`](knapsack.md) — the default per-call DP `Knapsack` (chosen
  for fastest proof verification) and the opt-in upfront-DAG
  `KnapsackUpfront` (#200), the *k*-coordinate generalisation of
  `BinPacking` Stage 3. Covers the `define_proof_model` /
  `install_initialiser` split, the paper-style reified scaffolding, the
  per-call proof chain, and the measured default-vs-opt-in trade-off.
- [Subset-sum strengthening](subset-sum-strengthening.md) — tightening a derived
  `Σ c_i x_i ≤ B` to the largest subset sum at most `B`, by Chvátal–Gomory
  rounding when the coefficients share a factor and by a layered dynamic
  programme otherwise. Covers why the two lines have the same solutions but not
  the same strength, the clause resolution that stands in for the case split
  unit propagation cannot do, and why a satisfiable test model and an `ia`
  content check are both needed to test it.
- [Strengthening a `Cumulative` by integrality](cumulative-strengthening.md) —
  Schulz's pre-solving rules as the `CumulativeStrengthening` presolver, posting
  the strengthened constraint in derived mode. Covers why the largest reachable
  load is the real capacity, why the tasks that fill the resource on their own
  have to be set aside from that sum and given the capacity as their height
  instead (which is both of Schulz's height rules arriving at the same place),
  why raising a coefficient in cutting planes is a loop rather than one
  division, why the rules are *time-table neutral* and how that turns into a
  node-for-node soundness tripwire, the `ia` step that pins every row to the
  declared capacity (and is the only thing that catches a sound derivation of
  the wrong line), and why the deep-gap fixture everyone quotes cannot be a
  `Cumulative` instance.
- [Inferring `Disjunctive` constraints across resources](inferred-disjunctive.md) —
  the `InferredDisjunctive` presolver: conflict cliques spanning several posted
  Cumulatives, posted in derived mode. Covers why the cross-resource case is an
  inference no single Cumulative can make, the three-piece certificate (pairwise
  at-most-one out of a witnessing row, flag bridge, clique merge), why two-task
  cliques are never worth posting, the camouflage fixture the mutations need, and
  the measured proof size — which is the thing to fix before pointing this at a
  real instance.
- [Inferring `Cumulative` constraints by lifting cover inequalities](inferred-cumulative.md) —
  the `InferredCumulative` presolver: cover inequalities over one posted
  Cumulative's rows, lifted to non-unit coefficients and posted in derived mode.
  Covers why energy is the only thing a valid cut can buy (and why that makes it
  time-table neutral for a one-line reason), why lifting is run *forward* —
  arithmetic first, cut second — rather than by computing the largest valid
  coefficient and hunting for a derivation of it, the three shapes of `pol` the
  certificate takes and why non-unit coefficients need the third, how a cut is
  restricted to the tasks present at one time point when its heights cannot move,
  and the differential fixture that separates this from the capacity-one stage.
- [Certified makespan lower bounds from a `Cumulative`'s energy](certified-makespan-bounds.md) —
  turning the `L` those two presolvers report into a number the proof contains.
  Covers the window-energy argument under the objective's order literal, the two
  places the derived bound is *not* `L`, why the deadline step has to be a `pol`
  and cannot be a RUP (and so why a makespan is a variable with rows around it
  rather than a kind of variable), the three mutations VeriPB refuses and the
  fourth that cannot be caught, and the RCPSP bounds artefact.
- [Restarts, nogoods, and dom/wdeg weighting](restarts-nogoods-weighting.md) —
  the search-side machinery from issue #315: the restart loop and its
  `SearchResult` unwind signal, `RestartSchedule`, the `ConflictObserver`
  weighting seam and the dom/wdeg schemes, the `Nogoods` constraint
  (entailment-based 2WL), reduced-nld extraction, and the proof lifecycle
  (root-keeps-level-1, deep-first-unwind RUP for reduced clauses, `solx`-enabled
  enumeration). Read when touching restarts, nogoods, or branching heuristics.
- [Refined triggers](refined-triggers.md) — the per-literal watch mechanism that
  lets a propagator wake only when specific literals (`x = v`, `x >= k`, ...)
  become entailed, instead of on every change to a whole variable: the
  `RefinedWatchContext`, the watch index with fire/consume/restore-on-backtrack,
  the per-literal trigger masks, the backtrackable `watch_state` scratch (and why
  it is not `add_constraint_state`), and the two-watched-literal `Nogoods` client
  that motivated it. Read when touching the propagation-queue/watch internals or
  nogood propagation performance.
- [Connectivity: encoding and proofs](connectivity-proofs.md) — the design note
  for `Reachable` / `DReachable` (#637): why the stdlib's arithmetic distance
  labelling makes every connectivity inference un-RUPable (unit propagation
  cannot do the induction the infinite-descent argument needs), and why a
  breadth-first *unfolding* of the same idea makes all of them plain RUP —
  unit propagation over the levels is the search the propagator ran. Covers the
  encoding, the one-hot root row and why the root is a caller-supplied variable,
  the border-cut reasons, why the propagator is GAC (the removals plus the
  residual graph's cut vertices and bridges, which are exactly the other half,
  one Tarjan pass undirected and a search per candidate root directed) and how
  the tests check that, why a forcing made before search has decided the root
  costs a proof line per candidate root while one made after costs one line
  (measured, not assumed), the `O(nodes × edges)` size that is the price,
  and the measured hitori comparison — 815 MB / 796 s of decomposition proof
  against 130 KB / 0.09 s.
- [`MinDistance`: encoding and proofs](min-distance-proofs.md) — the definitional
  OPB encoding for `min_distance(D, x, z)` (site-selection flags, per-site counts,
  pair clauses, and the min-attained ladder), the justification for each of the
  five propagation strengths, and the guarded counting derivation that certifies
  the conflict-matching upper bound — a worked example of riding a guard literal
  through an `all_different`-style at-most-one recurrence with an exact
  coefficient. Also records what was deliberately left out, and why.

More documents will be added here as we build up coverage of other parts of
the codebase.
