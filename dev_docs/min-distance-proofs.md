# The minimum-distance constraint: encoding and proofs

`min_distance(D, x, z)` links `p` selected-point variables `x_0, ..., x_{p-1}`,
each ranging over site indices `0..n-1`, to a variable `z` holding the smallest
pairwise distance between the sites they choose:

    z = min_{0 <= i < j < p} D[x_i, x_j],

with `D` a symmetric `n x n` integer matrix, zero diagonal, non-negative
entries. Duplicate selections are allowed and contribute the diagonal distance
`D[a,a] = 0`, so two positions on one site force `z <= 0`. The optional
requirements matrix `R` adds pairwise lower bounds `D[x_i, x_j] >= R_ij`. This
is the constraint of Lagerkvist, "Propagation Algorithms for the
Minimum-Distance Constraint over Selected Points" (ModRef 2026); the code is
`gcs/constraints/min_distance/min_distance.cc`, and the propagation strengths
(`MinDistancePropagation`) follow the paper's Sections 4.1, 4.2 and 4.4.

The design is deliberately conservative about proofs. The OPB encoding is
*definitional* — every proof-only flag is a full reification, and any complete
assignment of `x` unit-propagates every flag and pins `z`, so solution logging
is sound. The encoding was frozen and validated by a check-only propagator
before any bespoke justification was written (below). All five propagation
modes share that one encoding; the strength selector never touches
`define_proof_model`. Nothing under `gcs/innards/proofs/` was changed, and the
matching certificate reaches the encoding only through the public `PolBuilder`,
tracker and `emit_rup_proof_line` interfaces — never by OPB line number
(`add_constraint` returns void by policy). No inference anywhere uses an
unchecked `a` assertion.

## The definitional encoding

`define_proof_model` emits, over the *candidate sites* (values some `x_i` can
still take at post time, recorded in `_position_sites` / `_sites` by
`prepare`):

### Site-selection flags `u_a`

    u_a  <->  OR_i [x_i = a]      (arc-consistent full reif, one per site)

`u_a` records only that site `a` is selected by *at least one* position. It
cannot tell one selection from two, and that distinction is the whole reason
the diagonal (duplicate) case is handled separately below.

The naive diagonal encoding is the trap to avoid. It is tempting to obtain the
`z <= 0` duplicate bound by instantiating the pair clause (next section) at
`a = b`, giving `~u_a \/ ~u_a \/ [z <= 0] = ~u_a \/ [z <= 0]`. That is wrong:
it forces `z <= 0` the moment *any single* position selects `a`, because `u_a`
is already true then. Duplicate detection needs the multiplicity, not `u_a`,
which is what the per-site count constraint supplies.

### Per-site counts (the diagonal / duplicate bound)

    Sum_i [x_i = a]  <=  1 + (p-1) [z <= 0]

Two positions on one site witness `D[a,a] = 0`, so `z <= 0`. When `[z <= 0]` is
false the constraint is a plain at-most-one forbidding the duplicate; when two
or more positions do coincide the count reaches `>= 2`, which forces `[z <= 0]`
true (the `(p-1)` coefficient is exactly large enough: the count is at most
`p`, and `1 + (p-1) = p`).

The `(p-1)[z <= 0]` term takes three concrete forms, chosen at build time from
`z`'s initial domain rather than left to the checker (all in the loop over
`_sites`):

- `z_hi <= 0`: `[z <= 0]` is constant-true, the row is vacuous — **skipped**.
- `z_lo >= 1`: `[z <= 0]` is constant-false, the term drops — emitted as the
  **plain at-most-one** `count_a <= 1`.
- otherwise the **general** form, written with `[z <= 0] = 1 - [z >= 1]` moved
  to the left: `count_a + (p-1)[z >= 1] <= p`.

The row exists at all only when `>= 2` positions can take site `a` (otherwise
no duplicate is possible and it would be vacuous).

### Pair clauses (the distinct-site upper bound)

    ~u_a \/ ~u_b \/ [z <= D[a,b]]      for candidate sites a < b

If sites `a` and `b` are both selected then `z` is at most their distance.
Keying these on *sites* rather than position pairs is what collapses the
decomposition's `O(p^2)` links into `O(n^2)` clauses. A clause is **omitted**
only when it is tautological for `z`'s whole initial domain, i.e. when
`z_hi <= D[a,b]` (the disjunct `[z <= D[a,b]]` is already implied). The
top-distance witness pair is never even created, since nothing above it needs
guarding.

### Requirement clauses

    ~[x_i = a] \/ ~[x_j = b]      for i < j and D[a,b] < R_ij

Sparse forbidden-pair clauses, one per offending value pair, including the
`a = b` diagonal (`D[a,a] = 0 < R_ij` when `R_ij > 0`). Our `R` is already the
`>=` form; the `+1` conversion from the p-dispersion `r_ij` happens at the
call site, not here.

### The min-attained ladder (the lower bound on z)

The pair clauses and counts only push `z` down. The lower bound — that `z` is
*at least* the minimum distance actually attained — is a telescoping ladder
over the distinct levels `L = sorted({0} U {D[a,b] : candidate a < b})`. Two
families of witness flags say a given distance is attained:

    d_a  <->  Sum_i [x_i = a] >= 2         (a duplicate attains distance 0)
    w_ab <->  u_a /\ u_b                    (both sites selected attains D[a,b])

Both are full reifications, created lazily — only when a ladder level above
them refers to them. For each level `t_k` (with `z_lo < t_k`) the ladder emits

    [z >= t_k] \/ m_k

where `m_k` is a flag meaning "some pair at a distance *strictly below* `t_k`
is already attained". `m` accumulates telescopically:
`m_{next} <-> m_k \/ (witnesses at t_k)`, with the base `m` for level `0` being
`false` (so the base clause is just `[z >= 0]`, itself emitted only if `z`'s
domain dips below zero). Read together the ladder forces `z` up to each level
unless a smaller distance is witnessed — pinning `z` from below to the true
minimum attained distance. Because every flag is a full iff determined by unit
propagation from any complete `x`, a full assignment pins `z` to exactly the
minimum pairwise distance, and solution logging is sound.

## Check-only first: validating the encoding

Before any bespoke justification existed, the constraint shipped with a
*check-only* propagator (`install_check_only_propagator`, still the `CheckOnly`
mode and the encoding's regression test). It acts only once a pair's endpoints
are both assigned: it checks the requirement, tightens `z <= D[a,b]`, and once
every position is fixed pins `z` to the exact minimum. Every one of those
inferences is plain `JustifyUsingRUP{}` from the encoding — no `pol`, no
explicit steps. So the methodology was: if VeriPB accepts the whole data-driven
suite under check-only, the encoding is *definitionally correct and strong
enough* that RUP alone certifies every consequence it can reach. It did (Gate
2), which is what licensed building real propagation on top without ever
revisiting the encoding.

## Propagation and its justifications

### Plain-RUP prunes (ForwardBound / PairSupport)

`install_forward_propagator` runs one global propagator over all `x` and `z`
(paper Sections 4.1-4.2), with threshold `T_ij = max(R_ij, z_min)`:

- **Assigned-endpoint forward prune**: when `x_i = a`, remove every `b` from
  `dom(x_j)` with `D[a,b] < T_ij`. `JustifyUsingRUP{}`, reason `{x_i = a}` plus
  `z >= z_min` *only when the z part of the threshold binds* (i.e.
  `D[a,b] >= R_ij`, so the R forbidden-pair clause is not itself carrying it).
  RUP closes through `[x_i=a] -> u_a`, the pair clause (or the R clause) and
  `z`'s bound atoms.
- **Pair-support prune** (PairSupport only): remove `a` from `dom(x_i)` when no
  `b in dom(x_j)` has `D[a,b] >= T_ij`. `JustifyUsingRUP{}`, reason
  `dom(x_j)` plus `z >= z_min` when it binds; `a` itself is *not* in the reason
  (it is being removed). Assuming `[x_i=a]`, every `b in dom(x_j)` dies by unit
  propagation and `x_j`'s at-least-one closes it — a single RUP line.
- **Full-assignment pin**: `z >= mu` and `z <= mu` once all `x` are fixed,
  `JustifyUsingRUP{}` over all of `x` (the `z >= mu` half is the ladder).

### The pairwise objective upper bound

`u_ij = max{ D[a,b] : a in dom(x_i), b in dom(x_j), D[a,b] >= R_ij }`; tighten
`z <= u_ij` (or fail the node if the set is empty / below `z_min`). This one is
not plain RUP — it is a `JustifyExplicitly{emit, ThenRUP::Yes}` with a
per-value loop over the *smaller* endpoint domain (both work by symmetry; the
smaller one is cheaper). For each `a in dom(x_loop)` the callback emits one
`Temporary` line

    ~[x_loop = a] \/ [z <= u_ij]      (under the two-endpoint reason)

Each is RUP: assume `x_loop = a` and `z > u_ij`; every partner `b` in the other
domain has either `D[a,b] <= u_ij` (pair clause forces `~u_b`, hence
`~[x_j=b]`) or `D[a,b] < R_ij` (R clause kills `b`), and the other endpoint's
at-least-one closes. After the loop, `[z <= u_ij]` is RUP from the derived
clauses plus `x_loop`'s at-least-one, which `ThenRUP::Yes` concludes. The z
bound needed to kill each partner comes free from negating `[z <= u_ij]`, so
the reason is just the two endpoint domains — no z literal. The infeasible case
(empty `u_ij` set) runs the identical loop under `inference.contradiction`,
emitting `~[x_loop = a]` with no `[z <= ...]` disjunct; `z >= z_min` is added to
the reason exactly when a partner needs the pair clause plus the current lower
bound to die. Cost: `O(|dom(x_loop)|)` temporary lines per strict tightening.

### The conflict-matching upper bound (the interesting one)

`install_matching_propagator` (paper Section 4.4, Algorithm 1) is posted as a
*separate* propagator alongside the ForwardBound/PairSupport kernel in the
`...Match` modes. It only ever lowers `z`'s upper bound; the base kernel does
all lower-bound work.

Per wake it builds the active set `A` = union of the current selected-point
domains, and binary-searches the precomputed sorted distinct distance levels in
the window `max(z_min, 1) <= t <= z_max` for the smallest *refuted* level. A
level `t` is tested by building the conflict graph `G_t[A]` (edge `a~b` iff
`D[a,b] < t`), taking a greedy maximal matching `M`, and declaring `t` refuted
iff `|A| - |M| < p`. Soundness: any independent set of `G_t[A]` — a set of
sites pairwise at distance `>= t` — has at most `|A| - |M|` vertices (an
independent set misses at least one endpoint of every matched edge). If `z >= t`
then all pairwise distances are `>= t >= 1`, so the `p` positions occupy `p`
distinct sites forming an independent set of size `p`; if `|A| - |M| < p` no
such set exists, so `z < t`. The greedy matching is only *weakly monotone*, so
the binary search is a heuristic for a good level, not a monotonicity proof —
but every refutation is certified individually, so soundness never rests on the
search (paper Section 4.4). At the smallest refuted `t*` we infer `z <= t*-1`;
if `t* <= z_min` the node fails instead.

**The justification: a guarded counting derivation.** The guard literal is
`g = [z <= t-1] = ~[z >= t]`. Everything is proved under the assumption
`z >= t` (which makes `g` false), and `g` is the final conclusion. The emit
callback (`JustifyExplicitly{emit, ThenRUP::Yes}`, all lines `Temporary`)
mirrors `justify_all_different_hall_set_or_violator` from `justify.cc`:

1. **A guarded at-most-one per matched edge and per unmatched site.** For an
   edge `(a,b)` the literal set is `L = { [x_i=a] : i in positions_at[a] }` U
   `{ [x_i=b] : i in positions_at[b] }`; for an unmatched site `c` it is
   `{ [x_i=c] : i in positions_at[c] }`. Under `z >= t` at most one literal of
   `L` can hold, so `Sum_{l in L} ~l >= |L|-1`, which guarded reads

       Sum_{l in L} ~l  +  (|L|-1) g  >=  |L|-1.

   It is built from pairwise guarded binary clauses. For every unordered pair
   `{l_r, l_s}` in `L`, emit `~l_r \/ ~l_s \/ g` by RUP — RUP against the
   encoding in all three shapes:
   - **cross-site** (`[x_i=a]`, `[x_j=b]`, `a != b`): the pair clause plus
     `D[a,b] < t` gives `[z <= D[a,b]]`, contradicting `z >= t`;
   - **same-site** (`[x_i=a]`, `[x_j=a]`, `i != j`): the per-site count forces
     `[z <= 0]`, contradicting `z >= t >= 1`;
   - **same-position** (`[x_i=a]`, `[x_i=b]`): the variable's own at-most-one.

   These are combined by the `PolBuilder` layer recurrence: for `i` in
   `1..|L|-1`, if the layer `i >= 2` multiply the partial by `i`, add the `i`
   fresh pairwise clauses (`l_i` against each `l_j`, `j < i`), then divide by
   `i+1`. The invariant is that after literal `i` the partial reads
   `Sum_{j<=i} ~l_j + i g >= i`. The guard rides the ceil-divisions with an
   **exact** integer coefficient: entering layer `i` the coefficient is `i-1`;
   multiply by `i` gives `i(i-1)`; the `i` new clauses add `i` copies of `g`
   giving `i(i-1) + i = i^2`; and `ceil(i^2 / (i+1)) = i` because
   `i^2 = (i+1)(i-1) + 1`, so `i^2/(i+1) = (i-1) + 1/(i+1)`. No rounding slack
   ever accumulates on `g`, which is what keeps the final divide exact. A
   single-literal `L` has no pair to combine, so the code emits only the
   trivially-true `~[x_i=c] >= 0`, whose sole job is to cancel that position's
   at-least-one term below; an empty `L` contributes nothing.

2. **Sum and divide.** Add every edge/unmatched at-most-one to every
   non-constant position's at-least-one
   (`need_constraint_saying_variable_takes_at_least_one_value`), and divide by
   `C = Sum_edges(|L_ab|-1) + Sum_unmatched(|P_c|-1)` — the total guard
   coefficient. Each active site sits in exactly one at-most-one, and its
   `~[x_i=a]` terms cancel against the at-least-ones' `+[x_i=a]` terms; what
   remains is `g` with coefficient exactly one (the surviving numerator is
   `p - (|A| - |M|) >= 1`, which is precisely the refutation inequality),
   possibly plus a few `[x_i=a]` literals for pruned / holey / out-of-active
   values. `ThenRUP::Yes` then RUPs `z <= t-1` (or `false` on the contradiction
   path) under the reason, discharging those leftover literals.

**Why the reason is the x domains.** `generic_reason(x)` (all `x` domains) is
the reason; `z`'s own bound is *not* in it (the conclusion is about `z`). The
current domains define `A` and, crucially, the leftover root-domain literals
`[x_i=a]` for values `a` no longer live are false under this reason, so the
closing RUP discharges them. The literal sets `L` range only over
`positions_at` — positions whose *root* domain contains the site, mirroring the
encoding's map — so no `[x_i=a]` the OPB never mentions is ever emitted.
Constant positions carry no at-least-one from the tracker; their `[x_i=c]`
folds to the constant `1` in the pol sum and `0` in the `~` terms, cancelling
exactly, so they are simply skipped.

**The contradiction path** (`t* <= z_min`) runs the same emit under
`inference.contradiction` with `z >= z_min` added to the reason: the pol still
derives `g = [z <= t-1]`, which is domain-false given `z >= z_min >= t`, so RUP
closes the node.

**Why `z <= t-1` and not the previous distinct level `t*`.** Refuting `t`
proves `z` is strictly below `t`, i.e. `z <= t-1` — that is exactly what the
counting certificate gives. The stronger claim `z <= t*` (the largest distinct
distance below `t`) is *not* plain RUP: it would require the min-attained
ladder disjunction `[z >= t*] \/ m_{t*}` to unit-propagate `m_{t*}`, but
`m_{t*}` is a free disjunction of witness flags that the matching argument does
not force. A per-witness case analysis could recover it; it is a measured
follow-up only if search shows it matters, and only the single final refuted
level is justified per tightening. In practice `z <= t-1` plus the ladder and
the rest of propagation lands `z` on an achievable level anyway.

## Costs and measured numbers

Per strict matching tightening the certificate is `O(|M| p^2)` RUP lines (each
edge's at-most-one has `<= 2p` literals, hence `O(p^2)` pairwise clauses) plus
`O(|M|)` pol lines; all are `Temporary`, forgotten when the justification scope
closes, so they never enter the live database (VeriPB's hinted-RUP cost model).
The verified prototype (`min-distance-plan/proto/gen_proto.py`, p=4, |A|=5,
|M|=2) is 58 rup + 4 pol per tightening.

The proofs-on grid measurements (`min-distance-bench/proofon4.csv`, all `s
VERIFIED` optimal) bear out the trade. On grid 5x5 p=6 the matching cuts search
sharply — `min-distance-psm` proves optimality in 669 nodes versus
`min-distance-ps`'s 1505 (2.25x) — while each tightening's counting certificate
makes the proof about 1.5x larger per node (3.50 MB vs 2.23 MB); the node
reduction offsets it, so VeriPB time is flat-to-better (0.628 s vs 0.653 s).
Both stay roughly 9-10x smaller and faster than the `tuple` decomposition (30.6
MB / 8.08 s), whose `O(p^2)` Element + ArrayMin propagators each emit their own
proof traffic. On grid 4x4 p=4 the matching never fires (the pairwise bound is
already tight), so `fbm`/`psm` write byte-identical proofs to `fb`/`ps`. The
consolidated tables are in `min-distance-plan/BENCHMARKS.md`.

## Deliberately not implemented

- **The paper's `heur-aggr` variant (Section 4.5).** It prunes using sampled
  greedy completions — a heuristic estimate, not an entailment. The paper is
  explicit that it "may remove a branch that contains an optimal solution" and
  that "the loss of completeness is explicit" (a *half-checking* propagator).
  Such an inference has no sound proof, so it is fundamentally incompatible with
  certification and is excluded by design. (The `heur-safe` argument — the
  pairwise upper bound under a tentative assignment — *is* sound and is what the
  ForwardBound objective bound already does.)
- **Advisor-backed scheduling (Section 4.3).** Gecode advisors record which
  pairs go stale after a domain change so a propagator can skip rescanning
  unchanged pairs. gcs has no advisor mechanism, and these propagators recompute
  from scratch each wake (simple first, per `propagator-performance.md`'s
  "measure before adding incrementality"). It would be a pure *performance*
  lever — identical search, identical proofs — and the benchmarks already show
  the paper's qualitative result (matching wins at higher `p`) under the simple
  scheduling, so it is unneeded so far. Dirty-pair / incremental-active-set
  tracking is the obvious follow-up if a profile ever shows the full rescan
  dominating.

## See also

- `gcs/constraints/min_distance/min_distance.cc` — the constraint, all five
  modes, and `define_proof_model`.
- `min-distance-plan/proto/gen_proto.py` — the hand-built, VeriPB-verified
  prototype of the matching counting derivation.
- `dev_docs/arithmetic-proofs.md` — the companion for the `pol`/`rup` style and
  the VeriPB cost model this leans on.
- `dev_docs/propagator-performance.md` — the strength-vs-performance discipline
  behind the recompute-from-scratch choices here.

<!-- vim: set tw=78 spell spelllang=en : -->
