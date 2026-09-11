# `ParitySystem`: GF(2) reasoning over a conjunction of XORs

Working note for issue #647. **Status: the constraint is built and its proofs
verify with zero assertions. `ParitySystemGathering` is not written yet.**

`ParityOdd` reasons about one XOR at a time (`gcs/constraints/parity/parity.cc`,
the `if (++how_many_unknown > 1) return` bail-out). That is GAC for a single
XOR — unit propagation on one parity constraint *is* GAC, because any value has
a support while two literals are still free — so all of the available inference
lives in the conjunction, and we currently throw it away. Over GF(2) the
conjunction is one of the rare tractable cases: Gauss-Jordan on the system
exposes every implied literal, and implied literals are exactly what GAC on the
system means.

Two things get built:

- **`ParitySystem`**, a global constraint over a set of XOR rows; and
- **`ParitySystemGathering`**, a presolver that scans a posted `Problem` for
  XOR-shaped constraints, gathers them into a system, installs the global
  propagator over them, and retires the donors' own propagators.

The presolver is the one that will actually be used: the XOR structure survives
MiniZinc flattening intact (`array_bool_xor` → `ParityOdd`, `minizinc/fzn_glasgow.cc`),
so a model already arrives as a pile of individual `ParityOdd`s and nothing has
to be re-modelled to get the system propagation. `gcs/presolvers/difference_logic/`
is the template throughout: same shape, same reasons.

## What is new, and what is not

Nobody in mainline CP does the system (issue #647 has the survey). CP-SAT knows
it should and says so in a TODO. The two research artifacts are `abstractXOR`
(Rouquette and Solnon, CP 2020, a Choco prototype that never landed) and
MiniCPBP's linear modular constraint. The SAT side is far ahead — CryptoMiniSat
runs Gauss-Jordan during search — so **the claim here is the certificate, not
the speed**: first CP solver with *certified* system-level parity reasoning.
"Fastest" is not the claim and should not be made.

The proof technique is Gocht and Nordström, *Certifying Parity Reasoning
Efficiently Using Pseudo-Boolean Proofs* (AAAI 2022, arXiv:2209.12185); section
numbers below are theirs. What is new here is not the technique but the bridge:
their §4.4 recovers the pseudo-Boolean form of an XOR from a *CNF* encoding it
did not write, by brute force over all assignments. We wrote our encoding, and
it is already the split-into-3-XORs shape their (4.15) describes, so we get the
same row in a linear number of steps instead. See "Deriving the slack row".

## The proof shape, bottom up

### 1. The slack form, and why we cannot just write it in the OPB

Gocht and Nordström's (4.3): for fresh, otherwise unconstrained `y`,

```
    sum_{i in [k]} x_i  =  b + 2 * sum_{j in [floor(k/2)]} y_j
```

is satisfiable exactly when `x_1 XOR ... XOR x_k = b` is. Their (4.4)
generalises `2 * sum y_j` to `2B` for *any* integer linear form `B`, and that
generality is what makes everything below cheap. Under this form **a Gaussian
elimination step is adding two pseudo-Boolean equalities: one `pol` line.**

We cannot put that form in the `.opb`, for two independent reasons.

- `ParityOdd::define_proof_model` emits cake_pb_cp's accumulator chain, because
  the `.scp` says `parity` and cake re-derives its own OPB from that (workflow
  2, [workflow2_testing.md](workflow2_testing.md)). A proof line citing a row
  that only *our* OPB contains fails against cake's. The slack rows must
  therefore be **introduced inside the proof**, which is the
  chain-portable option — see [variable-encodings.md](variable-encodings.md),
  "Why 'not in OPB' is a first-class option".
- A presolver runs after the proof model is finalised. `Presolver::run` has no
  `ProofModel *` at all; that door is shut by the time it is reached.

So the slack rows are derived, once per donor, at `ProofLevel::Top`, from rows
the donor already emitted. That is the same discipline `DifferenceLogic`
follows, one step further along: it cites donors' rows directly, we derive one
row per donor from them first.

### 2. Deriving the slack row from the accumulator chain

`ParityOdd`'s encoding introduces flags `a_0 .. a_n` (`x[id][k]` in cake's
naming) with

| row | label | as `>= 0` |
|---|---|---|
| `a_0 <= 1` | `0ge` | `1 - a_0 >= 0` |
| `a_0 >= 1` | `0le` | `a_0 - 1 >= 0` |
| step `k`, `00` | `k_0_0` | `a_{k-1} + l_k - a_k >= 0` |
| step `k`, `11` | `k_1_1` | `-a_{k-1} - l_k - a_k >= -2` |
| step `k`, `10` | `k_1_0` | `-a_{k-1} + l_k + a_k >= 0` |
| step `k`, `01` | `k_0_1` | `a_{k-1} - l_k + a_k >= 0` |
| `a_n = 0` | `acc` | `-a_n >= 0` |

Each step is a 3-XOR, `a_{k-1} XOR l_k XOR a_k = 0`, which is exactly the
partial-parity split of Gocht and Nordström's (4.15) — so the long XOR is
recovered by summing the steps (their §4.2), and only the steps need a
translation. Writing `a`, `l`, `a'` for `a_{k-1}`, `l_k`, `a_k`, and
introducing one fresh in-proof flag `y_k` per step:

- **`red` 1, witness `y -> 1`:** `2y - a - l - a' >= 0`. The only goal is on
  the new constraint, `2 - a - l - a' >= 0`, and it discharges by RUP: negating
  it fixes all three of `a`, `l`, `a'` true, and `k_1_1` then reads `-3 >= -2`.
  The goals on the formula are vacuous because `y` is fresh, so nothing already
  in the database mentions it. No subproof.
- **`red` 2, witness `y -> 0`:** `a + l + a' - 2y >= 0`. The goal on the new
  constraint is `a + l + a' >= 0`, which normalises to degree 0 and
  auto-discharges. The one real goal is the *first* red's constraint under
  `y = 0`, namely `-a - l - a' >= 0`, and it needs a five-line `pol` subproof
  against the negation `N: 2y - a - l - a' >= 1`:

  ```
  S1 = N + 2 * (literal axiom ~y)  ->  -a - l - a' >= -1
  S2 = S1 + k_0_0  ->  -2a' >= -1  -> /2 ->  -a' >= 0
  S3 = S1 + k_1_0  ->  -2a  >= -1  -> /2 ->  -a  >= 0
  S4 = S1 + k_0_1  ->  -2l  >= -1  -> /2 ->  -l  >= 0
  S5 = S2 + S3 + S4 + (negated goal, a + l + a' >= 1)  ->  0 >= 1
  ```

  The three divisions are where the parity argument lives: unit propagation
  cannot do it, which is why this is not a RUP. **`S5` adds the negated goal**,
  because a `proofgoal` block has to end in a contradiction rather than in a
  derivation of the goal — deriving `-a - l - a' >= 0` and stopping there is
  the shape VeriPB rejects, and it costs nothing to avoid, since the negated
  goal is already in scope.

  Two line references inside that block, and both have to be **absolute**.
  `ProofLogger::get_current_proof_line()` at the top of the subproof body is
  the negated goal, and the negation of the constraint the `red` is adding sits
  one before it. Capture both there: a relative `-1` still says `-1` five lines
  later, by which point it means the line just emitted rather than the one
  intended — which is what the first attempt at this did, and what VeriPB
  reported as a `proofgoal` not ending in a contradiction.

Only steps of the *other* order carry goals over the earlier steps' rows: a
`y_{k'}` from step `k' < k` is not in step `k`'s witness domain, so those rows
restrict to themselves and generate nothing. That is also a canary — an
implementation that accidentally reused one `y` across steps would not go
quietly wrong, it would acquire goals it cannot discharge and fail at check
time.

The order of the two `red`s is not load-bearing for soundness, only for cost.
Swapping them moves the work: `red(D2)` first is entirely goal-free, and
`red(D1)` second then has to prove `a + l + a' >= 2`, which takes seven lines
rather than five. Take the cheaper order.

Rows of length 0 have no chain to telescope — `a_0` and `a_n` are the same flag
— so `derive_parity_slack_rows` returns nothing for one, and `ParitySystem`
does not build a system at all when it sees one: it installs an initial
contradiction instead, justified by plain RUP. That is the honest answer rather
than a special case. An empty odd row says zero is odd, its own `0ge` / `0le` /
`acc` rows pin `a_0` to one and to zero at once, and there is nothing for
elimination to do with a system containing it. Getting this wrong is what a
half-built row looks like from VeriPB's side: a justification citing a slack
row that was never derived, reported as a reference to a deleted constraint.

Summing the two directions over `k = 1..n` telescopes the accumulators (every
`a_j` for `0 < j < n` appears twice, so with coefficient 2, which is even and
therefore part of `B`):

```
  sum_k (red2_k) + `0ge` + `acc`                ->  sum_i l_i >= 1 + 2B
  sum_k (red1_k) + `0le` + (literal axiom a_n)  ->  sum_i l_i <= 1 + 2B
  where B = sum_k y_k - sum_{0<j<n} a_j - 1
```

which is (4.4a) and (4.4b) with `b = 1`. **Two `pol` lines per donor.**

Cost: `2n` `red` lines and `5n` subproof lines per donor of length `n`, all at
`Top`, plus two `pol`s. The `red`s and the per-step rows are scaffolding — only
the two summed rows are ever cited again, and nothing downstream needs `y`'s
definition — so they are deleted immediately afterwards. `Top` is never
forgotten, and every line left there taxes every later unhinted RUP (#666), so
the deletion is not tidiness. **Steady-state `Top` footprint: two lines per
donor.**

Deleting them is safe and is *unchecked*: redundance established
equisatisfiability while the rows still stood, and every model of the chain
rows extends to one of (A) and (B) by `y_k = (a_{k-1} + l_k + a_k) / 2`, which
those rows make integral. The deletion goes unchecked because `D1`/`D2` are
red-derived and so live in the derived set, and whether a deletion is checked
follows where the target lives rather than which rule wrote it — see
[veripb-facts.md](veripb-facts.md). Subproof lines need no deleting at all;
their scope ends with the block.

What does stay has a cost worth naming: (A) and (B) sit at `Top` mentioning
every `l_i` and every interior `a_j`, so any later `red` whose witness touches
one of those variables acquires proofgoals over them. Nothing in the tree does
today — the flag-reifying `red`s all use fresh witnesses — but it is the thing
that would make this expensive from a distance.

### 3. Elimination is one `pol`

Adding two donors' (4.4a) rows gives shared literals coefficient 2, which is
even and so folds into the new `B`; literals appearing with opposite polarity
in the two rows cancel to a constant, which is exactly `¬p = p XOR 1`. Either
way the sum is the (4.4a) row of the XOR of the two donors. Same for (4.4b).
So a row of the reduced system is one `pol` over the donor rows it is a sum of,
and the propagator tracks that sum as a bitset over donors while it eliminates.

### 4. Reason and conflict clauses: §4.3, and it folds into the same `pol`

Given a derived row and an assignment `ρ` over its support, with
`F = {i : ρ(l_i) = 0}` and `T = {j : ρ(l_j) = 1}`:

```
  (4.4a) + { literal axiom l_i : i in F } + { literal axiom ~l_j : j in T }
      ->  sum_F 2 l_i >= 1 - |T| + 2B
  /2 then *2                             (gains 1, because |T| is even here)
      ->  sum_F 2 l_i >= 2 - |T| + 2B
  + (4.4b)
      ->  sum_F l_i + sum_T ~l_j >= 1
```

which is a clause falsified by `ρ`. For a propagation, run it with `ρ` extended
by the *wrong* value for the one unassigned literal: the clause then has that
literal as its only non-falsified term, so it propagates.

The fold is not optional. (A) and (B) on their own do **not** make the XOR's
clauses RUP: fixing the literals to the wrong parity leaves the pair feasible
at a half-integral point — `n = 2` with both literals 0 gives
`2(y_1 + y_2 - a_1) >= 1` and `<= 1`, slack either way, nothing propagates.
The rounding in the `/2` is what closes it, exactly as in the subproof above.

Everything above — summing donors for both directions, the literal axioms, the
divide, the multiply — is one RPN expression, so it is **one `pol` line plus
one RUP per inference**, whatever the size of the combination. `PolBuilder`
builds it (`add(line)`, `add_for_literal`, `divide_by`, `multiply_by`).

## The propagator

Vocabulary: an **atom** is a canonicalised literal, a **row** is a set of atoms
plus a right-hand-side bit.

**Canonicalisation.** Each donor literal is reduced to (atom, flip). `v != c` is
`¬(v == c)`, `v < c` is `¬(v >= c)`; flips move to the row's right-hand side.
Duplicate atoms within a row cancel (`x XOR x = 0`); this is the same
cancellation `parity_test.cc`'s duplicate-variable case already exercises.
Root-fixed literals and `TrueLiteral`/`FalseLiteral` fold into `b`. A row that
cancels to empty is a root contradiction (`b = 1`) or is dropped (`b = 0`).

Two atoms over the same variable that happen to be equivalent (`v != 0` and
`v == 3` where the domain is `{0, 3}`) are treated as independent. That only
loses strength, never soundness: the system is a relaxation in which every atom
is free, and that is exactly the relaxation the PB rows state, so the proof and
the propagator agree about what is being claimed. It is also what "GAC" means
here, and the honest statement of it: **GAC on the PB relaxation of the
system**. Where each variable contributes one atom — which is every model that
arrives through a frontend, since `ParityOdd(vars)` builds `v != 0` — that
coincides with GAC on the conjunction.

**Canonicalisation must go through the tracker**, not the surface syntax: the
`pol` cancellation in step 3 is a representation-consistency argument, and
`v != 0` and `v == 0` have to resolve to the same `XLiteral` up to negation for
it to hold. See [view-proof-logging.md](view-proof-logging.md).

**Propagation.** On each wake: substitute the current assignment into every
row, Gauss-Jordan the result, and read off

- an empty row with `b = 1` → contradiction;
- a unit row `{a}` with `b = c` → infer `a` or `¬a`;
- a two-atom row → an implied equivalence, which is real strength but has
  nowhere to live (issue #649) and is **out of scope**. Detecting implied
  literals alone is GAC; equivalences are the layer above it.

Reason for an inference: the assigned literals of the derived row's support
before substitution, which is precisely the `ρ` of §4.3.

**From scratch, to begin with.** Each call re-eliminates. `abstractXOR` reports
that sparse sets do not trail cleanly here, because XORing rows *creates*
non-zero cells, and undoing has to be explicit; maintaining the RREF
incrementally under backtracking is the interesting engineering and it is not
where this should start. `DifferenceConstraints` took the same route — one
from-scratch pass first, an `incrementally()` option added afterwards, with the
audit mode that requires the two to agree. Bitset rows make from-scratch
`O(rows * atoms / 64)` per call, which is enough to find out whether any of this
pays.

**Components.** The posted XORs usually split into connected components, and
eliminating over the whole model when the rows do not interact is pure waste.
The presolver partitions by shared atom and installs one propagator per
component with at least two rows. A single-row component is left to its own
`ParityOdd`, which computes exactly the same thing more cheaply.

## The presolver

`ParitySystemGathering`, in `gcs/presolvers/parity_system_gathering/`, built to
the `DifferenceLogic` pattern: a shared `ComponentStats` block registered
unconditionally at the top of `run()`, donor discovery through
`Problem::each_constraint_of_type_with_proof_data` so the rows it cites are
named by the donor's published role rather than by a label it built itself, and
one bucket per reason a candidate was passed over — because a presolver that
silently gathered nothing passes every solution-equivalence, OPB byte-diff and
VeriPB check there is, and the counts are the only thing that tells "working"
from "no-op".

Donors come from two families.

**`ParityOdd`.** The main one; everything a frontend produces lands here
(`array_bool_xor` and `bool_xor` via `minizinc/fzn_glasgow.cc`, XCSP3, CPMpy,
`.scp`). Its slack row is derived as in §2 above, and that derivation is where
essentially all of this presolver's `Top` output goes.

**Boolean `Equals` / `NotEquals`**, when both operands' declared domains are
within `{0, 1}` — checkable from the `State` the presolver is handed. `x = y`
is the 2-XOR `[x != 0] XOR [y != 0] = 0`; `x != y` is the same with
right-hand side 1. This is where a MiniZinc model's `bool_eq` and `bool_not`
rows come from, and they are worth having because they are the edges that
connect otherwise separate XOR components.

Both are `ReifiedEquals` — `Equals` is `reif::MustHold`, `NotEquals` is
`reif::MustNotHold` — and `clone()` returns the base, so the enumeration asks
for `ReifiedEquals` and dispatches on `reification_condition()`, exactly as
`DifferenceLogic` does over `ReifiedLinearInequality`. `ReifiedEquals`
currently publishes neither its operands nor a `ConstraintProofModelData`, so
both get added, and the published data has to name **two** rows rather than one
primary (`Cumulative` is the precedent for a specialisation with more than one
named role).

These are also *much* cheaper to lift than a `ParityOdd`, which is the part
worth writing down: with only two literals, `B` needs no fresh variable, so
neither donor needs a `red` at all.

- `Equals` emits `v1 - v2 == 0` as the labelled pair
  `ge` / `le`. Writing `a` for `[x != 0]` and `b` for `[y != 0]`, those rows
  *are* (4.4a) and (4.4b) with right-hand side 0 and `B = b`: `a + b >= 0 + 2b`
  is `a - b >= 0`, and `a + b <= 0 + 2b` is `a - b <= 0`. Nothing to derive —
  the donor's own two rows are the slack form, cited directly.
- `NotEquals` emits big-M `gt` / `lt` rows half-reified on a per-constraint
  selector flag `b[id][ne]` (cake's `nev`), the flag true selecting `gt`. Here
  `B = 0`, so the slack form is just `a + b >= 1` and `a + b <= 1`, and both
  are plain **RUP** against those two rows: negating `a + b >= 1` assigns
  `a = b = 0`, which unit-propagates the selector through the `lt` row and then
  falsifies `gt`; negating `a + b <= 1` assigns `a = b = 1`
  and falsifies the other way round. Two RUP lines at `Top`, no witness, no
  subproof.

The one thing to check rather than assume: for a `{0, 1}` variable, the literal
`[x != 0]` and the variable's own OPB bit have to resolve to the same
`XLiteral`, or the `pol` cancellation in §3 does not happen. Go through
`NamesAndIDsTracker::need_pol_item_defining_literal`, never the surface form.

Everything else is skipped and counted: a non-`MustHold` reification kind, an
operand whose domain is not within `{0, 1}`, a donor whose row cannot be cited
(only ever possible with proofs on), a row that cancels to nothing.

## The constraint

`ParitySystem`, in `gcs/constraints/parity/`, alongside `ParityOdd`. It takes a
`vector<Literals>` — **every row is odd parity**, matching `ParityOdd`'s
spelling, so an even row is written with one literal negated. That is what the
GF(2) canonicalisation does internally anyway, and it keeps one convention
across the two constraints rather than two.

Its OPB encoding is `ParityOdd`'s, once per row: `prepare()` installs one child
`ParityOdd` per row (the `path.cc` / `tree.cc` pattern), which gives the rows
their accumulator chains, and `install_propagators` adds the system propagator
on top. The point is that **there is then one proof path, not two**: the posted
constraint and the presolver both derive their slack rows from accumulator
chains, so `define_proof_model`, the derivation, and the justifications are the
same code, exercised by both entry points.

`s_expr()` throws: the `.scp` grammar has `parity` for one row and nothing for a
system, and `write_scp` renders the whole file before opening it, so a throw
leaves no `.scp` behind. The SCP chain lane does not cover `ParitySystem`. It
does still cover the presolver's donors, which are ordinary `ParityOdd`s — and
that is the configuration that matters, because it is the one a real model
reaches.

## What this touches in existing code

- `ParityOdd` gains an accessor for its literals, and a
  `ConstraintProofModelData<ParityOdd>` specialisation in `parity.hh`
  publishing what the derivation cites: the four per-step clause roles, the
  `0ge` / `0le` / `acc` roles, and the accumulator `ProofFlagKey`s (values
  `{k}`, no annotation). Publishing is the point — the alternative is the
  presolver hard-coding another constraint's naming scheme, which is what
  `ConstraintProofModelData` exists to stop.
- `ReifiedEquals` gains operand accessors and its own specialisation, naming
  both rows of each reification kind it supports.
- `gcs/constraints/parity.hh` (the umbrella) picks up `parity_system.hh`, and
  `gcs/gcs.hh` picks up nothing new, since it already includes
  `constraints/parity.hh` — but the new header must reach it in the same commit
  as the constraint, not as a follow-up.
- `gcs/constraint_enumeration_test.cc` gets `ParityOdd` and `ReifiedEquals`
  cases: the enumeration is a `dynamic_cast` on what `clone()` returns, so it
  finds nothing at all if `clone()` ever starts returning a type outside the
  family, and that is a silent failure everywhere else.
- `dev_docs/README.md` gets an entry for this document, and
  `dev_docs/frontend-support-matrix.md` a row — neither the constraint nor the
  presolver is reachable from any frontend at first, and the matrix is the
  single source of truth for that.

## Staging

`constraints.md`, "Bringing up a new constraint", numbered as it numbers them —
the gates are what make each stage's failure diagnosable. All five are done for
the constraint; the presolver has not been started.

1. **The encoding, with a check-only propagator.** *Gate: the whole suite
   verifies* — which says the encoding is definitionally correct and that RUP
   alone certifies every consequence of a complete assignment. Passed.
2. **State the consistency level in the tests.** Switched to
   `solve_for_tests_checking_gac` before any pruning existed, so the tests
   failed for the reason about to be fixed. They did, with "consistency not
   achieved", and they still do if `ParitySystemPropagation::CheckOnly` is
   selected — which is what keeps that mode honest as the encoding's standing
   regression test.
3. **Gauss-Jordan, with every inference cheated.** *Gate: the stage 2 tests
   pass and VeriPB still accepts.* Passed, at 23 runs `s UNDER ASSERTIONS` and
   2 `s VERIFIED` (the two with no system inference to make).
4. **Discharge the cheats.** The slack-row derivation at `Top` first, then
   §4.3's fold. Both landed together rather than one inference kind at a time,
   which was a small mistake: the two failures that followed — the subproof's
   line references, and the empty row — each had to be separated out by reading
   the `.pbp`, and a stricter order would have pointed at them.
5. **Zero assertions.** 25 of 25 `s VERIFIED`, no assertion warning, and
   `grep -c '^a '` is zero on a preserved `.pbp`.

GAC here means *GAC on the PB relaxation of the system* — see "The propagator"
— which coincides with GAC on the conjunction for every model that reaches this
through a frontend.

### What mutation testing says

Seven mutations, five rejected by VeriPB and two not. The two are worth
recording, because neither is a defect:

| Mutation | Verdict |
|---|---|
| Drop the `/2` then `*2` in the §4.3 fold | rejected |
| Flip which polarity of each support atom is pushed as an axiom | rejected |
| Use two of the three step clauses in the `red` subproof | rejected |
| Close the `<=` telescoping with `~a_n` rather than `a_n` | rejected |
| Infer the opposite literal from a unit row | rejected (wrong solutions) |
| Telescope the `>=` direction with `a_0 >= 1` rather than `a_0 <= 1` | **accepted** |
| Telescope the `>=` direction without the `a_n <= 0` pin | **accepted** |

Both survivors only *weaken* the derived row, by a term the `.opb` pins anyway
(`a_0 = 1`, `a_n = 0`), so the row stays valid and the wrapping RUP still
closes by propagating that pin. This is
[veripb-facts.md](veripb-facts.md)'s "a `pol` only has to get close": the `pol`
is not the certificate, the RUP around it is, and a mutation that removes
slack is a corruption VeriPB is right to accept. What bites is corrupting the
*claim* — which is what the five rejections all do.

**The presolver comes after all five**, not alongside them. It has its own gate:
the counts in its stats block, which is the only thing that distinguishes
"gathered the system" from "silently gathered nothing" — the lesson
`DifferenceLogicStats` is written around — plus the node-for-node tripwire that
with donors *not* retired the search tree must be identical, since the system
propagator subsumes every donor's single-XOR unit propagation.

## What would exercise it

- MiniZinc Challenge 2012 `parity-learning`, the family CP-SAT's TODO names.
  It is the *optimisation* variant, so Gauss-Jordan alone will not crack it —
  the noise is the hard part — but it is the obvious first benchmark.
- MiniZinc Challenge 2016 `cryptanalysis` (Gérault, Minier and Solnon's AES
  related-key step 1). The 2017/2018/2021 `opt-cryptanalysis` model has no XOR
  system in it, so the honest challenge count is two families, both old.
- Hashing-based model counting; LDPC decoding as XOR-SAT.

Measure against [proof-benchmarks.md](proof-benchmarks.md) as well as
[benchmarking.md](benchmarking.md): the `Top` footprint and the per-inference
line count are the numbers this design is making claims about.

## Decisions taken

1. **`ParitySystem` installs child `ParityOdd`s** rather than writing a slack
   form into its own OPB. Writing the slack form directly would make
   elimination free and is much less code, but it would leave two proof paths
   to keep in step and a `ParitySystem` whose proofs are checked against
   nothing but our own OPB. One derivation, exercised by both entry points, is
   worth the extra work.
2. **Rows are all odd**, as above.
3. **Both donor families**: `ParityOdd`, and Boolean `Equals` / `NotEquals`.
4. **Donors are retired by default.** The issue says "replaces", and the system
   propagator subsumes every donor's single-XOR unit propagation, so a donor
   that has been lifted is pure overhead. The hybrid stays available behind an
   option because it is the stage-5 tripwire: with donors kept, the search tree
   must come out node-for-node identical, and it differing means the
   subsumption claim is wrong.

## Residue

- Implied equivalences (`x = y`, `x = ~y`) are the real payoff over unit
  propagation and have nowhere to live; issue #649 scopes an equivalence store.
  Out of scope here, and detecting implied literals alone is already GAC.
- Incremental RREF maintenance under backtracking; see "From scratch, to begin
  with".
- Deleting the per-step scaffolding. The `red`s and their subproof lines are
  only needed until the two telescoping `pol`s have run, and everything above
  says to delete them afterwards — but that is not implemented yet, so the
  current `Top` footprint is the full `7n` lines per row rather than two. Do
  this before pointing it at anything large: every line left at `Top` taxes
  every later unhinted RUP (#666).
- Caching derived rows. Each inference re-emits its `pol` over donor rows even
  when the same combination recurs, which it will. Emitting the root RREF once
  at `Top` and citing those rows instead is the obvious next move, and it is a
  measurement, not a guess: it trades `Top` footprint (which taxes every later
  unhinted RUP) against per-inference line count.
