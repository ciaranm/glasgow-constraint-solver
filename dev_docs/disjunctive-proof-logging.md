# Proof logging for `Disjunctive`

This document explains how the `Disjunctive` propagator's proofs are
backed by VeriPB, focusing on the *bridge* pattern that lets us keep a
declarative OPB encoding while still using time-table reasoning in the
propagator. Read [`cumulative-proof-logging.md`](cumulative-proof-logging.md)
first — `Disjunctive`'s time-table machinery (mandatory profile,
contradiction proof, chain-step bound pushes) is a specialisation of
cumulative's at `h_i = 1`, `capacity = 1`, and most of the difficult
ideas are documented there. This document covers what's new: the
bridge between encoding and propagation, and the third reusable
proof-logging idea that comes out of it.

For the constraint itself — semantics, propagator, the strict / non-strict
flag — read `gcs/constraints/disjunctive.{hh,cc}`.

## The declarative OPB encoding

`define_proof_model` emits exactly one shape: for every unordered pair
of participating tasks `(i, j)`,

```
before_{i,j}  <->  s_i + l_i <= s_j     (i finishes at-or-before j starts)
before_{j,i}  <->  s_j + l_j <= s_i
before_{i,j}  v   before_{j,i}          (one of them must finish first)
```

That's the whole OPB contribution. It directly mirrors the constraint's
spec: "for every pair, one task finishes before the other starts". A
human reading the OPB recognises the disjunctive constraint without
knowing how Glasgow's propagator works.

Notably absent: any time-indexed `before_{i,t}` / `after_{i,t}` /
`active_{i,t}` flags. Cumulative emits those into the OPB; for
disjunctive they belong to the propagator, not the model definition,
and we keep that separation.

## The bridge

The TT propagator wants to reason "task `i` is active at time `t`",
which means using `before_{i,t}` / `after_{i,t}` / `active_{i,t}` flags
identical in shape to cumulative's. The OPB doesn't define them, so we
introduce them in the proof instead — as one-shot scaffolding emitted
by an `install_initialiser` that runs once before search:

```cpp
propagators.install_initialiser(
    [/* captures */](State &, auto &, ProofLogger * const logger) -> void {
        if (! logger) return;
        for (auto i : active_tasks)
            for (Integer t = per_task_t_lo[i]; t <= per_task_t_hi[i]; ++t) {
                auto [B, B_fwd, B_rev] = logger->create_proof_flag_reifying(
                    WPBSum{} + 1_i * starts[i] <= t, "djbef", ProofLevel::Top);
                auto [F, F_fwd, F_rev] = logger->create_proof_flag_reifying(
                    WPBSum{} + 1_i * starts[i] >= t - lengths[i] + 1_i,
                    "djaft", ProofLevel::Top);
                auto [A, A_fwd, A_rev] = logger->create_proof_flag_reifying(
                    WPBSum{} + 1_i * B + 1_i * F >= 2_i, "djact", ProofLevel::Top);
                bridge->emplace({i, t}, BridgeFlags{B, B_fwd, B_rev, F, F_fwd, F_rev, A, A_fwd, A_rev});
            }
    });
```

A few things to note about this:

- **Why an initialiser, not `define_proof_model`?** Putting the
  bridge in `define_proof_model` would put it in the OPB — defeating
  the declarative-encoding split. The initialiser writes to the `.pbp`
  prefix instead, which is *proof* not *model*.
- **Why `ProofLevel::Top`?** Glasgow has no flag-deletion API: every
  call to `create_proof_flag` records a name in
  `NamesAndIDsTracker` that lives forever. If the bridge created
  flags lazily during justification, the per-flag footprint would
  grow with the search-tree depth (potentially exponential).
  Creating them once at root, at `Top`, bounds the total to
  `O(n × horizon)` per `Disjunctive` instance.
- **Sharing with the propagator.** The propagator captures a copy of
  the same `shared_ptr<BridgeMap>` and looks up flag handles by
  `(task_idx, t)` from inside its justification callbacks. The
  initialiser writes; the propagator reads.

## Recovering the at-most-one lemma

Time-table reasoning at `h = 1`, `c = 1` needs the analogue of
cumulative's `C_t` constraint — the per-time-point sum
`Σ_i active_{i,t} ≤ 1`. Cumulative has this as an axiomatic OPB
constraint; we don't, so we derive it.

For the cases the propagator actually uses (mandatory-overflow
contradiction with two contributing tasks; a chain step with one
blocker and the pushed task), the **pairwise at-most-one**
`active_{i,t} + active_{j,t} ≤ 1` is enough — we never need the global
sum over all tasks possibly active at `t`. The
[`recover_am1`](../gcs/constraints/innards/recover_am1.hh) helper,
applied to two atoms, becomes a thin wrapper around a single
`pair_ne` callback, and that callback emits a three-step `pol` from
the encoded pairwise clause and the bridge flag forward reifs:

```
L1 = pol (E_{i,j}_fwd) (after_{i,t}_fwd) + (before_{j,t}_fwd) + s
     -> ¬E_{i,j} + ¬after_{i,t} + ¬before_{j,t} >= 1
L2 = pol (E_{j,i}_fwd) (after_{j,t}_fwd) + (before_{i,t}_fwd) + s
     -> ¬E_{j,i} + ¬after_{j,t} + ¬before_{i,t} >= 1
AM1 = pol L1 L2 + (clause) + (active_{i,t}_fwd) + (active_{j,t}_fwd) + s
      -> ¬active_{i,t} + ¬active_{j,t} >= 1
```

The arithmetic that makes this go through: in `L1` the integer
variables cancel exactly — `(s_j - s_i)` from the encoded forward reif
plus `(s_i)` from after's forward plus `(-s_j)` from before's forward
sums to zero, leaving `M · (¬E_{i,j} + ¬after_{i,t} + ¬before_{j,t}) ≥ 1`
which saturates to a flag-only constraint. `L2` is symmetric.
Combining `L1 + L2` with the clause picks one side of the encoded
disjunction; the active flag's forward reif then folds before/after
contributions into the active flag.

The result line is recorded at `Top`, and the per-call pol expression
(L1, L2, the AM1 itself, and the closing combination with the two
active=1-under-reason lines) is at `Temporary`.

`recover_am1` had to be taught how to isolate its inner workings from
a `JustifyExplicitlyThenRUP` context to avoid wiping the framework's
own scope on exit — see the comment in `recover_am1.cc`.

## The three time-table inferences

With the bridge in place, the time-table inferences specialise
cumulative's exactly, with `h_i = 1` and `capacity = 1`:

- **Mandatory-overflow contradiction.** Two tasks with mandatory
  parts covering the same `t` collide. Pin both their `active_{·,t}`
  lines under reason (via before / after / active chain), derive the
  pairwise at-most-one via the helper above, pol with the active=1
  lines, contradiction. See `cumulative-proof-logging.md`'s
  inference 1 for the same shape with general heights.

- **`lb`-push and `ub`-push.** The chain-step machinery from
  cumulative applies verbatim with the bridge supplying the
  per-step at-most-one. The shared `emit_chain_step` helper takes the
  push direction's `ext_lit` and `emit_intermediate` parameters; the
  per-step proof emits the at-most-one via `recover_am1`, pols it
  with the two active=1 lines (one under reason, the other under
  extended reason `{reason ∪ ¬ext_lit}`), and saturates to derive
  `ext_lit + ¬reason ≥ 1`. Intermediate steps deposit `ext_lit`
  explicitly as a unit fact for the next step's preconditions to UP.

## Strict-mode zero-length tasks

Strict mode forbids a zero-length task from sitting strictly inside
another task's open active interval. The TT machinery doesn't help
here because zero-length tasks have empty mandatory parts and never
enter the profile. A separate all-fixed pairwise check covers them,
and the proof is straightforward: at the all-fixed leaf, the
declarative pairwise encoding alone is RUP-closable. With `s_z` and
`s_k` fixed at `vz`, `vk` satisfying `vk < vz < vk + l_k`,
`before_{z,k}` and `before_{k,z}` both UP to 0 from the unit
assignments and the encoded clause `before_{z,k} + before_{k,z} ≥ 1`
unit-fails. So this contradiction uses plain `JustifyUsingRUP{}`.

## The third reusable idea

[`cumulative-proof-logging.md`](cumulative-proof-logging.md) ends with
two reusable patterns:

1. `pol` over `active = 1` reified flags.
2. Extended-reason pinning for hypothetical literals.

The disjunctive scaffolding adds a third:

3. **Declarative OPB encoding with a propagator-introduced bridge.**
   When a constraint has a clean declarative encoding but the
   propagator wants a different vocabulary (typically time-indexed
   reifications) for its reasoning, don't pollute the OPB with the
   propagator's vocabulary. Instead, emit the propagator's flags as
   *proof scaffolding* via `install_initialiser`, at `ProofLevel::Top`
   so they survive the entire search without leaking into
   `NamesAndIDsTracker` per node. Share them with the propagator via
   a `shared_ptr<BridgeMap>` captured by both the initialiser and the
   propagator. The propagator's justifications then derive any
   propagator-specific lemmas on demand (here: per-pair at-most-one
   via `recover_am1`).

   This pattern lets the same OPB serve as the spec-faithful
   constraint definition and the proof's axiomatic foundation, while
   still allowing the propagator to do non-spec-shaped reasoning. The
   declarative encoding is what a human (referee, future-us) reads to
   verify the constraint; the bridge is what the propagator pols
   against to back its inferences.

   Expected to apply to: `BinPacking` (#148) when its propagator
   wants per-bin / per-item flags but its declarative encoding is the
   per-bin capacity sum; future `Disjunctive2D` with per-axis bridge
   flags; possibly future stronger `Cumulative` propagators whose
   reasoning vocabulary outgrows the time-table flags currently in
   the OPB.

## Open follow-ups

- **Variable lengths.** The OPB encoding generalises directly
  (`s_i + l_i ≤ s_j` is still pseudo-Boolean over the bit
  decompositions), but the bridge derivation per `(task, t)` would
  need to account for `l_i` being a variable rather than a constant.
- **2D / k-D `Disjunctive2D`.** The OPB encoding would still be
  pairwise, but per-pair per-dimension: `Σ_d before_{i,j,d} +
  before_{j,i,d} ≥ 1`. The bridge would presumably introduce per-axis
  `active_{i,t,d}` flags.
- **Optional tasks (`*_opt`).** A presence flag per task gates the
  encoded pairwise clauses; the bridge gets a per-(task, t) flag
  that's only meaningful when the task is present.

<!-- vim: set tw=72 spell spelllang=en : -->
