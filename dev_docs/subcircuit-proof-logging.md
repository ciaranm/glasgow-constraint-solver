# SubCircuit: encoding and proofs

The design note for `SubCircuit` (issue #788), the propagator behind MiniZinc's
`subcircuit` and XCSP3-core's `<circuit>`.

The short version: the encoding is a position labelling, which is the *expensive*
shape by [`connectivity-proofs.md`](connectivity-proofs.md)'s argument — and here
it is the right one anyway, because a subcircuit's propagators have to *count*
the tour as well as walk it, and only an arithmetic labelling lets a proof do
that in a bounded number of steps. The price is that every reachability inference
has to perform an induction the checker will not do for itself: `n` layers of
lemmas, each a plain RUP, chained by hand.

## What the constraint says

`subcircuit(succ)` holds when `succ` is a permutation and the nodes that do not
point at themselves form *at most one* cycle. Three corners are worth stating
outright, because each of them costs something later:

* the **empty** subcircuit, every node pointing at itself, is a solution;
* the smallest non-empty tour has **two** nodes — a node pointing at itself is by
  definition off the tour, so there is no one-node cycle either to allow or to
  forbid;
* the successors are a permutation *whether or not* a node is on the tour, so
  all-different holds over the whole array. A node off the tour takes its own
  index, which is exactly what stops it being anyone else's successor.

## Why it is not a mode on `Circuit`

`Circuit::install_propagators` opens by inferring `succ[i] != i` for every `i`,
which is precisely what subcircuit must allow, so `SubCircuit` is a sibling class
in the same directory rather than an option on that one. Neither is a special case
of the other: `Circuit` additionally requires every node to be on the tour.

XCSP3-core's `<circuit>` allows isolated vertices and asks for exactly one
circuit, so it binds to `SubCircuit` with a tour size of at least 2 — see
[`xcsp.md`](xcsp.md). `Circuit` is reachable from MiniZinc, C++ and `.scp` only.

## The encoding

`define_proof_model` writes the all-different clique, then a position variable per
node and two facts about every edge. Positions are proof-only, bit-represented,
and range over `0..n-1`.

The tour length is written as

```
    L  =  Σ_i [succ[i] ≠ i]
```

a **sum of literals**, not an auxiliary variable. That is what keeps the whole
encoding linear: the wrap-around row below multiplies nothing by `L`, it adds it.

```
    pos[anchor]                     =  0            (anchored)
    first[i]                        →  pos[i] = 0   (unanchored)
    succ[i] = i                     →  pos[i] = 0
    succ[i] = j  (j not the wrap)   →  pos[j] - pos[i]     = 1
    succ[i] = j  (j is the wrap)    →  pos[j] - pos[i] + L = 1
```

### Off-tour nodes sit at position zero

Not "after every on-tour one, in index order", which is what the stdlib
decomposition does and what makes *its* positions a permutation. Nothing here
needs them distinct: an off-tour node takes part in no position row at all, since
it has no successor other than itself and by all-different nothing else can point
at it either. All these rows have to do is leave `pos` determined by the
successors under unit propagation, which is what solution checking needs, and zero
does that as well as anything.

It saves only `n` rows of `n+1` terms, about 2% of the bytes, and that is not why
it is worth doing. Two much larger consequences:

* **`pos[x] ≥ 1` already means "on the tour"**, so no reachability argument has to
  count how long the tour is. This is load-bearing for the SCC certificates.
* It moved the mutation-catching property from a hand-built scenario into the
  plain enumeration test. With the old numbering, replacing the whole
  check-and-prevent certificate with a plain `JustifyUsingRUP` passed the *entire*
  enumeration at every `n` and every view wrapping, because by the time a chain
  closes there enough is fixed that unit propagation determines the `first` flags
  itself. Now it fails at `n = 5`.

### Anchored and unanchored

Which edge of the tour wraps around is the whole difference between the two
shapes this encoding comes in.

**Unanchored**, it is not known statically. The wrap edge is the one into whichever
node is `first[j]` — "node `j` is on the tour and every lower-numbered node is off
it", a flag `create_proof_flag_fully_reifying` over that conjunction — and that is
only pinned down once the membership literals are. So *both* cases have to be
written for every edge, four rows per edge rather than two, and every certificate
splits over the candidates.

**Anchored** on a node already known to be on the tour, only the edges into that
node can wrap. That is exactly the shape `Circuit` gets for free by anchoring on
node 0: one row family per edge, no `first` flags, and one polish-notation step
per certificate rather than one per node of the cycle.

Measured on `2013/mario` truncated to 12 houses, the same model through the same
harness, the two builds differing only in whether an anchor is found:

| | position rows | `.opb` rows | `.opb` bytes |
|---|---|---|---|
| unanchored | 528 (264 step + 264 wrap) | 2282 | 527,583 |
| anchored | 264 (242 step + 22 wrap) | 1983 | **378,458** |

The position rows halve exactly. Counting row *families* rather than rows: the
step edges are the ones **not** into the anchor, `(n-1)² = 121` of them, and the
wrap edges are the `n-1 = 11` into it, so anchored is `(n-1)² + (n-1) = n(n-1)`
families against the unanchored `2n(n-1)` — half, for every `n`. Each family is a
`<=` row and a `>=` row, which is where the table's doubled figures come from.

Bytes fall further than rows because the wrap rows are the long ones — each carries
`L`, so each is `n` terms longer than a step row, and the anchored encoding keeps
`n-1` of them where the unanchored one keeps `n(n-1)`.

On the real 15-house instance the `.opb` goes 873,418 → **594,193** bytes, −32.0%.
What that does *not* buy is verification time: the `.pbp` falls only 3.7%
(193.6 MB → 186.5 MB) and checking it takes 174 s either way. The saving is in
what has to be written down and read in, not in what the checker has to do.

### Where the anchor comes from

`prepare()` looks for one: a node is on the tour exactly when it does not point at
itself, so any node whose own index is already out of its successor's *declared*
domain is one, and that is all an anchor has to be. The lowest-numbered such node
is used. `with_required_node()` overrides the choice and turns "no node is
declared on the tour" into an error rather than something quietly accepted;
neither is a way to *declare* a node on the tour, and nothing about the anchor
reaches the `.scp`, because it is read off domains the `.scp` already records.

Only the **declared** domains are visible there, so what reaches them is what
matters — and both challenge families that use `subcircuit` do pin a node, in
different ways:

* **mario** writes `constraint succ[LuigiHouse] = MarioHouse;`, which the
  flattener folds into the successor array as a **constant**. The anchor is there
  to be found, whatever the source order.
* **tpp** writes `constraint succ[numcities] != numcities;`, which survives as an
  `int_ne` over a variable whose declared domain the flattener does narrow.

Neither depends on source order, which is the first thing to suspect and the
wrong thing: the pin in both models is written *after* the `subcircuit` call, and
it makes no difference. What matters is whether the pin reaches the array **the
constraint actually sees**, and `fzn_subcircuit.mzn` used to break that for tpp.
It shifted the successors to be zero-based with a comprehension,
`[x[i] - min(index_set(x)) | i in index_set(x)]`, which introduces a fresh
FlatZinc variable per node, declared over the full range before its defining
constraint has propagated — so every narrowing the model had made was invisible.

The redefinitions now pass the **offset**, and `fzn_glasgow.cc` applies it as a
view: the domain survives, and `n` fewer variables and `n` fewer `int_lin_eq`
constraints get written. On `2016/tpp_4_5_20_1` the FlatZinc goes 31,534 → 26,417
bytes and the `.opb` 2,411,111 → 1,936,718, with the position rows halving
(1520 → 760) and the twenty `first_pos` rows gone. `Circuit` takes the same
treatment: no anchor to lose, since it always anchors on node 0, but the same
variables not to write.

### Why the unanchored encoding keeps its wrap rows

Dropping the wrap family leaves an encoding *smaller than the stdlib
decomposition's* that is still exact — a cycle avoiding the anchor still chains to
`0 = k`. It is not a free reformulation, though, because the wrap rows are what
let a propagator that has found a closed cycle **count**: chaining them gives "the
tour is no longer than this cycle" in a bounded number of steps. Without them that
counting fact has to be derived instead, and deriving it needs "the on-tour
positions are exactly `0..L-1`" — a pigeonhole induction *conditional on the
variable `L`*. Naming an anchor is the way to the small encoding; deleting rows is
not.

## The propagators, and their certificates

Francis and Stuckey's three algorithms, selected with `with_algorithm()`.

### `check` — a closed cycle is the whole tour

Follow each chain of fixed successors; when one closes into a cycle of two or more
nodes, force every node outside it to be a self loop. For `Circuit` a short cycle
is a flat contradiction; here it only pins down everyone else.

The one subtlety is what "outside it" may skip. Only a node *already sitting on its
own index* can be skipped: one fixed to anything else has to go through `infer()`
so that the contradiction is raised and justified. That is the whole of what makes
`check` complete — F&S report failure exactly when a node outside the cycle cannot
be a self cycle, and a node fixed elsewhere cannot. Skipping those silently
accepted two disjoint 2-cycles at `n = 4`.

The certificate, `derive_tour_at_most`, sums the step rows round the cycle to get
`L ≤ |cycle|`. Unanchored that is a `|cycle|+1`-way case split, because the wrap
edge is not known: sum the step rows for "none of these is first", sum again per
candidate for "this one is", then add the first row to the rest to resolve the
flags away.

Anchored it is one `pol`, in one of two shapes, and which one is the propagation
difference as much as the proof difference:

* the cycle **contains** the anchor, so the edge into the anchor is the wrap and
  chaining the rest bounds the tour — the same conclusion as above;
* the cycle **misses** the anchor, so every one of its edges steps and chaining
  them telescopes to `0 ≥ k`. The cycle cannot exist at all. No evidence node has
  to be found, because the anchor is itself a node outside the cycle that has to
  be on the tour.

### `prevent` — the evidence node

A chain of fixed edges must not *close* into a cycle while some node outside it
cannot be a self loop, because that node would have nowhere to go. That node is
F&S's **evidence node**, and unlike `Circuit`, nothing can be inferred without
one: the chain closing and everyone else opting out is a perfectly good solution.
`prevent` is incomplete on its own, so it always runs with `check`. This is the
default.

An anchor is a guaranteed evidence node whenever it lies outside the chain, which
is why anchoring strengthens propagation as well as shrinking the encoding.

### `scc` — the tour lies in the anchor's component

The tour is a cycle *through* the anchor, so every node on it is reachable from
the anchor **and** reaches the anchor back. Anything failing either has to opt out.
Two separate walks, two separate arguments, either able to fire alone; together
they are F&S's rule for a strongly connected sub-component containing a required
node, specialised to the one component that is always guaranteed to have one.

It does nothing at all without an anchor, which is F&S's own observation about
applying this family to `subcircuit`: there is nothing to be reachable *from*
until some node is known to be on the tour.

Self loops are not followed in either walk. A node pointing at itself is off the
tour, so that is not a tour edge to travel along — the same care F&S call for.

#### The induction the checker will not do

[`connectivity-proofs.md`](connectivity-proofs.md) explains why an arithmetic
distance labelling makes unreachability un-RUPable: the argument is an infinite
descent, unit propagation does not do induction, and it would have to case-split
over which node is the parent. That is exactly this encoding, and exactly this
problem. `Reachable` escaped it by writing a breadth-first unfolding instead;
`SubCircuit` cannot, because it needs the labelling for `derive_tour_at_most`'s
counting. So the induction is performed explicitly, and the case split written out.

Forward, the fact derived at each layer `t` for each node `x` the anchor has not
reached within `t` steps is

```
    E(t, x):   pos[x] = t  →  succ[x] = x
```

"`x` sitting at position `t` has to be off the tour". Somebody is `x`'s
predecessor, and for each candidate `q`, either `q = x`, which is the conclusion,
or the step row puts `q` at `t-1`. A `q` the anchor *had* reached within `t-1`
steps cannot point at `x`, or `x` would have been reached within `t` — that is in
the reason. A `q` it had not reached carries `E(t-1, q)`, so `q` at `t-1` is off
the tour and cannot point at `x` either. At `t = 0` the step row asks for position
`-1`, which the position variable's own lower bound refuses, so the first layer
stands alone. `E(t, x)` is emitted at `ProofLevel::Current` so the next layer has
it; that is how the layers chain.

Backward is the same shape and the same length of induction with `t` running from
`n-1` **down** to `0`, because there it is what `x`'s *successor* does that settles
`x`. Each candidate `y` that also cannot reach the anchor is put at `t+1` by the
step row, `G(t+1, y)` makes it a self loop, and value `y` is then taken twice.

#### What is load-bearing, and what only looked it

"Somebody is `x`'s predecessor" is **not in the encoding**. The all-different rows
are a pairwise clique, which says at most one variable takes a value and nothing
about at least one, so it is derived by pigeonhole — every variable takes a value,
every *other* value is taken at most once — at `ProofLevel::Top`, cached, exactly
as `justify_all_different_hall_set_or_violator` does it.

**That pigeonhole is the only cutting-planes step in either certificate**, and the
first version of the forward walk got that wrong in the cautious direction. It
wrote a `pol` per candidate to carry "`x` is at `t`" through the step row to "its
predecessor is at `t-1`", on the belief that unit propagation could not. It can:
the step row is written as two half-reified halves, and with the guard true and
`pos[x]` fixed, one bounds the neighbour's position from above and the other from
below, pinning every bit between them. Which half does which flips with the
direction of the walk, since the row is always written over `pos[j] - pos[i]` for
the edge `i -> j`: chasing a *predecessor* it is the `≥` half that bounds from
above, and chasing a *successor* it is the `≤` half. Both pols — the per-candidate
one and the one combining the candidates with the pigeonhole — were probed by
deletion, and every test still verifies with neither, for a 6.3% smaller `.pbp`.

Nothing has to cite a step row either, since those are model rows, and that works
only because the encoding is anchored: unanchored, each half also carries a
`first` flag guard that nothing in this argument would have fixed.

The backward walk needs no derivation of its own at all. Following `x`'s own
successor asks only that `succ[x]` take *some* value, which is the variable's own
at-least-one row; every other fact it uses is a model row too. So where both
directions fire, that half is very nearly free.

What *is* load-bearing was checked the same way, by mutation: a plain
`JustifyUsingRUP` in place of either walk is rejected, and dropping the pigeonhole
is rejected.

## What the rules are worth

Honestly: `check` and `prevent` are the whole of the value so far. Everything in
this section compares the constraint against MiniZinc's own `fzn_subcircuit`
decomposition, in gcs, on the same models — the five `subcircuit` families of the
challenge corpus (`2012/tpp`, `2016/tpp`, `2013/mario`, `2014/mario`,
`2017/mario`), 27 instances, at a 60 s cap.

* **Certification is the decisive win.** Real `mario_easy_2`, 15 houses
  unmodified: 10,021 nodes, a 594 KB `.opb` and a 186 MB `.pbp`, verified in
  176 s. The decomposition needs 1.51M nodes there; at 12 cut-down houses it
  already took 1,133 s to check 537 MB, so 15 was never attempted. The cut-down
  curve, verifying decomposition against native: 45.0 s → 0.5 s at `k = 10`,
  1,133 s → 13.1 s at `k = 12`.
* **Coverage, not speed.** Seven mario instances return *only the empty
  subcircuit* with the decomposition and none do with the constraint; all three
  `t_hard` and all four 2017 `medium` go from objective 0 to real solutions.
* **`tpp` is flat**: identical node counts on every uncapped instance, about 7%
  faster per node, which is enough to flip one instance inside the cap.
* **Two regressions on the `n_medium` family** at the time of that sweep:
  `2013/n_medium_4` and `2014/n_medium_3` both lost a proved optimum. Both are
  **recovered and beaten** now — 832 in 18.6 s against the decomposition's 57.8 s,
  and 943 in 6.3 s against its 30.8 s — and the cause was not what it looked like.
  See "Where the pruning was going" below; that section is the one to read before
  trusting any other number in this list, since it moved several of them.
* **Reachability is worth two search nodes out of 558** on the test built to show
  it working at all. Check-and-prevent with an evidence node gets to nearly the
  same place by another route. On the corpus the full `scc` arm loses outright —
  see below.

Careful reading capped rows in any of these sweeps: node counts there measure
throughput, not effort.

### `scc` against `prevent`

All 27 instances, 60 s cap, gcs against itself with `scc` as the default instead
of `prevent`. Measured on the encoding *after* the offset fix below, which matters:
an earlier version of this sweep predated it and so compared `scc` against a
`prevent` that was itself losing most of its pruning — a verdict against a
crippled opponent is worth nothing, and those numbers are gone.

**`scc` loses.**

* **Optimal-in-cap: `prevent` 14/27, `scc` 11/27** — mario 9/15 against 6/15, tpp
  5/12 either way. Of the instances where either configuration caps, `scc` reaches
  a worse objective on **8**, an equal one on 19, and a better one on **none**.
* **It loses proved optima it does not need to lose.** `2013/n_medium_2` goes from
  OPTIMAL 1053 in 23.3 s to capped at 967; `2013/n_medium_4` from OPTIMAL 832 in
  18.4 s to capped at 799; `2014/n_medium_5` from OPTIMAL 771 in 17.7 s to capped
  at the same 771 it can no longer prove.
* **Where both finish, it is far slower.** `2013/t_hard_1` 0.7 s → 15.9 s,
  `2014/t_hard_5` 2.3 s → 58.8 s, `2014/n_medium_3` 6.2 s → 48.7 s.
* **The inference itself is strong**, which is what makes this worth recording
  rather than just abandoning: mario node counts fall by 1.1× at n = 15, ~3-10× at
  n = 30 and up to **34.8×** at n = 100 (`2014/t_hard_2`, 5.72M → 164K).

**The per-node cost is what beats it, and it is only readable on the instances
both configurations finish.** On a capped row both ran for the same 60 s, so
"nodes per second" there is just the node count restated — a trap worth naming,
because that table looks like a finding and is not. On the uncapped rows:

| family | n | `prevent` nodes/s | `scc` nodes/s | penalty |
|---|---|---|---|---|
| mario | 15 | 15,485-77,000 | 14,205-27,422 | 1.1-2.8× |
| mario | 30 | 116,709 | 11,582 | 10.1× |
| mario | 100 | 78,670-96,735 | 2,707-2,740 | 29-35× |
| tpp | 15-35 | 255,927-360,731 | 261,503-357,280 | **1.0×** |

So on mario the walk costs roughly what the inference saves, and on the biggest
instances rather more.

**tpp is the interesting row, and the unexplained one.** The offset fix gives tpp
an anchor, so the arm is no longer inert there — it fires, and node counts differ
by up to 0.9%, so it is doing real work. But it costs **nothing** measurable, at
every size up to n = 35, which is larger than the mario instances where it costs
10×. Whatever makes the walk expensive is therefore not `n` alone. Propagation
counts do not explain it either: propagations *per node* are within 10% between
the two configurations on both families (12.4 against 12.7 on `tpp_7_5_20_1`, 40
against 45 on `mario_medium_1`), so the arm is not adding propagator invocations —
the cost is inside them, and something makes the subcircuit propagator run far
less often per node on tpp. **That is not established, and it should be settled
before anyone invests in making the walks incremental**, because on the family
where the walk is already free, making it cheaper buys nothing.

This reproduces Francis and Stuckey's own conclusion — without explanation-based
learning, `scc` for `subcircuit` is worse than `check` alone, "too expensive to
pay off" (they measure 17.0 s against 15.1 s; with explanations *and* learning it
goes 155 s → 2 s, and gcs has the explanations but no learning). It refines the
diagnosis. The rule is not weak; **the walk is.** Both reachability walks are
recomputed from scratch on every call, over a trigger that fires on any value
being removed rather than on a successor being fixed, so each costs `O(n²)` where
F&S run one Tarjan pass and a maintained component would cost far less.

It is also **not** the answer to the `n_medium` regression, which was the reason
for building it: `scc` makes those instances worse, and the offset fix below is
what actually fixed them.

`prevent` therefore stays the default, and `scc` stays a `with_algorithm()`
choice.

### Where the pruning was going

The `n_medium` regression had a diagnosis — the decomposition's `order` variables
were helping the brancher, and Chuffed's own native propagator showed the same
shape on that family, which looked like corroboration. It was wrong, and the real
cause was in our own MiniZinc redefinition.

`fzn_subcircuit.mzn` shifted the successors to be zero-based with a comprehension,
which introduces a fresh FlatZinc variable per node tied to the original by an
`int_lin_eq`. `LinearEquality` is bounds consistent by default, so a **hole**
punched in a shifted copy never reached `succ` — only its bounds did. This
constraint prunes almost entirely by removing individual successor values, so
almost all of its work was being discarded before it reached the array the rest of
the model uses. And mario's search annotation is
`int_search(succ, first_fail, indomain_min, complete)`, so `first_fail` was reading
stale domain sizes and `indomain_min` was trying values already ruled out.

Passing the offset and applying it as a view instead, with everything else the
same: optimal-in-cap on mario goes **4/15 to 9/15**, `2013/mario_t_hard_1` goes
from 1,133,233 nodes in 17.8 s to **55,069 in 0.7 s**, and no instance in the
family gets a worse objective. `tpp` is unmoved, because there was little pruning
there to lose.

**The probe that identifies the cause** — worth recording, because the fix and the
diagnosis are easy to conflate: keep the comprehension exactly as it was, change
nothing else, and make only the two-variable unit-coefficient equalities GAC. That
alone recovers the search (10,021 → 3,099 on `easy_2`, 1,133,233 → 55,157 on
`t_hard_1`), landing within a couple of nodes of the view version. So it is the
equalities' consistency, not the extra variables. Views are still the right fix,
since a view shares the domain outright and costs nothing to propagate.

The same shape is in four more redefinitions — the three `bin_packing` ones and
`fzn_regular` — and is [issue #803](https://github.com/ciaranm/glasgow-constraint-solver/issues/803).
The graph family shifts *parameters*, which costs nothing.

## The pruning rules: implemented, certified, and expensive

`with_prune_root()` and `with_prune_within()`, both off by default. Together they are
Francis and Stuckey's remaining `scc` rules, and they cost between 1x and 95x the
proof for about a ten per cent reduction in search. They are here because they are
*certifiable*, and a corpus of expensive-but-correct rules that a checker can be
pointed at is worth having on its own account.

### Why the encoding takes them at all

F&S state the rules over the **subtree structure of a depth-first traversal**: which
subtree was visited before which, and the lowpoint of a node's first child. This
encoding knows nothing about that. `pos` is a *tour-order* labelling, not a DFS one,
and it is pinned at exactly one place, `pos[anchor] = 0`.

That looked like the obstacle and mostly is not, because the DFS tree turns out to be
how the propagator *finds* these inferences rather than why they hold. Working each of
§5.3.2's seven explanation clauses back to what makes it true:

**Rules 1 and 5, and the conflict cases of 3 and 4, were already ours.** They all rest
on one cut fact: if both sides of a cut hold a node that must be on the tour and no
edge crosses it, then whichever side the anchor is on, the other side is stranded ---
and stranding is exactly what the two plain walks derive. Rule 1's component `S`
either contains the anchor, in which case nothing outside it is forward-reachable, or
does not, in which case its evidence node cannot reach the anchor.

**Prune root (rule 6) and prune within (rule 7) are strictly stronger, and both are
the existing induction run under one assumed edge.** Assume `succ[p] = c`, run the
reachability rules against the domains that leaves, and if a node that must be on the
tour would be stranded in either direction, `c` is not a value `succ[p]` can take.
Neither fires on the live domains --- while a successor is still free the anchor
reaches everything any of its values reaches --- which is precisely why they add
strength and why they cost a walk per candidate.

So in this encoding **the two rules are singleton arc consistency (shaving) on the
successor variables**, and both are one function, `shave_by_reachability`, with the two
flags selecting which nodes it runs over: prune root the anchor, prune within
everything else. Splitting them at the anchor keeps them non-overlapping.

### What the certificates needed: nothing new

No new row family, no new proof-only variable, and no new cutting-planes step. Three
small pieces of mechanism:

* **`AssumedEdge`**, and walks that take one. Carried as data rather than read back out
  of the `State`, because the walk's result and the justification that reproduces it
  must be over the same edge set --- and a justification may read only the reason and
  the model, never the live state, which by then has moved on.
* **The hypothesis as a guard.** Every row the induction emits picks up
  `succ[from] != to` as an extra disjunct, so it says "*if* that edge is taken, then x
  at position t is off the tour", and the conclusion drawn from such a chain is not "x
  is off the tour" but "that edge is not taken". One extra literal per row. The
  alternative --- emitting the chain at a proof level deleted once the conclusion is
  drawn --- saves those literals and costs the level discipline; the guard was chosen
  because it cannot be got subtly wrong.
* **Candidates snapshotted** before the loop infers anything. Judging each against the
  domains the pass started from is sound and not merely convenient: a walk only ever
  uses the *absence* of a value to rule a neighbour out, so a domain that has since
  lost more values makes the reason a stronger premise, not a weaker one.

Both mutation probes are caught: dropping the guard, and replacing the induction with a
plain `JustifyUsingRUP`. The guard one is caught three times over --- by
`subcircuit_prune_root_test`, by `subcircuit_prune_within_test`, and by the anchored
enumeration sweep in `subcircuit_test.cc`, which reports the signature worth recognising:
the solution set is still right and VeriPB refuses the certificate.

### The cost, measured

One random instance per `n` (the same one across configs), complete enumeration with
proofs on, VeriPB 3.0.2. Harness `costcurve.cc` + `curve.sh` in
`~/claude/tmp/788-subcircuit-step0/`.

| n | recursions (scc / +root / +within) | `.pbp` scc | +prune_root | +prune_within | verify scc → +within |
|---|---|---|---|---|---|
| 6 | 16 / 16 / 17 | 11 KB | 1.0x | **13.1x** | 0.10 → 0.11 s |
| 7 | 119 / 119 / 117 | 139 KB | 1.5x | **15.4x** | 0.11 → 0.10 s |
| 8 | 492 / 492 / 478 | 212 KB | 1.0x | **51.6x** | 0.11 → 0.51 s |
| 9 | 1281 / 1281 / 1199 | 586 KB | 1.6x | **72.2x** | 0.21 → 2.11 s |
| 10 | 8057 / 8057 / 7461 | 4.3 MB | 1.0x | **94.9x** | 1.71 → 24.3 s |
| 11 | 25469 / 25420 / 22846 | 72.9 MB | 1.7x | **25.5x** | 12.8 → 108 s |
| 12 | 104134 / 104044 / — | 73.0 MB | 3.7x | *abandoned* | 93.1 s → — |

**Every proof verified**, up to and including the 1.86 GB one at `n = 11`. That is the
result worth having: the rules are checkable, at every size the checking is affordable
at all.

Read the multiplier column carefully. It is not monotone --- 95x at `n = 10` and 25x at
`n = 11` --- because the denominator moves too: `scc`'s own proof jumps 17x between
those sizes as its search grows. The absolute figures are the honest ones.

At `n = 12` prune within passed **10.8 GB** of `.pbp` before being abandoned, which on
this machine means it does not fit: the scratchpad is a 16 GB tmpfs and therefore
*shares the guest's RAM*. Complete enumeration with prune within has a practical
ceiling somewhere around `n = 11`.

And what it buys: **about ten per cent fewer search nodes** (8057 → 7461 is 7.4%,
25469 → 22846 is 10.3%, 1281 → 1199 is 6.4%), and for prune root essentially nothing at
all (104134 → 104044).
Which is consistent with everything else measured on this arm --- the node reduction
where it is measurable at all is 1.09x to 1.38x --- and is the argument for treating
the proof-size constant as the thing to attack rather than the propagator.

### What is still hard, and what is not

1. **Proof size is the whole problem.** `O(n²)` rows per inference, `O(n³)` per call
   for prune root and `O(n^4)` for prune within. The table above is that constant.
2. **Forced edges come out of shaving**, which is the cheap route even though it looks
   the wasteful one. Rules 2 and 3 conclude `succ[c] = b`; shaving yields it as a
   by-product once every other candidate is gone, at one induction per candidate each
   carrying **one** guard literal. Deriving the cut row
   `Σ_{i∈A, j∉A} [succ[i] = j] ≥ 1` instead needs one induction, but every row of it
   carries the whole crossing set as guards: `O(n²)` guards on `O(n²)` rows against
   `O(n³)` literals for the shave. Nothing here derives a cut row.
3. **Rule 1 with no anchor is still out of reach.** F&S guard it with `in(a)` alone and
   need no root; this induction has to start somewhere, and `pos` is pinned only at the
   anchor, so an arbitrary component would need layers indexed relative to the unknown
   `pos[a]`. It is the one place the "arbitrary root" position-offset problem is real
   --- and unreachable for us anyway, since the arm does nothing without an anchor.
4. **A constant in the successor array breaks the certificate**, which is
   [issue #812](https://github.com/ciaranm/glasgow-constraint-solver/issues/812) and
   not these rules' fault: the pigeonhole sums "this variable takes at least one value"
   over every successor and that is `UnimplementedException` for a constant. Every
   `mario` instance has one, because its `succ[LuigiHouse] = MarioHouse` pin folds into
   the array as a literal --- so the one thing that gives the arm an anchor is the one
   thing that stops it writing a proof, and the cost table above is measured on
   constant-free instances for that reason.

### A sign error in the paper, for whoever implements from it

§5.3.2 defines `in(a)` as "node `a` must be included in the circuit ... (i.e.
`a ∈ D(x_a)`)". Those two halves disagree: a node that must be on the tour is one
whose own index has been *removed*, `a ∉ D(x_a)`. Every clause body in the section
writes `x_a ≠ a`, which is the correct reading, so it is the parenthetical that is
inverted.

Also not implemented, and deliberately: F&S's evidence-literal selection
heuristic. They report that "fixed highest in the search tree" is a little better
than the lowest-numbered default, which is a knob to add once something measures
it here.

## Testing notes

* **A mutation probe is the only thing that shows a certificate is load-bearing,
  and it needs a pinned seed.** Swap `derive_tour_at_most` / `derive_unreachable`
  / `derive_cannot_reach_anchor` for a plain `JustifyUsingRUP` and confirm VeriPB
  rejects — with `--seed=N`. `subcircuit_test` randomises its view-wrap
  configuration, and an unseeded probe can come out *passing*: the wrap it happens
  to pick decides whether unit propagation reaches the conflict unaided. A probe
  that can silently come out the wrong way is worse than no probe. With the seed
  pinned it rejects at `n = 5`, and `n = 3` and `n = 4` still pass, so the
  scenario size matters too. Redo it after any encoding change: changing the
  off-tour numbering moved which test catches it.
* **Showing an SCC rule does anything takes care.** With the reachable and
  unreachable halves swapped, or equal-sized, both algorithms give *exactly* the
  same recursion count, because the brancher never enters the unreachable half
  before the tour closes and then `check` forces it off for free. Give the
  unreachable half the **smallest domains**. Assert the **root state**, not a
  recursion margin.
* **`subcircuit_scc_reaches_anchor_test` isolates the backward walk** by adding
  one arrow from the reachable half into the stranded one. That makes everything
  forward-reachable, so only the backward walk can produce the root state.
* **`--fzn-pattern` on a MiniZinc lane is load-bearing.** Without it the lane
  passes against the decomposition. Check by deleting `mznlib/fzn_subcircuit.mzn`
  and confirming the lane goes red.
* **A `.scp` byte-stability round trip cannot catch a dropped semantic argument**
  — the writer omits it, the reader builds the weaker constraint, the second write
  matches. Assert the term is in the `.scp` *and* that reading it back still
  constrains.
* **XCSP3's `size` semantics were measured off ACE, not read off the spec.** On 4
  vertices: size 3 → 8 solutions, size 4 → 6, variable size over `0..4` → **20,
  not 21** (the empty tour is excluded even with 0 in the domain), sizes 0 and 1 →
  UNSAT.

## See also

* [`connectivity-proofs.md`](connectivity-proofs.md) — why an arithmetic labelling
  is the expensive encoding for reachability, and the unfolding that avoids it.
* [`xcsp.md`](xcsp.md) — how `<circuit>` binds here.
* Kathryn Glenn Francis and Peter J. Stuckey, "Explaining circuit propagation",
  *Constraints* 19(1):1–29, 2014. §4.2 the constraint, §5.1 `check`, §5.2.1
  `prevent`, §5.3.1 `scc` for subcircuit, §5.3.2 the explanation clauses.
