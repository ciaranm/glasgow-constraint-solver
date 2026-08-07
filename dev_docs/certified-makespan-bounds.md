# Certified makespan lower bounds from a `Cumulative`'s energy

A `Cumulative` of capacity `C` over tasks with lengths `d_i` and heights `h_i`
says the schedule cannot be short. The tasks need `Σ_i d_i h_i` units of a
resource supplying `C` per time step, so no schedule can finish before their
ratio. That is Sidorov's `L`, the number
[`InferredCumulative`](inferred-cumulative.md) and
[`InferredDisjunctive`](inferred-disjunctive.md) report as
`largest_capacity_bound`, and for a lifted cut it can beat anything the donor's
own row gives.

Reporting it and proving it are different things. What a proof contained before
this was the derived constraint's per-time rows and whatever its propagator
happened to say at the nodes the search reached; the ratio argument appeared
nowhere. `gcs/constraints/innards/makespan_energy.hh` makes it, and the
constraint infers the bound at the root, so a `.pbp` now contains the number as
well as the run that used it.

## The argument

Let `M` be the makespan and suppose `M ≤ μ`. Then:

- every task is confined to `[lo, μ)`, where `lo` is the earliest time any of
  them can be running;
- [the window-energy lemma](cumulative-proof-logging.md) gives each task
  `Σ_{t ∈ [lo, μ)} active_{i,t} ≥ d_i`;
- summing those weighted by `h_i`, against the constraint's capacity rows summed
  over the same window, cancels every activity term and leaves a line with
  nothing but negative coefficients against a positive right-hand side — a
  contradiction exactly when `Σ_i d_i h_i > C · |rows in the window|`;
- the wrapping RUP concludes `M ≥ μ + 1`.

`makespan_energy_bound` walks the candidate `μ` and returns the largest one
refuted; `derive_makespan_bound` emits the argument for it, as one `pol` over
the rows and the per-task lemmas. The constraint then infers `M ≥ μ + 1` with
that as its `JustifyExplicitly`, from an initialiser, so it fires once at the
root.

### Two places the bound is not `L`

**It can be larger.** `L` divides by `μ`, assuming the tasks may start at time
zero. The derivation divides by the number of time points it has a capacity row
for, which starts at the earliest time any task can be running — so a set of
tasks that precedences keep away from the origin gets a better bound, and every
time point before that window is a unit of supply the resource never had to
provide.

**It can be smaller,** or absent. The lemma speaks only about tasks with a
constant length and height and a start that is a plain variable (see
`prepare_cumulative_overload_check`); a task it cannot speak about carries none
of the energy `L` counted. And a window narrow enough to exclude a task's whole
duration gets only the part that fits — which is why the search starts from what
the model already implies rather than from the makespan variable's declared
lower bound. That distinction is not cosmetic: initialisers run before anything
has propagated, so the makespan's own lower bound is still zero at that point,
and without it the search settles for a window too narrow to hold every task.
Sound, and a weaker number than the constraint deserves.

## The deadline is a `pol`, not a RUP

The step that makes this an argument about the makespan rather than about the
tasks' own domains is `start_i ≤ μ - d_i`. It follows from the model's
`makespan - start_i ≥ d_i` and the negated conclusion `M ≤ μ`, and it is **not**
reverse unit propagation: a checker will not carry a bound from one variable's
bits to another's across a linear row, whatever the two order literals say. That
is the same wall [`VeriPB` RUP limits](../dev_docs/README.md) put in front of
every cross-variable linear inference, and the answer is the same — a cutting
planes step.

Adding the model's row to the two order literals' own definitions cancels both
variables' bits exactly:

```
    bits(s) + K₁·¬[s ≥ v]                      ≥ v        (definition of [s ≥ v])
    bits(M) - bits(s)                          ≥ b        (the model's row)
   -bits(M) + K₂·[M ≥ μ+1]                     ≥ -μ       (definition of [M ≥ μ+1])
   -------------------------------------------------------
             K₁·¬[s ≥ v] + K₂·[M ≥ μ+1]        ≥ v + b - μ
```

and with `v = μ - b + 1` the right-hand side is exactly one, so saturating lands
on the clause `¬[s ≥ v] ∨ [M ≥ μ+1]`. The lemma's own RUPs then resolve against
it one order literal at a time, which they can, because that reasoning stays
inside a single variable's bits.

So a makespan is not a kind of variable — it is a variable a model has put rows
around. `find_makespan_links`
([`gcs/presolvers/innards/makespan_links.hh`](../gcs/presolvers/innards/makespan_links.hh))
goes looking for them rather than taking them on trust, so naming a variable
that is not a makespan gives a weaker bound instead of a rejected proof. It
matches the linear family's two-term unconditional rows over plain variables,
which is what a scheduling model's makespan rows are and what MiniZinc's
`int_lin_le` flattens them to. A comparison spelling (`start + length ≤
makespan`) says the same thing over an offset view, whose bits would not cancel
against the plain variable's, so it is not matched.

## Testing it

`derived_cumulative_test.cc` has the mechanism: three tasks of length two on a
unary resource, which must run one after another, so no schedule finishes before
six — and the model's rows say only that the makespan is at least two. Over
`[0, 5)` the tasks need six units and the resource supplies five, a margin of
exactly one, which is what makes the mutations below bite.

Three of them, all refused by VeriPB:

- **`ClaimHigherBound`**, the signature test: claim one more than the energy
  supports. A derivation with slack in it verifies whatever it concludes, and
  only a refused `+1` says the honest number is the one the arithmetic reaches.

  Two shapes, because neither works everywhere. Where a wider window would have
  another capacity row in it, the argument moves to that window and comes up
  exactly one unit of supply short. Where it would not — the honest window
  already reaching the last row — widening changes nothing, so instead the
  honest window keeps its honest contradiction and only the *conclusion* moves:
  the `pol` then contradicts under `[M ≤ bound-1]` while the wrapping RUP
  asserts under `[M ≤ bound]`, which is one order literal short of firing.
- **`OmitCapacityRow`**: count the window one row short. The omitted row's
  activity terms then have nothing to cancel against and survive with a
  *positive* sign, so the line reached is `Σ_i h_i a_{i,t} ≥ k` rather than a
  contradiction.
- **`ForgetTheDeadline`**: derive the tasks' window energy without the negated
  conclusion in its context, so the end-of-window literals are claimed without
  the deadline that gives them.

A fourth was tried and dropped, and the reason is worth keeping: **deriving a
task's energy over a window *narrower* than the rows cover is not catchable.**
Its leftovers survive negatively, so the line stays contradictory and VeriPB
rightly accepts a derivation that is merely longer than it needed to be. Only
corruptions that make the sum come up *short* can be refused.

### When the `+1` is a test at all

Two conditions, and both bite on real instances.

**The horizon has to be at least the bound.** Below it the honest derivation is
a refutation rather than an inference, and every claim follows from a
contradiction.

**The instance has to be feasible at the bound** — which is to say the bound has
to be the optimum. Anywhere else, "the makespan is at least one more" is *true*,
and a checker that finds a way to agree has found nothing wrong: the run is
refuting an infeasible instance either way, and the derivation's sound half
(the `pol` still says the tasks cannot be active outside their windows) is
enough to let unit propagation get there. That is not a defect in the mutation,
it is what a mutation means — a corruption you cannot distinguish from the truth
is not a corruption.

So the discipline lives in two places. The margin-of-one fixture above is where
it is *made* to bite, and the artefact below runs it per instance and requires a
refusal only on the instances the bound closes.

## The RCPSP artefact

`examples/rcpsp --dzn` reads the MiniZinc `.dzn` flavour the Pack and Pack_d
collections use; `--infer-disjunctive` and `--infer-cumulative` run the two
stages, and `--infer-makespan-bound` (on by default) has them derive their
bounds rather than only report them. `--mutate-makespan-bound` claims one more,
for the discipline above.

The certificate for a bound `B` is the decision variant at `B - 1`: the
derivation refutes it at the root, so the proof is the bound's certificate and
nothing else. Before that, the same question with the bound switched off, which
must *not* close at the root — or something else in the model is doing the work
and the instance says nothing about the bound.

A bound at or below the critical path is reported and skipped: `--deadline`
never takes the horizon below the critical path, so the question those runs
would ask is not the one they look like.

See `~/claude/tmp/rcpsp-bounds-672/` for the sweep, which runs every instance in
both collections through all three stages, verifies each honest proof, records
each `+1`, and checks every bound against a makespan somebody has actually
achieved.

**Every number in this section is stale and none of them may be quoted until the
artefact has been rerun** (issue #708) — see the note below, which says what has
changed under them since. They are recorded rather than deleted because what they establish is
the *shape* of the result, and that has not moved.

Over the Pack collection in all three stages and Pack_d in the capacity-one
stage — 227 runs, no failures — 92 of the 110 instances get a certified bound,
every one of them beating the critical path, and **29 are closed**: the bound
equals the best makespan anybody found, so no search is needed at all.

The paper's §5.1 claims "no less than twelve", and the two numbers are **not
measuring the same thing**, so do not put them side by side without saying so.
His twelve counts instances whose *unrounded* elastic lower bound improves on
the previously known lower bound; his own closure test, run over the same
artefact, gives twenty, and taking the ceiling of the bound — which is the
integral quantity a solver could actually use — gives thirty-six. Ours counts
instances whose certified bound *equals the best known makespan*. Twenty-nine
against thirty-six is the comparison closest to like-for-like, and it is a
comparison of two different collections' worth of stages at that; see
`~/claude/tmp/sidorov-548/RESUME.md` for the reproduction of all four numbers.

The largest is 3050; the median
`.pbp` is 28 MB and the largest 504 MB, and `veripb` took 45 s on that one *at
the time* --- see the note below, which the checking figure needs even more than
the bounds do.

Some instances fall short of Sidorov's `L`, and on every one of them it is this
presolver's *own* `L` that falls short while the derivation reaches it exactly:
an inference gap and not a certification one. Most of the apparent gap is not
even that — five of the largest shortfalls are Pack_d instances whose lifted
stages were never run, and are compute rather than code. What is left, once the
lifting stage has actually run, is a handful of instances short by two to four,
and it was the measurement that motivated lifting over every resource rather
than one, which the presolver now does; four of those instances have an `L` equal
to their best known makespan, so closing the gap closes them.

**These numbers predate that change and have not been rerun.** They are the
single-resource lifting's, and the artefact's `run.bash` is what regenerates
them.

Three later changes move them again, all in the direction of a better `L`:
lifting now orders the remaining tasks by the duration they are guaranteed to
occupy rather than by a variable's identity (which agrees on these instances,
whose durations are all constants, but the ordering was not what it claimed);
the candidate pairs the clique search grows are the best by bound rather than
the first by scan order, which forty of the hundred and ten instances have
enough conflicting pairs to notice; and a clique one posted capacity-one
resource already contains is no longer posted, nor its bound reported. The
twenty cross-check targets still match exactly under all three.

The *checking times* above are staler still, and for a second reason: hinting the
replay's RUPs made verification six to fourteen times faster on exactly these
certificates (see [inferred-cumulative.md](inferred-cumulative.md)), so the 45 s
is an upper bound on an upper bound. Rerunning the artefact fixes both at once.

Note the makespan rows have to be there to be cited: `--variant=global` puts the
whole temporal network into one `DifferenceConstraints` propagator, so there is
no per-task row to sum and the bound falls back to whatever the tasks' own
domains give.
