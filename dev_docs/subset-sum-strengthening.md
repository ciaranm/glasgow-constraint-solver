# Subset-sum strengthening

A derived line saying

```
    Σ c_i x_i  ≤  B
```

over 0/1 terms can nearly always be tightened for free. The sum can only ever
take a value that is a subset sum of the coefficients, so if no subset sums into
`(B′, B]` then `Σ c_i x_i ≤ B′` holds too, where `B′` is the largest subset sum
at most `B`. `derive_subset_sum_strengthening`
([`gcs/innards/proofs/subset_sum_strengthening.hh`](../gcs/innards/proofs/subset_sum_strengthening.hh))
derives that line.

The two lines have the **same 0/1 solutions** — nothing lives in the gap — so
this buys no propagation on its own. What it buys is a tighter *inequality*, and
that matters as soon as the line is added to another one: `Σ c_i x_i ≤ B` plus
`Σ c_i x_i ≥ B′ + 1` is perfectly consistent over the rationals, while the
strengthened form contradicts it in one `pol` step. That is the shape all three
consumers need — the knapsack-augmented overload check's availability bound
(#550), Schulz's capacity reduction (#547), and cover lifting
certificates (#549).

## The two derivations

### Divisibility, when the coefficients share a factor

If `d = gcd(c_i) > 1` and `d·⌊B/d⌋` is the answer, the whole thing is
Chvátal–Gomory rounding: divide the source line by `d`, multiply back. Two
`pol` steps, no flags. This is the common case whenever a model's coefficients
have a scale to them.

The condition is on the gcd of **every** coefficient. `{6, 10, 15}` has pairwise
gcds all above one and an overall gcd of one, and rounding `14` down to `12`
would be wrong (the answer is `10`) — so a fast path keyed on anything weaker
than the full gcd is a bug, and there is a fixture for exactly that.

### Layered dynamic programming, otherwise

One layer per item. Layer `k` speaks about the prefix sum `P_k = Σ_{i≤k} c_i x_i`,
and has one state per value that prefix can reach without already exceeding `B`.
Each state `(k, v)` gets three flags, reified at the requested `ProofLevel`:

```
    ge_{k,v}  ⇔  P_k ≥ v
    le_{k,v}  ⇔  P_k ≤ v
    st_{k,v}  ⇔  ge_{k,v} ∧ le_{k,v}        (the prefix sum is exactly v)
```

This is the shape [`Knapsack`'s upfront DAG](knapsack.md) uses, specialised to
one coordinate and 0/1 items.

**Transitions.** Four clauses per state, each a `pol` over two reification
halves plus a literal axiom, saturated — the prefix-sum terms cancel exactly,
the same cancellation the `Cumulative` window-energy bridges use:

```
    ¬ge_{k-1,u}  ∨  ge_{k,u}                    (the sum only grows)
    ¬x_k ∨ ¬ge_{k-1,u}  ∨  ge_{k,u+c_k}         (taking the item)
    ¬le_{k-1,u}  ∨  le_{k,u+c_k}                (the item adds at most c_k)
    x_k  ∨ ¬le_{k-1,u}  ∨  le_{k,u}             (leaving the item)
```

From those, two state-level transitions are RUP — `¬st_{k-1,u} ∨ x_k ∨ st_{k,u}`
and `¬st_{k-1,u} ∨ ¬x_k ∨ st_{k,u+c_k}` — and adding those two and saturating
**resolves them on the item literal**:

```
    ¬st_{k-1,u}  ∨  st_{k,u}  ∨  st_{k,u+c_k}
```

That resolution is the load-bearing step. Unit propagation cannot case-split on
`x_k`, and a `pol` over the weighted lines cannot either; resolving two clauses
is how cutting planes does it, which is why the derivation goes through
clause-shaped intermediates rather than staying with the weighted forms.

**Layer at-least-ones.** `Σ_{v} st_{k,v} ≥ 1` — "the prefix sum is in one of
these states" — is then a RUP against the previous layer's version: negating it
falsifies every successor, each transition forces `¬st_{k-1,u}`, and the
previous at-least-one is contradicted.

**Dead states.** A prefix sum over `B` cannot be completed: the source line
bounds the whole sum and no coefficient is negative. So states above `B` are
never created. Instead the clause `¬st_{k-1,u} ∨ ¬x_k` is derived from the
source line (plus a literal axiom per later item, to cancel the tail), and
resolved into the transition, which leaves the state with only its stay branch.

**Finishing.** Every state of the last layer is at most `B′` — that is what makes
`B′` the answer — so each gives `¬st_{n,v} ∨ under`, where `under ⇔ Σ c_i x_i ≤ B′`.
With the last at-least-one, `under` is a RUP; discharging its forward half
against that unit is the returned line.

Size is O(items × bound) flags in the worst case. In practice: six coprime
weights against a bound of 83 — sixteen states over seven layers — is about 630
proof lines and 50 KB. A caller working with a large bound should budget, and
reach for this where it pays rather than everywhere.

## Testing it

`subset_sum_strengthening_test` makes three separate claims, because they are
three different things:

1. **The answer is right.** The bitset subset-sum is checked against brute force
   over random weight sets — primes, near-duplicates, gcd-structured — and over
   the hand-verified fixtures.
2. **The derivation follows.** Each fixture is proved against a *satisfiable*
   micro model (the source line alone), so every step has to stand on its own.
   This is the model that catches a derivation claiming more than it proved: an
   unsatisfiable model would make every RUP step valid and let a corrupted
   derivation through, which is worth remembering when writing this kind of test.
3. **The line says what the caller was told.** veripb accepting every step does
   *not* say this: a sound step can land on something weaker than intended, and
   a caller scaling it by a height or adding it to a capacity row would then be
   working from a line that does not carry the bound it is supposed to. So each
   proof also pins the returned line's content with an `ia` step, whose
   implication check is syntactic — a weaker line does not imply the claimed one,
   and veripb says so.

Plus the end-to-end use: against a model with an extra axiom putting the sum
above `B′`, the strengthened line and that axiom combine into a contradiction in
one `pol`, and an `ia` against the result insists it really is one.

The mutations (`SubsetSumMutation`, tests only) are each caught by exactly one
of those nets, which is the point of keeping them separate: claiming one better
than the largest reachable sum breaks a RUP step (net 2); skipping a layer's
transitions leaves its at-least-one unsupported (net 2); and dividing by
something that does not divide every coefficient is a perfectly sound proof step
that simply does not establish the claimed bound (net 3, and nothing else would
notice).

<!-- vim: set tw=72 spell spelllang=en : -->
