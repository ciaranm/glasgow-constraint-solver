# Abbreviating a reason to one extension variable

A `JustifyExplicitly` often writes several temporary lines under the same
reason. Cumulative's edge-finding and energy justifications write about ten per
inference, each restating a reason of 10–30 literals. A justification can
instead ask for those lines to name a single flag that stands for the reason.
That makes the proof smaller and quicker to write. On Cumulative it also makes
the proof quicker to check, but that does not hold everywhere, which is why
this is opt-in. This note covers what is written, why the deletions are safe,
the rules for a justification that opts in, and the measurements behind the
current opt-ins.

## The call

A call site wraps its emit:

```cpp
inference.infer(logger, lit, JustifyExplicitly{WithAbbreviatedReason{justify}, ThenRUP::Yes, hint}, reason);
```

That runs `justify` under a `ProofLogger::AbbreviateReason`, which can also be
held directly inside an emit. While the guard is alive, the first temporary line
under exactly its reason makes the logger write, at that temporary level:

```
red k ~f + l_1 + ... + l_k >= k : f -> 0 ;     forward: f implies every l_i
red ~l_1 + ... + ~l_k + f >= 1 : f -> 1 ;      reverse: every l_i implies f
```

The literals are the ones that [`assumed-root-bounds.md`](assumed-root-bounds.md)
does not leave out, so `f` stands for the whole reason, given the root units.
From then on, a temporary line `C + W·(~l_1 + ... + ~l_k) >= d` is written as
`C + W·~f >= d`. The inferred line at the end keeps the whole reason. It is
an unhinted RUP, which reaches `f` through the reverse line.

| line | handling |
|---|---|
| unhinted `rup`, `a`, at the guard's temporary level, under exactly its reason | names `f` |
| hinted `rup`, same | names `f`. Its hints are prefixed with the root units the definition left out, then the forward line, so that propagating `f` sets every literal before the line's own hints are reached. |
| `ia` | keeps the whole reason, because it is checked term by term against the line it cites, and that is usually a definition or a model row with no `f` in it |
| current level, or a deeper temporary level | keeps the whole reason |
| while `KeepAssumedReasonLiterals` is alive | keeps the whole reason |
| inside a subproof | uses a flag already defined, but never defines one, since the definition would not outlive the `qed` |
| fewer than 4 literals once the root-fixed ones are left out | keeps the whole reason, because the two definition lines cost about as much as they save |

Nested guards: only the innermost one rewrites anything.

## Why the deletions are safe

The definition is recorded at the guard's temporary level, and only lines at
that level name `f`. `forget_proof_level` therefore deletes the definition
together with every line that uses it. No current-level line names `f`, so
neither does anything that may later be moved to core: backtrack and nogood
lines are written outside any guard. The definitions are derived lines, and
deleting a derived line is not checked. Flag names are never reused.

If the guard's level is forgotten while the guard is still alive, the logger
treats the definition as gone. The next use writes a new definition, under a
new name.

`abbreviate_reason_test` checks these cases and fails if any of them is broken:

- a hinted RUP whose hint needs the reason's literals set
- a level forgotten mid-guard
- an `ia` citing a model row
- the size floor
- a false claim, which must still be refused once abbreviated

The mechanism was also tested switched on for every `JustifyExplicitly` with a
floor of 1, and the whole suite then verifies.

## The rules for a justification that opts in

- **Write every line that a later step combines under the guard, at its level.**
  A `pol` over one abbreviated line and one full-reason line is still sound,
  but its result carries both `W·~f` and `W·Σ~l_i`. A step that expected those
  terms to cancel is then left holding them.
- **Derive nothing that outlives the level from abbreviated lines,** except by
  unhinted RUP. A `pol` result at the current level would name a flag whose
  definition is about to be deleted. A hinted RUP with the full reason would
  need the reverse line, and nothing prefixes it. `ThenRUP::Yes` ends with an
  unhinted RUP, so it is fine.
- **Do not combine it with `KeepAssumedReasonLiterals`.** That guard exists for
  justifications whose later `pol`, `ia` or `pbc` expects the reason spelled out.

## Why it is opt-in

A smaller proof is not always a faster check. Before this landed, the same
mechanism was applied to every `JustifyExplicitly` with a reason of 8 or more
literals:

| instance | constraint | proof size | check time before → after |
|---|---|--:|--:|
| `2025_hitori` | Reachable | 0.10 | 2406 s → 3900 s |
| `p11` (r6-6-7 job shop) | Disjunctive | 0.92 | 41 s → 51 s |

A variant that shared one flag across inferences had `2017_rel2onto` go from
376 s to 836 s at 0.78 of the size.

On a prefix of the hitori proof the 2× slowdown reproduces exactly, and these
changes did not remove it:

- removing the deletions
- asserting the definitions instead of checking them
- writing the definitions as clauses
- putting the flag first in each line

Adding the same number of unused variables costs nothing, and the propagation
trails are the same length, so VeriPB is doing more work per propagation, not
more propagation. The cause is not known.

So measure before opting a constraint in. Measure solver instructions and a
paired VeriPB check, with the search identical either side (see
[`benchmarking.md`](benchmarking.md)), and keep the opt-in only where the check
does not get slower.

## Who opts in, and what it bought

**Cumulative,** at all 13 of its `JustifyExplicitly` sites, measured against
root filtering alone. The runs covered the CPAIOR 2027 scheduling pairs, j30
(opt−1) and the #1035 MiniZinc corpus: 49 instances, search identical, all
verified. 27 instances produce byte-identical proofs.

| family | proof size | solver instructions | check time |
|---|--:|--:|--:|
| scheduling pairs (14) | 0.65 | 0.87 | 0.58 (the 10 whose proofs change) |
| j30, opt−1 (9) | 0.43 | 0.76 | 0.60 |
| `2013_fjsp` | 0.48 | 0.84 | 0.93 |
| rest of the MiniZinc corpus (25) | 1.00 | 1.00 | see below |

Some individual instances:

| instance | check time before → after |
|---|--:|
| p04 | 27.6 s → 11.2 s |
| p06 | 74.9 s → 29.1 s |
| J30_6_4 | 155.5 s → 78.1 s |
| J30_30_5 | 913 s → 567 s |

Two more Cumulative models in the MiniZinc corpus change, but only slightly:

- `2011_cyclic-rcpsp` checks in 41.5 s → 41.6 s.
- `2013_rcpsp` checks in 26.6 s → 20.3 s. With a floor of 2 the proof is
  nearly the same and the check took 25.6 s, so this is probably noise.

The other 23 produce byte-identical proofs.

A floor of 2 measured the same as 4. A floor of 8 lost most of the saving on p04
(0.65 of the size rather than 0.46).

**Measured, but not opted in.** These figures come from the experiment, which
applied the mechanism to every `JustifyExplicitly` with a floor of 8:

| constraint | instances | size | check time |
|---|---|--:|---|
| Element | `2017_crosswords` | 0.36 | within 2.5% |
| Element | `2011_depot-placement` | 0.68 | within 2.5% |
| MinMax | `2013_league` | 0.55 | within 2.5% |
| MinMax | `2025_EchoSched` | 0.76 | within 2.5% |
| Reachable | hitori | 0.10 | slower, see above |
| Disjunctive | p11 | 0.92 | slower, see above |

Element and MinMax are candidates if proof size alone is worth having.
