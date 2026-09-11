# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with
code in this repository.

It is deliberately short. Nearly everything a developer needs here is project
documentation rather than agent guidance, and it lives in `dev_docs/`,
`README.md` or `CONTRIBUTING.md`. A fact copied into two files goes stale in
one of them, so this file routes rather than restates: what to read, the
mistakes that have actually been made in this tree, and what to run before
committing.

## Read the relevant document first

The solver is a C++23 constraint programming solver whose defining feature is
**proof logging**: every inference it makes can be checked externally by
VeriPB. That constraint shapes almost every design decision in the tree, and
very little of it is guessable from the code alone. `dev_docs/README.md` is the
index; read the document that covers what you are about to change *before* you
change it. It is the most efficient way to absorb the conventions and the
reasoning behind them.

| If you are... | Start with |
|---------------|------------|
| adding a constraint that does not exist yet | [`dev_docs/constraints.md`](dev_docs/constraints.md), "Bringing up a new constraint" — the order to do the work in, before anything else |
| changing an existing constraint | the rest of [`dev_docs/constraints.md`](dev_docs/constraints.md), then [`reification.md`](dev_docs/reification.md) if it is reified |
| touching domains, backtracking, or the inference paths | [`state-and-variables.md`](dev_docs/state-and-variables.md) |
| writing or debugging a justification | `constraints.md` (Justifications), [`infer-redesign.md`](dev_docs/infer-redesign.md), and the per-constraint proof notes in the index |
| wondering what the checker will accept, or why a proof is slow to check | [`veripb-facts.md`](dev_docs/veripb-facts.md) |
| creating an auxiliary variable for a proof | [`variable-encodings.md`](dev_docs/variable-encodings.md) |
| touching views | [`view-proof-logging.md`](dev_docs/view-proof-logging.md) |
| making a propagator faster | [`propagator-performance.md`](dev_docs/propagator-performance.md), then [`benchmarking.md`](dev_docs/benchmarking.md) |
| changing the build, an option, or a toolchain assumption | [`building.md`](dev_docs/building.md) |
| writing C++ that clang-format does not settle | [`code-style.md`](dev_docs/code-style.md) |
| working on a frontend | [`minizinc.md`](dev_docs/minizinc.md), [`xcsp.md`](dev_docs/xcsp.md), [`frontend-support-matrix.md`](dev_docs/frontend-support-matrix.md) |
| releasing the Python bindings | [`releasing-gcspy.md`](dev_docs/releasing-gcspy.md) |

For orientation in the source itself, `README.md` (Navigating the Source Code)
covers the public API in `gcs/`; `gcs/innards/` is everything that is not part
of it, and `dev_docs/constraints.md` (The big picture) is the map of how a
constraint, its propagators, its OPB definition and its proof fit together.

## When to ask for a second opinion

Reproducing a proof shape this tree already uses is reliable. Inventing one is
where things go wrong, and the failure mode is quiet: a derivation that verifies
but is needlessly baroque, or that leans on something which happens to hold for
the instance in front of you.

Two triggers. Either the constraint needs a proof technique that is not already
somewhere in `dev_docs/`, or the technique you did use looks inelegant or
suspicious *to you* — treat that feeling as evidence rather than as fussiness.

When either fires, spawn a subagent on the **Fable** model as a critical proofs
consultant, and keep its instructions narrow. Give it one derivation and one
question; tell it what the encoding provides and what the reason contains; ask
it to attack the argument, not to write code. A broad "review my proof logging"
gets a vague answer, whereas "here is the `pol`, here is why I think each step
is sound, find the case where it is not" gets a useful one. This is a good use
of tokens: much cheaper than meeting the same problem as a rejected VeriPB line
three stages later, and much cheaper than not meeting it.

The staged method in `dev_docs/constraints.md` ("Bringing up a new constraint")
is what makes this cheap to act on — each stage's gate localises the problem
before you go asking about it.

## Mistakes that have been made here before

Each of these is a real regression or a real wasted afternoon, not a
hypothetical. The reasoning is in the linked document; the instruction is here
so that it is visible without following the link.

- **Do not "tidy" the per-configuration flags in `CMakeLists.txt` into cache
  variables.** A cached `set()` there is a silent no-op, and that is how the
  Sanitize build spent months containing no sanitizers (issue #597). Nor does
  grepping `CMakeCache.txt` tell you which flags are in use — read
  `flags.make`. See [`building.md`](dev_docs/building.md).
- **Do not delete `util/enumerate.hh`.** `std::views::enumerate` is missing
  from libc++, so 46 files depend on it. Same for anything else the tree
  hand-rolls: check [`building.md`](dev_docs/building.md) before replacing it
  with the standard-library spelling.
- **Do not reformat an `overloaded{...}` block by hand.** The empty `//` after
  the opening brace is load-bearing; add it and re-run clang-format. See
  [`code-style.md`](dev_docs/code-style.md), which also has the `using`
  ordering that the tree follows and that is easy to guess wrong.
- **A capped test run does not check completeness.** The data-driven constraint
  tests run with per-solve caps by default, which check soundness and a partial
  proof only. When you have changed a propagator, configure with
  `-DGCS_TEST_CAP_DEFAULTS=OFF` and re-run.
- **Never leave an `AssertRatherThanJustifying` in code you commit.** It emits
  VeriPB's `a` rule, which puts an *unchecked* claim into the proof, so the
  inference is not verified and the proof establishes nothing about it. It is
  legitimate as temporary scaffolding while bringing a propagator up, and
  nothing but you will catch it if it stays: `veripb` exits 0 on an asserted
  proof, so the whole suite stays green. The only signal is `s UNDER ASSERTIONS`
  instead of `s VERIFIED` on a real run. See `constraints.md`, stages 3 and 5.
- **A proof that verifies is not the same as a derivation that is tight.**
  If you are claiming an inference is justified, sabotage the justification and
  check that VeriPB then rejects it — see `constraints.md` (Mutation testing).
- **Removing work is not automatically saving time.** Dropping 9.9M of 17.8M
  propagator calls on `tpp` moved the wall clock by nothing measurable, while
  the same change on a different model was a reproducible 6.9%. Counts, proof
  sizes and wall clock move independently here, and a ratio means nothing
  unless the search shape is identical either side of it. See
  [`propagator-performance.md`](dev_docs/propagator-performance.md) for what to
  measure and [`benchmarking.md`](dev_docs/benchmarking.md) for how.

## Before committing

`CONTRIBUTING.md` is the contract: it covers the policy on AI-assisted
contributions (declare it, with a `Co-Authored-By:` trailer naming the tool),
the clang-format requirement, and what a contribution should pass. Work on a
branch and open a pull request; do not commit to `main`.

```shell
# format (clang-format 21, matching CI)
git ls-files '*.cc' '*.hh' | grep -v '^XCSP3-CPP-Parser/' | xargs clang-format -i

# jobs for ctest; the build presets already parallelise on their own
j=$(nproc 2>/dev/null || sysctl -n hw.logicalcpu)

cmake --preset release  && cmake --build --preset release  && ctest --preset release  -j $j
cmake --preset sanitize && cmake --build --preset sanitize && ctest --preset sanitize -j $j
```

Run a single test binary directly (`./build/equals_test`); the data-driven
constraint tests verify their own proofs whenever `veripb` is on the `PATH`.
[`building.md`](dev_docs/building.md) has the rest: the build options, which
wrapper runs which kind of test, the supported toolchains and their gaps, and
what each CI lane covers.
