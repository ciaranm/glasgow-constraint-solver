Policy on AI Agents
===================

This policy is experimental and is subject to change at the whims of the
maintainers.

Use of AI agents is permitted, but must be declared explicitly. Any submitted
contribution made with the assistance of an AI agent must have been carefully
checked by a qualified human. All contributions will additionally need to be
reviewed by one of the maintainers before merge, which we are happy to do, but
we do not have unlimited time to spend on low-effort, automated submissions.

Declare AI use in the commit message (a `Co-Authored-By:` trailer naming the
tool and version is appropriate) and in the pull request description. Reviewers
should be able to see at a glance that AI was involved and which tool was used.

"Carefully checked by a qualified human" means the human can explain why each
change is correct---not merely that it compiles and passes tests. Rubber-stamping
AI output without understanding it is not acceptable.

All contributions should pass both the `release` and `sanitize` build and tests
before submission, including the full test suite (with VeriPB installed) in
both modes. See `README.md` for the build and test commands, and
`dev_docs/building.md` for the build options, the supported toolchains, and
what each CI lane covers. Note that a default build applies
per-solve caps to the data-driven constraint tests, which check soundness and a
partial proof but not completeness; when you have changed a propagator,
configure with `-DGCS_TEST_CAP_DEFAULTS=OFF` so that they enumerate fully, as
the two default-GCC Ubuntu CI lanes do.

What agents are currently good and bad at here
----------------------------------------------

If you want a global constraint this solver does not have, this section is aimed
at you: the answer to "could I get an agent to write it, and would that be worth
anyone's time?" has changed recently enough to be worth writing down. It is not
an invitation to send us unsupervised output --- what makes a contribution like
that reviewable is the supervision described here, not the model that wrote it.

This is a moving target, so it is dated, and it is one project's experience
rather than a study. As of September 2026:

**Implementing a global constraint is now a reasonable thing to attempt with an
agent, under supervision.** We have found that Claude Opus 5, run at the `xhigh`
reasoning effort, is generally able to implement a propagator from the
literature --- read the paper, get the algorithm right, encode it in PB, and
certify it --- provided two things hold.

The first is that it works in *stages* rather than trying to land a whole
constraint at once. `dev_docs/constraints.md` ("Bringing up a new constraint")
sets out the staging we have found works: the encoding certified on its own
before any propagation exists, the intended consistency level written into the
tests before anything can pass it, then propagation, then the proofs. The gate
at the end of each stage is what keeps a mistake attributable to the piece that
caused it, which is most of the value.

The second is that it actually reads the developer documentation for whatever it
is touching. Most of what goes wrong when it does not is a convention or an
invariant that *is* written down in `dev_docs/` and was not read. This is the
single biggest lever, and it is why those documents exist in the form they do.

**The weak spot is novel proof technique.** Reproducing a proof shape the tree
already uses is reliable. Devising a new one is not: that is where you get
derivations which verify but are needlessly baroque, or which lean on a step
that happens to hold for the instance in front of them. Two triggers to watch
for --- the constraint needs a technique that is not already somewhere in
`dev_docs/`, or the technique it did use looks inelegant or suspicious to you.

When either fires, what we have found effective is to tell Opus to **spawn a
subagent on the Fable model as a critical proofs consultant, with narrow
instructions**: one derivation, one question, and an instruction to attack the
argument rather than to write code. It is good at that, and it is a good use of
tokens --- considerably cheaper than finding the same problem from a rejected
VeriPB line three stages later, and much cheaper than not finding it.

**The older warning still holds where it always did.** Claude knows the C++
language and libraries well, but makes subtle mistakes in complicated
conditions, which propagators are full of. Read the branch structure yourself,
particularly around the edge cases a paper glosses over.

**Two things to check by hand, because nothing else will.** That no
`AssertRatherThanJustifying` survives into the submission: an asserted proof
still exits successfully, so the test suite passes with the cheats in, and only
the `s UNDER ASSERTIONS` line on a real run gives it away (see
`dev_docs/constraints.md`, "Bringing up a new constraint", stage 5). And that
the consistency level claimed in the class comment is the one the tests
actually check, with the caps off.

None of this changes what you take on by submitting the work: you still have to
be able to explain why each change is correct.

Licensing
=========

The solver is dual licensed under the Apache License, Version 2.0 and the MIT
License, at the user's option; see `COPYRIGHT` for the full statement. Unless
you explicitly state otherwise, any contribution you intentionally submit for
inclusion in this work, as defined in the Apache License, Version 2.0, shall be
dual licensed as above, without any additional terms or conditions. There is no
copyright assignment: you keep the copyright in what you write.

If a contribution contains code you did not write yourself, say where it came
from and under what terms in the pull request, so that we can check it can be
released both ways before merging.

Code Formatting
===============

All C++ source is formatted with
[clang-format](https://clang.llvm.org/docs/ClangFormat.html) using the
`.clang-format` in the repository root. Use **clang-format 21**: formatting
output can differ between major releases, and CI pins this version, so a
different one will report spurious changes.

Format the whole tree before submitting:

```shell
git ls-files '*.cc' '*.hh' | grep -v '^XCSP3-CPP-Parser/' | xargs clang-format -i
```

The `clang-format` CI workflow runs `clang-format --dry-run --Werror` over the
same files on every push and pull request, so an unformatted contribution will
fail the check.

To catch this locally before CI does, a `pre-commit` hook that runs the same
check over the staged C++ is tracked in `.githooks/`. Enable it once per clone:

```shell
git config core.hooksPath .githooks
```

`clang-format` settles only the mechanical questions. The conventions it does
not enforce --- the ordering of the `using` block, `using enum` placement, the
`//` that pins an `overloaded{...}` visitor, the `#if` guard around `format()`
--- are written down in `dev_docs/code-style.md`.

It rejects a commit whose staged files are not formatted, printing the exact
`clang-format -i` command to fix them; `git commit --no-verify` bypasses it for
a one-off. The hook uses `clang-format-21` if present, otherwise `clang-format`,
so install version 21 (CI pins 21.1.8) for results that match CI --- and note
that if neither is on `PATH` the hook warns and lets the commit through, so an
installed clang-format is what makes it a check at all. It also only sees what
is staged, whereas CI formats the whole tree; the two agree on a clean tree, but
run the command above by hand if you are unsure.

Branches and History
====================

A pull request's MERGED status is **not** a reliable signal that its content is
in `main`, and stacked pull requests are how that goes wrong. A PR based on
another branch rather than on `main` is merged *into that branch*, and GitHub
marks it MERGED at that point — whether or not the parent ever carries it the
rest of the way. If the parent is then merged from a commit that predates the
child, or is merged and the stack is not re-pushed, the child's content never
reaches `main` while its PR page says it did. PR #261 is the worked example: it
read MERGED while the example it added was absent from `main` entirely, because
`main`'s merge of its parent stopped one commit short of it.

To decide whether a branch's content has landed, ask the content rather than the
PR status:

```shell
git merge-base --is-ancestor origin/<branch> origin/main   # exit 0: it is in
git cherry origin/main origin/<branch>                     # no '+' lines: it is in
```

A branch that GitHub calls merged but that still has `+` lines needs its unique
commits diffing against `main` by hand: it may have been squash-merged (fine) or
it may be carrying commits that were dropped along the way.

Before deleting a remote branch, check that no open pull request is based on it
(`gh pr list --base <branch> --state open`). Deleting a branch that is an open
PR's base **closes that PR**; GitHub does not retarget it, and the close is not
reversible by recreating the branch.

Developer Documentation
=======================

Architectural notes on individual subsystems live in `dev_docs/`. AI agents in
particular should read the relevant document before making non-trivial changes
to a subsystem — this is the most efficient way to absorb the design
decisions and conventions that aren't obvious from the code alone. See
`dev_docs/README.md` for the current index.
