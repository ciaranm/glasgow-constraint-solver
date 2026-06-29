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

Have particular care when working with logic. Our experience to date with
Claude is that it knows the C++ libraries and language well, but that it can
make subtle mistakes when dealing with complicated conditions (which show up
quite a lot in propagators). The proof logging code is similarly high-risk.

All contributions should pass both the `release` and `sanitize` build and tests
before submission, including the full test suite (with VeriPB installed) in
both modes. See `README.md` for details.

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

It rejects a commit whose staged files are not formatted, printing the exact
`clang-format -i` command to fix them; `git commit --no-verify` bypasses it for
a one-off. The hook uses `clang-format-21` if present, otherwise `clang-format`,
so install version 21 (CI pins 21.1.8) for results that match CI.

Developer Documentation
=======================

Architectural notes on individual subsystems live in `dev_docs/`. AI agents in
particular should read the relevant document before making non-trivial changes
to a subsystem — this is the most efficient way to absorb the design
decisions and conventions that aren't obvious from the code alone. See
`dev_docs/README.md` for the current index.
