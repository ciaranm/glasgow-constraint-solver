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
before submission, including the full test suite (witth VeriPB installed) in
both modes. See `README.md` for details.
