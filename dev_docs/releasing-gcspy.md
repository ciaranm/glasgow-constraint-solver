# Releasing gcspy (the Python bindings)

`gcspy` is the pybind11 module built from `python/gcspy.cc`, published to
[PyPI](https://pypi.org/project/gcspy/). This note is the procedure for cutting
a release. It exists because none of it is derivable from the code: the version
lives in one file, the compiler floor makes portable wheels awkward, and the
publish path relies on out-of-repo configuration on PyPI.

The whole thing is driven by
[`.github/workflows/release-gcspy.yml`](../.github/workflows/release-gcspy.yml).
Read that file alongside this note — the comments there explain each job; this
note explains the *why* and the human steps around it.

## What a release produces

- **An sdist** (`gcspy-X.Y.Z.tar.gz`) — the portable artifact. `python/`'s
  `cmake.source-dir` is the repo root, so the tarball bundles the entire solver
  source, and anyone with a supported compiler (GCC ≥ 13 / clang 21) can
  `pip install gcspy` and build it. This is the guaranteed path: every user not
  covered by a prebuilt wheel gets this.
- **Wheels** for macOS (arm64 + x86_64) and manylinux_2_28 x86_64, CPython
  3.10–3.13. Convenience only — a wheel just spares the user the compile. They
  are **best-effort**: a wheel lane failing does not block the release; the
  sdist plus whatever wheels succeeded still ship.

There are no Windows or Linux-aarch64 wheels, and no PyPy/musl wheels. Those
users compile from the sdist. Widen `CIBW_BUILD` / the job matrix if that
changes.

## The compiler floor (why Linux wheels are fiddly)

The solver is bleeding-edge C++23. The default toolchain inside a manylinux
image is far too old. The workflow therefore builds Linux wheels in the
`manylinux_2_28` image (AlmaLinux 8), `dnf install`s **gcc-toolset-13** (GCC 13
is the oldest compiler this project supports — see `CLAUDE.md`), and points
`CC`/`CXX` at it. It also passes `-static-libstdc++ -static-libgcc` so the
extension does not depend on a newer `libstdc++` than the `manylinux_2_28`
policy guarantees on the user's machine. If a future compiler bump raises the
floor above GCC 13, bump the `gcc-toolset-NN` version (14 is also available in
AlmaLinux 8; beyond that you may need a newer manylinux image).

macOS builds with the runner's Apple Clang + libc++. C++23 pieces libc++ lacks
(`<generator>`, `<print>`) fall back to the bundled `fmt` / `generator`
polyfills via `FetchContent`, so no special compiler wrangling is needed there.

## Step-by-step: cutting a release

1. **Bump the version.** Edit `version` in `python/pyproject.toml`. This string —
   not the git tag — is what gets published. Check PyPI first: versions are
   immutable and cannot be reused, so a collision means the upload is rejected.
   (E.g. 0.1.9 was published by hand before the CI existed while the repo still
   read 0.1.8; the first CI release skipped to 0.1.10.)
2. **Commit** the bump on `main` (or via PR).
3. **Dry-run on TestPyPI.** Actions → *Release gcspy* → *Run workflow*, leave the
   target as `testpypi`. This builds the sdist and all wheels and uploads them to
   [test.pypi.org](https://test.pypi.org/project/gcspy/). Confirm the artifact
   list looks right and, ideally, `pip install -i https://test.pypi.org/simple/
   gcspy==X.Y.Z` in a clean venv.
4. **Release for real** by pushing a tag matching `gcspy-v*`:
   ```shell
   git tag gcspy-v0.1.10
   git push origin gcspy-v0.1.10
   ```
   A tag push publishes to the real PyPI. (Alternatively, *Run workflow* with the
   target set to `pypi`.)
5. **Verify** it installs: `pip install gcspy==X.Y.Z` in a clean environment.

Keep the tag and the `pyproject.toml` version in step — the workflow publishes
the file's version regardless of the tag string, so a mismatched tag just
mislabels the git history.

## Authentication: Trusted Publishing (one-time PyPI setup)

The workflow uses PyPI **Trusted Publishing** (OIDC): there is no API token
stored in the repo. PyPI is configured once to trust this repository + workflow
+ environment, and GitHub mints a short-lived credential per run. This is
deliberately the low-maintenance option — nothing to rotate, and nothing that
belongs to one person.

To set it up (needed once per index, by a PyPI project owner):

1. On [pypi.org](https://pypi.org/manage/project/gcspy/settings/publishing/) →
   the `gcspy` project → *Settings* → *Publishing* → *Add a new publisher*
   (GitHub Actions):
   - **Owner / repository**: this repo.
   - **Workflow name**: `release-gcspy.yml`.
   - **Environment**: `pypi`.
2. Repeat on [test.pypi.org](https://test.pypi.org/) with environment `testpypi`
   if you want the TestPyPI dry-run to work.
3. Optionally create matching GitHub *Environments* named `pypi` and `testpypi`
   (repo → Settings → Environments) and add required reviewers to `pypi` so a
   real publish needs a human approval click.

**Token fallback.** If you would rather use a stored API token (e.g. before
Trusted Publishing is set up), store it as the `PYPI_API_TOKEN` repo secret and
follow the commented instructions at the bottom of the workflow. This is the
worse option for the long term: the token is a long-lived secret tied to whoever
created it, and it must be rotated when they leave.

## When a wheel build goes red

Wheels are best-effort, so a red lane still lets the sdist publish — but you'll
want to fix it. The Linux lane is the usual suspect (manylinux image contents
and the C++23 frontier both drift). To iterate without cutting a release, use
*Run workflow* against `testpypi` and read the failing job's log. The build runs
`cibuildwheel` over the sdist tarball, so anything that reproduces locally does
so with `pipx run cibuildwheel <sdist>.tar.gz` and the same `CIBW_*` environment
the workflow sets. Common fixes: bump `gcc-toolset-NN`, move to a newer
`manylinux_2_XX` image, or (last resort) drop a platform from the matrix and let
its users compile from the sdist until it can be restored.
