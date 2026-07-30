# Developer tools

Scripts that support development but are not built, installed, or run by
the test suite.

## opb_snapshot.bash

Snapshots every registered example test's OPB definition, for byte-diffing a
refactor that is meant to leave the encoding alone. Runs each test with
`--prove`, keeps that run's `.opb` and `.scp`, and deletes the `.pbp` and
`.varmap` immediately: neither the `.opb` nor the `.scp` is branching-seed
dependent, so two snapshots either side of an output-preserving change should
diff empty, while the proof itself would differ on seed alone. Any binary whose
help mentions `--seed` is given one, so the examples that build a random
instance are pinned rather than skipped.

Run from the repository root after a build, once either side of the change:

```shell
./tools/opb_snapshot.bash /tmp/opb-before
# make the change, rebuild
./tools/opb_snapshot.bash /tmp/opb-after
diff -rq /tmp/opb-before /tmp/opb-after
```

Naming ctest targets as extra arguments snapshots only those. This is a
developer tool, not a ctest: it is never run by the test suite.

## capture_encodings.py

Runs the data-driven constraint test binaries found under `./build` and
captures the `.scp` encoding reports they emit, together with metadata
(constraint type, configuration, expected solution count, VeriPB result),
into structured reports under `./build/scp_capture`. Used when checking
OPB encoding conformance against the verified CakePB encodings (see
`verified_encodings/`).

Run from the repository root after a build:

```shell
python3 tools/capture_encodings.py
```
