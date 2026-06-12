# Developer tools

Scripts that support development but are not built, installed, or run by
the test suite.

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
