#!/bin/bash
#
# Drives the full verified-encoding workflow (workflow 2) for a --prove-capable
# example and cross-checks it with opbdiff:
#
#   1. <prog> --prove            -> <name>.scp + <name>.opb + <name>.pbp
#   2. cake_pb_cp <name>.scp     -> <name>.verifiedopb   (re-derive OPB from scp)
#   3. veripb verifiedopb pbp --elaborate corepb         (check solver proof
#                                                         against cake's OPB)
#   4. cake_pb_cp <name>.scp <name>.corepb               (cake checks the core)
#   5. opbdiff <name>.opb <name>.verifiedopb (oracle)    (solver OPB == cake OPB,
#                                                         modulo the preserved set)
#
# Exits 77 (the ctest SKIP_RETURN_CODE for this test) when a *required* external
# tool is missing, so the test is skipped rather than failed on machines without
# cake_pb_cp or veripb. The opbdiff oracle (steps needing opbdiff + jq) is an
# extra cross-check: if those are absent it is reported and skipped, but the cake
# verification in steps 2-4 still runs and is authoritative.

set -u

prog=$1
progname=$(basename "$prog")
shift || true

export PATH=$HOME/.cargo/bin:$PATH

# The prebuilt cake_pb_cp is not generally installed; allow an override.
CAKE_PB_CP=${CAKE_PB_CP:-$HOME/claude/CakePB-dev/cp/cake_pb_cp}

have() { command -v "$1" >/dev/null 2>&1; }

if [[ ! -x "$CAKE_PB_CP" ]]; then
    echo "SKIP: cake_pb_cp not found at '$CAKE_PB_CP' (set CAKE_PB_CP to override)"
    exit 77
fi
if ! have veripb; then
    echo "SKIP: veripb not found on PATH"
    exit 77
fi

set -e

echo "[1/5] $progname --prove"
"$prog" --prove "$@"

echo "[2/5] cake_pb_cp: re-derive OPB from ${progname}.scp"
"$CAKE_PB_CP" "${progname}.scp" > "${progname}.verifiedopb"

echo "[3/5] veripb: elaborate solver proof against cake's OPB"
veripb "${progname}.verifiedopb" "${progname}.pbp" --elaborate "${progname}.corepb"

echo "[4/5] cake_pb_cp: check the elaborated core"
"$CAKE_PB_CP" "${progname}.scp" "${progname}.corepb"

echo "[5/5] opbdiff oracle: solver OPB vs cake OPB"
if have opbdiff; then
    # `--ignore-no-preserved-in b`: cake_pb_cp emits no `preserved:` line (it is
    # file B here), so its one-sided absence is treated as equivalent rather than
    # a difference. Any real disagreement (exit 1) or error (exit 2) then aborts
    # the script via `set -e`, failing the test.
    opbdiff "${progname}.opb" "${progname}.verifiedopb" --unordered --ignore-no-preserved-in b
else
    echo "      opbdiff absent; cake verification above is authoritative"
fi

echo "OK: verified-encoding chain passed for ${progname}"
