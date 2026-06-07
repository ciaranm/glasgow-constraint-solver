#!/bin/bash
#
# Workflow-2 regression check for a curated .scp, fed through glasgow_scp_solver.
# When cake_pb_cp is available it runs the *full verified chain*; when it is not
# (e.g. GitHub CI, where building CakeML is awkward) it degrades to a workflow-1
# self-verify so the case is still exercised rather than skipped.
#
#   1. <solver> --all --prove <scp>    -> <base>.scp (re-emitted, with the final
#                                         (enumerate) / objective element) + .opb + .pbp
#
#   With cake_pb_cp (full workflow 2 -- the verified checker has the last word):
#   2. cake_pb_cp <base>.scp            -> <base>.verifiedopb   (re-derive OPB, verified)
#   3. veripb verifiedopb pbp --elaborate <base>.corepb        (elaborate to a core;
#                                         VeriPB is an *untrusted* translator here)
#   4. cake_pb_cp <base>.scp <base>.corepb                     (verified re-check of the
#                                         core -- "s VERIFIED ...": UNSAT or enumeration)
#   5. opbdiff opb verifiedopb --match-labels [mode]           (label oracle)
#
#   Without cake_pb_cp (fallback): veripb checks the solver's proof against the
#   solver's *own* OPB (workflow 1). The cake re-derivation, the verified core
#   re-check and the opbdiff oracle are skipped (reported).
#
# opbdiff mode (3rd arg): strict | aux | none  (see scp_cases/CMakeLists.txt).
#
# Exits 77 (ctest SKIP_RETURN_CODE) only when VeriPB itself is missing.

set -u

solver=$1
scp=$2
opbdiff_mode=${3:-strict}

export PATH=$HOME/.cargo/bin:$PATH
CAKE_PB_CP=${CAKE_PB_CP:-$HOME/claude/CakePB-dev/cp/cake_pb_cp}

have() { command -v "$1" >/dev/null 2>&1; }
verified() { grep -qE '^s VERIFIED' <<< "$1"; }

[[ -x "$solver" ]] || { echo "SKIP: glasgow_scp_solver not built at '$solver'"; exit 77; }
have veripb || { echo "SKIP: veripb not on PATH"; exit 77; }

base=$(basename "$scp" .scp).chain

set -e

echo "[1] $(basename "$solver") --all --prove $(basename "$scp")"
"$solver" --all --prove --proof-files-basename "$base" "$scp" > /dev/null

if [[ ! -x "$CAKE_PB_CP" ]]; then
    # cake_pb_cp unavailable -- fall back to a workflow-1 self-verify so the case
    # still gets checked (the solver's proof is valid against its own OPB).
    echo "[fallback] cake_pb_cp not found at '$CAKE_PB_CP'; workflow-1 self-verify only"
    out=$(veripb "${base}.opb" "${base}.pbp" 2>&1)
    if ! verified "$out"; then echo "FAIL: self-verify"; tail -5 <<< "$out"; exit 1; fi
    grep -E '^s VERIFIED' <<< "$out"
    rm -f "${base}".{scp,opb,pbp,varmap}
    echo "OK: workflow-1 self-verify passed for $(basename "$scp") (cake_pb_cp absent)"
    exit 0
fi

echo "[2] cake_pb_cp: re-derive OPB from ${base}.scp"
"$CAKE_PB_CP" "${base}.scp" > "${base}.verifiedopb"
[[ -s "${base}.verifiedopb" ]] || { echo "FAIL: cake_pb_cp produced no OPB"; exit 1; }

echo "[3] veripb --elaborate: solver proof against cake's OPB -> core"
out=$(veripb "${base}.verifiedopb" "${base}.pbp" --elaborate "${base}.corepb" 2>&1)
if ! verified "$out"; then echo "FAIL: veripb did not verify"; tail -5 <<< "$out"; exit 1; fi

echo "[4] cake_pb_cp: re-check the elaborated core (the verified step)"
core_out=$("$CAKE_PB_CP" "${base}.scp" "${base}.corepb")
if ! verified "$core_out"; then echo "FAIL: cake_pb_cp rejected the core"; tail -5 <<< "$core_out"; exit 1; fi
echo "$core_out"

echo "[5] opbdiff oracle (mode: $opbdiff_mode)"
if [[ "$opbdiff_mode" == none ]]; then
    echo "      skipped (chain-only case)"
elif have opbdiff; then
    flags=(--match-labels --ignore-no-preserved-in b)
    [[ "$opbdiff_mode" == aux ]] && flags+=(--ignore-aux-names)
    opbdiff "${base}.opb" "${base}.verifiedopb" "${flags[@]}"
else
    echo "      opbdiff absent; the verified chain above is authoritative"
fi

rm -f "${base}".{scp,opb,pbp,verifiedopb,corepb,varmap}
echo "OK: full workflow-2 chain passed for $(basename "$scp") [$opbdiff_mode]"
