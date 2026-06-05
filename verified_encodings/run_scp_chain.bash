#!/bin/bash
#
# Workflow-2 regression check for a curated .scp, fed through glasgow_scp_solver:
#
#   1. <solver> --all --prove <scp>   -> <base>.scp (re-emitted, with the final
#                                        (enumerate) / objective element) + .opb + .pbp
#   2. cake_pb_cp <base>.scp           -> <base>.verifiedopb   (re-derive OPB)
#   3. veripb verifiedopb pbp          -> expect "s VERIFIED ..." (UNSAT *or*
#                                        complete enumeration -- the (enumerate)
#                                        element makes cake emit `preserved:`, so
#                                        SAT/enumeration proofs verify too)
#   4. opbdiff opb verifiedopb --match-labels [mode]   (label oracle: solver OPB
#                                        agrees with cake's, by @label)
#
# opbdiff mode (3rd arg): strict | aux | none
#   strict : --match-labels                       (expect semantically equivalent)
#   aux    : --match-labels --ignore-aux-names     (a constraint-local flag's name
#                                                   differs, e.g. all_different /
#                                                   not_equals selectors)
#   none   : skip opbdiff (chain only -- e.g. a reified form whose [0,1] condition
#            variable hits the direct-vs-bits divergence)
#
# Exits 77 (ctest SKIP_RETURN_CODE) when a required external tool is missing.

set -u

solver=$1
scp=$2
opbdiff_mode=${3:-strict}

export PATH=$HOME/.cargo/bin:$PATH
CAKE_PB_CP=${CAKE_PB_CP:-$HOME/claude/CakePB-dev/cp/cake_pb_cp}

have() { command -v "$1" >/dev/null 2>&1; }

[[ -x "$solver" ]] || { echo "SKIP: glasgow_scp_solver not built at '$solver'"; exit 77; }
[[ -x "$CAKE_PB_CP" ]] || { echo "SKIP: cake_pb_cp not found at '$CAKE_PB_CP' (set CAKE_PB_CP)"; exit 77; }
have veripb || { echo "SKIP: veripb not on PATH"; exit 77; }

base=$(basename "$scp" .scp).chain

set -e

echo "[1/4] $(basename "$solver") --all --prove $(basename "$scp")"
"$solver" --all --prove --proof-files-basename "$base" "$scp" > /dev/null

echo "[2/4] cake_pb_cp: re-derive OPB from ${base}.scp"
"$CAKE_PB_CP" "${base}.scp" > "${base}.verifiedopb"
[[ -s "${base}.verifiedopb" ]] || { echo "FAIL: cake_pb_cp produced no OPB"; exit 1; }

echo "[3/4] veripb: check solver proof against cake's OPB"
veripb_out=$(veripb "${base}.verifiedopb" "${base}.pbp" 2>&1)
if ! grep -qE '^s VERIFIED' <<< "$veripb_out"; then
    echo "FAIL: veripb did not verify"; tail -5 <<< "$veripb_out"; exit 1
fi
grep -E '^s VERIFIED' <<< "$veripb_out"

echo "[4/4] opbdiff oracle (mode: $opbdiff_mode)"
if [[ "$opbdiff_mode" == none ]]; then
    echo "      skipped (chain-only case)"
elif have opbdiff; then
    flags=(--match-labels --ignore-no-preserved-in b)
    [[ "$opbdiff_mode" == aux ]] && flags+=(--ignore-aux-names)
    # opbdiff exits 1 on a real difference; set -e then fails the test.
    opbdiff "${base}.opb" "${base}.verifiedopb" "${flags[@]}"
else
    echo "      opbdiff absent; the veripb chain above is authoritative"
fi

rm -f "${base}".{scp,opb,pbp,verifiedopb,varmap}
echo "OK: workflow-2 chain passed for $(basename "$scp") [$opbdiff_mode]"
