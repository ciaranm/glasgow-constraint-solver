#!/bin/bash
#
# Usage: run_checkpoint_recovery_leak_check.bash SOLVER MODEL.scp [prefix|whole]
#
# Issue #780: check that Cumulative's start-checkpoint recovery never leans on a
# per-time capacity row.
#
# The recovery derives the per-time capacity rows from the start-checkpoint
# ones, and the whole point of it is that it keeps working once the per-time
# block is deleted from the model. While both blocks are there, an ordinary run
# says nothing about whether it does: the recovery's `rup` steps propagate over
# the entire database, so one of them could be closing against the very row it
# claims to be deriving, and the proof would verify just the same. Every `pol`
# in it is safe --- a pol names its operands --- but the rups are not.
#
# So: solve under GCS_CUMULATIVE_ENCODING=both-recovering, cut the proof at the
# marker the recovery emits when it finishes, and re-check that prefix against
# an OPB with every per-time capacity row stripped out. Anything the recovery
# took from one of those rows fails here, and nothing else does.
#
# In `whole` mode the proof is not cut at all, so what is checked is the *whole*
# certificate standing without the per-time block --- which is the end state
# #780 is walking towards, and which only holds for a model whose every firing
# rule has been moved over to the recovered rows. Today that is the time-table
# overflow contradiction and nothing else, so a `whole` model has to be one that
# fires only that. Each rule moved over is another model that can go in here.
#
# Exits 77 (ctest SKIP_RETURN_CODE) when veripb is missing.

set -u

# shellcheck source-path=SCRIPTDIR
# shellcheck source=proof_file_disposal.bash
. "$(dirname "$0")/proof_file_disposal.bash"

solver=$1
scp=$2
mode=${3:-prefix}

export PATH=$HOME/.cargo/bin:$PATH

[[ -x "$solver" ]] || { echo "SKIP: solver not built at '$solver'"; exit 77; }
command -v veripb >/dev/null 2>&1 || { echo "SKIP: veripb not on PATH"; exit 77; }

base=$(basename "$scp" .scp).leakcheck

GCS_CUMULATIVE_ENCODING=both-recovering "$solver" --all --prove --proof-files-basename "$base" "$scp" > /dev/null || {
    echo "FAIL: the solve itself failed"; exit 1; }

# Where the recovery finished. Its absence means the recovery never ran, which
# would make everything below pass while checking nothing --- the one way this
# test could go quietly vacuous, so it is an error and not a skip.
ends=$(grep -n '^% #780 checkpoint recovery ends$' "${base}.pbp" | tail -1 | cut -d: -f1)
[[ -n $ends ]] || { echo "FAIL: no recovery in ${base}.pbp; does the model qualify for it?"; exit 1; }

if [[ $mode == whole ]] ; then
    cp "${base}.pbp" "${base}.prefix.pbp"
else
    head -n "$ends" "${base}.pbp" > "${base}.prefix.pbp"
    printf 'output NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n' >> "${base}.prefix.pbp"
fi

# And that it recovered something: one implication check per row it derived.
checks=$(grep -c '^ia ' "${base}.prefix.pbp")
[[ $checks -gt 0 ]] || { echo "FAIL: the recovery derived no rows, so this checks nothing"; exit 1; }

# In whole mode, that no rule cited a per-time row behind the recovery's back.
# veripb would say so anyway --- the label is gone from the model it is given
# --- but saying it here names what went wrong.
if [[ $mode == whole ]] ; then
    cites=$(grep -c '@c\[[^]]*\]\[cap_' "${base}.pbp")
    if [[ $cites -gt 0 ]] ; then
        echo "FAIL: ${cites} citations of a per-time capacity row; this model fires a rule that has not moved over"
        exit 1
    fi
fi

# `[cap_` does not match `[scap_`, so the start-checkpoint rows stay.
grep -v '\[cap_' "${base}.opb" > "${base}.nocap.opb"

# If that stripped nothing, the label has moved and this check is vacuous.
if [[ $(wc -l < "${base}.opb") -le $(wc -l < "${base}.nocap.opb") ]] ; then
    echo "FAIL: no per-time capacity rows were stripped; has the cap_<t> label changed?"
    exit 1
fi

out=$(veripb "${base}.nocap.opb" "${base}.prefix.pbp" 2>&1)
if ! grep -qE '^s VERIFIED' <<< "$out"; then
    echo "FAIL: the recovery does not stand without the per-time capacity rows"
    tail -8 <<< "$out"
    exit 1
fi

echo "OK (${mode}): ${checks} recovered rows, all standing without a per-time capacity row in the model"
rm -f "${base}.prefix.pbp" "${base}.nocap.opb"
dispose_proof "${base}"
