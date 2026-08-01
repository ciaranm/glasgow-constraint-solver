#!/bin/bash
#
# Usage: run_test_and_expect_rejection.bash [--basename NAME] --expect SUBSTRING PROGRAM [ARGS...]
#
# Runs PROGRAM with --prove, then checks that veripb REJECTS the resulting proof,
# with SUBSTRING somewhere in its output.
#
# This is the must-fail control harness. A test that only ever checks that a proof
# verifies cannot tell a working mechanism from one that has quietly stopped
# constraining anything: the proof of a solver that deleted nothing, or hoisted
# nothing, verifies perfectly well. A control pairs the positive scenario with a
# deliberately broken one and insists VeriPB says so.
#
# Both halves of the check matter. The exit code alone would be satisfied by a
# crash in PROGRAM, a missing input file, or a proof VeriPB could not even parse,
# any of which would let a genuinely broken mechanism sit green forever; hence
# --expect, which pins the rejection to the reason the control was written for.
# (This is the discipline the standalone drivers under
# order-encoding-deletion-artifacts/ use -- see their run.sh -- brought into the
# suite.) PROGRAM itself must still exit 0: it is expected to write a proof, not
# to fail.
#
# See run_test_and_verify.bash for --basename, which exists for the same reason
# here: a scenario-per-ctest-entry test would otherwise race over one set of proof
# files under a parallel ctest (issue #562).
#
# Proof-file disposal follows the same policy as the positive harness, with the
# outcomes the other way up: the proof is deleted once it has been rejected as
# expected, and kept when it was not, which is the case someone will want to
# inspect.

set -u

# shellcheck source-path=SCRIPTDIR
# shellcheck source=proof_file_disposal.bash
. "$(dirname "$0")/proof_file_disposal.bash"

basename_override=
if [[ ${1:-} == --basename ]] ; then
    basename_override=$2
    shift 2
fi

if [[ ${1:-} != --expect ]] ; then
    echo "$0: --expect SUBSTRING is required: a control must say what it expects to be rejected with" 1>&2
    exit 1
fi
expect=$2
shift 2

prog=$1
shift

progname=$(basename "$prog")
progname=${progname%.exe}

proofname=${basename_override:-$progname}

export PATH=$HOME/.cargo/bin:$PATH

if [[ -n $basename_override ]] ; then
    "$prog" --prove --proof-files-basename "$proofname" "$@" || exit 1
else
    "$prog" --prove "$@" || exit 1
fi

# -c for the same reason the positive harness passes it: a failed deletion stops at the
# deletion rather than at some distant conclusion. See run_test_and_verify.bash.
output=$(veripb -c "${proofname}.opb" "${proofname}.pbp" 2>&1)
status=$?

if [[ $status -eq 0 ]] ; then
    echo "$0: veripb ACCEPTED ${proofname}.pbp, but this is a control that must be rejected." 1>&2
    echo "$0: the mechanism under test has stopped constraining anything -- fix the code, do not relax the control." 1>&2
    echo "$output" 1>&2
    exit 1
fi

if ! grep -qF -- "$expect" <<< "$output" ; then
    echo "$0: veripb rejected ${proofname}.pbp, but not for the expected reason." 1>&2
    echo "$0: wanted output containing: $expect" 1>&2
    echo "$output" 1>&2
    exit 1
fi

# Rejected, as intended, so dispose of the proof unless asked to preserve it.
dispose_proof "$proofname"
