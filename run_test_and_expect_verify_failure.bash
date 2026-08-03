#!/bin/bash
#
# Usage: run_test_and_expect_verify_failure.bash [--basename NAME] PROGRAM [ARGS...]
#
# The inverse of run_test_and_verify.bash: runs PROGRAM with --prove, then
# checks that veripb *rejects* the resulting proof.
#
# This is for mutation testing. A propagator whose derivation has slack in it
# writes proofs that verify even when one step is deliberately corrupted --- so
# "veripb accepts" on its own says little about whether the honest derivation
# is load-bearing. A test binary run under this harness emits a knowingly wrong
# proof (see e.g. CumulativeProofMutation), and the run passes only if veripb
# says no. If veripb accepts, the honest derivation was slack, and that is a
# finding about the propagator, not about the harness.
#
# PROGRAM must still exit successfully: this checks the proof, not the program,
# and a crash or a failed assertion is a test failure like any other. As in
# run_test_and_verify.bash, pass --basename when several ctest entries share one
# binary, so they do not race over one set of proof files (issue #562); PROGRAM
# must accept --proof-files-basename for the override to work.
#
# The proof files are always disposed of on success (i.e. on rejection), since
# they are exactly the ones we expected to be bad; they are kept when veripb
# unexpectedly accepts, which is when there is something to look at. Set
# GCS_PRESERVE_PROOF_FILES to keep them either way.

set -u

# shellcheck source-path=SCRIPTDIR
# shellcheck source=proof_file_disposal.bash
. "$(dirname "$0")/proof_file_disposal.bash"

basename_override=
if [[ ${1:-} == --basename ]] ; then
    basename_override=$2
    shift 2
fi

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

if veripb "${proofname}.opb" "${proofname}.pbp" ; then
    echo "veripb accepted ${proofname}.pbp, but this proof was deliberately corrupted:" >&2
    echo "the honest derivation it was made from has slack in it." >&2
    exit 1
fi

echo "veripb rejected ${proofname}.pbp, as expected"
dispose_proof "$proofname"
