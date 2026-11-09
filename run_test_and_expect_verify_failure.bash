#!/bin/bash
#
# Usage: run_test_and_expect_verify_failure.bash [--basename NAME] --expect REASON PROGRAM [ARGS...]
#
# The inverse of run_test_and_verify.bash: runs PROGRAM with --prove, then
# checks that veripb *rejects* the resulting proof, and rejects it for the
# expected reason.
#
# This is for mutation testing. A propagator whose derivation has slack in it
# writes proofs that verify even when one step is deliberately corrupted --- so
# "veripb accepts" on its own says little about whether the honest derivation
# is load-bearing. A test binary run under this harness emits a knowingly wrong
# proof (see e.g. CumulativeProofMutation), and the run passes only if veripb
# says no. If veripb accepts, the honest derivation was slack, and that is a
# finding about the propagator, not about the harness.
#
# A rejection only counts if it is the one the lane was written for. Two checks
# stand behind that:
#
#  - veripb must have reported a failed step in *this* proof ("Checking error
#    at NAME.pbp:"). A proof file that is missing, empty, truncated, or that does
#    not parse is rejected too, but that is a broken test, not a caught mutation,
#    and on its own the exit code cannot tell the two apart.
#  - veripb's output must contain REASON. Pass the GCS_VERIPB_REJECTS_* variable
#    from the top-level CMakeLists.txt that names the rule the corruption is
#    meant to break, so that a mutation which starts failing somewhere else (a
#    RUP step where a proofgoal was meant to fail, say) is noticed rather than
#    silently counted as caught.
#
# PROGRAM must still exit successfully: this checks the proof, not the program,
# and a crash or a failed assertion is a test failure like any other. As in
# run_test_and_verify.bash, pass --basename when several ctest entries share one
# binary, so they do not race over one set of proof files (issue #562); PROGRAM
# must accept --proof-files-basename for the override to work.
#
# veripb runs with --force-checked-deletion, as in run_test_and_verify.bash, so
# the corrupted proof is checked under the same rules as its honest twin.
#
# The proof files are disposed of when veripb rejects them for the expected
# reason, since they are exactly the ones we expected to be bad; they are kept
# when veripb accepts, or rejects for some other reason, which is when there is
# something to look at. Set GCS_PRESERVE_PROOF_FILES to keep them either way.

set -u

# shellcheck source-path=SCRIPTDIR
# shellcheck source=proof_file_disposal.bash
. "$(dirname "$0")/proof_file_disposal.bash"

basename_override=
expect=
while [[ ${1:-} == --basename || ${1:-} == --expect ]] ; do
    case $1 in
        --basename) basename_override=$2 ;;
        --expect) expect=$2 ;;
    esac
    shift 2
done

if [[ -z $expect ]] ; then
    echo "$0: --expect REASON is required: a mutation lane must say why veripb should reject it" >&2
    exit 1
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

output=$(veripb --force-checked-deletion "${proofname}.opb" "${proofname}.pbp" 2>&1)
status=$?
echo "$output"

if [[ $status -eq 0 ]] ; then
    echo "veripb accepted ${proofname}.pbp, but this proof was deliberately corrupted:" >&2
    echo "the honest derivation it was made from has slack in it." >&2
    exit 1
fi

if ! grep -qF -- "Checking error at ${proofname}.pbp:" <<< "$output" ; then
    echo "veripb rejected ${proofname}.pbp without failing a step of it: the proof is" >&2
    echo "missing, malformed or unreadable, so the mutation was never actually checked." >&2
    exit 1
fi

if ! grep -qF -- "$expect" <<< "$output" ; then
    echo "veripb rejected ${proofname}.pbp, but not for the expected reason." >&2
    echo "wanted output containing: $expect" >&2
    exit 1
fi

echo "veripb rejected ${proofname}.pbp, as expected"
dispose_proof "$proofname"
