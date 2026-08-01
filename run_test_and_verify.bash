#!/bin/bash
#
# Usage: run_test_and_verify.bash [--basename NAME] PROGRAM [ARGS...]
#
# Runs PROGRAM with --prove, then checks the resulting proof with veripb.
#
# The proof basename defaults to PROGRAM's filename stem, which is what the
# binaries themselves default to. Pass --basename to override it: several
# examples are registered as more than one ctest entry with different options,
# and without distinct basenames those entries race over a single set of proof
# files under a parallel ctest, leaving whichever ran last (issue #562).
# PROGRAM must accept --proof-files-basename for the override to work, which
# every example, benchmark and frontend binary now does; the gcs innards tests,
# which hardcode their proof name and take no options, just use the default.
#
# On success the proof files are deleted, matching what the constraint test
# harness does internally (see verify_proof_and_clean_up in
# gcs/constraints/innards/constraints_test_utils.hh): proofs are large, and a
# full parallel ctest that kept them all could exhaust the disk mid-run and
# make an unrelated lane's proof write fail. They are always kept when veripb
# fails, so a failing proof can be inspected. Set GCS_PRESERVE_PROOF_FILES to a
# non-empty value other than 0 to keep them on success too.

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
# On Windows the target file ends in .exe, but the test binaries name their proof
# files after the plain stem (e.g. ProofOptions{"range_witness_w1_test"}), so strip
# the suffix to find name.opb / name.pbp rather than name.exe.opb.
progname=${progname%.exe}

proofname=${basename_override:-$progname}

export PATH=$HOME/.cargo/bin:$PATH

if [[ -n $basename_override ]] ; then
    "$prog" --prove --proof-files-basename "$proofname" "$@" || exit 1
else
    "$prog" --prove "$@" || exit 1
fi

# -c (--force-checked-deletion) is not a soundness requirement: VeriPB's default is to
# downgrade a failed deletion check rather than accept it, and it then enforces the downgrade
# at exactly the conclusions that need it. It is a DIAGNOSTIC requirement. Without it a bad
# deletion surfaces at some later conclusion -- "claimed upper bound mismatches the best
# recorded", or a constraint that has already been deleted -- a long way from the line that
# caused it. With it, the run stops at the deletion. Order-encoding deletion emits deletions
# by the thousand, so that distance is the difference between a diagnosable failure and a
# puzzle. See dev_docs/brancher-design.md, "Validated delc mechanics".
veripb -c "${proofname}.opb" "${proofname}.pbp" || exit 1

# Verification passed, so dispose of the proof unless asked to preserve it.
dispose_proof "$proofname"
