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

veripb "${proofname}.opb" "${proofname}.pbp" || exit 1

# Writer/reader symmetry: whatever .scp the run wrote must be one gcs::read_scp
# can rebuild. The chain harness re-solves the .scp as its first step, so a
# constraint whose keyword the reader has never heard of fails the chain long
# after the fact, in a place that looks like a solver bug. Checking it here
# means the example that posts the constraint is what reports it. The constraint
# tests do the same thing in-process (check_scp_writer_reader_symmetry); this
# covers the examples, benchmarks and frontend binaries, which are where the
# less-common constraints actually get posted.
#
# The solver's path comes from scp_solver_path, which CMake generates beside the
# binaries; GCS_SCP_SOLVER overrides it. Both absent (running outside a build
# tree) simply skips the check, as does a run that wrote no .scp.
scp_solver=${GCS_SCP_SOLVER:-}
if [[ -z $scp_solver ]] ; then
    scp_solver_path_file=$(dirname "$prog")/scp_solver_path
    [[ -r $scp_solver_path_file ]] && scp_solver=$(<"$scp_solver_path_file")
fi

# Only exit status 2 -- a keyword read_scp has no case for -- fails the test.
# Status 1 is a keyword it knows in a shape it cannot rebuild: a view operand
# renders as the list `(-X + 17)`, which the grammar does not parse, and that is
# a documented limitation rather than a coverage gap. (It does mean a model
# whose first unreadable thing is a view can hide a bad keyword later in the
# same file; the in-process check in the constraint tests has the same
# property, and between them the constraints are covered either way.)
if [[ -n $scp_solver && -x $scp_solver && -e ${proofname}.scp ]] ; then
    "$scp_solver" --parse-only "${proofname}.scp"
    scp_read_status=$?
    if [[ $scp_read_status -eq 2 ]] ; then
        echo "$0: ${proofname}.scp names a constraint gcs::read_scp cannot read -- see dev_docs/workflow2_testing.md" 1>&2
        exit 1
    fi
fi

# Verification passed, so dispose of the proof unless asked to preserve it.
dispose_proof "$proofname"
