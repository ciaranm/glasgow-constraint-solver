#!/bin/bash

# Differential-tests a model against MiniZinc's default solver: runs
# <minizincdir>/tests/<testname>.mzn through both fzn-glasgow and MiniZinc's
# default solver, and diffs the solutions (all of them if <enumeration> is
# true, otherwise just the final objective value). If <doproofs> is true and
# veripb is available, also reruns with --prove and verifies the proof.
# Skips (exit 66, the ctest SKIP_RETURN_CODE) if minizinc is not installed.
#
# <solverflags> is a whitespace-separated list of extra flags handed to
# MiniZinc for the Glasgow run only (they must be declared in the .msc's
# stdFlags or extraFlags for MiniZinc to forward them); the default-solver run
# never sees them. Each <requiredpattern> after it is an extended regex that
# must match at least one line of the Glasgow run's output. That is how a
# feature whose whole effect is invisible from the solution set --- a presolver,
# say --- gets checked at all: it preserves the solutions and leaves the proof
# verifying whether it fired or not, so only its own counters can tell the
# difference.
#
# A leading `--fzn-pattern REGEX` (repeatable) is an extended regex that must
# match the *flattened* model handed to the solver. That is the guard against a
# test passing vacuously against a library decomposition: MiniZinc's global
# wrappers are free to rewrite a constraint into something else entirely before
# any redefinition is consulted, and when they do, the solutions still agree and
# the proof still verifies --- the builtin under test simply never ran.
#
# A leading `--reference-solver NAME` (repeatable) adds another solver to
# differential-test against, on top of MiniZinc's default. Use it where a second
# independent implementation is worth having: Gecode (the default) propagates
# optional tasks natively, while Chuffed falls back to the library
# decomposition, so agreeing with both pins the semantics against a propagator
# and against MiniZinc's own reference reading. A named solver that is not
# installed is reported and skipped rather than failing the test, in the same
# spirit as the veripb check below.
#
# Usage: run_minizinc_test.bash [--fzn-pattern <regex>]... [--reference-solver <name>]...
#                               <fzn-glasgow> <minizincdir>
#                               <testname> <enumeration> <doproofs>
#                              [<solverflags> [<requiredpattern>...]]

set -euo pipefail

fzn_patterns=()
reference_solvers=()
while [[ ${1:-} == --fzn-pattern || ${1:-} == --reference-solver ]] ; do
    case $1 in
        --fzn-pattern) fzn_patterns+=("$2") ;;
        --reference-solver) reference_solvers+=("$2") ;;
    esac
    shift 2
done

# shellcheck source-path=SCRIPTDIR
# shellcheck source=../proof_file_disposal.bash
. "$(dirname "$0")/../proof_file_disposal.bash"

solverexe=$1
builddir=$(dirname "$1")
minizincdir=$2
testname=$3
enumeration=$4
doproofs=$5
read -r -a solverflags <<< "${6:-}"
shift $(( $# < 6 ? $# : 6 ))
required_patterns=("$@")

export PATH="$builddir:$HOME/.local/bin:$PATH"

if ! command -v minizinc ; then
    echo "can't run minizinc, skipping test" 1>&2
    exit 66
fi

# MiniZinc resolves the solver executable named in the .msc; a bare name relying on
# PATH is not enough on Windows (it is not found / spawned as .exe), so generate a
# config pointing at the absolute path of the built solver ($1, which already
# carries the .exe suffix on Windows) with an absolute mznlib. Same result on Unix.
solver_msc="$testname.glasgow.msc"
sed -e "s|\"executable\": \"fzn-glasgow\"|\"executable\": \"$solverexe\"|" \
    -e "s|\"mznlib\": \"mznlib\"|\"mznlib\": \"$minizincdir/mznlib\"|" \
    "$minizincdir/glasgow-for-tests.msc" > "$solver_msc"

minizinc --solver "$solver_msc" --fzn "$testname.fzn" -a \
    ${solverflags[@]+"${solverflags[@]}"} "$minizincdir/tests/$testname.mzn" | tee "$testname.glasgow.out" || exit 1
minizinc -a "$minizincdir/tests/$testname.mzn" | tee "$testname.default.out" || exit 2

for pattern in ${fzn_patterns[@]+"${fzn_patterns[@]}"} ; do
    if ! grep -Eq -- "$pattern" "$testname.fzn" ; then
        echo "expected flattened model matching '$pattern'; the model was rewritten before it reached the solver"
        exit 10
    fi
done

for pattern in ${required_patterns[@]+"${required_patterns[@]}"} ; do
    if ! grep -Eq -- "$pattern" "$testname.glasgow.out" ; then
        echo "expected output matching '$pattern', which the Glasgow run did not produce"
        exit 9
    fi
done

if [[ "$enumeration" == "true" ]] ; then
    grep -q '^ENUMSOL:' < "$testname.glasgow.out" || exit 3
    grep '^ENUMSOL:' < "$testname.glasgow.out" | sort > "$testname.glasgow.sols"
    # tolerate grep finding nothing: an empty default-solver solution set
    # shows up as a difference in the diff below
    grep '^ENUMSOL:' < "$testname.default.out" | sort > "$testname.default.sols" || true

    if ! diff -u "$testname.glasgow.sols" "$testname.default.sols" ; then
        echo "found different enumeration solutions"
        exit 4
    fi
else
    grep -q '^OPTSOL:' < "$testname.glasgow.out" || exit 5
    grep '^OPTSOL:' < "$testname.glasgow.out" | tail -n1 > "$testname.glasgow.sols"
    grep '^OPTSOL:' < "$testname.default.out" | tail -n1 > "$testname.default.sols" || true

    if ! diff -u "$testname.glasgow.sols" "$testname.default.sols" ; then
        echo "found different objective solutions"
        exit 6
    fi
fi

for reference in ${reference_solvers[@]+"${reference_solvers[@]}"} ; do
    # `--solver NAME --version` reports the *driver's* version and succeeds
    # whatever NAME is, so ask the solver list instead. The tags in parentheses
    # on each line are what --solver matches against.
    if ! minizinc --solvers 2>/dev/null | grep -Fq "$reference" ; then
        echo "reference solver $reference is not installed, skipping that comparison"
        continue
    fi
    minizinc --solver "$reference" -a "$minizincdir/tests/$testname.mzn" | tee "$testname.$reference.out" || exit 11
    if [[ "$enumeration" == "true" ]] ; then
        grep '^ENUMSOL:' < "$testname.$reference.out" | sort > "$testname.$reference.sols" || true
    else
        grep '^OPTSOL:' < "$testname.$reference.out" | tail -n1 > "$testname.$reference.sols" || true
    fi
    if ! diff -u "$testname.glasgow.sols" "$testname.$reference.sols" ; then
        echo "found different solutions from reference solver $reference"
        exit 12
    fi
done

if [[ "$doproofs" == "true" ]] && veripb --help >/dev/null ; then
    minizinc --solver "$solver_msc" -a ${solverflags[@]+"${solverflags[@]}"} "$minizincdir/tests/$testname.mzn" \
        --prove --proof-files-basename "$testname" | tee "$testname.glasgow.out" || exit 7
    if ! veripb "$testname.opb" "$testname.pbp" ; then
        echo "Rerunning last 100 lines of proof verification in trace mode..."
        echo '$ ' veripb --trace "$(readlink -f "$testname.opb")" "$(readlink -f "$testname.pbp")"
        # the trace rerun fails again by construction; we still want exit 8
        veripb --trace "$testname.opb" "$testname.pbp" 2>&1 | tail -n100 || true
        exit 8
    fi

    # Verification passed, so dispose of the proof unless asked to preserve it;
    # the failure path above exits first, leaving a failing proof to inspect.
    dispose_proof "$testname"
fi

exit 0
