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
# A leading `--fzn-count N REGEX` (repeatable) is `--fzn-pattern` for a model
# that exercises several shapes of one global at once: the regex must match
# exactly N times in the flattened model, so that one shape being rewritten away
# cannot hide behind another that still reaches the builtin.
#
# A leading `--reference-std` adds MiniZinc's default solver given the standard
# library's decompositions (`-G std`) in place of its own globals. That is the
# independent reading of what the model means, and it is the one to trust on the
# shapes a front end gets wrong --- empty arrays, index sets not starting at 1 ---
# where the default solver's own redefinitions can be wrong too. Where they are
# known to be, a leading `--skip-default-reference` drops the comparison against
# them; it needs `--reference-std`, so that some reference is always left.
#
# A leading `--unsatisfiable` says the model has no solutions: every run must
# report UNSATISFIABLE, where otherwise the Glasgow run must find at least one.
# The default is the guard against a lane degenerating quietly, since a typo
# that makes a model unsatisfiable leaves every solver agreeing; the flag is for
# a shape that is meant to be. MiniZinc's UNSATISFIABLE status is part of what
# is compared either way.
#
# Usage: run_minizinc_test.bash [--fzn-pattern <regex>]... [--fzn-count <n> <regex>]...
#                               [--reference-solver <name>]... [--reference-std]
#                               [--skip-default-reference] [--unsatisfiable]
#                               <fzn-glasgow> <minizincdir>
#                               <testname> <enumeration> <doproofs>
#                              [<solverflags> [<requiredpattern>...]]

set -euo pipefail

fzn_patterns=()
fzn_count_patterns=()
fzn_count_expected=()
reference_solvers=()
reference_std=false
default_reference=true
unsatisfiable=false
while [[ ${1:-} == --* ]] ; do
    case $1 in
        --fzn-pattern) fzn_patterns+=("$2") ; shift 2 ;;
        --fzn-count) fzn_count_expected+=("$2") ; fzn_count_patterns+=("$3") ; shift 3 ;;
        --reference-solver) reference_solvers+=("$2") ; shift 2 ;;
        --reference-std) reference_std=true ; shift ;;
        --skip-default-reference) default_reference=false ; shift ;;
        --unsatisfiable) unsatisfiable=true ; shift ;;
        *) echo "unknown option $1" 1>&2 ; exit 1 ;;
    esac
done

if [[ "$default_reference" == "false" && "$reference_std" == "false" ]] ; then
    echo "--skip-default-reference needs --reference-std, or nothing is left to compare against" 1>&2
    exit 1
fi

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

# The build generates this next to the solver, with absolute paths to that binary
# and to the source tree's mznlib (see minizinc/CMakeLists.txt), so the test runs
# exactly what a user of this build tree would.
solver_msc="$builddir/glasgow.msc"
if ! grep -qF "\"executable\": \"$solverexe\"" "$solver_msc" ; then
    echo "$solver_msc does not name $solverexe as its executable" 1>&2
    exit 1
fi

minizinc --solver "$solver_msc" --fzn "$testname.fzn" -a \
    ${solverflags[@]+"${solverflags[@]}"} "$minizincdir/tests/$testname.mzn" | tee "$testname.glasgow.out" || exit 1
if [[ "$default_reference" == "true" ]] ; then
    minizinc -a "$minizincdir/tests/$testname.mzn" | tee "$testname.default.out" || exit 2
fi

for pattern in ${fzn_patterns[@]+"${fzn_patterns[@]}"} ; do
    if ! grep -Eq -- "$pattern" "$testname.fzn" ; then
        echo "expected flattened model matching '$pattern'; the model was rewritten before it reached the solver"
        exit 10
    fi
done

for i in ${fzn_count_patterns[@]+"${!fzn_count_patterns[@]}"} ; do
    found=$(grep -Eo -- "${fzn_count_patterns[i]}" "$testname.fzn" | wc -l || true)
    if (( found != fzn_count_expected[i] )) ; then
        echo "expected flattened model matching '${fzn_count_patterns[i]}' ${fzn_count_expected[i]} times, not $found; part of the model was rewritten before it reached the solver"
        exit 10
    fi
done

for pattern in ${required_patterns[@]+"${required_patterns[@]}"} ; do
    if ! grep -Eq -- "$pattern" "$testname.glasgow.out" ; then
        echo "expected output matching '$pattern', which the Glasgow run did not produce"
        exit 9
    fi
done

# The solutions a run found, in a canonical order: every ENUMSOL line, sorted,
# or the last OPTSOL line. MiniZinc's UNSATISFIABLE status comes too, so that
# runs which all proved there are none agree, where otherwise they would all
# look empty.
solutions_of() {
    if [[ "$enumeration" == "true" ]] ; then
        grep -E '^(ENUMSOL:|=====UNSATISFIABLE=====$)' < "$1" | sort || true
    else
        { grep '^OPTSOL:' < "$1" | tail -n1 ; grep -x '=====UNSATISFIABLE=====' < "$1" ; } || true
    fi
}

if [[ "$unsatisfiable" == "true" ]] ; then
    if grep -qE '^(ENUMSOL|OPTSOL):' < "$testname.glasgow.out" || ! grep -qx '=====UNSATISFIABLE=====' < "$testname.glasgow.out" ; then
        echo "expected the Glasgow run to report the model unsatisfiable"
        exit 13
    fi
elif [[ "$enumeration" == "true" ]] ; then
    grep -q '^ENUMSOL:' < "$testname.glasgow.out" || exit 3
else
    grep -q '^OPTSOL:' < "$testname.glasgow.out" || exit 5
fi
solutions_of "$testname.glasgow.out" > "$testname.glasgow.sols"

if [[ "$default_reference" == "true" ]] ; then
    # an empty default-solver solution set shows up as a difference here
    solutions_of "$testname.default.out" > "$testname.default.sols"
    if ! diff -u "$testname.glasgow.sols" "$testname.default.sols" ; then
        if [[ "$enumeration" == "true" ]] ; then
            echo "found different enumeration solutions"
            exit 4
        else
            echo "found different objective solutions"
            exit 6
        fi
    fi
fi

if [[ "$reference_std" == "true" ]] ; then
    minizinc -G std -a "$minizincdir/tests/$testname.mzn" | tee "$testname.std.out" || exit 14
    solutions_of "$testname.std.out" > "$testname.std.sols"
    if ! diff -u "$testname.glasgow.sols" "$testname.std.sols" ; then
        echo "found different solutions from the default solver on the standard library's decompositions"
        exit 15
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
    solutions_of "$testname.$reference.out" > "$testname.$reference.sols"
    if ! diff -u "$testname.glasgow.sols" "$testname.$reference.sols" ; then
        echo "found different solutions from reference solver $reference"
        exit 12
    fi
done

# --force-checked-deletion: a failed core deletion check is only a warning by
# default -- VeriPB downgrades to unchecked deletion, drops its
# equi-enumerable / equi-optimal guarantees and still prints `s VERIFIED`.
# The solver deletes `solx` and `soli` constraints, which are exactly the
# deletions that check applies to, so ask for the strict behaviour.
# See dev_docs/solution-clause-deletion.md.
if [[ "$doproofs" == "true" ]] && veripb --help >/dev/null ; then
    minizinc --solver "$solver_msc" -a ${solverflags[@]+"${solverflags[@]}"} "$minizincdir/tests/$testname.mzn" \
        --prove --proof-files-basename "$testname" | tee "$testname.glasgow.out" || exit 7
    if ! veripb --force-checked-deletion "$testname.opb" "$testname.pbp" ; then
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
