#!/bin/bash

# Differential-tests a model against MiniZinc's default solver: runs
# <minizincdir>/tests/<testname>.mzn through both fzn-glasgow and MiniZinc's
# default solver, and diffs the solutions (all of them if <enumeration> is
# true, otherwise just the final objective value). If <doproofs> is true and
# veripb is available, also reruns with --prove and verifies the proof.
# Skips (exit 66, the ctest SKIP_RETURN_CODE) if minizinc is not installed.
#
# Usage: run_minizinc_test.bash <fzn-glasgow> <minizincdir> <testname> <enumeration> <doproofs>

set -euo pipefail

builddir=$(dirname "$1")
minizincdir=$2
testname=$3
enumeration=$4
doproofs=$5

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
sed -e "s|\"executable\": \"fzn-glasgow\"|\"executable\": \"$1\"|" \
    -e "s|\"mznlib\": \"mznlib\"|\"mznlib\": \"$minizincdir/mznlib\"|" \
    "$minizincdir/glasgow-for-tests.msc" > "$solver_msc"

minizinc --solver "$solver_msc" --fzn "$testname.fzn" -a "$minizincdir/tests/$testname.mzn" | tee "$testname.glasgow.out" || exit 1
minizinc -a "$minizincdir/tests/$testname.mzn" | tee "$testname.default.out" || exit 2

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

if [[ "$doproofs" == "true" ]] && veripb --help >/dev/null ; then
    minizinc --solver "$solver_msc" -a "$minizincdir/tests/$testname.mzn" --prove "$testname" | tee "$testname.glasgow.out" || exit 7
    if ! veripb "$testname.opb" "$testname.pbp" ; then
        echo "Rerunning last 100 lines of proof verification in trace mode..."
        echo '$ ' veripb --trace "$(readlink -f "$testname.opb")" "$(readlink -f "$testname.pbp")"
        # the trace rerun fails again by construction; we still want exit 8
        veripb --trace "$testname.opb" "$testname.pbp" 2>&1 | tail -n100 || true
        exit 8
    fi
fi

exit 0
