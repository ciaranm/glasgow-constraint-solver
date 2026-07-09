#!/bin/bash
#
# Cache-based XCSP3 test runner. Two modes, selected by which cache file
# exists under tests/expected/:
#
# - <name>.sols (CSP enumeration): runs the binding with --prove --all,
#   sorts the streamed ENUMSOL lines, and diffs against the cache.
# - <name>.opt (COP optimisation): runs the binding with --prove (no
#   --all), extracts the optimum value from the last `o N` line, and
#   compares against the single integer in the cache. The presence of
#   `s OPTIMUM FOUND` is also required.
#
# When neither cache file exists the test is skipped (ctest exit code
# 66) rather than failed: caches are populated explicitly via
# regenerate_expected.bash, not silently as a side effect of `ctest`.
#
# After the comparison, runs veripb on the proof artefacts.

set -u

prog=$1
testsdir=$2
testname=$3

sols_cache="$testsdir/expected/$testname.sols"
opt_cache="$testsdir/expected/$testname.opt"

export PATH=$HOME/.local/bin:$PATH

if [[ -f $sols_cache ]]; then
    mode=enumerate
elif [[ -f $opt_cache ]]; then
    mode=optimise
else
    echo "no cached expected output for $testname" >&2
    echo "skip: regenerate via xcsp/regenerate_expected.bash $testname" >&2
    exit 66
fi

echo "writing output to $testname.out"

# Normalise line endings before comparing: on Windows the solver's stdout arrives
# CRLF (cout is in text mode) and git may check the LF-committed caches out as CRLF
# too, so strip CR from both the captured output and the cached expectations.
if [[ $mode == enumerate ]]; then
    $prog --prove --all "$testsdir/$testname.xml" > "$testname.out" || exit 1
    tr -d '\r' < "$testname.out" > "$testname.out.nocr" && mv -f "$testname.out.nocr" "$testname.out"

    actualfile="$testname.sols.actual"
    grep '^ENUMSOL: ' "$testname.out" | sed 's/^ENUMSOL: //' | sort > "$actualfile"

    expectedfile="$testname.sols.expected"
    tr -d '\r' < "$sols_cache" > "$expectedfile"

    if ! diff -u "$expectedfile" "$actualfile"; then
        echo "solution set differs from cached expected" >&2
        echo "--- od -c expected (first lines) ---" >&2; od -c "$expectedfile" | head -4 >&2
        echo "--- od -c actual   (first lines) ---" >&2; od -c "$actualfile" | head -4 >&2
        exit 2
    fi
    rm -f "$actualfile" "$expectedfile"
else
    $prog --prove "$testsdir/$testname.xml" > "$testname.out" || exit 1
    tr -d '\r' < "$testname.out" > "$testname.out.nocr" && mv -f "$testname.out.nocr" "$testname.out"

    if ! grep -q '^s OPTIMUM FOUND$' "$testname.out"; then
        echo "expected 's OPTIMUM FOUND' in solver output" >&2
        exit 2
    fi

    actual_opt=$(grep '^o ' "$testname.out" | tail -1 | awk '{print $2}')
    expected_opt=$(tr -d '\r' < "$opt_cache")
    if [[ "$actual_opt" != "$expected_opt" ]]; then
        echo "optimum mismatch: gcs=$actual_opt, expected=$expected_opt" >&2
        exit 3
    fi
fi

veripb xcsp.{opb,pbp} || exit 4

rm -f xcsp.{opb,pbp} "$testname.out"
