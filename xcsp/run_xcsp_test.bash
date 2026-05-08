#!/bin/bash
#
# Cache-based XCSP3 test runner. Runs the gcs binding in --all mode,
# extracts the streamed ENUMSOL lines, sorts them, and diffs against a
# canonical expected output committed under tests/expected/<name>.sols.
#
# When a cache file does not exist, the test is skipped (ctest exit code
# 66) rather than failed: caches are populated explicitly via
# regenerate_expected.bash, not silently as a side effect of `ctest`.
#
# After the comparison, runs veripb on the proof artefacts.

set -u

prog=$1
testsdir=$2
testname=$3

cachefile="$testsdir/expected/$testname.sols"

export PATH=$HOME/.local/bin:$PATH

if [[ ! -f $cachefile ]]; then
    echo "no cached expected output for $testname (looked at $cachefile)" >&2
    echo "skip: regenerate via xcsp/regenerate_expected.bash $testname" >&2
    exit 66
fi

actualfile="$testname.sols.actual"

echo "writing output to $testname.out"
$prog --prove --all "$testsdir/$testname.xml" > "$testname.out" || exit 1

# Extract solution stream and sort.
grep '^ENUMSOL: ' "$testname.out" | sed 's/^ENUMSOL: //' | sort > "$actualfile"

if ! diff -u "$cachefile" "$actualfile"; then
    echo "solution set differs from cached expected" >&2
    exit 2
fi

veripb xcsp.{opb,pbp} || exit 3

rm -f xcsp.{opb,pbp} "$testname.out" "$actualfile"
