#!/bin/bash

# Runs fzn-glasgow directly on a hand-written JSON FlatZinc file, rather than
# going through MiniZinc. This is for exercising frontend paths that MiniZinc's
# flattener folds away before they reach the solver (e.g. set_in over an empty
# set, which MiniZinc rewrites to `false`), so they cannot be reached from a
# .mzn model.
#
# Usage: run_fzn_json_test.bash <fzn-glasgow> <minizincdir> <testname>
# Reads   <minizincdir>/tests/json/<testname>.fzn       (JSON FlatZinc input)
# against <minizincdir>/tests/json/<testname>.expected  (sorted solver output)

set -euo pipefail

fznglasgow=$1
minizincdir=$2
testname=$3

export PATH="$HOME/.cargo/bin:$PATH"

jsondir=$minizincdir/tests/json
infile=$jsondir/$testname.fzn

"$fznglasgow" -a "$infile" | tee "$testname.fzn.out" || exit 1

# Sort the output so the comparison is independent of solution enumeration
# order; VeriPB below independently certifies the result is complete.
sort < "$testname.fzn.out" > "$testname.fzn.sols"
if ! diff -u <(sort < "$jsondir/$testname.expected") "$testname.fzn.sols" ; then
    echo "found unexpected solver output"
    exit 2
fi

if veripb --help >/dev/null 2>&1 ; then
    "$fznglasgow" -a --prove "$testname" "$infile" || exit 3
    if ! veripb "$testname.opb" "$testname.pbp" ; then
        echo "Rerunning last 100 lines of proof verification in trace mode..."
        echo '$ ' veripb --trace "$(readlink -f "$testname.opb")" "$(readlink -f "$testname.pbp")"
        # the trace rerun fails again by construction; we still want exit 4
        veripb --trace "$testname.opb" "$testname.pbp" 2>&1 | tail -n100 || true
        exit 4
    fi
fi

exit 0
