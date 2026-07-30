#!/bin/bash
#
# Usage: opb_snapshot.bash OUTDIR [ctest-name ...]
#
# Runs the registered example (and scp-chain) tests with --prove, keeps only
# each run's .opb and .scp, and deletes the .pbp/.varmap immediately. The point
# is a byte-diffable snapshot of every constraint's OPB definition: .opb and
# .scp are NOT branching-seed dependent, so a diff across a refactor that is
# meant to be output-preserving should be empty.
#
# With no test names, snapshots every example test.
#
# This is a developer tool for refactor verification; it is not a ctest.

set -u

root=$(cd "$(dirname "$0")/.." && pwd)
build=$root/build
outdir=$1
shift

mkdir -p "$outdir"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Pull "name;binary;args..." out of the generated CTestTestfile.cmake files,
# rewriting the run_test_and_verify.bash wrapper into a direct call.
list_tests()
{
    python3 - "$build" <<'PYEOF'
import pathlib, re, shlex, sys
build = pathlib.Path(sys.argv[1])
for f in sorted(build.rglob('CTestTestfile.cmake')):
    for m in re.finditer(r'^add_test\(\[=*\[([^\]]+)\]=*\] (.*)\)$', f.read_text(), re.M):
        name, rest = m.group(1), m.group(2)
        try:
            argv = shlex.split(rest)
        except ValueError:
            continue
        if not argv or 'run_test_and_verify.bash' not in argv[0]:
            continue
        argv = argv[1:]
        if argv[:1] == ['--basename']:
            argv = argv[2:]
        print(';'.join([name] + argv))
PYEOF
}

want=$*
n_ok=0 n_fail=0 n_skip=0

while IFS= read -r line; do
    name=${line%%;*}
    rest=${line#*;}
    IFS=';' read -r -a argv <<< "$rest"

    if [[ -n $want ]] && ! grep -qw -- "$name" <<< "$want" ; then
        continue
    fi

    # The five *_random harnesses generate a fresh instance per run, so their
    # .opb differs run-to-run on an unchanged binary and is worthless for a
    # byte-diff. Pin any binary that takes a seed, rather than dropping the
    # coverage.
    seed=()
    if "${argv[0]}" --help 2>&1 | grep -q -- '--seed' ; then
        seed=(--seed 42)
    fi

    ( cd "$work" && rm -f -- *.opb *.pbp *.varmap *.scp
      timeout 300 "${argv[@]}" "${seed[@]}" --prove --proof-files-basename "$name" >/dev/null 2>&1 )
    rc=$?

    if [[ -f $work/$name.opb ]] ; then
        cp "$work/$name.opb" "$outdir/"
        [[ -f $work/$name.scp ]] && cp "$work/$name.scp" "$outdir/"
        n_ok=$((n_ok + 1))
    else
        # Binaries that take no --proof-files-basename, or that failed before
        # writing a model, are simply not part of the snapshot.
        echo "skip: $name (rc=$rc, no .opb)" >&2
        n_skip=$((n_skip + 1))
        [[ $rc -ne 0 ]] && n_fail=$((n_fail + 1))
    fi
    rm -f "$work"/*.pbp "$work"/*.varmap
done < <(list_tests)

echo "snapshot: $n_ok captured, $n_skip skipped ($n_fail nonzero exit) -> $outdir" >&2
# A snapshot that captured nothing is a broken harness, not a clean result.
[[ $n_ok -gt 0 ]]
