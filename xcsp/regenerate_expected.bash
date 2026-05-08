#!/bin/bash
#
# Regenerate the cached expected-solutions file for a single XCSP3 test by
# running ACE (https://github.com/xcsp3team/ACE) on the instance and
# extracting all solutions in canonical form.
#
# Usage:
#   ACE_JAR=/path/to/ACE-2.6.jar xcsp/regenerate_expected.bash <testname>
#
# The output file is written to xcsp/tests/expected/<testname>.sols, with
# one solution per line in the form `name=val name=val ...` (variable
# names sorted alphabetically), and the file as a whole sorted lexically
# so that `diff -u` against the gcs solution stream is order-insensitive.

set -eu

if [[ $# -ne 1 ]]; then
    echo "usage: $0 <testname>" >&2
    exit 1
fi

testname=$1
script_dir=$(cd "$(dirname "$0")" && pwd)
testsdir="$script_dir/tests"
instance="$testsdir/$testname.xml"
expected="$testsdir/expected/$testname.sols"

if [[ -z "${ACE_JAR:-}" ]]; then
    echo "error: ACE_JAR is not set" >&2
    echo "  export ACE_JAR=/path/to/ACE-2.6.jar" >&2
    exit 1
fi

if [[ ! -f "$ACE_JAR" ]]; then
    echo "error: ACE_JAR does not point at a file: $ACE_JAR" >&2
    exit 1
fi

if [[ ! -f "$instance" ]]; then
    echo "error: instance not found: $instance" >&2
    exit 1
fi

mkdir -p "$testsdir/expected"

# ACE prints solutions as
#   v  <instantiation id='solN' type='solution'> <list> a b c </list> <values> 1 2 3 </values> </instantiation>
# with ANSI colour escapes around the leading 'v'. The list may use array
# shorthand like `s[]` or `m[][]`, which we expand here using the array
# dimensions parsed from the instance XML. -xc=false disables ACE's
# compression of repeated values (`0x3` for "0,0,0").
java -jar "$ACE_JAR" "$instance" -s=all -xe -xc=false 2>/dev/null \
    | python3 -c '
import re, sys
import xml.etree.ElementTree as ET

instance = sys.argv[1]
tree = ET.parse(instance)
arrays = {}
for arr in tree.iter("array"):
    name = arr.get("id")
    size_str = arr.get("size", "")
    dims = [int(s) for s in re.findall(r"\d+", size_str)]
    if name and dims:
        arrays[name] = dims

def expand(token):
    """Expand `name`, `name[i]`, `name[]`, `name[i..j]`, `name[][]`, etc.
    into a flat list of indexed variable names."""
    bracket_idx = token.find("[")
    if bracket_idx == -1:
        return [token]
    base = token[:bracket_idx]
    parts = re.findall(r"\[([^\]]*)\]", token[bracket_idx:])
    if base not in arrays or len(parts) != len(arrays[base]):
        return None
    dims = arrays[base]
    expanded = [[]]
    for p, dim in zip(parts, dims):
        if p == "":
            indices = list(range(dim))
        elif ".." in p:
            lo, hi = [int(x) for x in p.split("..")]
            indices = list(range(lo, hi + 1))
        else:
            indices = [int(p)]
        expanded = [pre + [i] for pre in expanded for i in indices]
    return [base + "".join(f"[{i}]" for i in idx) for idx in expanded]

ansi = re.compile(r"\x1b\[[0-9;]*m")
inst_pat = re.compile(
    r"<instantiation[^>]*>\s*<list>\s*([^<]+?)\s*</list>"
    r"\s*<values>\s*([^<]+?)\s*</values>")

for line in sys.stdin:
    m = inst_pat.search(ansi.sub("", line))
    if not m:
        continue
    tokens = m.group(1).split()
    vals = m.group(2).split()
    names = []
    ok = True
    for t in tokens:
        e = expand(t)
        if e is None:
            print(f"WARN: cannot expand list token \"{t}\"", file=sys.stderr)
            ok = False
            break
        names.extend(e)
    if not ok:
        continue
    if len(names) != len(vals):
        print(f"WARN: name count {len(names)} != values count {len(vals)}",
              file=sys.stderr)
        continue
    print(" ".join(f"{n}={v}" for n, v in sorted(zip(names, vals))))
' "$instance" \
    | sort > "$expected"

count=$(wc -l < "$expected")
echo "wrote $expected ($count solutions)"
