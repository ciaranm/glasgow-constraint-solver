#!/bin/bash
# Fetch the instance families the scheduling sweeps need, from their upstream
# sources. Everything here is public and freely redistributable; none of it is
# kept in this repository, which is why this script exists.
#
#   tools/fetch_scheduling_instances.bash [DEST] [family ...]
#
# DEST defaults to ./scheduling-instances. With no families named it fetches all
# three. Re-running skips what is already there, so an interrupted fetch is
# restarted by running it again.
#
# Needs network access. On a cluster that usually means running this on a login
# node, not inside a batch job.

set -eu

DEST="${1:-scheduling-instances}"
shift || true
FAMILIES=("$@")
[[ ${#FAMILIES[@]} -eq 0 ]] && FAMILIES=(rcpsp jobshop multimode)

# PSPLIB multi-mode sets to take. j10 and j20 are the ones with published
# optimal makespans for every instance; j30 is bigger and harder.
MM_SETS="${MM_SETS:-j10 j20}"

mkdir -p "$DEST"
DEST="$(cd "$DEST" && pwd)"

have() { command -v "$1" >/dev/null 2>&1; }
for tool in curl git python3 unzip; do
    have "$tool" || { echo "need $tool on PATH" >&2; exit 1; }
done

note() { printf '\n=== %s\n' "$*"; }

# --- RCPSP, as MiniZinc .dzn -------------------------------------------------
#
# From the MiniZinc benchmark suite (MIT). A blob-filtered sparse clone of just
# the rcpsp directory is ~19 MB against a very large repository.
fetch_rcpsp() {
    local dir="$DEST/rcpsp"
    if [[ -d "$dir/data_bl" ]]; then
        echo "rcpsp: already present"
        return
    fi
    note "rcpsp: sparse-cloning the MiniZinc benchmark suite"
    rm -rf "$dir.tmp"
    git clone --filter=blob:none --no-checkout --depth 1 \
        https://github.com/MiniZinc/minizinc-benchmarks.git "$dir.tmp"
    git -C "$dir.tmp" sparse-checkout init --cone
    git -C "$dir.tmp" sparse-checkout set rcpsp
    git -C "$dir.tmp" checkout
    mv "$dir.tmp/rcpsp" "$dir"
    rm -rf "$dir.tmp"
}

# --- Job shop ----------------------------------------------------------------
#
# The OR-Library ships all 82 instances as one file; the sweep wants one file
# each. Everything between an `instance <name>` line and the next one is that
# instance, blurb included --- the reader skips down to the first line that is
# numeric throughout.
fetch_jobshop() {
    local dir="$DEST/jobshop"
    if [[ -d "$dir" ]] && [[ $(find "$dir" -name '*.jss' | wc -l) -ge 82 ]]; then
        echo "jobshop: already present"
        return
    fi
    note "jobshop: fetching the OR-Library set"
    mkdir -p "$dir"
    curl -sSLf -o "$dir/jobshop1.txt" \
        "http://people.brunel.ac.uk/~mastjjb/jeb/orlib/files/jobshop1.txt"
    python3 - "$dir" <<'PY'
import re, sys, pathlib
d = pathlib.Path(sys.argv[1])
lines = (d / "jobshop1.txt").read_text().splitlines()
starts = [(i, m.group(1)) for i, l in enumerate(lines)
          if (m := re.match(r'\s*instance\s+(\S+)\s*$', l))]
for k, (i, name) in enumerate(starts):
    end = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
    (d / f"{name}.jss").write_text("\n".join(lines[i:end]).rstrip() + "\n")
print(f"split into {len(starts)} instances")
PY
}

# --- Multi-mode RCPSP --------------------------------------------------------
#
# PSPLIB, with the published optimal makespans alongside. The .opt table is what
# makes this family worth having twice over: it is the only one of the three
# that can tell you the solver's answer is not merely self-consistent but right.
#
# Note the shipped set holds only the feasible instances --- the 104
# (parameter, instance) rows the table marks 16384 have no file --- so this
# family never exercises infeasibility detection.
fetch_multimode() {
    local dir="$DEST/multimode"
    mkdir -p "$dir"
    for set in $MM_SETS; do
        if [[ -d "$dir/$set" ]]; then
            echo "multimode $set: already present"
            continue
        fi
        note "multimode: fetching PSPLIB $set"
        curl -sSLf -o "$dir/$set.zip" \
            "https://www.om-db.wi.tum.de/psplib/download_dataset.php?set=$set&mode=mm&format=zip"
        mkdir -p "$dir/$set"
        unzip -q -o "$dir/$set.zip" -d "$dir/$set"
        rm -f "$dir/$set.zip"
        curl -sSLf -o "$dir/$set.opt" \
            "https://www.om-db.wi.tum.de/psplib/download_solution.php?set=$set&mode=mm&type=opt" \
            || echo "  (no published optima for $set)"
    done
}

for family in "${FAMILIES[@]}"; do
    case "$family" in
        rcpsp) fetch_rcpsp ;;
        jobshop) fetch_jobshop ;;
        multimode) fetch_multimode ;;
        *) echo "unknown family: $family (want rcpsp, jobshop or multimode)" >&2; exit 1 ;;
    esac
done

note "what is in $DEST"
for d in "$DEST"/rcpsp/data_*; do
    [[ -d "$d" ]] || continue
    n=$(find "$d" -name '*.dzn' | wc -l)
    printf '  %-28s %5d .dzn\n' "rcpsp/$(basename "$d")" "$n"
done
[[ -d "$DEST/jobshop" ]] && printf '  %-28s %5d .jss\n' "jobshop" "$(find "$DEST/jobshop" -name '*.jss' | wc -l)"
for d in "$DEST"/multimode/*/; do
    [[ -d "$d" ]] || continue
    printf '  %-28s %5d .mm\n' "multimode/$(basename "$d")" "$(find "$d" -name '*.mm' | wc -l)"
done

cat <<'EOF'

Expected, if the upstreams have not changed under us:
  rcpsp/data_bl 40, data_pack 55, data_pack_d 55, data_ksd15_d 480, data_la_x 80
  jobshop 82
  multimode/j10 536, multimode/j20 554

data_at and data_psplib hold their instances in subdirectories rather than
directly, so they read as zero above and want --dzn-dir pointing a level deeper.

None of these has a capacity-one resource, which is why the job shops are here:
see dev_docs/cluster-experiments.md.
EOF
