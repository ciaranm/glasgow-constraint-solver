#!/usr/bin/env bash
# Pilot benchmark harness — compares two builds against the benchmark set
# in dev_docs/benchmarking.md. Used for the variant experiments (boost::variant2,
# custom slim variant); any A/B that produces drop-in binaries works.

# Runs the eight benchmarks from dev_docs/benchmarking.md, alternating
# trials between two builds, capturing solve time + recursions +
# propagations + external wall time, and writes a TSV log.
#
# Usage (from any directory):
#   ./pilot_benchmarks.sh BASELINE_BUILD_DIR PILOT_BUILD_DIR [TRIALS] [LOG_FILE]
#
# Defaults: TRIALS=3, LOG_FILE=pilot_results.tsv (in $PWD).
#
# Expects each build dir to contain the example binaries
# (magic_series, magic_square, langford, n_queens, ortho_latin, qap, tsp).
# Uses /usr/bin/time -f (GNU time) so this is Linux-only as written.
# Total runtime at TRIALS=3 is ~50 minutes, dominated by n_queens_88.

set -euo pipefail

if [[ $# -lt 2 ]]; then
    sed -n '2,15p' "$0" >&2
    exit 1
fi

BASELINE_DIR="$1"
PILOT_DIR="$2"
TRIALS="${3:-3}"
LOG_FILE="${4:-pilot_results.tsv}"

# Sanity: confirm both build dirs look real.
for dir in "$BASELINE_DIR" "$PILOT_DIR"; do
    for bin in magic_series magic_square langford n_queens ortho_latin qap tsp; do
        if [[ ! -x "$dir/$bin" ]]; then
            echo "missing binary: $dir/$bin" >&2
            exit 1
        fi
    done
done

# GNU time. macOS BSD time doesn't support -f.
if ! /usr/bin/time -f '%e' true >/dev/null 2>&1; then
    echo "/usr/bin/time -f is not available; this harness expects GNU time (Linux)" >&2
    exit 1
fi

# TSV header (overwrites prior file).
{
    echo -e "benchmark\tbuild\ttrial\twall_s\tsolve_s\trecursions\tpropagations\tcheck"
} > "$LOG_FILE"

run_one() {
    local name="$1"; shift
    local build_label="$1"; shift
    local build_dir="$1"; shift
    local trial="$1"; shift
    local bin="$1"; shift
    # remaining args are the binary's arguments

    local out wall solve recs props check
    # Capture stderr (where /usr/bin/time -f writes) and stdout into one buffer.
    out=$(/usr/bin/time -f 'WALL=%e' "$build_dir/$bin" "$@" 2>&1) || {
        echo -e "$name\t$build_label\t$trial\tERROR\tERROR\tERROR\tERROR\trun-failed" >> "$LOG_FILE"
        return
    }
    wall=$(printf '%s\n' "$out" | awk -F= '/^WALL=/ {print $2}')
    solve=$(printf '%s\n' "$out" | awk '/^solve time:/ {gsub("s","",$3); print $3}')
    recs=$(printf '%s\n'  "$out" | awk '/^recursions:/ {print $2}')
    # propagations line is "propagations: N M K" — we want the first integer.
    props=$(printf '%s\n' "$out" | awk '/^propagations:/ {print $2}')

    # Sanity check: solve time should be present.
    if [[ -z "$solve" ]]; then
        check="no-solve-time"
    else
        check="ok"
    fi
    echo -e "$name\t$build_label\t$trial\t$wall\t$solve\t$recs\t$props\t$check" >> "$LOG_FILE"
    printf "  %-22s %-9s trial=%d  wall=%-6s solve=%-7s recs=%-10s props=%s\n" \
        "$name" "$build_label" "$trial" "${wall:-?}" "${solve:-?}" "${recs:-?}" "${props:-?}"
}

# The benchmark set. Format: (name, binary, args...)
declare -a BENCHMARKS=(
    "magic_series_300   magic_series   --size=300"
    "magic_square_5     magic_square   --size=5"
    "langford_11        langford       --size=11 --stats"
    "n_queens_14_all    n_queens       --size=14 --all"
    "ortho_latin_6_all  ortho_latin    --size=6 --all --stats"
    "qap_12             qap            --size=12"
    "tsp_default        tsp"
    "n_queens_88        n_queens       --size=88"
)

echo "Logging to $LOG_FILE"
echo "Baseline: $BASELINE_DIR"
echo "Pilot:    $PILOT_DIR"
echo "Trials:   $TRIALS"
echo

# Interleave: for each benchmark, for each trial, run baseline then pilot.
# (Per benchmarking.md guidance: alternate trials between the two builds.)
for bench in "${BENCHMARKS[@]}"; do
    read -r name bin args <<< "$bench"
    for trial in $(seq 1 "$TRIALS"); do
        run_one "$name" baseline "$BASELINE_DIR" "$trial" "$bin" $args
        run_one "$name" pilot    "$PILOT_DIR"    "$trial" "$bin" $args
    done
done

echo
echo "Done. Summary (median solve time per build):"
awk -F'\t' 'NR>1 && $5 != "ERROR" {key=$1"\t"$2; vals[key] = vals[key] " " $5} END {
    for (k in vals) {
        n = split(vals[k], a, " ");
        # awk array indices start at 2 because of leading space
        for (i = 2; i <= n; i++) sorted[i-1] = a[i];
        # simple sort
        for (i = 1; i < n-1; i++)
            for (j = i+1; j <= n-1; j++)
                if (sorted[i]+0 > sorted[j]+0) { t = sorted[i]; sorted[i] = sorted[j]; sorted[j] = t }
        med = sorted[int((n-1)/2)+1];
        print k "\t" med "s";
    }
}' "$LOG_FILE" | sort
