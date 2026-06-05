#!/usr/bin/env bash
# Run the full verification pipeline. Stops at the first failure.
# Usage: ./verification_pipeline.sh money

set -euo pipefail

CAKE_PB_CP="../../cakepb-dev/cp/cake_pb_cp"
BIN="../build/$1"
TRACE_FLAG="--trace-failed"

function replace_nested_brackets() {
    awk '{
        result = ""
        depth = 0
        for (i = 1; i <= length($0); i++) {
            c = substr($0, i, 1)
            if (c == "[") {
                depth++
                result = result (depth > 1 ? "{" : "[")
            } else if (c == "]") {
                result = result (depth > 1 ? "}" : "]")
                depth--
            } else {
                result = result c
            }
        }
        print result
    }' "$1"
}

if [[ "${1:-}" == "--trace-failed" ]]; then
    TRACE_FLAG="--trace-failed"
fi

step() {
    echo
    echo "=== $1 ==="
}

step "1/5: generate OPB and proof"
echo "$ $BIN --prove"
"$BIN" --prove

step "1.5/5: Replace square brackets with curly braces in OPB, PBP and SCP"
replace_nested_brackets "$1.opb" > "$1.opb.tmp"
mv "$1.opb.tmp" "$1.opb"
replace_nested_brackets "$1.pbp" > "$1.pbp.tmp"
mv "$1.pbp.tmp" "$1.pbp"
sed -i '' 's/\[/\{/g; s/\]/\}/g' "$1.scp"

step "2/5: verify original OPB against proof"
echo "$ veripb $1.opb $1.pbp"
veripb "$1.opb" "$1.pbp"

step "3/5: produce verified OPB from SCP"
echo "$ $CAKE_PB_CP $1.scp > $1.verifiedopb"
"$CAKE_PB_CP" "$1.scp" > "$1.verifiedopb"

# step "3.5/5: work around a bug where escape characters end up in the verifiedopb file"
# echo "$ sed -i '' 's/\\\\//g' $1.verifiedopb"
# sed -i '' 's/\\//g' "$1.verifiedopb"

step "4/5: verify verified-OPB against proof, elaborating core"
echo "$ veripb $1.verifiedopb $1.pbp --elaborate $1.corepb $TRACE_FLAG"
veripb "$1.verifiedopb" "$1.pbp" --elaborate "$1.corepb" $TRACE_FLAG

step "5/5: check core against SCP"
echo "$ $CAKE_PB_CP $1.scp $1.corepb"
"$CAKE_PB_CP" "$1.scp" "$1.corepb"

echo
step "END"
