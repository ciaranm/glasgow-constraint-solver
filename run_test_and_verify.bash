#!/bin/bash

prog=$1
progname=$(basename "$prog")
# On Windows the target file ends in .exe, but the test binaries name their proof
# files after the plain stem (e.g. ProofOptions{"range_witness_w1_test"}), so strip
# the suffix to find name.opb / name.pbp rather than name.exe.opb.
progname=${progname%.exe}
shift

export PATH=$HOME/.cargo/bin:$PATH

$prog --prove $@ || exit 1
veripb ${progname}.{opb,pbp} || exit 1
# rm -f ${progname}.{opb,pbp}
