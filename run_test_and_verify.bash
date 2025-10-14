#!/bin/bash

prog=$1
progname=$(basename $prog )
shift

export PATH=$HOME/.local/bin:$PATH
export PATH=$HOME/.cargo/bin:$PATH

$prog --prove $@ || exit 1
veripb ${progname}.{opb,pbp} || exit 1
rm -f ${progname}.{opb,pbp}
