#!/bin/bash

prog=$1
progname=$(basename $prog )
shift

export PATH=$HOME/.local/bin:$PATH

$prog --prove $@ || exit 1
veripb ${progname}.{opb,veripb} || exit 1
rm -f ${progname}.{opb,veripb}