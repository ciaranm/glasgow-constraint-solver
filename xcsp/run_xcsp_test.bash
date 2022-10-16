#!/bin/bash

prog=$1
testsdir=$2
testname=$3
checkfor=$4
progname=$(basename $prog )

export PATH=$HOME/.local/bin:$PATH

echo writing output to $testname.out
$prog --prove --all $testsdir/$testname.xml > $testname.out || exit 1
grep -q "$checkfor" $testname.out || exit 1
veripb xcsp.{opb,veripb} || exit 1
rm -f xcsp.{opb,veripb} $testname.out
