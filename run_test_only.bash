#!/bin/bash

prog=$1
progname=$(basename $prog )

shift

$prog "$@"
