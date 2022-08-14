#!/bin/bash

prog=$1
progname=$(basename $prog )

export PATH=$HOME/.local/bin:$PATH

$prog
