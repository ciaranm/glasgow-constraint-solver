#!/bin/bash

# Checks the installed MiniZinc solver configuration (issue #977): installs the
# minizinc component into a scratch prefix, moves the prefix somewhere else, and
# solves <model> through the installed glasgow.msc from a working directory in
# which its relative paths lead nowhere. MiniZinc resolves a relative executable
# against the .msc's own directory, but falls back silently to the working
# directory and then PATH when nothing is there, so this only passes if the
# paths written at configure time are right, and if they are relative to the
# .msc rather than to anything else.
#
# An install configured with an absolute bindir or datadir gets absolute paths
# in its .msc, which cannot survive being moved, so that case skips the move.
#
# Skips (exit 66, the ctest SKIP_RETURN_CODE) if minizinc is not installed.
#
# Usage: run_installed_msc_test.bash <cmake> <builddir> <config> <scratchdir>
#                                    <msc path under prefix> <model>

set -euo pipefail

cmake=$1
builddir=$2
config=$3
scratchdir=$4
mscpath=$5
model=$6

export PATH="$HOME/.local/bin:$PATH"

if ! command -v minizinc ; then
    echo "can't run minizinc, skipping test" 1>&2
    exit 66
fi

rm -rf "$scratchdir"
mkdir -p "$scratchdir"
"$cmake" --install "$builddir" --config "$config" --component minizinc --prefix "$scratchdir/installed"

msc="$scratchdir/installed/$mscpath"
executable=$(sed -n 's/^ *"executable": "\(.*\)",$/\1/p' "$msc")
if [[ -z "$executable" ]] ; then
    echo "no executable found in $msc" 1>&2
    exit 1
fi

if [[ "$executable" == /* || "$executable" =~ ^[A-Za-z]: ]] ; then
    echo "absolute executable $executable, so not moving the prefix" 1>&2
    prefix="$scratchdir/installed"
else
    mv "$scratchdir/installed" "$scratchdir/moved"
    prefix="$scratchdir/moved"
fi
msc="$prefix/$mscpath"

# An executable left pointing at the build tree would solve the model just as
# well, so check that it names the installed copy.
if [[ "$executable" == /* || "$executable" =~ ^[A-Za-z]: ]] ; then
    resolved=$executable
else
    resolved=$(dirname "$msc")/$executable
fi
case $(realpath "$resolved") in
    "$(realpath "$prefix")"/*) ;;
    *) echo "$msc names $executable, which is not inside $prefix" 1>&2 ; exit 1 ;;
esac

# Deep enough that a path relative to it, with the .msc's handful of `..`s,
# stays inside the scratch directory and names nothing.
workdir="$prefix/cwd/a/b/c/d"
mkdir -p "$workdir"
cd "$workdir"

minizinc --solver "$msc" -a "$model" | tee "$scratchdir/out"
# The final line of a complete enumeration.
if ! grep -qx '==========' "$scratchdir/out" ; then
    echo "the installed solver did not finish the enumeration" 1>&2
    exit 1
fi
