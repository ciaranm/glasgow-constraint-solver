#!/bin/bash

builddir=$(dirname $1 )
minizincdir=$2
testname=$3
enumeration=$4
doproofs=$5

export PATH=$builddir:$HOME/.local/bin:$PATH

if ! which minizinc ; then
    echo "can't run minizinc, skipping test" 1>&2
    exit 0
fi

minizinc --solver $minizincdir/glasgow-for-tests.msc -a $minizincdir/tests/$testname.mzn | tee $testname.glasgow.out || exit 1
minizinc -a $minizincdir/tests/$testname.mzn | tee $testname.default.out || exit 2

if [[ "$enumeration" == "true" ]] ; then
    grep -q '^ENUMSOL:' < $testname.glasgow.out || exit 3
    grep '^ENUMSOL:' < $testname.glasgow.out | sort > $testname.glasgow.sols
    grep '^ENUMSOL:' < $testname.default.out | sort > $testname.default.sols

    if ! diff -u $testname.glasgow.sols $testname.default.sols ; then
        echo "found different enumeration solutions"
        exit 4
    fi
else
    grep -q '^OPTSOL:' < $testname.glasgow.out || exit 5
    grep '^OPTSOL:' < $testname.glasgow.out | tail -n1 > $testname.glasgow.sols
    grep '^OPTSOL:' < $testname.default.out | tail -n1 > $testname.default.sols

    if ! diff -u $testname.glasgow.sols $testname.default.sols ; then
        echo "found different objective solutions"
        exit 6
    fi
fi

if [[ $doproofs == "true" ]] && veripb --help >/dev/null ; then
    minizinc --solver $minizincdir/glasgow-for-tests.msc -a $minizincdir/tests/$testname.mzn --prove $testname | tee $testname.glasgow.out || exit 7
    veripb $testname.opb $testname.pbp || exit 8
fi

exit 0
