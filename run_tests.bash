#!/bin/bash

export PATH=$HOME/.local/bin:$PATH

./abs_test || exit 1
./arithmetic_test || exit 1
./comparison_test || exit 1
./element_test || exit 1

