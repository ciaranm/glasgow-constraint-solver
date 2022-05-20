#!/bin/bash

export PATH=$HOME/.local/bin:$PATH

./build/abs_test || exit 1
./build/arithmetic_test || exit 1
./build/comparison_test || exit 1
./build/count_test || exit 1
./build/element_test || exit 1
./build/equals_test || exit 1
./build/linear_equality_test || exit 1
./build/logical_test || exit 1
./build/min_max_test || exit 1
./build/n_value_test || exit 1

./build/cake --prove || exit 1
veripb cake.{opb,veripb} || exit 1

./build/colour --prove || exit 1
veripb colour.{opb,veripb} || exit 1

./build/crystal_maze --prove || exit 1
veripb crystal_maze.{opb,veripb} || exit 1

./build/crystal_maze --abs --prove || exit 1
veripb crystal_maze.{opb,veripb} || exit 1

./build/crystal_maze --gac --prove || exit 1
veripb crystal_maze.{opb,veripb} || exit 1

./build/crystal_maze --gac --abs --prove || exit 1
veripb crystal_maze.{opb,veripb} || exit 1

./build/langford --prove || exit 1
veripb langford.{opb,veripb} || exit 1

./build/money --prove || exit 1
veripb money.{opb,veripb} || exit 1

./build/n_queens --all 10 --prove || exit 1
veripb n_queens.{opb,veripb} || exit 1

./build/magic_series 10 --prove || exit 1
veripb magic_series.{opb,veripb} || exit 1

./build/magic_square 3 --prove || exit 1
veripb magic_square.{opb,veripb} || exit 1

./build/odd_even_sum --prove || exit 1
veripb odd_even_sum.{opb,veripb} || exit 1

./build/ortho_latin 5 --prove || exit 1
veripb ortho_latin.{opb,veripb} || exit 1

./build/qap 5 --prove || exit 1
veripb qap.{opb,veripb} || exit 1

./build/skyscrapers 5 --prove || exit 1
veripb skyscrapers.{opb,veripb} || exit 1

if [[ -f ./build/xcsp_glasgow_constraint_solver ]] ; then
    ./build/xcsp_glasgow_constraint_solver --prove --all xcsp/tests/sum_not_equals.xml > >(tee sum_not_equals.out) || exit 1
    grep -q '^d FOUND SOLUTIONS 8$' sum_not_equals.out || exit 1
    veripb xcsp.{opb,veripb} || exit 1
    rm -f sum_not_equals.out
else
    echo "skipping xcsp tests"
fi

echo tests passed
