#!/bin/bash

export PATH=$HOME/.local/bin:$PATH

./abs_test || exit 1
./arithmetic_test || exit 1
./comparison_test || exit 1
./element_test || exit 1
./equals_test || exit 1
./linear_equality_test || exit 1

./cake --prove || exit 1
veripb cake.{opb,veripb} || exit 1

./crystal_maze --prove || exit 1
veripb crystal_maze.{opb,veripb} || exit 1

./money --prove || exit 1
veripb money.{opb,veripb} || exit 1

./n_queens --all 10 --prove || exit 1
veripb n_queens.{opb,veripb} || exit 1

./magic_series 10 --prove || exit 1
veripb magic_series.{opb,veripb} || exit 1

./magic_square 3 --prove || exit 1
veripb magic_square.{opb,veripb} || exit 1

./qap 5 --prove || exit 1
veripb qap.{opb,veripb} || exit 1

echo tests passed
