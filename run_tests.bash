#!/bin/bash

export PATH=$HOME/.local/bin:$PATH

./abs_test || exit 1
./arithmetic_test || exit 1
./comparison_test || exit 1
./element_test || exit 1
./equals_test || exit 1
./linear_equality_test || exit 1
./logical_test || exit 1
./min_max_test || exit 1
./n_value_test || exit 1

./cake --prove || exit 1
veripb cake.{opb,veripb} || exit 1

./colour --prove || exit 1
veripb colour.{opb,veripb} || exit 1

./crystal_maze --prove || exit 1
veripb crystal_maze.{opb,veripb} || exit 1

./crystal_maze --abs --prove || exit 1
veripb crystal_maze.{opb,veripb} || exit 1

./crystal_maze --gac --prove || exit 1
veripb crystal_maze.{opb,veripb} || exit 1

./crystal_maze --gac --abs --prove || exit 1
veripb crystal_maze.{opb,veripb} || exit 1

./langford --prove || exit 1
veripb langford.{opb,veripb} || exit 1

./money --prove || exit 1
veripb money.{opb,veripb} || exit 1

./n_queens --all 10 --prove || exit 1
veripb n_queens.{opb,veripb} || exit 1

./magic_series 10 --prove || exit 1
veripb magic_series.{opb,veripb} || exit 1

./magic_square 3 --prove || exit 1
veripb magic_square.{opb,veripb} || exit 1

./odd_even_sum --prove || exit 1
veripb odd_even_sum.{opb,veripb} || exit 1

./ortho_latin 5 --prove || exit 1
veripb ortho_latin.{opb,veripb} || exit 1

./qap 5 --prove || exit 1
veripb qap.{opb,veripb} || exit 1

./skyscrapers 5 --prove || exit 1
veripb skyscrapers.{opb,veripb} || exit 1

echo tests passed
