BUILD_DIR := intermediate
TARGET_DIR := ./

SUBMAKEFILES := \
    gcs/gcs.mk \
    gcs/constraints/arithmetic_test.mk \
    gcs/constraints/comparison_test.mk \
    gcs/constraints/equals_test.mk \
    gcs/constraints/abs_test.mk \
    gcs/constraints/element_test.mk \
    gcs/constraints/linear_equality_test.mk \
    examples/sum_all_different/sum_all_different.mk \
    examples/sudoku/sudoku.mk \
    examples/money/money.mk \
    examples/langford/langford.mk \
    examples/reif_eq/reif_eq.mk \
    examples/crystal_maze/crystal_maze.mk \
    examples/triangle/triangle.mk \
    examples/colour/colour.mk \
    examples/ortho_latin/ortho_latin.mk \
    examples/three_all_differents/three_all_differents.mk \
    examples/skyscrapers/skyscrapers.mk \
    examples/stable_matching/stable_matching.mk \
    examples/magic_series/magic_series.mk \
    examples/qap/qap.mk \
    examples/n_queens/n_queens.mk \
    examples/magic_square/magic_square.mk \
    examples/cake/cake.mk \
    examples/odd_even_sum/odd_even_sum.mk

override CXXFLAGS += -O3 -march=native -std=c++20 -Isrc/ -W -Wall -Wextra -g -ggdb3 -pthread

boost_ldlibs := -lboost_program_options

