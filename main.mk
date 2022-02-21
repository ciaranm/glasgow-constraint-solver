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
    gcs/constraints/min_max_test.mk \
    examples/cake/cake.mk \
    examples/colour/colour.mk \
    examples/crystal_maze/crystal_maze.mk \
    examples/langford/langford.mk \
    examples/magic_series/magic_series.mk \
    examples/magic_square/magic_square.mk \
    examples/money/money.mk \
    examples/n_queens/n_queens.mk \
    examples/odd_even_sum/odd_even_sum.mk \
    examples/ortho_latin/ortho_latin.mk \
    examples/qap/qap.mk \
    examples/skyscrapers/skyscrapers.mk

override CXXFLAGS += -O3 -march=native -std=c++20 -Isrc/ -W -Wall -Wextra -g -ggdb3 -pthread -flto
override LDFLAGS += -flto

boost_ldlibs := -lboost_program_options

