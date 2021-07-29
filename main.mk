BUILD_DIR := intermediate
TARGET_DIR := ./

SUBMAKEFILES := \
    gcs/gcs.mk \
    examples/sum_all_different/sum_all_different.mk \
    examples/sudoku/sudoku.mk \
    examples/money/money.mk \
    examples/langford/langford.mk \
    examples/reif_eq/reif_eq.mk \
    examples/crystal_maze/crystal_maze.mk \
    examples/triangle/triangle.mk \
    examples/colour/colour.mk \
    examples/ortho_latin/ortho_latin.mk

override CXXFLAGS += -O3 -march=native -std=c++20 -Isrc/ -W -Wall -Wextra -g -ggdb3 -pthread

ifeq ($(shell uname -s), Linux)
override LDFLAGS += -pthread -lstdc++fs
boost_ldlibs := -lboost_thread -lboost_system -lboost_program_options -lboost_iostreams
else
override LDFLAGS += -pthread
boost_ldlibs := -lboost_thread-mt -lboost_system-mt -lboost_program_options-mt -lboost_filesystem-mt -lboost_iostreams-mt
endif
