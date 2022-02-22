TARGET := min_max_test

SOURCES := \
    min_max_test.cc

SRC_INCDIRS := ../..

TGT_PREREQS := libglasgow_constraint_solver.a
ifeq ($(shell uname -s), Linux)
TGT_LDLIBS := libglasgow_constraint_solver.a -lstdc++fs
else
TGT_LDLIBS := libglasgow_constraint_solver.a
endif
