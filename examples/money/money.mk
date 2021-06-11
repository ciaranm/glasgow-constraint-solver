TARGET := money

SOURCES := \
    money.cc

SRC_INCDIRS := ../..

TGT_PREREQS := libglasgow_constraint_solver.a
ifeq ($(shell uname -s), Linux)
TGT_LDLIBS := libglasgow_constraint_solver.a $(boost_ldlibs) -lstdc++fs
else
TGT_LDLIBS := libglasgow_constraint_solver.a $(boost_ldlibs)
endif
