TARGET := libglasgow_constraint_solver.a

SRC_INCDIRS := ..

SOURCES := \
    constraint.cc \
    exception.cc \
    integer_variable.cc \
    linear.cc \
    literal.cc \
    problem.cc \
    state.cc \
    stats.cc \
    solve.cc \
    constraints/all_different.cc \
    constraints/element.cc \
    constraints/equals_reif.cc \
    constraints/linear_equality.cc

