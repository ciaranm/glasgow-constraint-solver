TARGET := libglasgow_constraint_solver.a

SRC_INCDIRS := ..

SOURCES := \
    constraint.cc \
    exception.cc \
    integer_variable.cc \
    linear.cc \
    literal.cc \
    low_level_constraint_store.cc \
    problem.cc \
    state.cc \
    stats.cc \
    solve.cc \
    constraints/abs.cc \
    constraints/all_different.cc \
    constraints/element.cc \
    constraints/equals.cc \
    constraints/linear_equality.cc

