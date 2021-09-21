TARGET := libglasgow_constraint_solver.a

SRC_INCDIRS := ..

SOURCES := \
    constraint.cc \
    exception.cc \
    extensional.cc \
    integer_variable.cc \
    linear.cc \
    literal.cc \
    low_level_constraint_store.cc \
    problem.cc \
    proof.cc \
    state.cc \
    stats.cc \
    solve.cc \
    variable_id.cc \
    constraints/abs.cc \
    constraints/all_different.cc \
    constraints/arithmetic.cc \
    constraints/element.cc \
    constraints/comparison.cc \
    constraints/linear_equality.cc \
    constraints/min_max.cc \
    constraints/table.cc

