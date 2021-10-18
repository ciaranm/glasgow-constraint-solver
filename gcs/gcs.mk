TARGET := libglasgow_constraint_solver.a

SRC_INCDIRS := ..

SOURCES := \
    constraint.cc \
    exception.cc \
    extensional.cc \
    integer_variable_state.cc \
    linear.cc \
    literal.cc \
    problem.cc \
    propagators.cc \
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

