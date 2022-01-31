TARGET := libglasgow_constraint_solver.a

SRC_INCDIRS := ..

SOURCES := \
    constraint.cc \
    exception.cc \
    literal.cc \
    problem.cc \
    proof.cc \
    detail/state.cc \
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
    constraints/table.cc \
    detail/extensional.cc \
    detail/integer_variable_state.cc \
    detail/linear.cc \
    detail/propagators.cc \

