TARGET := libglasgow_constraint_solver.a

SRC_INCDIRS := ..

SOURCES := \
    constraint.cc \
    current_state.cc \
    exception.cc \
    literal.cc \
    problem.cc \
    stats.cc \
    solve.cc \
    variable_id.cc \
    constraints/abs.cc \
    constraints/all_different.cc \
    constraints/arithmetic.cc \
    constraints/element.cc \
    constraints/equals.cc \
    constraints/comparison.cc \
    constraints/linear_equality.cc \
    constraints/min_max.cc \
    constraints/table.cc \
    detail/extensional.cc \
    detail/integer_variable_state.cc \
    detail/linear_utils.cc \
    detail/literal_utils.cc \
    detail/proof.cc \
    detail/propagators.cc \
    detail/state.cc \
    detail/variable_id_utils.cc

