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
    constraints/logical.cc \
    constraints/linear_equality.cc \
    constraints/min_max.cc \
    constraints/table.cc \
    innards/extensional.cc \
    innards/integer_variable_state.cc \
    innards/linear_utils.cc \
    innards/literal_utils.cc \
    innards/proof.cc \
    innards/propagators.cc \
    innards/state.cc \
    innards/variable_id_utils.cc

