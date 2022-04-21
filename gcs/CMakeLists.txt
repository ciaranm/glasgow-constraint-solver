add_library(glasgow_constraint_solver
    constraint.cc
    current_state.cc
    exception.cc
    literal.cc
    problem.cc
    search_heuristics.cc
    solve.cc
    stats.cc
    variable_id.cc
    constraints/abs.cc
    constraints/abs_test.cc
    constraints/all_different.cc
    constraints/arithmetic.cc
    constraints/arithmetic_test.cc
    constraints/comparison.cc
    constraints/comparison_test.cc
    constraints/count.cc
    constraints/count_test.cc
    constraints/element.cc
    constraints/element_test.cc
    constraints/equals.cc
    constraints/equals_test.cc
    constraints/in.cc
    constraints/linear_equality.cc
    constraints/linear_equality_test.cc
    constraints/logical.cc
    constraints/logical_test.cc
    constraints/min_max.cc
    constraints/min_max_test.cc
    constraints/n_value.cc
    constraints/n_value_test.cc
    constraints/table.cc
    innards/extensional_utils.cc
    innards/integer_variable_state.cc
    innards/linear_utils.cc
    innards/literal_utils.cc
    innards/proof.cc
    innards/propagators.cc
    innards/state.cc
    innards/variable_id_utils.cc
    )

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
link_libraries(glasgow_constraint_solver)
add_executable(abs_test constraints/abs_test.cc)
add_executable(arithmetic_test constraints/arithmetic_test.cc)
add_executable(comparison_test constraints/comparison_test.cc)
add_executable(count_test constraints/count_test.cc)
add_executable(element_test constraints/element_test.cc)
add_executable(equals_test constraints/equals_test.cc)
add_executable(linear_equality_test constraints/linear_equality_test.cc)
add_executable(logical_test constraints/logical_test.cc)
add_executable(min_max_test constraints/min_max_test.cc)
add_executable(n_value_test constraints/n_value_test.cc)

