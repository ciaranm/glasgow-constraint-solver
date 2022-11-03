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
    constraints/all_different.cc
    constraints/arithmetic.cc
    constraints/comparison.cc
    constraints/count.cc
    constraints/element.cc
    constraints/equals.cc
    constraints/in.cc
    constraints/linear_equality.cc
    constraints/logical.cc
    constraints/min_max.cc
    constraints/n_value.cc
    constraints/table.cc
    innards/extensional_utils.cc
    innards/integer_variable_state.cc
    innards/linear_utils.cc
    innards/literal_utils.cc
    innards/opb_utils.cc
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

add_test(NAME abs COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:abs_test>)
add_test(NAME arithmetic COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:arithmetic_test>)
add_test(NAME comparison COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:comparison_test>)
add_test(NAME count COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:count_test>)
add_test(NAME element COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:element_test>)
add_test(NAME equals COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:equals_test>)
add_test(NAME linear_equality COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:linear_equality_test>)
add_test(NAME logical COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:logical_test>)
add_test(NAME min_max COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:min_max_test>)
add_test(NAME n_value COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:n_value_test>)

add_executable(state_test innards/state_test.cc)
target_link_libraries(state_test PRIVATE Catch2::Catch2WithMain)
add_test(NAME state_test COMMAND $<TARGET_FILE:state_test>)

add_executable(linear_utils_test innards/linear_utils_test.cc)
target_link_libraries(linear_utils_test PRIVATE Catch2::Catch2WithMain)
add_test(NAME linear_utils_test COMMAND $<TARGET_FILE:linear_utils_test>)
