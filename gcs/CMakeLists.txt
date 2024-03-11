add_library(glasgow_constraint_solver
        constraint.cc
        current_state.cc
        exception.cc
        presolver.cc
        problem.cc
        proof_options.cc
        search_heuristics.cc
        solve.cc
        stats.cc
        variable_condition.cc
        variable_id.cc
        constraints/abs.cc
        constraints/all_different/gac_all_different.cc
        constraints/all_different/vc_all_different.cc
        constraints/arithmetic.cc
        constraints/at_most_one.cc
        constraints/circuit/circuit_base.cc
        constraints/circuit/circuit_disconnected_test.cc
        constraints/circuit/circuit_multiple_sccs_test.cc
        constraints/circuit/circuit_no_backedges_test.cc
        constraints/circuit/circuit_prevent.cc
        constraints/circuit/circuit_prune_root_test.cc
        constraints/circuit/circuit_prune_skip_test.cc
        constraints/circuit/circuit_scc.cc
        constraints/comparison.cc
        constraints/count.cc
        constraints/element.cc
        constraints/equals.cc
        constraints/in.cc
        constraints/knapsack.cc
        constraints/lex.cc
        constraints/linear_equality.cc
        constraints/logical.cc
        constraints/min_max.cc
        constraints/n_value.cc
        constraints/not_equals.cc
        constraints/regular.cc
        constraints/smart_table.cc
        constraints/table.cc
        innards/bits_encoding.cc
        innards/extensional_utils.cc
        innards/integer_variable_state.cc
        innards/linear_utils.cc
        innards/literal.cc
        innards/opb_utils.cc
        innards/proof.cc
        innards/propagators.cc
        innards/state.cc
        innards/variable_id_utils.cc
        presolvers/auto_table.cc
        constraints/all_different/vc_all_different.cc
        constraints/all_different/vc_all_different.hh
        constraints/all_different/gac_all_different.hh
)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
link_libraries(glasgow_constraint_solver)

add_executable(solve_test solve_test.cc)
target_link_libraries(solve_test PRIVATE Catch2::Catch2WithMain)
add_test(NAME solve_test COMMAND $<TARGET_FILE:solve_test>)

add_executable(abs_test constraints/abs_test.cc)
add_executable(arithmetic_test constraints/arithmetic_test.cc)
add_executable(comparison_test constraints/comparison_test.cc)
add_executable(count_test constraints/count_test.cc)
add_executable(circuit_disconnected_test constraints/circuit/circuit_disconnected_test)
add_executable(circuit_multiple_sccs_test constraints/circuit/circuit_multiple_sccs_test)
add_executable(circuit_no_backedges_test constraints/circuit/circuit_no_backedges_test)
add_executable(circuit_prune_root_test constraints/circuit/circuit_prune_root_test)
add_executable(circuit_prune_skip_test constraints/circuit/circuit_prune_skip_test)
add_executable(element_test constraints/element_test.cc)
add_executable(equals_test constraints/equals_test.cc)
add_executable(knapsack_test constraints/knapsack_test.cc)
add_executable(linear_equality_test constraints/linear_equality_test.cc)
add_executable(logical_test constraints/logical_test.cc)
add_executable(min_max_test constraints/min_max_test.cc)
add_executable(n_value_test constraints/n_value_test.cc)
add_executable(not_equals_test constraints/not_equals_test.cc)
add_executable(smart_table_test constraints/smart_table_test.cc)


add_test(NAME abs_constraint COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:abs_test>)
add_test(NAME arithmetic_constraint COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:arithmetic_test>)
add_test(NAME circuit_disconnected COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:circuit_disconnected_test>)
add_test(NAME circuit_multiple_sccs COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:circuit_multiple_sccs_test>)
add_test(NAME circuit_no_backedges COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:circuit_no_backedges_test>)
add_test(NAME circuit_prune_root COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:circuit_prune_root_test>)
add_test(NAME circuit_prune_skip COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:circuit_prune_skip_test>)
add_test(NAME comparison_constraint COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:comparison_test>)
add_test(NAME count_constraint COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:count_test>)
add_test(NAME element_constraint COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:element_test>)
add_test(NAME equals_constraint COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:equals_test>)
add_test(NAME knapsack_constraint COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:knapsack_test>)
add_test(NAME linear_equality_constraint COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:linear_equality_test>)
add_test(NAME logical_constraint COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:logical_test>)
add_test(NAME min_max_constraint COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:min_max_test>)
add_test(NAME n_value_constraint COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:n_value_test>)
add_test(NAME smart_table_constraint COMMAND ${CMAKE_SOURCE_DIR}/run_test_only.bash $<TARGET_FILE:smart_table_test>)

add_executable(interval_set_test innards/interval_set_test.cc)
target_link_libraries(interval_set_test PRIVATE Catch2::Catch2WithMain)
add_test(NAME interval_set_test COMMAND $<TARGET_FILE:interval_set_test>)

add_executable(state_test innards/state_test.cc)
target_link_libraries(state_test PRIVATE Catch2::Catch2WithMain)
add_test(NAME state_test COMMAND $<TARGET_FILE:state_test>)

add_executable(linear_utils_test innards/linear_utils_test.cc)
target_link_libraries(linear_utils_test PRIVATE Catch2::Catch2WithMain)
add_test(NAME linear_utils_test COMMAND $<TARGET_FILE:linear_utils_test>)

add_executable(bits_encoding_test innards/bits_encoding_test.cc)
target_link_libraries(bits_encoding_test PRIVATE Catch2::Catch2WithMain)
add_test(NAME bits_encoding_test COMMAND $<TARGET_FILE:bits_encoding_test>)
