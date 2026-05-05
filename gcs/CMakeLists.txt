add_library(glasgow_constraint_solver
        constraint.cc
        current_state.cc
        exception.cc
        presolver.cc
        problem.cc
        proof.cc
        search_heuristics.cc
        solve.cc
        stats.cc
        variable_condition.cc
        variable_id.cc
        constraints/abs.cc
        constraints/abs/justify.cc
        constraints/all_different/all_different_except.cc
        constraints/all_different/encoding.cc
        constraints/all_different/gac_all_different.cc
        constraints/all_different/justify.cc
        constraints/all_different/symmetric_all_different.cc
        constraints/all_different/vc_all_different.cc
        constraints/among.cc
        constraints/arithmetic.cc
        constraints/at_most_one.cc
        constraints/circuit/circuit_base.cc
        constraints/circuit/circuit_prevent.cc
        constraints/circuit/circuit_scc.cc
        constraints/comparison.cc
        constraints/count.cc
        constraints/element.cc
        constraints/equals.cc
        constraints/in.cc
        constraints/increasing.cc
        constraints/innards/recover_am1.cc
        constraints/innards/reified_state.cc
        constraints/inverse.cc
        constraints/knapsack.cc
        constraints/lex.cc
        constraints/lex_smart_table.cc
        constraints/linear/justify.cc
        constraints/linear/linear_equality.cc
        constraints/linear/linear_greater_than_equal.cc
        constraints/linear/linear_inequality.cc
        constraints/linear/linear_less_than_equal.cc
        constraints/linear/propagate.cc
        constraints/linear/utils.cc
        constraints/logical.cc
        constraints/min_max.cc
        constraints/minus.cc
        constraints/mult_bc.cc
        constraints/n_value.cc
        constraints/parity.cc
        constraints/plus.cc
        constraints/regular.cc
        constraints/seq_precede_chain.cc
        constraints/smart_table.cc
        constraints/table.cc
        constraints/value_precede.cc
        innards/extensional_utils.cc
        innards/integer_variable_state.cc
        innards/literal.cc
        innards/power.cc
        innards/proofs/bits_encoding.cc
        innards/proofs/emit_inequality_to.cc
        innards/proofs/names_and_ids_tracker.cc
        innards/proofs/proof_error.cc
        innards/proofs/proof_logger.cc
        innards/proofs/proof_model.cc
        innards/proofs/proof_only_variables.cc
        innards/proofs/simplify_literal.cc
        innards/propagators.cc
        innards/reason.cc
        innards/state.cc
        innards/variable_id_utils.cc
        presolvers/auto_table.cc
)

# The repo root contains both gcs/ and util/, so it must be on the include path.
# CMAKE_CURRENT_SOURCE_DIR is gcs/, so .. is the repo root.
target_include_directories(glasgow_constraint_solver PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/..>
        $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>)

# Namespaced alias so consumers use the same target name whether they arrived
# via FetchContent or find_package.
add_library(GlasgowConstraintSolver::glasgow_constraint_solver ALIAS glasgow_constraint_solver)

if(GCS_COMPILER_HAS_STACKTRACE)
    # stacktrace is only used in .cc files, not public headers, so PRIVATE suffices.
    target_link_libraries(glasgow_constraint_solver PRIVATE stdc++exp)
endif()

if(NOT GCS_COMPILER_HAS_GENERATOR)
    add_dependencies(glasgow_constraint_solver generator)
    target_link_libraries(glasgow_constraint_solver PUBLIC generator_include)
endif()

target_link_libraries(glasgow_constraint_solver PUBLIC gcs_fmt)

# nlohmann_json is header-only and used only in .cc files (not public headers), so we
# pull in its include directory directly rather than linking the CMake target.  Linking
# the target would create a reference in the installed export set that consumers can't
# resolve without having nlohmann_json installed themselves.
target_include_directories(glasgow_constraint_solver PRIVATE
        $<BUILD_INTERFACE:${json_SOURCE_DIR}/include>)

if(GCS_BUILD_TESTS)
    add_executable(solve_test solve_test.cc)
    target_link_libraries(solve_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME solve_test COMMAND $<TARGET_FILE:solve_test>)

    add_executable(problem_test problem_test.cc)
    target_link_libraries(problem_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME problem_test COMMAND $<TARGET_FILE:problem_test>)

    add_executable(abs_test constraints/abs_test.cc)
    add_executable(all_different_test constraints/all_different_test.cc)
    add_executable(all_different_except_test constraints/all_different/all_different_except_test.cc)
    add_executable(among_test constraints/among_test.cc)
    add_executable(arithmetic_test constraints/arithmetic_test.cc)
    add_executable(at_most_one_test constraints/at_most_one_test.cc)
    add_executable(comparison_test constraints/comparison_test.cc)
    add_executable(count_test constraints/count_test.cc)
    add_executable(element_test constraints/element_test.cc)
    add_executable(equals_test constraints/equals_test.cc)
    add_executable(in_test constraints/in_test.cc)
    add_executable(increasing_test constraints/increasing_test.cc)
    add_executable(inverse_test constraints/inverse_test.cc)
    add_executable(knapsack_test constraints/knapsack_test.cc)
    add_executable(lex_test constraints/lex_test.cc)
    add_executable(linear_test constraints/linear/linear_test.cc)
    add_executable(logical_test constraints/logical_test.cc)
    add_executable(min_max_test constraints/min_max_test.cc)
    add_executable(mult_bc_test constraints/mult_bc_test.cc)
    add_executable(n_value_test constraints/n_value_test.cc)
    add_executable(parity_test constraints/parity_test.cc)
    add_executable(plus_minus_test constraints/plus_minus_test.cc)
    add_executable(regular_test constraints/regular_test.cc)
    add_executable(seq_precede_chain_test constraints/seq_precede_chain_test.cc)
    add_executable(smart_table_test constraints/smart_table_test.cc)
    add_executable(symmetric_all_different_test constraints/all_different/symmetric_all_different_test.cc)
    add_executable(table_test constraints/table_test.cc)
    add_executable(value_precede_test constraints/value_precede_test.cc)

    foreach(test_target
            abs_test all_different_test all_different_except_test among_test arithmetic_test at_most_one_test comparison_test
            count_test element_test equals_test in_test increasing_test inverse_test knapsack_test lex_test linear_test
            logical_test min_max_test mult_bc_test n_value_test parity_test
            plus_minus_test regular_test seq_precede_chain_test smart_table_test symmetric_all_different_test table_test value_precede_test)
        target_link_libraries(${test_target} PRIVATE glasgow_constraint_solver)
    endforeach()

    add_test(NAME abs_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:abs_test>)
    add_test(NAME all_different_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:all_different_test>)
    add_test(NAME all_different_except_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:all_different_except_test>)
    add_test(NAME among_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:among_test>)
    add_test(NAME arithmetic_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:arithmetic_test>)
    add_test(NAME at_most_one_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:at_most_one_test>)
    add_test(NAME comparison_constraint_ge COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> ge)
    add_test(NAME comparison_constraint_ge_if COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> ge_if)
    add_test(NAME comparison_constraint_ge_iff COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> ge_iff)
    add_test(NAME comparison_constraint_gt COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> gt)
    add_test(NAME comparison_constraint_gt_if COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> gt_if)
    add_test(NAME comparison_constraint_gt_iff COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> gt_iff)
    add_test(NAME comparison_constraint_le COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> le)
    add_test(NAME comparison_constraint_le_if COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> le_if)
    add_test(NAME comparison_constraint_le_iff COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> le_iff)
    add_test(NAME comparison_constraint_lt COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> lt)
    add_test(NAME comparison_constraint_lt_if COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> lt_if)
    add_test(NAME comparison_constraint_lt_iff COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> lt_iff)
    add_test(NAME count_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:count_test>)
    add_test(NAME element_constraint_const COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:element_test> const)
    add_test(NAME element_constraint_const2d COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:element_test> const2d)
    add_test(NAME element_constraint_var COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:element_test> var)
    add_test(NAME element_constraint_var2d COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:element_test> var2d)
    add_test(NAME equals_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:equals_test>)
    add_test(NAME in_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:in_test>)
    add_test(NAME increasing_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:increasing_test>)
    add_test(NAME inverse_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:inverse_test>)
    add_test(NAME knapsack_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:knapsack_test>)
    add_test(NAME lex_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:lex_test>)
    add_test(NAME linear_constraint_eq COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> eq)
    add_test(NAME linear_constraint_eq_if COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> eq_if)
    add_test(NAME linear_constraint_eq_iff COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> eq_iff)
    add_test(NAME linear_constraint_ge COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> ge)
    add_test(NAME linear_constraint_ge_if COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> ge_if)
    add_test(NAME linear_constraint_ge_iff COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> ge_iff)
    add_test(NAME linear_constraint_le COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> le)
    add_test(NAME linear_constraint_le_if COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> le_if)
    add_test(NAME linear_constraint_le_iff COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> le_iff)
    add_test(NAME linear_constraint_ne COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> ne)
    add_test(NAME linear_constraint_ne_if COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> ne_if)
    add_test(NAME linear_constraint_ne_iff COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> ne_iff)
    add_test(NAME logical_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:logical_test>)
    add_test(NAME min_max_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:min_max_test>)
    add_test(NAME mult_bc_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:mult_bc_test>)
    add_test(NAME n_value_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:n_value_test>)
    add_test(NAME parity_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:parity_test>)
    add_test(NAME plus_minus_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:plus_minus_test>)
    add_test(NAME regular_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:regular_test>)
    add_test(NAME seq_precede_chain_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:seq_precede_chain_test>)
    add_test(NAME smart_table_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:smart_table_test>)
    add_test(NAME symmetric_all_different_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:symmetric_all_different_test>)
    add_test(NAME table_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:table_test>)
    add_test(NAME value_precede_constraint COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:value_precede_test>)

    add_executable(circuit_disconnected_test constraints/circuit/circuit_disconnected_test.cc)
    target_link_libraries(circuit_disconnected_test PRIVATE glasgow_constraint_solver)
    add_test(NAME circuit_disconnected COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:circuit_disconnected_test>)

    add_executable(circuit_multiple_sccs_test constraints/circuit/circuit_multiple_sccs_test.cc)
    target_link_libraries(circuit_multiple_sccs_test PRIVATE glasgow_constraint_solver)
    add_test(NAME circuit_multiple_sccs COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:circuit_multiple_sccs_test>)

    add_executable(circuit_no_backedges_test constraints/circuit/circuit_no_backedges_test.cc)
    target_link_libraries(circuit_no_backedges_test PRIVATE glasgow_constraint_solver)
    add_test(NAME circuit_no_backedges COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:circuit_no_backedges_test>)

    add_executable(circuit_prune_root_test constraints/circuit/circuit_prune_root_test.cc)
    target_link_libraries(circuit_prune_root_test PRIVATE glasgow_constraint_solver)
    add_test(NAME circuit_prune_root COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:circuit_prune_root_test>)

    add_executable(circuit_prune_skip_test constraints/circuit/circuit_prune_skip_test.cc)
    target_link_libraries(circuit_prune_skip_test PRIVATE glasgow_constraint_solver)
    add_test(NAME circuit_prune_skip COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:circuit_prune_skip_test>)

    add_executable(reification_test innards/proofs/reification_test.cc)
    target_link_libraries(reification_test PRIVATE glasgow_constraint_solver)
    add_test(NAME reification_test COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:reification_test>)

    add_executable(interval_set_test innards/interval_set_test.cc)
    target_link_libraries(interval_set_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME interval_set_test COMMAND $<TARGET_FILE:interval_set_test>)

    add_executable(state_test innards/state_test.cc)
    target_link_libraries(state_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME state_test COMMAND $<TARGET_FILE:state_test>)

    add_executable(linear_utils_test constraints/linear/utils_test.cc)
    target_link_libraries(linear_utils_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME linear_utils_test COMMAND $<TARGET_FILE:linear_utils_test>)

    add_executable(bits_encoding_test innards/proofs/bits_encoding_test.cc)
    target_link_libraries(bits_encoding_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    target_compile_definitions(bits_encoding_test PRIVATE CATCH_CONFIG_ENABLE_ALL_STRINGMAKERS=1)
    add_test(NAME bits_encoding_test COMMAND $<TARGET_FILE:bits_encoding_test>)
endif()
