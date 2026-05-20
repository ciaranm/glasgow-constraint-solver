add_library(glasgow_constraint_solver
        constraint.cc
        current_state.cc
        exception.cc
        presolver.cc
        problem.cc
        proof.cc
        scp_reader.cc
        search_heuristics.cc
        solve.cc
        stats.cc
        variable_condition.cc
        variable_id.cc
        constraints/abs/abs.cc
        constraints/abs/justify.cc
        constraints/all_different/all_different.cc
        constraints/all_different/all_different_except.cc
        constraints/all_different/encoding.cc
        constraints/all_different/gac_all_different.cc
        constraints/all_different/justify.cc
        constraints/all_different/symmetric_all_different.cc
        constraints/all_different/vc_all_different.cc
        constraints/all_equal/all_equal.cc
        constraints/among/among.cc
        constraints/at_most_one/at_most_one.cc
        constraints/circuit/circuit.cc
        constraints/circuit/circuit_base.cc
        constraints/circuit/circuit_prevent.cc
        constraints/circuit/circuit_scc.cc
        constraints/comparison/comparison.cc
        constraints/count/count.cc
        constraints/cumulative/cumulative.cc
        constraints/disjunctive/disjunctive.cc
        constraints/disjunctive_2d/disjunctive_2d.cc
        constraints/divide_modulus/divide_modulus.cc
        constraints/element/element.cc
        constraints/equals/equals.cc
        constraints/extensional_utils.cc
        constraints/global_cardinality/bounds_global_cardinality.cc
        constraints/global_cardinality/gac_global_cardinality.cc
        constraints/global_cardinality/global_cardinality.cc
        constraints/global_cardinality/justify.cc
        constraints/in/in.cc
        constraints/increasing/increasing.cc
        constraints/innards/cake_truthiness.cc
        constraints/innards/linear_stages.cc
        constraints/innards/product_encoding.cc
        constraints/innards/product_justify.cc
        constraints/innards/justify_not_in_range.cc
        constraints/innards/recover_am1.cc
        constraints/innards/reified_state.cc
        constraints/innards/tabulation.cc
        constraints/innards/triggers.cc
        constraints/inverse/inverse.cc
        constraints/knapsack/knapsack.cc
        constraints/lex/lex.cc
        constraints/lex/lex_smart_table.cc
        constraints/linear/justify.cc
        constraints/linear/linear_equality.cc
        constraints/linear/linear_greater_than_equal.cc
        constraints/linear/linear_inequality.cc
        constraints/linear/linear_less_than_equal.cc
        constraints/linear/propagate.cc
        constraints/linear/utils.cc
        constraints/logical/logical.cc
        constraints/min_max/min_max.cc
        constraints/plus_minus/minus.cc
        constraints/multiply/multiply.cc
        constraints/multiply/signed_multiply.cc
        constraints/n_value/n_value.cc
        constraints/parity/parity.cc
        constraints/plus_minus/plus.cc
        constraints/power/power.cc
        constraints/power/power_table.cc
        constraints/regular/regular.cc
        constraints/regular/regular_bacchus.cc
        constraints/regular/regular_legacy.cc
        constraints/regular/regex.cc
        constraints/seq_precede_chain/seq_precede_chain.cc
        constraints/smart_table/smart_table.cc
        constraints/sort/arg_sort.cc
        constraints/sort/sort.cc
        constraints/table/negative_table.cc
        constraints/table/table.cc
        constraints/value_precede/value_precede.cc
        innards/integer_overflow.cc
        innards/literal.cc
        innards/power.cc
        innards/proofs/bits_encoding.cc
        innards/proofs/emit_inequality_to.cc
        innards/proofs/names_and_ids_tracker.cc
        innards/proofs/pol_builder.cc
        innards/proofs/proof_error.cc
        innards/proofs/proof_logger.cc
        innards/proofs/proof_model.cc
        innards/proofs/proof_only_variables.cc
        innards/proofs/scp_writer.cc
        innards/proofs/simplify_literal.cc
        innards/propagators.cc
        innards/reason.cc
        innards/s_expr.cc
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

if(GCS_COMPILER_HAS_STACKTRACE AND NOT MSVC)
    # stacktrace is only used in .cc files, not public headers, so PRIVATE suffices.
    # stdc++exp is the libstdc++ support library for <stacktrace>/<print>; it is
    # GCC-specific. MSVC also provides <stacktrace> (so GCS_COMPILER_HAS_STACKTRACE
    # is true there) but has no such library to link, hence the NOT MSVC guard.
    target_link_libraries(glasgow_constraint_solver PRIVATE stdc++exp)
endif()

if(NOT GCS_COMPILER_HAS_GENERATOR)
    add_dependencies(glasgow_constraint_solver generator)
    target_link_libraries(glasgow_constraint_solver PUBLIC generator_include)
endif()

target_link_libraries(glasgow_constraint_solver PUBLIC gcs_fmt)

# gch::small_vector is used in interval_set.hh which is transitively reached
# through state.hh, so the include directories must propagate to consumers.
target_link_libraries(glasgow_constraint_solver PUBLIC gch::small_vector)

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

    add_executable(array_param_test array_param_test.cc)
    target_link_libraries(array_param_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME array_param_test COMMAND $<TARGET_FILE:array_param_test>)

    # The lifetime annotations in gcs/lifetime.hh only expand to anything under
    # clang, so these probes are clang-only. Each dangling_*.cc probe contains a
    # lifetime misuse that the annotations must turn into a -Wdangling
    # diagnostic, promoted to an error here: the test builds the probe and
    # passes only if the output contains that diagnostic, so it fails both if
    # an annotation stops working and if a probe breaks for some other reason.
    # valid_uses.cc holds the corrected twins and must build cleanly under the
    # same flags. The RESOURCE_LOCK stops parallel ctest from running several
    # builds of this tree at once.
    if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
        add_library(lifetime_annotation_valid_uses OBJECT EXCLUDE_FROM_ALL lifetime_annotation_tests/valid_uses.cc)
        target_link_libraries(lifetime_annotation_valid_uses PRIVATE glasgow_constraint_solver)
        target_compile_options(lifetime_annotation_valid_uses PRIVATE -Werror=dangling -Werror=dangling-gsl)
        add_test(NAME lifetime_annotation_valid_uses
                COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target lifetime_annotation_valid_uses --config $<CONFIG>)
        set_tests_properties(lifetime_annotation_valid_uses PROPERTIES RESOURCE_LOCK lifetime_annotation_build)

        foreach(probe dangling_array_param_deref dangling_all_normal_variables dangling_create_integer_variable)
            add_library(lifetime_annotation_${probe} OBJECT EXCLUDE_FROM_ALL lifetime_annotation_tests/${probe}.cc)
            target_link_libraries(lifetime_annotation_${probe} PRIVATE glasgow_constraint_solver)
            target_compile_options(lifetime_annotation_${probe} PRIVATE -Werror=dangling -Werror=dangling-gsl)
            add_test(NAME lifetime_annotation_${probe}
                    COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --target lifetime_annotation_${probe} --config $<CONFIG>)
            set_tests_properties(lifetime_annotation_${probe} PROPERTIES
                    PASS_REGULAR_EXPRESSION "-Wdangling"
                    RESOURCE_LOCK lifetime_annotation_build)
        endforeach()
    endif()

    add_executable(abs_test constraints/abs/abs_test.cc)
    add_executable(all_different_test constraints/all_different/all_different_test.cc)
    add_executable(all_different_except_test constraints/all_different/all_different_except_test.cc)
    add_executable(all_equal_test constraints/all_equal/all_equal_test.cc)
    add_executable(among_test constraints/among/among_test.cc)
    add_executable(at_most_one_test constraints/at_most_one/at_most_one_test.cc)
    add_executable(comparison_test constraints/comparison/comparison_test.cc)
    add_executable(count_test constraints/count/count_test.cc)
    add_executable(cumulative_test constraints/cumulative/cumulative_test.cc)
    add_executable(disjunctive_test constraints/disjunctive/disjunctive_test.cc)
    add_executable(disjunctive_2d_test constraints/disjunctive_2d/disjunctive_2d_test.cc)
    add_executable(divide_modulus_test constraints/divide_modulus/divide_modulus_test.cc)
    add_executable(element_test constraints/element/element_test.cc)
    add_executable(equals_test constraints/equals/equals_test.cc)
    add_executable(bounds_global_cardinality_test constraints/global_cardinality/bounds_global_cardinality_test.cc)
    add_executable(gac_global_cardinality_test constraints/global_cardinality/gac_global_cardinality_test.cc)
    add_executable(in_test constraints/in/in_test.cc)
    add_executable(increasing_test constraints/increasing/increasing_test.cc)
    add_executable(inverse_test constraints/inverse/inverse_test.cc)
    add_executable(knapsack_test constraints/knapsack/knapsack_test.cc)
    add_executable(lex_test constraints/lex/lex_test.cc)
    add_executable(linear_test constraints/linear/linear_test.cc)
    add_executable(linear_constant_test constraints/linear/linear_constant_test.cc)
    add_executable(logical_test constraints/logical/logical_test.cc)
    add_executable(min_max_test constraints/min_max/min_max_test.cc)
    add_executable(multiply_test constraints/multiply/multiply_test.cc)
    add_executable(n_value_test constraints/n_value/n_value_test.cc)
    add_executable(parity_test constraints/parity/parity_test.cc)
    add_executable(plus_minus_test constraints/plus_minus/plus_minus_test.cc)
    add_executable(power_test constraints/power/power_test.cc)
    add_executable(product_bounds_test constraints/innards/product_bounds_test.cc)
    add_executable(product_justify_test constraints/innards/product_justify_test.cc)
    add_executable(regular_test constraints/regular/regular_test.cc)
    add_executable(regular_bacchus_test constraints/regular/regular_bacchus_test.cc)
    add_executable(regular_legacy_test constraints/regular/regular_legacy_test.cc)
    add_executable(seq_precede_chain_test constraints/seq_precede_chain/seq_precede_chain_test.cc)
    add_executable(smart_table_test constraints/smart_table/smart_table_test.cc)
    add_executable(smart_table_dup_test constraints/smart_table/smart_table_dup_test.cc)
    target_link_libraries(smart_table_dup_test PRIVATE glasgow_constraint_solver)
    add_test(NAME smart_table_dup COMMAND $<TARGET_FILE:smart_table_dup_test>)
    add_executable(sort_test constraints/sort/sort_test.cc)
    add_executable(arg_sort_test constraints/sort/arg_sort_test.cc)
    add_executable(negative_table_test constraints/table/negative_table_test.cc)
    add_executable(symmetric_all_different_test constraints/all_different/symmetric_all_different_test.cc)
    add_executable(table_test constraints/table/table_test.cc)
    add_executable(tabulation_test constraints/innards/tabulation_test.cc)
    add_executable(value_precede_test constraints/value_precede/value_precede_test.cc)

    foreach(test_target
            abs_test all_different_test all_different_except_test all_equal_test among_test at_most_one_test comparison_test
            count_test cumulative_test disjunctive_test disjunctive_2d_test divide_modulus_test element_test equals_test bounds_global_cardinality_test gac_global_cardinality_test in_test increasing_test inverse_test knapsack_test lex_test linear_test linear_constant_test
            logical_test min_max_test multiply_test n_value_test parity_test
            plus_minus_test power_test product_bounds_test product_justify_test regular_test regular_bacchus_test regular_legacy_test seq_precede_chain_test smart_table_test sort_test arg_sort_test symmetric_all_different_test
            negative_table_test table_test tabulation_test value_precede_test)
        target_link_libraries(${test_target} PRIVATE glasgow_constraint_solver)
    endforeach()

    add_test(NAME abs_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:abs_test>)
    add_test(NAME all_different_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:all_different_test>)
    add_test(NAME all_different_except_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:all_different_except_test>)
    add_test(NAME all_equal_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:all_equal_test>)
    add_test(NAME among_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:among_test>)
    add_test(NAME at_most_one_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:at_most_one_test>)
    foreach(mode ge ge_if ge_iff gt gt_if gt_iff le le_if le_iff lt lt_if lt_iff)
        add_test(NAME comparison_constraint_${mode}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> ${mode})
    endforeach()
    add_test(NAME count_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:count_test>)
    add_test(NAME bounds_global_cardinality_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:bounds_global_cardinality_test>)
    add_test(NAME gac_global_cardinality_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:gac_global_cardinality_test>)
    add_test(NAME cumulative_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_test>)
    foreach(mode strict nonstrict)
        add_test(NAME disjunctive_constraint_${mode}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_test> ${mode})
    endforeach()
    foreach(mode strict nonstrict)
        add_test(NAME disjunctive_2d_constraint_${mode}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_2d_test> ${mode})
    endforeach()
    foreach(mode const const2d var var2d)
        add_test(NAME element_constraint_${mode}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:element_test> ${mode})
    endforeach()
    add_test(NAME equals_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:equals_test>)
    foreach(linmode incremental stateless)
        add_test(NAME linear_constant_constraint_${linmode}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_constant_test>)
    endforeach()
    add_test(NAME sort_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:sort_test>)
    add_test(NAME arg_sort_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:arg_sort_test>)

    # View-wrap sweep: feeds the constraint each variable as a ViewOfIntegerVariableID
    # (offset / negation / both) instead of a bare SimpleIntegerVariableID. The
    # underlying domain is inverted through the wrap so the visible value set
    # (and hence the test's predicate / expected set) is unchanged — only the
    # constraint-side encoding differs. Wrap indices are positions in
    # all_view_wraps(); index 0 is the bare baseline already covered above and
    # is skipped here. n_positions = the number of variable arguments the test
    # wraps; per-position single-variable sweeps land between 0 and n-1.
    # Registers the view-based tests for a constraint whose test threads a
    # ViewWrapConfig. Two tiers:
    #   * the `mixed` policy (distinct per-position wraps: different large
    #     offsets, mixed signs) is ALWAYS registered. It is the only policy
    #     that puts two *different* views in one constraint at once, it is
    #     cheap (a single run), and it is the most likely to surface a
    #     cross-view bug -- so it runs as part of the ordinary test suite.
    #   * the full per-wrap sweep (every wrap x every position; index 0 is the
    #     bare baseline covered elsewhere and skipped) is large and only
    #     registered when GCS_ENABLE_VIEW_WRAP_SWEEP is on.
    # n_positions = the number of variable arguments the test wraps; per-
    # position single-variable sweeps land between 0 and n-1. Extra positional
    # args (e.g. the "mode" argv for comparison_test / linear_test) are
    # forwarded into the binary before the view flags.
    function(add_view_tests test_name target n_positions)
        set(extra_args ${ARGN})
        add_test(NAME ${test_name}_view_mixed
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:${target}>
            ${extra_args} --view-position=mixed)
        if(GCS_ENABLE_VIEW_WRAP_SWEEP)
            math(EXPR last_position "${n_positions} - 1")
            foreach(wrap RANGE 1 18)
                add_test(NAME ${test_name}_view_w${wrap}_pall
                    COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:${target}>
                    ${extra_args} --view-wrap=${wrap} --view-position=all)
                foreach(pos RANGE 0 ${last_position})
                    add_test(NAME ${test_name}_view_w${wrap}_p${pos}
                        COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:${target}>
                        ${extra_args} --view-wrap=${wrap} --view-position=${pos})
                endforeach()
            endforeach()
        endif()
    endfunction()

    # Called unconditionally: the function self-gates the heavy sweep, so the
    # always-on `_view_mixed` test is registered either way.
    add_view_tests(equals_constraint equals_test 2)
    add_view_tests(abs_constraint abs_test 2)
    add_view_tests(divide_modulus_constraint divide_modulus_test 3)
    add_view_tests(power_constraint power_test 2)
    add_view_tests(multiply_constraint multiply_test 3)
    add_view_tests(plus_minus_constraint plus_minus_test 3)
    foreach(mode ge ge_if ge_iff gt gt_if gt_iff le le_if le_iff lt lt_if lt_iff)
        add_view_tests(comparison_constraint_${mode} comparison_test 2 ${mode})
    endforeach()
    add_view_tests(all_different_constraint all_different_test 6)
    add_view_tests(all_equal_constraint all_equal_test 4)
    add_view_tests(increasing_constraint increasing_test 5)
    add_view_tests(min_max_constraint min_max_test 6)
    add_view_tests(at_most_one_constraint at_most_one_test 5)
    add_view_tests(parity_constraint parity_test 4)
    add_view_tests(n_value_constraint n_value_test 6)
    add_view_tests(seq_precede_chain_constraint seq_precede_chain_test 5)
    add_view_tests(count_constraint count_test 6)
    add_view_tests(among_constraint among_test 5)
    add_view_tests(all_different_except_constraint all_different_except_test 4)
    add_view_tests(value_precede_constraint value_precede_test 5)
    foreach(mode eq eq_if eq_iff ge ge_if ge_iff le le_if le_iff ne ne_if ne_iff)
        add_view_tests(linear_constraint_${mode} linear_test 3 ${mode})
    endforeach()
    add_view_tests(table_constraint table_test 3)
    add_view_tests(negative_table_constraint negative_table_test 3)
    add_view_tests(in_constraint in_test 1)
    add_view_tests(lex_constraint lex_test 6)
    add_view_tests(element_constraint_var element_test 6 var)
    add_view_tests(element_constraint_const element_test 2 const)
    add_view_tests(element_constraint_const2d element_test 3 const2d)
    add_view_tests(element_constraint_var2d element_test 5 var2d)
    add_view_tests(logical_constraint logical_test 4)
    add_view_tests(inverse_constraint inverse_test 6)
    foreach(mode strict nonstrict)
        add_view_tests(disjunctive_constraint_${mode} disjunctive_test 4 ${mode})
    endforeach()
    add_view_tests(cumulative_constraint cumulative_test 4)
    add_view_tests(regular_constraint regular_test 4)
    add_test(NAME in_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:in_test>)
    add_test(NAME increasing_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:increasing_test>)
    add_test(NAME inverse_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:inverse_test>)
    add_test(NAME knapsack_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:knapsack_test>)
    add_test(NAME lex_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:lex_test>)
    # Run every linear test in both propagation modes: incremental (threshold 0) and
    # stateless (a huge threshold). The threshold env is appended below (after the cap
    # block, so it doesn't clobber it) and is folded into the proof file name by the
    # test, so the two modes never collide under parallel ctest.
    foreach(mode eq eq_if eq_iff ge ge_if ge_iff le le_if le_iff ne ne_if ne_iff)
        foreach(linmode incremental stateless)
            add_test(NAME linear_constraint_${mode}_${linmode}
                COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> ${mode})
        endforeach()
    endforeach()
    add_test(NAME logical_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:logical_test>)
    add_test(NAME min_max_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:min_max_test>)
    add_test(NAME divide_modulus_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:divide_modulus_test>)
    add_test(NAME power_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:power_test>)
    add_test(NAME multiply_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:multiply_test>)
    add_test(NAME n_value_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:n_value_test>)
    add_test(NAME parity_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:parity_test>)
    add_test(NAME plus_minus_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:plus_minus_test>)
    add_test(NAME regular_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:regular_test>)
    add_test(NAME regular_bacchus_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:regular_bacchus_test>)
    add_test(NAME regular_legacy_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:regular_legacy_test>)
    add_test(NAME seq_precede_chain_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:seq_precede_chain_test>)
    foreach(mode lex_gt lex_ge lex_lt lex_le
                 lex_gt_fixed lex_ge_fixed lex_lt_fixed lex_le_fixed
                 am1_eq am1_in_set al1_eq al1_in_set
                 mixed_same_var stacked_unary wide_constants degenerate)
        add_test(NAME smart_table_constraint_${mode}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:smart_table_test> ${mode})
    endforeach()
    add_test(NAME negative_table_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:negative_table_test>)
    add_test(NAME symmetric_all_different_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:symmetric_all_different_test>)
    add_test(NAME table_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:table_test>)
    add_test(NAME product_bounds COMMAND $<TARGET_FILE:product_bounds_test>)
    add_test(NAME product_justify COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:product_justify_test>)
    add_test(NAME tabulation_test COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:tabulation_test>)
    add_test(NAME value_precede_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:value_precede_test>)

    # The circuit scenario tests self-verify (they call veripb internally on a
    # view-label-suffixed proof file), so they register with run_test_only.bash
    # and plug into add_view_tests like the data-driven tests. The plain
    # registration is the bare (no-view) config.
    add_executable(circuit_disconnected_test constraints/circuit/circuit_disconnected_test.cc)
    target_link_libraries(circuit_disconnected_test PRIVATE glasgow_constraint_solver)
    add_test(NAME circuit_disconnected COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:circuit_disconnected_test>)
    add_view_tests(circuit_disconnected circuit_disconnected_test 8)

    add_executable(circuit_multiple_sccs_test constraints/circuit/circuit_multiple_sccs_test.cc)
    target_link_libraries(circuit_multiple_sccs_test PRIVATE glasgow_constraint_solver)
    add_test(NAME circuit_multiple_sccs COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:circuit_multiple_sccs_test>)
    add_view_tests(circuit_multiple_sccs circuit_multiple_sccs_test 9)

    add_executable(circuit_no_backedges_test constraints/circuit/circuit_no_backedges_test.cc)
    target_link_libraries(circuit_no_backedges_test PRIVATE glasgow_constraint_solver)
    add_test(NAME circuit_no_backedges COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:circuit_no_backedges_test>)
    add_view_tests(circuit_no_backedges circuit_no_backedges_test 8)

    add_executable(circuit_prune_root_test constraints/circuit/circuit_prune_root_test.cc)
    target_link_libraries(circuit_prune_root_test PRIVATE glasgow_constraint_solver)
    add_test(NAME circuit_prune_root COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:circuit_prune_root_test>)
    add_view_tests(circuit_prune_root circuit_prune_root_test 6)

    add_executable(circuit_prune_skip_test constraints/circuit/circuit_prune_skip_test.cc)
    target_link_libraries(circuit_prune_skip_test PRIVATE glasgow_constraint_solver)
    add_test(NAME circuit_prune_skip COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:circuit_prune_skip_test>)
    add_view_tests(circuit_prune_skip circuit_prune_skip_test 7)

    # Data-driven enumerating harness (small full-domain instances), matching
    # the shape of the other constraints' *_test.cc; self-verifies via veripb.
    add_executable(circuit_test constraints/circuit/circuit_test.cc)
    target_link_libraries(circuit_test PRIVATE glasgow_constraint_solver)
    add_test(NAME circuit_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:circuit_test>)
    add_view_tests(circuit_constraint circuit_test 5)

    add_executable(circuit_dup_test constraints/circuit/circuit_dup_test.cc)
    target_link_libraries(circuit_dup_test PRIVATE glasgow_constraint_solver)
    add_test(NAME circuit_dup COMMAND $<TARGET_FILE:circuit_dup_test>)

    add_executable(reification_test innards/proofs/reification_test.cc)
    target_link_libraries(reification_test PRIVATE glasgow_constraint_solver)
    add_test(NAME reification_test COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:reification_test>)

    add_executable(proof_model_tautology_test innards/proofs/proof_model_tautology_test.cc)
    target_link_libraries(proof_model_tautology_test PRIVATE glasgow_constraint_solver)
    add_test(NAME proof_model_tautology_test COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:proof_model_tautology_test>)

    add_executable(introduce_bits_test innards/proofs/introduce_bits_test.cc)
    target_link_libraries(introduce_bits_test PRIVATE glasgow_constraint_solver)
    add_test(NAME introduce_bits_test COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:introduce_bits_test>)

    add_executable(invar_test innards/proofs/invar_test.cc)
    target_link_libraries(invar_test PRIVATE glasgow_constraint_solver)
    add_test(NAME invar_test COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:invar_test>)

    add_executable(range_branch_test innards/proofs/range_branch_test.cc)
    target_link_libraries(range_branch_test PRIVATE glasgow_constraint_solver)
    add_test(NAME range_branch_test COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:range_branch_test>)

    add_executable(range_infer_test innards/proofs/range_infer_test.cc)
    target_link_libraries(range_infer_test PRIVATE glasgow_constraint_solver)
    add_test(NAME range_infer_test COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:range_infer_test>)

    # The range-literal witness suite (dev_docs/range_literals_spec.md §8): each test
    # fails VeriPB within milliseconds if its clause family is removed or weakened.
    # W4 is range_branch_test above plus the suite-wide interval-reject branching.
    foreach(witness w1 w2 w3 w5)
        add_executable(range_witness_${witness}_test innards/proofs/range_witness_${witness}_test.cc)
        target_link_libraries(range_witness_${witness}_test PRIVATE glasgow_constraint_solver)
        add_test(NAME range_witness_${witness}_test COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:range_witness_${witness}_test>)
    endforeach()

    add_executable(interval_set_test innards/interval_set_test.cc)
    target_link_libraries(interval_set_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME interval_set_test COMMAND $<TARGET_FILE:interval_set_test>)

    add_executable(table_shared_tuples_test constraints/table/shared_tuples_test.cc)
    target_link_libraries(table_shared_tuples_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME table_shared_tuples_test COMMAND $<TARGET_FILE:table_shared_tuples_test>)

    add_executable(interval_tree_test innards/interval_tree_test.cc)
    target_link_libraries(interval_tree_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME interval_tree_test COMMAND $<TARGET_FILE:interval_tree_test>)

    add_executable(s_expr_test innards/s_expr_test.cc)
    target_link_libraries(s_expr_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME s_expr_test COMMAND $<TARGET_FILE:s_expr_test>)

    add_executable(scp_reader_test scp_reader_test.cc)
    target_link_libraries(scp_reader_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME scp_reader_test COMMAND $<TARGET_FILE:scp_reader_test>)

    add_executable(integer_test integer_test.cc)
    target_link_libraries(integer_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME integer_test COMMAND $<TARGET_FILE:integer_test>)

    add_executable(exception_test exception_test.cc)
    target_link_libraries(exception_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME exception_test COMMAND $<TARGET_FILE:exception_test>)

    add_executable(state_test innards/state_test.cc)
    target_link_libraries(state_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME state_test COMMAND $<TARGET_FILE:state_test>)

    add_executable(propagators_test innards/propagators_test.cc)
    target_link_libraries(propagators_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME propagators_test COMMAND $<TARGET_FILE:propagators_test>)

    add_executable(idempotent_claim_checker_test innards/idempotent_claim_checker_test.cc)
    target_link_libraries(idempotent_claim_checker_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME idempotent_claim_checker_test COMMAND $<TARGET_FILE:idempotent_claim_checker_test>)

    add_executable(linear_utils_test constraints/linear/utils_test.cc)
    target_link_libraries(linear_utils_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME linear_utils_test COMMAND $<TARGET_FILE:linear_utils_test>)

    add_executable(regex_test constraints/regular/regex_test.cc)
    target_link_libraries(regex_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME regex_test COMMAND $<TARGET_FILE:regex_test>)

    add_executable(bits_encoding_test innards/proofs/bits_encoding_test.cc)
    target_link_libraries(bits_encoding_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    target_compile_definitions(bits_encoding_test PRIVATE CATCH_CONFIG_ENABLE_ALL_STRINGMAKERS=1)
    add_test(NAME bits_encoding_test COMMAND $<TARGET_FILE:bits_encoding_test>)

    add_executable(pol_builder_test innards/proofs/pol_builder_test.cc)
    target_link_libraries(pol_builder_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    target_compile_definitions(pol_builder_test PRIVATE CATCH_CONFIG_ENABLE_ALL_STRINGMAKERS=1)
    add_test(NAME pol_builder_test COMMAND $<TARGET_FILE:pol_builder_test>)

    # Apply the default runtime caps (see GCS_TEST_CAP_DEFAULTS) to every test
    # registered above by setting them in each test's environment. Only the
    # data-driven constraint tests read these variables; the rest ignore them
    # harmlessly. Turning the option off (e.g. the Ubuntu release CI lane)
    # leaves the environment untouched, giving full-enumeration checking.
    if(GCS_TEST_CAP_DEFAULTS)
        get_property(gcs_registered_tests DIRECTORY PROPERTY TESTS)
        set_tests_properties(${gcs_registered_tests} PROPERTIES ENVIRONMENT
            "GCS_TEST_MAX_SOLUTIONS=${GCS_TEST_MAX_SOLUTIONS};GCS_TEST_MAX_RECURSIONS=${GCS_TEST_MAX_RECURSIONS}")
    endif()

    # Pin the linear incremental threshold per test variant: 0 = always incremental,
    # a huge value = always stateless, so CI exercises both linear propagation paths.
    # APPEND so the runtime-cap environment set just above is preserved.
    foreach(mode eq eq_if eq_iff ge ge_if ge_iff le le_if le_iff ne ne_if ne_iff)
        set_property(TEST linear_constraint_${mode}_incremental APPEND PROPERTY ENVIRONMENT "GCS_LINEAR_INCREMENTAL_THRESHOLD=0")
        set_property(TEST linear_constraint_${mode}_stateless APPEND PROPERTY ENVIRONMENT "GCS_LINEAR_INCREMENTAL_THRESHOLD=1000000")
    endforeach()
    set_property(TEST linear_constant_constraint_incremental APPEND PROPERTY ENVIRONMENT "GCS_LINEAR_INCREMENTAL_THRESHOLD=0")
    set_property(TEST linear_constant_constraint_stateless APPEND PROPERTY ENVIRONMENT "GCS_LINEAR_INCREMENTAL_THRESHOLD=1000000")
endif()
