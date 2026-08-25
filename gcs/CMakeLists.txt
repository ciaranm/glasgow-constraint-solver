add_library(glasgow_constraint_solver
        constraint.cc
        current_state.cc
        exception.cc
        presolver.cc
        problem.cc
        proof.cc
        restarts.cc
        scp_reader.cc
        search_heuristics.cc
        solve.cc
        stats.cc
        variable_condition.cc
        variable_id.cc
        variable_weighting.cc
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
        constraints/bin_packing/bin_packing.cc
        constraints/circuit/circuit.cc
        constraints/circuit/circuit_base.cc
        constraints/circuit/circuit_prevent.cc
        constraints/circuit/circuit_scc.cc
        constraints/comparison/comparison.cc
        constraints/count/count.cc
        constraints/cumulative/cumulative.cc
        constraints/cumulative/checkpoint_recovery.cc
        constraints/cumulative/derived_cumulative.cc
        constraints/cumulative/derived_cumulative_stats.cc
        constraints/cumulative/donor_view.cc
        constraints/difference/difference_constraints.cc
        constraints/difference/difference_graph.cc
        constraints/difference/difference_incremental.cc
        constraints/difference/difference_simplify.cc
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
        constraints/innards/guaranteed_contribution.cc
        constraints/innards/makespan_energy.cc
        constraints/innards/product_encoding.cc
        constraints/innards/product_justify.cc
        constraints/innards/justify_not_in_range.cc
        constraints/innards/recover_am1.cc
        constraints/innards/reified_state.cc
        constraints/innards/tabulation.cc
        constraints/innards/task_presence.cc
        constraints/innards/triggers.cc
        constraints/innards/window_energy.cc
        constraints/inverse/inverse.cc
        constraints/knapsack/knapsack.cc
        constraints/knapsack/knapsack_upfront.cc
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
        constraints/mdd/mdd.cc
        constraints/min_distance/min_distance.cc
        constraints/min_max/min_max.cc
        constraints/plus_minus/minus.cc
        constraints/multiply/multiply.cc
        constraints/multiply/signed_multiply.cc
        constraints/n_value/n_value.cc
        constraints/nogoods/nogoods.cc
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
        innards/proofs/am1_from_pairs.cc
        innards/proofs/comparator_network.cc
        innards/proofs/am1_from_row.cc
        innards/proofs/bits_encoding.cc
        innards/proofs/constraint_proof_model_data.cc
        innards/proofs/emit_inequality_to.cc
        innards/proofs/flag_bridge.cc
        innards/proofs/lifted_cover_cut.cc
        innards/proofs/names_and_ids_tracker.cc
        innards/proofs/pol_builder.cc
        innards/proofs/proof_error.cc
        innards/proofs/proof_logger.cc
        innards/proofs/proof_model.cc
        innards/proofs/proof_only_variables.cc
        innards/proofs/proof_scaffolding_scope.cc
        innards/proofs/scp_writer.cc
        innards/proofs/simplify_literal.cc
        innards/proofs/subset_sum_strengthening.cc
        innards/propagators.cc
        innards/reason.cc
        innards/s_expr.cc
        innards/state.cc
        innards/variable_id_utils.cc
        presolvers/auto_table/auto_table.cc
        presolvers/cumulative_strengthening/cumulative_strengthening.cc
        presolvers/difference_logic/difference_logic.cc
        presolvers/inferred_cumulative/inferred_cumulative.cc
        presolvers/inferred_disjunctive/inferred_disjunctive.cc
        presolvers/innards/makespan_links.cc
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

# gch::small_vector is used in the public interval_set.hh, so the include
# directories must propagate to consumers.
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

    # Checks that the GCS_VERBOSE_LOGGING proof annotation resolves gcs source
    # frames, which depends on the debug info the Release build keeps (-g1 on
    # GCC/Clang, /Z7 + /DEBUG on MSVC; see the top-level CMakeLists.txt). It
    # self-skips where <stacktrace> is unavailable (macOS libc++).
    add_executable(stacktrace_logging_test stacktrace_logging_test.cc)
    target_link_libraries(stacktrace_logging_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME stacktrace_logging_test COMMAND $<TARGET_FILE:stacktrace_logging_test>)

    # The Sanitize counterpart of stacktrace_logging_test: it fails if a Sanitize
    # build was compiled without the sanitizers it is named after (issue #597).
    # This test unit is compiled with the same configuration-wide flags as the
    # library, so what it sees is what the library got. GCS_CONFIG_IS_SANITIZE is
    # what tells it to expect them; in any other configuration, and on MSVC where
    # the Sanitize build type is not supported at all, the test trivially passes.
    add_executable(sanitizers_enabled_test sanitizers_enabled_test.cc)
    target_link_libraries(sanitizers_enabled_test PRIVATE Catch2::Catch2WithMain)
    if(NOT MSVC)
        target_compile_definitions(sanitizers_enabled_test PRIVATE $<$<CONFIG:Sanitize>:GCS_CONFIG_IS_SANITIZE>)
    endif()
    add_test(NAME sanitizers_enabled_test COMMAND $<TARGET_FILE:sanitizers_enabled_test>)

    add_executable(problem_test problem_test.cc)
    target_link_libraries(problem_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME problem_test COMMAND $<TARGET_FILE:problem_test>)

    add_executable(difference_logic_presolver_test presolvers/difference_logic/difference_logic_test.cc)
    target_link_libraries(difference_logic_presolver_test PRIVATE glasgow_constraint_solver)
    foreach(mode detection equivalence tripwire opb)
        add_test(NAME difference_logic_presolver_${mode}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:difference_logic_presolver_test> ${mode})
    endforeach()
    add_test(NAME difference_logic_presolver_proofs
        COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:difference_logic_presolver_test> proofs)

    # ---- issue #780: the start-checkpoint encoding, run beside the time-indexed one
    #
    # Every cumulative lane registered through add_cumulative_test runs twice:
    # once as it always did, over the time-indexed OPB block alone, and once as
    # `<name>_checkpoint` with the start-checkpoint block (CumulativeEncoding)
    # emitted beside it. Nothing derives anything from the second block yet, so
    # what the twin buys is the check that its rows are *sound*: a checkpoint
    # row that says too much is a solution veripb refuses on the `solx` line of
    # any enumeration lane. What no lane can check yet is sufficiency, since
    # nothing cites them.
    #
    # The encoding comes from the environment rather than an argv flag because
    # the fixtures build Cumulatives in sixty places, and threading a parameter
    # through all of them would say nothing that GCS_CUMULATIVE_ENCODING does
    # not. The twin gets its own working directory because the two copies write
    # proof files under the same names (issue #562's problem, one directory up).
    #
    # Mutation lanes are the exception, and are twinned one at a time rather
    # than by default. More model is more for unit propagation to reach, so a
    # corrupted proof that veripb rejects against the time-indexed block alone
    # need not be rejected with the checkpoint rows beside it --- and three are
    # not, which is why they are registered bare below with a note apiece. A
    # twin of one of those would assert something false. When a lane comes off
    # that list it should be because its certificate stopped leaning on rows
    # the encoding is about to lose, not because the list got tidied.
    #
    # A third arm, `<name>_recovering`, derives every capacity row back out of
    # the start-checkpoint rows and checks it against the one the model still
    # carries (CumulativeEncoding::BothRecovering). It goes only on the lanes
    # registered through add_cumulative_test_with_recovery, which is every
    # cumulative lane except two kinds. A mutation lane must not have one: the
    # recovery puts yet more in the database for unit propagation to reach, and
    # four more of them stop discriminating under it than under `both` alone. A
    # `scp_chain_cumulative*` case must not have one either, for a better
    # reason: the chain checks our proof against *cake's* OPB, which has no
    # start-checkpoint rows in it at all, so a recovery has nothing to cite.
    #
    # A fourth arm, `<name>_startcheckpoint`, drops the per-time capacity rows
    # from the model altogether (CumulativeEncoding::StartCheckpoint). This is
    # the leak check, and it replaces the OPB-stripping one the script beside it
    # does: a rule that still reads `capacity_lines` finds nothing there, its pol
    # loses the supply it was counting on, and veripb rejects. Nobody has to
    # enumerate where the old rows are read from --- the arm asks the question
    # everywhere at once, and it reaches the rules CumulativeRules leaves off by
    # default, which an .scp-driven check cannot.
    #
    # It goes only on lanes whose every firing rule has moved over. The list of
    # lanes that are *not* on it, further down, is #780's progress bar: when it
    # is empty, the time-indexed block can go.
    file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/cumulative_checkpoint)
    file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/cumulative_recovering)
    file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/cumulative_startcheckpoint)
    #
    # Which arm a lane belongs to is *recorded* here and applied further down,
    # after the runtime-cap block: that block sets ENVIRONMENT on every test in
    # the directory with set_tests_properties, which replaces the property
    # rather than adding to it, so an encoding set here would be silently
    # dropped and the twin would run the arm it was meant to be twinning. That
    # is not hypothetical --- it is how these lanes were first written, and
    # every one of them was quietly vacuous until a mutation lane that must
    # fail started passing. Follow the APPEND idiom the linear and disjunctive
    # lanes below already use.
    function(add_cumulative_arm name arm directory)
        add_test(NAME ${name}_${arm} COMMAND ${ARGN})
        set_tests_properties(${name}_${arm} PROPERTIES WORKING_DIRECTORY ${directory})
        set_property(GLOBAL APPEND PROPERTY gcs_cumulative_${arm}_tests ${name}_${arm})
    endfunction()
    function(add_cumulative_test name)
        add_test(NAME ${name} COMMAND ${ARGN})
        add_cumulative_arm(${name} checkpoint ${CMAKE_CURRENT_BINARY_DIR}/cumulative_checkpoint ${ARGN})
    endfunction()
    function(add_cumulative_test_with_recovery name)
        add_test(NAME ${name} COMMAND ${ARGN})
        add_cumulative_arm(${name} checkpoint ${CMAKE_CURRENT_BINARY_DIR}/cumulative_checkpoint ${ARGN})
        add_cumulative_arm(${name} recovering ${CMAKE_CURRENT_BINARY_DIR}/cumulative_recovering ${ARGN})
    endfunction()
    # For a lane every rule of which has moved over to the recovered rows: as
    # add_cumulative_test_with_recovery, plus the arm that deletes the per-time
    # block from the model entirely. See the note above about what that checks.
    function(add_cumulative_test_converted name)
        add_test(NAME ${name} COMMAND ${ARGN})
        add_cumulative_arm(${name} checkpoint ${CMAKE_CURRENT_BINARY_DIR}/cumulative_checkpoint ${ARGN})
        add_cumulative_arm(${name} recovering ${CMAKE_CURRENT_BINARY_DIR}/cumulative_recovering ${ARGN})
        add_cumulative_arm(${name} startcheckpoint ${CMAKE_CURRENT_BINARY_DIR}/cumulative_startcheckpoint ${ARGN})
    endfunction()

    add_executable(inferred_cumulative_presolver_test presolvers/inferred_cumulative/inferred_cumulative_test.cc)
    target_link_libraries(inferred_cumulative_presolver_test PRIVATE glasgow_constraint_solver)
    add_cumulative_test_with_recovery(inferred_cumulative_presolver
        ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:inferred_cumulative_presolver_test>)

    add_executable(inferred_disjunctive_presolver_test presolvers/inferred_disjunctive/inferred_disjunctive_test.cc)
    target_link_libraries(inferred_disjunctive_presolver_test PRIVATE glasgow_constraint_solver)
    # Twinned too: it cites a *Cumulative* donor's per-(task, time) flags.
    add_cumulative_test_with_recovery(inferred_disjunctive_presolver
        ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:inferred_disjunctive_presolver_test>)

    add_executable(cumulative_strengthening_presolver_test presolvers/cumulative_strengthening/cumulative_strengthening_test.cc)
    target_link_libraries(cumulative_strengthening_presolver_test PRIVATE glasgow_constraint_solver)
    add_cumulative_test_with_recovery(cumulative_strengthening_presolver
        ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_strengthening_presolver_test>)

    add_executable(constraint_enumeration_test constraint_enumeration_test.cc)
    target_link_libraries(constraint_enumeration_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME constraint_enumeration_test COMMAND $<TARGET_FILE:constraint_enumeration_test>)

    add_executable(constraint_row_test constraint_row_test.cc)
    target_link_libraries(constraint_row_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME constraint_row_test COMMAND $<TARGET_FILE:constraint_row_test>)

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
    add_executable(bin_packing_test constraints/bin_packing/bin_packing_test.cc)
    add_executable(comparison_test constraints/comparison/comparison_test.cc)
    add_executable(count_test constraints/count/count_test.cc)
    add_executable(cumulative_test constraints/cumulative/cumulative_test.cc)
    add_executable(cumulative_overload_test constraints/cumulative/cumulative_overload_test.cc)
    add_executable(cumulative_edge_finding_test constraints/cumulative/cumulative_edge_finding_test.cc)
    add_executable(cumulative_ttef_test constraints/cumulative/cumulative_ttef_test.cc)
    add_executable(cumulative_energetic_test constraints/cumulative/cumulative_energetic_test.cc)
    add_executable(cumulative_nfnl_test constraints/cumulative/cumulative_nfnl_test.cc)
    add_executable(cumulative_published_nfnl_test constraints/cumulative/cumulative_published_nfnl_test.cc)
    add_executable(cumulative_kaoc_test constraints/cumulative/cumulative_kaoc_test.cc)
    add_executable(derived_cumulative_test constraints/cumulative/derived_cumulative_test.cc)
    add_executable(cumulative_optional_test constraints/cumulative/cumulative_optional_test.cc)
    add_executable(difference_test constraints/difference/difference_constraints_test.cc)
    add_executable(disjunctive_test constraints/disjunctive/disjunctive_test.cc)
    add_executable(disjunctive_optional_test constraints/disjunctive/disjunctive_optional_test.cc)
    add_executable(disjunctive_overload_test constraints/disjunctive/disjunctive_overload_test.cc)
    add_executable(disjunctive_edge_finding_test constraints/disjunctive/disjunctive_edge_finding_test.cc)
    add_executable(disjunctive_nfnl_test constraints/disjunctive/disjunctive_nfnl_test.cc)
    add_executable(disjunctive_precedences_test constraints/disjunctive/disjunctive_precedences_test.cc)
    add_executable(disjunctive_set_precedences_test constraints/disjunctive/disjunctive_set_precedences_test.cc)
    add_executable(disjunctive_published_nfnl_test constraints/disjunctive/disjunctive_published_nfnl_test.cc)
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
    add_executable(knapsack_upfront_test constraints/knapsack/knapsack_upfront_test.cc)
    add_executable(lex_test constraints/lex/lex_test.cc)
    add_executable(linear_test constraints/linear/linear_test.cc)
    add_executable(linear_constant_test constraints/linear/linear_constant_test.cc)
    add_executable(logical_test constraints/logical/logical_test.cc)
    add_executable(mdd_test constraints/mdd/mdd_test.cc)
    add_executable(min_distance_test constraints/min_distance/min_distance_test.cc)
    add_executable(min_distance_matching_test constraints/min_distance/min_distance_matching_test.cc)
    add_executable(min_max_test constraints/min_max/min_max_test.cc)
    add_executable(mini_linear_test constraints/mini_linear_test.cc)
    add_executable(multiply_test constraints/multiply/multiply_test.cc)
    add_executable(n_value_test constraints/n_value/n_value_test.cc)
    add_executable(nogoods_test constraints/nogoods/nogoods_test.cc)
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
            abs_test all_different_test all_different_except_test all_equal_test among_test at_most_one_test bin_packing_test comparison_test
            count_test cumulative_test cumulative_overload_test cumulative_edge_finding_test cumulative_ttef_test cumulative_energetic_test cumulative_nfnl_test cumulative_published_nfnl_test cumulative_kaoc_test cumulative_optional_test derived_cumulative_test difference_test disjunctive_test disjunctive_optional_test disjunctive_overload_test disjunctive_edge_finding_test disjunctive_nfnl_test disjunctive_precedences_test disjunctive_set_precedences_test disjunctive_published_nfnl_test disjunctive_2d_test divide_modulus_test element_test equals_test bounds_global_cardinality_test gac_global_cardinality_test in_test increasing_test inverse_test knapsack_test knapsack_upfront_test lex_test linear_test linear_constant_test
            logical_test mdd_test min_distance_test min_distance_matching_test min_max_test mini_linear_test multiply_test n_value_test nogoods_test parity_test
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
    add_test(NAME bin_packing_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:bin_packing_test>)
    foreach(mode ge ge_if ge_iff gt gt_if gt_iff le le_if le_iff lt lt_if lt_iff)
        add_test(NAME comparison_constraint_${mode}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:comparison_test> ${mode})
    endforeach()
    add_test(NAME count_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:count_test>)
    add_test(NAME bounds_global_cardinality_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:bounds_global_cardinality_test>)
    add_test(NAME gac_global_cardinality_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:gac_global_cardinality_test>)
    add_cumulative_test_converted(cumulative_constraint ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_test>)
    add_cumulative_test_converted(cumulative_overload ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_overload_test>)
    add_cumulative_test_with_recovery(cumulative_edge_finding ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_edge_finding_test>)
    foreach(mutation drop toofar capacity mirror_drop mirror_toofar)
        add_cumulative_test(cumulative_edge_finding_mutation_${mutation}
            ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename cumulative_edge_finding_mutation_${mutation} $<TARGET_FILE:cumulative_edge_finding_test> --mutate=${mutation})
    endforeach()
    add_cumulative_test_with_recovery(cumulative_ttef ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_ttef_test>)
    add_cumulative_test_with_recovery(cumulative_nfnl ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_nfnl_test>)
    add_cumulative_test_with_recovery(cumulative_kaoc ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_kaoc_test>)
    foreach(fixture cloutier_ex2 dp_path compulsory)
        foreach(mutation claim_one_better strengthen_one_fewer capacity)
            add_cumulative_test(cumulative_kaoc_mutation_${fixture}_${mutation}
                ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                    --basename cumulative_kaoc_mutation_${fixture}_${mutation} $<TARGET_FILE:cumulative_kaoc_test>
                    --mutate=${mutation} --fixture=${fixture})
        endforeach()
    endforeach()
    foreach(mutation toofar drop roomy_toofar roomy_drop)
        add_cumulative_test(cumulative_nfnl_mutation_${mutation}
            ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename cumulative_nfnl_mutation_${mutation} $<TARGET_FILE:cumulative_nfnl_test> --mutate=${mutation})
    endforeach()
    # The detection as published (#746), certified by contiguity rather than by
    # the window-energy lemma. `emit_nothing` is the control and `drop_pin` the
    # lane aimed at what is new; dropping the contiguity rows themselves cannot
    # be caught, and cumulative_mutations.hh records why.
    add_cumulative_test_with_recovery(cumulative_published_nfnl
        ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_published_nfnl_test>)
    add_cumulative_test_with_recovery(cumulative_published_nfnl_random
        ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_published_nfnl_test> --random 7)
    foreach(mutation emit_nothing drop_pin toofar roomy_toofar roomy_drop_pin)
        add_cumulative_test(cumulative_published_nfnl_mutation_${mutation}
            ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename cumulative_published_nfnl_mutation_${mutation} $<TARGET_FILE:cumulative_published_nfnl_test> --mutate=${mutation})
    endforeach()
    # Not twinned (#780): `drop` removes a contiguity row, and the start-
    # checkpoint rows put back enough for the wrapping RUP to close without it,
    # so veripb accepts the corrupted proof under `both`. The lane still says
    # what it always said about the time-indexed encoding.
    add_test(NAME cumulative_published_nfnl_mutation_drop
        COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
            --basename cumulative_published_nfnl_mutation_drop $<TARGET_FILE:cumulative_published_nfnl_test> --mutate=drop)
    foreach(mutation pins pin drop toofar mirror_pins mirror_pin mirror_toofar)
        add_cumulative_test(cumulative_ttef_mutation_${mutation}
            ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename cumulative_ttef_mutation_${mutation} $<TARGET_FILE:cumulative_ttef_test> --mutate=${mutation})
    endforeach()
    # The energetic form (#755), which charges every task its guaranteed energy
    # rather than a contained one's whole energy plus a non-contained one's
    # mandatory part. `drop_energetic` is the lane that matters: it removes the
    # row of a task the window does not contain, which is the only energy plain
    # edge-finding would not have cited.
    add_cumulative_test_with_recovery(cumulative_energetic
        ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_energetic_test>)
    add_cumulative_test_with_recovery(cumulative_energetic_random
        ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_energetic_test> --random 17)
    foreach(mutation drop_energetic drop toofar capacity mirror_drop_energetic mirror_toofar)
        add_cumulative_test(cumulative_energetic_mutation_${mutation}
            ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename cumulative_energetic_mutation_${mutation} $<TARGET_FILE:cumulative_energetic_test> --mutate=${mutation})
    endforeach()
    add_cumulative_test_with_recovery(derived_cumulative ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:derived_cumulative_test>)
    # Mutation lanes: each writes a deliberately corrupted proof of the
    # sharp-margin fixture, and passes only if veripb rejects it. Distinct
    # basenames so the lanes do not race over one set of proof files.
    #
    # These three are twinned onto the recovering arm as well, which most
    # mutation lanes are not: adding model rows gives unit propagation more to
    # reach, so a lane that discriminates under one encoding need not under
    # another, and each twin goes on only once it has been shown to still fail.
    # These have been, and it matters here specifically --- since the overload
    # check's window supply moved onto the recovered rows (#780), `capacity`
    # corrupts a *derived* row rather than a model one, and without the twin the
    # recovering arm would have no negative test over that path at all.
    foreach(mutation energy capacity window)
        add_cumulative_test_converted(cumulative_overload_mutation_${mutation}
            ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename cumulative_overload_mutation_${mutation} $<TARGET_FILE:cumulative_overload_test> --mutate=${mutation})
    endforeach()
    # #780: the corruption no `pol` failure catches. Recovering a capacity row
    # from the neighbouring task's checkpoint leaves every step of the
    # derivation valid and produces a perfectly good line --- it is simply not
    # the row the model states, and only the implication check against that row
    # rejects it. Needs the recovering encoding, since under any other the
    # recovery does not run and the proof comes out honest.
    add_cumulative_arm(cumulative_overload_mutation_recover_wrong checkpoint_recovering
        ${CMAKE_CURRENT_BINARY_DIR}/cumulative_recovering
        ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
            --basename cumulative_overload_mutation_recover_wrong $<TARGET_FILE:cumulative_overload_test>
            --mutate=recover_wrong_checkpoint)

    # And the other half of what the recovering arm has to be held to: that the
    # recovery stands on the start-checkpoint rows *alone*. Every lane above
    # runs with both blocks in the model, where a rup inside the recovery could
    # be closing against the very row it claims to derive and nothing would say
    # so. These cut the proof at the recovery's own marker (`prefix`) or leave
    # it whole (`whole`), and recheck against an OPB with the per-time capacity
    # rows stripped out.
    #
    # `whole` is the stronger claim: it refuses any model whose proof still cites
    # a per-time row, so a model can only go in that mode once every rule it
    # fires has been moved over to the recovered rows. Every case here is `whole`
    # now, which says the *default* rule set --- time-tabling, the overload check
    # and its (TTOC) strengthening --- is converted.
    #
    # These stay as a direct check on the recovery's own derivation --- `prefix`
    # mode cuts the proof at the recovery's marker, which nothing else does ---
    # but they are no longer #780's progress bar. The `startcheckpoint` arm is,
    # and it is a better one in every way: it deletes the per-time rows at the
    # source rather than post-processing a finished OPB, it needs no .scp
    # vehicle, and it therefore reaches the rules CumulativeRules leaves off by
    # default, which these four models cannot fire at all. See the list of lanes
    # not yet on that arm, below.
    function(add_checkpoint_recovery_leak_check case mode)
        add_test(NAME cumulative_checkpoint_recovery_${case}_${mode}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_checkpoint_recovery_leak_check.bash
                $<TARGET_FILE:glasgow_scp_solver>
                ${CMAKE_CURRENT_SOURCE_DIR}/constraints/cumulative/checkpoint_recovery_${case}.scp ${mode})
        set_tests_properties(cumulative_checkpoint_recovery_${case}_${mode} PROPERTIES SKIP_RETURN_CODE 77
            WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/cumulative_recovering)
    endfunction()
    # Two tasks that must overlap and do not fit: the overflow contradiction and
    # nothing else, which is the minimal end-state regression.
    add_checkpoint_recovery_leak_check(overflow_only whole)
    # Four tasks with four different durations, so the candidate set differs
    # from one time point to the next and the weakening path is exercised. Fires
    # both bound pushes as well as the overflow check.
    add_checkpoint_recovery_leak_check(leak_check whole)
    # Three tasks whose mandatory parts are all empty, so time-tabling sees
    # nothing and the overload check is what refutes it. This is the (OC) arm:
    # the contained tasks' own energy is what overflows the window.
    add_checkpoint_recovery_leak_check(overload whole)
    # And the (TTOC) arm, which supplies the same window and then adds the
    # mandatory load of a task the window does *not* contain. Capacity 3 over
    # [0,4): S1 (fixed at 0) and S2 are contained and carry 6 + 6 = 12 against a
    # supply of 12, so (OC) alone finds nothing --- S0, which is not contained,
    # has mandatory part [3,4) at height 2, and that is what tips it to 14 > 12.
    # So the case cannot pass by accident on the plain overload check.
    add_checkpoint_recovery_leak_check(ttoc whole)
    # And each again in `no-block` mode, which never emits the per-time rows at
    # all rather than deleting them afterwards. These are what stop the
    # `startcheckpoint` ctest arm going vacuous: they fail if the encoding falls
    # back for these models instead of dropping the block. See the script.
    add_checkpoint_recovery_leak_check(overflow_only no-block)
    add_checkpoint_recovery_leak_check(leak_check no-block)
    add_checkpoint_recovery_leak_check(overload no-block)
    add_checkpoint_recovery_leak_check(ttoc no-block)

    # #780's progress bar: the cumulative lanes that are *not* on the
    # `startcheckpoint` arm, and what has to happen before they can be. Each is
    # a lane whose proof still reads capacity_lines somewhere, so deleting the
    # per-time rows leaves one of its pols short of supply and veripb rejects.
    # Confirmed by running each under GCS_CUMULATIVE_ENCODING=start-checkpoint;
    # they fail, and they fail loudly.
    #
    #   cumulative_kaoc                    the knapsack / elastic per-time
    #                                      availability lines
    #   cumulative_edge_finding            edge-finding's window rows
    #   cumulative_ttef                    (same, via the profile term)
    #   cumulative_energetic               (same, energetic form)
    #   cumulative_energetic_random
    #   cumulative_nfnl                    not-first / not-last
    #   cumulative_published_nfnl          published not-first / not-last
    #   cumulative_published_nfnl_random
    #   derived_cumulative                 derived_cumulative.cc: donor rows and
    #                                      the makespan bound
    #   inferred_cumulative_presolver      (reach derived_cumulative)
    #   cumulative_strengthening_presolver
    #
    # Move a lane onto the arm by changing its add_cumulative_test_with_recovery
    # to add_cumulative_test_converted, and delete its line here. **When this
    # list is empty, the time-indexed block can go.**
    #
    # Two lanes are absent from the arm for a different reason and are not part
    # of the bar: cumulative_optional_mutation_wrong_task and
    # cumulative_optional_mutation_emit_nothing stop discriminating under it, as
    # they already do under `both` and for the same reason --- more model is
    # more for unit propagation to reach. They are not unconverted; the arm just
    # cannot hold them. The scp_chain_cumulative* cases are out for the reason
    # they are out of the recovering arm: they check our proof against cake's
    # OPB, which has no start-checkpoint rows at all.

    # One ctest entry per mode, each writing proofs under its own basename, so a
    # parallel run does not have two entries racing over one set of files.
    foreach(mode enumerate falsify bijection objective)
        add_cumulative_test_converted(cumulative_optional_constraint_${mode}
            ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_optional_test> ${mode})
    endforeach()
    # Presence-falsification mutation lanes, the same shape as the overload
    # ones above: each writes a deliberately corrupted proof and passes only if
    # veripb rejects it.
    foreach(mutation one_too_far)
        add_cumulative_test(cumulative_optional_mutation_${mutation}
            ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename cumulative_optional_mutation_${mutation} $<TARGET_FILE:cumulative_optional_test> --mutate=${mutation})
    endforeach()
    # Not twinned (#780): both of these corrupt the presence-falsification
    # chain, and the start-checkpoint rows relate the falsified task's start to
    # every other task's directly, which is enough for the wrapping RUP to
    # close without the chain. veripb accepts them under `both`. They still say
    # what they always said about the time-indexed encoding.
    foreach(mutation wrong_task emit_nothing)
        add_test(NAME cumulative_optional_mutation_${mutation}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename cumulative_optional_mutation_${mutation} $<TARGET_FILE:cumulative_optional_test> --mutate=${mutation})
    endforeach()
    foreach(mode basic cycles views alias reified simplify incremental random random_reified)
        add_test(NAME difference_constraint_${mode}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:difference_test> ${mode})
    endforeach()
    foreach(mode strict nonstrict)
        add_test(NAME disjunctive_constraint_${mode}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_test> ${mode})
    endforeach()
    foreach(mode enumerate falsify bijection cumulative objective)
        add_test(NAME disjunctive_optional_constraint_${mode}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_optional_test> ${mode})
    endforeach()
    # Mutation lanes for the presence falsification: see
    # innards/disjunctive_mutations.hh for why the list is short and what each
    # one has to break.
    foreach(mutation emit_nothing wrong_task one_too_far)
        add_test(NAME disjunctive_optional_mutation_${mutation}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename disjunctive_optional_mutation_${mutation} $<TARGET_FILE:disjunctive_optional_test> --mutate=${mutation})
    endforeach()
    # The test writes several proofs under names of its own and checks each
    # with veripb in-process, as cumulative_overload_test does, so the harness
    # only has to run it.
    add_test(NAME disjunctive_overload COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_overload_test>)
    foreach(mutation emit_nothing skip_fold skip_energy rup_bridge)
        add_test(NAME disjunctive_overload_mutation_${mutation}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename disjunctive_overload_mutation_${mutation} $<TARGET_FILE:disjunctive_overload_test> --mutate=${mutation})
    endforeach()
    # Edge-finding, same shape: the test writes its own proofs and checks each
    # with veripb in-process. The --search lane is separate because it verifies
    # a proof per generated instance and takes correspondingly longer --- and it
    # is the one that matters, hand-built fixtures being symmetric and generous
    # enough to verify straight through a certificate bug.
    add_test(NAME disjunctive_edge_finding COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_edge_finding_test>)
    add_test(NAME disjunctive_edge_finding_search
        COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_edge_finding_test> --search 28)
    # The pushed-task row cited at an unclipped threshold is deliberately not a
    # lane here: see innards/disjunctive_mutations.hh for why it cannot bite.
    foreach(mutation emit_nothing skip_fold drop_contained one_too_far drop_pushed)
        add_test(NAME disjunctive_edge_finding_mutation_${mutation}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename disjunctive_edge_finding_mutation_${mutation} $<TARGET_FILE:disjunctive_edge_finding_test> --mutate=${mutation})
    endforeach()
    # Not-first / not-last, over edge-finding's certificate. The mutation lanes
    # are edge-finding's own, unchanged, which is the claim: a different
    # threshold and a different guard are all that differ, so the same
    # corruptions have to bite. The fixture they run on has the pairwise rules
    # off --- see the header comment on disjunctive_nfnl_test.cc for why a
    # load-bearing fixture cannot serve the one_too_far lane.
    add_test(NAME disjunctive_nfnl COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_nfnl_test>)
    add_test(NAME disjunctive_nfnl_search
        COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_nfnl_test> --search 28)
    foreach(mutation emit_nothing skip_fold drop_contained one_too_far drop_pushed)
        add_test(NAME disjunctive_nfnl_mutation_${mutation}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename disjunctive_nfnl_mutation_${mutation} $<TARGET_FILE:disjunctive_nfnl_test> --mutate=${mutation})
    endforeach()
    # Vilim's set-based form, over #757's certificate mirrored. Its own
    # mutation lanes rather than edge-finding's, because what is new here is the
    # derived two-way clause that discharges the guard the reason cannot ---
    # `drop_clause` and `rup_clause` are aimed at exactly that, and the rest
    # check the pieces it is built on are load-bearing too.
    add_test(NAME disjunctive_set_precedences
        COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_set_precedences_test>)
    add_test(NAME disjunctive_set_precedences_search
        COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_set_precedences_test> --search 28)
    foreach(mutation emit_nothing skip_fold drop_energy drop_clause rup_clause one_too_far)
        add_test(NAME disjunctive_set_precedences_mutation_${mutation}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename disjunctive_set_precedences_mutation_${mutation} $<TARGET_FILE:disjunctive_set_precedences_test> --mutate=${mutation})
    endforeach()
    # The rule as published, over the window the negated conclusion derives
    # (#757). Its own lanes rather than the sweep-window rule's: what is new is
    # the derived two-literal clause, so `drop_clause` and `rup_clause` are the
    # ones that matter and the rest check the pieces it is built on.
    add_test(NAME disjunctive_published_nfnl
        COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_published_nfnl_test>)
    add_test(NAME disjunctive_published_nfnl_search
        COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_published_nfnl_test> --search 28)
    foreach(mutation emit_nothing skip_fold drop_energy drop_clause rup_clause one_too_far)
        add_test(NAME disjunctive_published_nfnl_mutation_${mutation}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename disjunctive_published_nfnl_mutation_${mutation} $<TARGET_FILE:disjunctive_published_nfnl_test> --mutate=${mutation})
    endforeach()
    add_test(NAME disjunctive_precedences COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:disjunctive_precedences_test>)
    # Mutation lanes: each writes a deliberately corrupted proof of the
    # sharp-margin fixture, and passes only if veripb rejects it. Distinct
    # basenames so the lanes do not race over one set of proof files.
    foreach(mutation emit_nothing skip_refutation skip_fold loose_bound one_too_far)
        add_test(NAME disjunctive_precedences_mutation_${mutation}
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_expect_verify_failure.bash
                --basename disjunctive_precedences_mutation_${mutation} $<TARGET_FILE:disjunctive_precedences_test> --mutate=${mutation})
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
    add_test(NAME mini_linear_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:mini_linear_test>)
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
    # Ten of the nineteen wraps negate, and DifferenceConstraints rejects a
    # negated operand by design; the test turns those into a rejection check
    # rather than skipping them. The two hand-built modes (incremental,
    # simplify) take no wrap and self-skip.
    foreach(mode basic cycles views alias reified random random_reified)
        add_view_tests(difference_constraint_${mode} difference_test 5 ${mode})
    endforeach()
    add_view_tests(all_different_constraint all_different_test 6)
    add_view_tests(all_equal_constraint all_equal_test 4)
    add_view_tests(increasing_constraint increasing_test 5)
    add_view_tests(min_max_constraint min_max_test 6)
    add_view_tests(at_most_one_constraint at_most_one_test 5)
    add_view_tests(parity_constraint parity_test 4)
    add_view_tests(n_value_constraint n_value_test 6)
    add_view_tests(min_distance_constraint min_distance_test 6)
    add_view_tests(seq_precede_chain_constraint seq_precede_chain_test 5)
    add_view_tests(count_constraint count_test 6)
    add_view_tests(among_constraint among_test 5)
    add_view_tests(all_different_except_constraint all_different_except_test 4)
    add_view_tests(value_precede_constraint value_precede_test 5)
    foreach(mode eq eq_if eq_iff ge ge_if ge_iff le le_if le_iff le_not le_notif ne ne_if ne_iff)
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
    # And its always-on mixed-view lane under the other encoding (#780): two
    # different views in one constraint is the shape the checkpoint rows meet
    # that the per-time ones never do, since a checkpoint row names two starts.
    add_cumulative_arm(cumulative_constraint_view_mixed checkpoint ${CMAKE_CURRENT_BINARY_DIR}/cumulative_checkpoint
        ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_test> --view-position=mixed)
    add_cumulative_arm(cumulative_constraint_view_mixed recovering ${CMAKE_CURRENT_BINARY_DIR}/cumulative_recovering
        ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_test> --view-position=mixed)
    add_cumulative_arm(cumulative_constraint_view_mixed startcheckpoint ${CMAKE_CURRENT_BINARY_DIR}/cumulative_startcheckpoint
        ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:cumulative_test> --view-position=mixed)
    add_view_tests(regular_constraint regular_test 4)
    add_test(NAME in_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:in_test>)
    add_test(NAME increasing_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:increasing_test>)
    add_test(NAME inverse_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:inverse_test>)
    add_test(NAME knapsack_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:knapsack_test>)
    add_test(NAME knapsack_upfront_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:knapsack_upfront_test>)
    add_test(NAME lex_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:lex_test>)
    # Run every linear test in both propagation modes: incremental (threshold 0) and
    # stateless (a huge threshold). The threshold env is appended below (after the cap
    # block, so it doesn't clobber it) and is folded into the proof file name by the
    # test, so the two modes never collide under parallel ctest.
    foreach(mode eq eq_if eq_iff ge ge_if ge_iff le le_if le_iff le_not le_notif ne ne_if ne_iff)
        foreach(linmode incremental stateless)
            add_test(NAME linear_constraint_${mode}_${linmode}
                COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> ${mode})
        endforeach()
    endforeach()
    # Also exercise the slack-based-waking path (refined watches on a covering set)
    # for the decided linear *inequality* directions; the env below forces it on
    # regardless of the covering-fraction heuristic. Only ReifiedLinearInequality
    # reads it, so this is meaningful for the le/ge modes and their install-decided
    # reified forms. linear_test verifies each instance's proof internally, so the
    # slack path is proof-checked here too.
    foreach(mode ge ge_if ge_iff le le_if le_iff le_not le_notif)
        add_test(NAME linear_constraint_${mode}_slack
            COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:linear_test> ${mode})
    endforeach()
    add_test(NAME logical_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:logical_test>)
    add_test(NAME mdd_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:mdd_test>)
    add_test(NAME min_distance_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:min_distance_test>)
    add_test(NAME min_distance_matching COMMAND $<TARGET_FILE:min_distance_matching_test>)
    add_test(NAME min_max_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:min_max_test>)
    add_test(NAME divide_modulus_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:divide_modulus_test>)
    add_test(NAME power_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:power_test>)
    add_test(NAME multiply_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:multiply_test>)
    add_test(NAME n_value_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:n_value_test>)
    add_test(NAME nogoods_constraint COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_only.bash $<TARGET_FILE:nogoods_test>)
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

    add_executable(duplicate_label_test innards/proofs/duplicate_label_test.cc)
    target_link_libraries(duplicate_label_test PRIVATE glasgow_constraint_solver)
    add_test(NAME duplicate_label_test COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:duplicate_label_test>)

    add_executable(eqvar_polarity_test innards/proofs/eqvar_polarity_test.cc)
    target_link_libraries(eqvar_polarity_test PRIVATE glasgow_constraint_solver)
    add_test(NAME eqvar_polarity_test COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:eqvar_polarity_test>)

    add_executable(flag_bridge_test innards/proofs/flag_bridge_test.cc)
    target_link_libraries(flag_bridge_test PRIVATE glasgow_constraint_solver)
    # Verifies (and deliberately fails to verify) its own proofs internally, so
    # it needs no wrapper.
    add_test(NAME flag_bridge_test COMMAND $<TARGET_FILE:flag_bridge_test>)

    add_executable(am1_from_pairs_test innards/proofs/am1_from_pairs_test.cc)
    target_link_libraries(am1_from_pairs_test PRIVATE glasgow_constraint_solver)
    add_executable(comparator_network_test innards/proofs/comparator_network_test.cc)
    target_link_libraries(comparator_network_test PRIVATE glasgow_constraint_solver)
    # Verifies (and deliberately fails to verify) its own proofs internally, so
    # it needs no wrapper.
    add_test(NAME am1_from_pairs_test COMMAND $<TARGET_FILE:am1_from_pairs_test>)
    add_test(NAME comparator_network_test COMMAND $<TARGET_FILE:comparator_network_test>)

    add_executable(am1_from_row_test innards/proofs/am1_from_row_test.cc)
    target_link_libraries(am1_from_row_test PRIVATE glasgow_constraint_solver)
    # Verifies (and deliberately fails to verify) its own proofs internally, so
    # it needs no wrapper.
    add_test(NAME am1_from_row_test COMMAND $<TARGET_FILE:am1_from_row_test>)

    add_executable(lifted_cover_cut_test innards/proofs/lifted_cover_cut_test.cc)
    target_link_libraries(lifted_cover_cut_test PRIVATE glasgow_constraint_solver)
    # Verifies (and deliberately fails to verify) its own proofs internally, so
    # it needs no wrapper.
    add_test(NAME lifted_cover_cut_test COMMAND $<TARGET_FILE:lifted_cover_cut_test>)

    add_executable(subset_sum_strengthening_test innards/proofs/subset_sum_strengthening_test.cc)
    target_link_libraries(subset_sum_strengthening_test PRIVATE glasgow_constraint_solver)
    # Verifies (and deliberately fails to verify) its own proofs internally, so
    # it needs no wrapper.
    add_test(NAME subset_sum_strengthening_test COMMAND $<TARGET_FILE:subset_sum_strengthening_test>)

    add_executable(introduce_bits_test innards/proofs/introduce_bits_test.cc)
    target_link_libraries(introduce_bits_test PRIVATE glasgow_constraint_solver)
    add_test(NAME introduce_bits_test COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:introduce_bits_test>)

    add_executable(direct_only_gevar_bound_test innards/proofs/direct_only_gevar_bound_test.cc)
    target_link_libraries(direct_only_gevar_bound_test PRIVATE glasgow_constraint_solver)
    add_test(NAME direct_only_gevar_bound_test COMMAND ${GCS_BASH} ${CMAKE_CURRENT_SOURCE_DIR}/../run_test_and_verify.bash $<TARGET_FILE:direct_only_gevar_bound_test>)

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

    add_executable(interval_set_test interval_set_test.cc)
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

    add_executable(conflict_observer_test innards/conflict_observer_test.cc)
    target_link_libraries(conflict_observer_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME conflict_observer_test COMMAND $<TARGET_FILE:conflict_observer_test>)

    add_executable(variable_weighting_test variable_weighting_test.cc)
    target_link_libraries(variable_weighting_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME variable_weighting_test COMMAND $<TARGET_FILE:variable_weighting_test>)

    add_executable(restarts_test restarts_test.cc)
    target_link_libraries(restarts_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME restarts_test COMMAND $<TARGET_FILE:restarts_test>)

    add_executable(search_heuristics_test search_heuristics_test.cc)
    target_link_libraries(search_heuristics_test PRIVATE glasgow_constraint_solver Catch2::Catch2WithMain)
    add_test(NAME search_heuristics_test COMMAND $<TARGET_FILE:search_heuristics_test>)

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

    # #780's encoding arms, APPENDed after the runtime caps above rather than
    # set at registration, since set_tests_properties there replaces the whole
    # ENVIRONMENT property. See add_cumulative_arm.
    get_property(gcs_cumulative_checkpoint_tests GLOBAL PROPERTY gcs_cumulative_checkpoint_tests)
    foreach(cumulative_arm_test IN LISTS gcs_cumulative_checkpoint_tests)
        set_property(TEST ${cumulative_arm_test} APPEND PROPERTY ENVIRONMENT "GCS_CUMULATIVE_ENCODING=both")
    endforeach()
    get_property(gcs_cumulative_recovering_tests GLOBAL PROPERTY gcs_cumulative_recovering_tests)
    foreach(cumulative_arm_test IN LISTS gcs_cumulative_recovering_tests)
        set_property(TEST ${cumulative_arm_test} APPEND PROPERTY ENVIRONMENT "GCS_CUMULATIVE_ENCODING=both-recovering")
    endforeach()
    get_property(gcs_cumulative_startcheckpoint_tests GLOBAL PROPERTY gcs_cumulative_startcheckpoint_tests)
    foreach(cumulative_arm_test IN LISTS gcs_cumulative_startcheckpoint_tests)
        set_property(TEST ${cumulative_arm_test} APPEND PROPERTY ENVIRONMENT "GCS_CUMULATIVE_ENCODING=start-checkpoint")
    endforeach()
    get_property(gcs_cumulative_checkpoint_recovering_tests GLOBAL PROPERTY gcs_cumulative_checkpoint_recovering_tests)
    foreach(cumulative_arm_test IN LISTS gcs_cumulative_checkpoint_recovering_tests)
        set_property(TEST ${cumulative_arm_test} APPEND PROPERTY ENVIRONMENT "GCS_CUMULATIVE_ENCODING=both-recovering")
    endforeach()

    # Clear the runtime caps for the two lanes whose whole content is comparing
    # one model's solution *set* against another's. A cap that fires truncates
    # both sides at different points, and comparing the prefixes tests the
    # search order rather than the semantics --- there is no independent oracle
    # here for check_results()'s soundness-only fallback to lean on. Safe to
    # uncap because these lanes write no proofs at all, and proof size and
    # VeriPB time are what the caps exist to bound; the instances are 2-3 tasks
    # over four start values, so the enumeration is bounded by construction. The
    # test also fails loudly if a cap ever does fire, rather than comparing
    # prefixes.
    foreach(mode bijection cumulative)
        set_property(TEST disjunctive_optional_constraint_${mode} APPEND PROPERTY ENVIRONMENT
            "GCS_TEST_MAX_SOLUTIONS=;GCS_TEST_MAX_RECURSIONS=")
    endforeach()

    # Pin the linear incremental threshold per test variant: 0 = always incremental,
    # a huge value = always stateless, so CI exercises both linear propagation paths.
    # APPEND so the runtime-cap environment set just above is preserved.
    foreach(mode eq eq_if eq_iff ge ge_if ge_iff le le_if le_iff le_not le_notif ne ne_if ne_iff)
        set_property(TEST linear_constraint_${mode}_incremental APPEND PROPERTY ENVIRONMENT "GCS_LINEAR_INCREMENTAL_THRESHOLD=0")
        set_property(TEST linear_constraint_${mode}_stateless APPEND PROPERTY ENVIRONMENT "GCS_LINEAR_INCREMENTAL_THRESHOLD=1000000")
    endforeach()
    # Force slack-based waking on (threshold 0, no covering-fraction cap) so the
    # slack path is exercised for every decided inequality direction.
    foreach(mode ge ge_if ge_iff le le_if le_iff le_not le_notif)
        set_property(TEST linear_constraint_${mode}_slack APPEND PROPERTY ENVIRONMENT
            "GCS_LINEAR_SLACK_WATCH_THRESHOLD=0;GCS_LINEAR_SLACK_WATCH_COVER_PERCENT=100")
    endforeach()
    set_property(TEST linear_constant_constraint_incremental APPEND PROPERTY ENVIRONMENT "GCS_LINEAR_INCREMENTAL_THRESHOLD=0")
    set_property(TEST linear_constant_constraint_stateless APPEND PROPERTY ENVIRONMENT "GCS_LINEAR_INCREMENTAL_THRESHOLD=1000000")
endif()
