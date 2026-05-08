include(FetchContent)

FetchContent_Declare(xcsp3_cpp_parser
    GIT_REPOSITORY https://github.com/xcsp3team/XCSP3-CPP-Parser.git
    GIT_TAG 179670dd97cd2b87cdeb93aa7268b57bba719490
    EXCLUDE_FROM_ALL)
FetchContent_MakeAvailable(xcsp3_cpp_parser)

find_package(LibXml2 REQUIRED)

add_executable(xcsp_glasgow_constraint_solver xcsp_glasgow_constraint_solver.cc)
target_link_libraries(xcsp_glasgow_constraint_solver PRIVATE
    xcsp3parser
    LibXml2::LibXml2
    glasgow_constraint_solver
    cxxopts)

add_test(NAME xcsp_sum_not_equals COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ sum_not_equals "^d FOUND SOLUTIONS 8$")
set_tests_properties(xcsp_sum_not_equals PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_intension_basic COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ intension_basic "^d FOUND SOLUTIONS 5$")
set_tests_properties(xcsp_intension_basic PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_intension_arithmetic COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ intension_arithmetic "^d FOUND SOLUTIONS 3$")
set_tests_properties(xcsp_intension_arithmetic PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_intension_boolean COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ intension_boolean "^d FOUND SOLUTIONS 3$")
set_tests_properties(xcsp_intension_boolean PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_intension_reified COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ intension_reified "^d FOUND SOLUTIONS 2$")
set_tests_properties(xcsp_intension_reified PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_all_equal COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ all_equal "^d FOUND SOLUTIONS 3$")
set_tests_properties(xcsp_all_equal PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_ordered_strict COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ ordered_strict "^d FOUND SOLUTIONS 4$")
set_tests_properties(xcsp_ordered_strict PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_ordered_lengths COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ ordered_lengths "^d FOUND SOLUTIONS 10$")
set_tests_properties(xcsp_ordered_lengths PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_precedence COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ precedence "^d FOUND SOLUTIONS 14$")
set_tests_properties(xcsp_precedence PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_count COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ count "^d FOUND SOLUTIONS 24$")
set_tests_properties(xcsp_count PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_count_among COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ count_among "^d FOUND SOLUTIONS 24$")
set_tests_properties(xcsp_count_among PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_n_values COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ n_values "^d FOUND SOLUTIONS 2$")
set_tests_properties(xcsp_n_values PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_cardinality COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ cardinality "^d FOUND SOLUTIONS 12$")
set_tests_properties(xcsp_cardinality PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_minimum COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ minimum "^d FOUND SOLUTIONS 19$")
set_tests_properties(xcsp_minimum PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_maximum COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ maximum "^d FOUND SOLUTIONS 19$")
set_tests_properties(xcsp_maximum PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_channel_self COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ channel_self "^d FOUND SOLUTIONS 4$")
set_tests_properties(xcsp_channel_self PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_channel_two COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ channel_two "^d FOUND SOLUTIONS 6$")
set_tests_properties(xcsp_channel_two PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_circuit COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ circuit "^d FOUND SOLUTIONS 2$")
set_tests_properties(xcsp_circuit PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_instantiation COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ instantiation "^d FOUND SOLUTIONS 1$")
set_tests_properties(xcsp_instantiation PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_lex COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ lex "^d FOUND SOLUTIONS 6$")
set_tests_properties(xcsp_lex PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_lex_matrix COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ lex_matrix "^d FOUND SOLUTIONS 7$")
set_tests_properties(xcsp_lex_matrix PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_all_different_matrix COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ all_different_matrix "^d FOUND SOLUTIONS 2$")
set_tests_properties(xcsp_all_different_matrix PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_slide COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ slide "^d FOUND SOLUTIONS 48$")
set_tests_properties(xcsp_slide PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_regular COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ regular "^d FOUND SOLUTIONS 4$")
set_tests_properties(xcsp_regular PROPERTIES RESOURCE_LOCK xcsp)
