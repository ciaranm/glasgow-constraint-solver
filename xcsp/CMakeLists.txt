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

# Each XCSP3 ctest runs the binding with --prove --all on the given
# instance and diffs the streamed solutions against a cached expected
# output committed under tests/expected/<name>.sols. If the cache is
# missing, the test skips (ctest exit code 66) rather than failing.
function(add_xcsp_test name)
    add_test(NAME xcsp_${name}
        COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash
            $<TARGET_FILE:xcsp_glasgow_constraint_solver>
            ${CMAKE_SOURCE_DIR}/xcsp/tests/
            ${name})
    set_tests_properties(xcsp_${name} PROPERTIES
        RESOURCE_LOCK xcsp
        SKIP_RETURN_CODE 66)
endfunction()

add_xcsp_test(all_different_matrix)
add_xcsp_test(all_equal)
add_xcsp_test(cardinality)
add_xcsp_test(channel_self)
add_xcsp_test(channel_two)
add_xcsp_test(circuit)
add_xcsp_test(count)
add_xcsp_test(count_among)
add_xcsp_test(instantiation)
add_xcsp_test(intension_arithmetic)
add_xcsp_test(intension_basic)
add_xcsp_test(intension_boolean)
add_xcsp_test(intension_reified)
add_xcsp_test(lex)
add_xcsp_test(lex_matrix)
add_xcsp_test(maximum)
add_xcsp_test(minimum)
add_xcsp_test(n_values)
add_xcsp_test(ordered_lengths)
add_xcsp_test(ordered_strict)
add_xcsp_test(precedence)
add_xcsp_test(regular)
add_xcsp_test(slide)
add_xcsp_test(sum_not_equals)
