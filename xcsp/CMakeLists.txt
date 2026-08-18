include(FetchContent)

FetchContent_Declare(xcsp3_cpp_parser
    GIT_REPOSITORY https://github.com/xcsp3team/XCSP3-CPP-Parser.git
    GIT_TAG 179670dd97cd2b87cdeb93aa7268b57bba719490
    EXCLUDE_FROM_ALL)
FetchContent_MakeAvailable(xcsp3_cpp_parser)

# The top-level add_compile_options(-W -Wall) applies to every target in the
# build, including this fetched one, so the parser's sources are compiled with
# a warning set they were never written against: eleven warnings
# (-Wsign-compare, -Wunused-parameter, -Wdeprecated-copy, and a deprecated
# libxml2 entity call) that are not ours to fix and that we do not want between
# us and our own. Turn warnings off for the parser's own compilation only;
# nothing else in the build is affected, and headers it exposes to us are still
# compiled with our warnings when we include them.
foreach(_gcs_xcsp_target xcsp3parser xcsp3parser_dynamic)
    if(TARGET ${_gcs_xcsp_target})
        if(MSVC)
            target_compile_options(${_gcs_xcsp_target} PRIVATE /w)
        else()
            target_compile_options(${_gcs_xcsp_target} PRIVATE -w)
        endif()
    endif()
endforeach()

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
#
# Anything after the name is passed straight on: the first extra argument
# is a whitespace-separated list of solver flags (ACE never sees them, so
# the cache stays a genuine cross-check), and the rest are extended
# regexes that must each match a line of the binding's output.
#
# Under the sanitize build these tests would also report a leak that is not ours:
# the parser allocates an XVariable per variable and never frees them, so point
# LeakSanitizer at the suppressions file that ignores exactly that (and nothing
# else) and leave leak detection on for the rest of the run. Setting it here rather
# than in the sanitize test preset means it applies however ctest is invoked, and
# only to the tests that need it. LSAN_OPTIONS is inert in a non-sanitizer build.
function(add_xcsp_test name)
    add_test(NAME xcsp_${name}
        COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash
            $<TARGET_FILE:xcsp_glasgow_constraint_solver>
            ${CMAKE_SOURCE_DIR}/xcsp/tests/
            ${name}
            ${ARGN})
    set_tests_properties(xcsp_${name} PROPERTIES
        SKIP_RETURN_CODE 66
        ENVIRONMENT "LSAN_OPTIONS=suppressions=${CMAKE_SOURCE_DIR}/lsan_suppressions.txt:print_suppressions=0")
endfunction()

add_xcsp_test(all_different_matrix)
add_xcsp_test(all_equal)
add_xcsp_test(bin_packing)
add_xcsp_test(cardinality)
add_xcsp_test(cardinality_occvars)
add_xcsp_test(cardinality_intervals)
add_xcsp_test(channel_self)
add_xcsp_test(channel_two)
add_xcsp_test(circuit)
add_xcsp_test(cop_maximize_sum)
add_xcsp_test(cop_minimize)
add_xcsp_test(count)
add_xcsp_test(count_among)
add_xcsp_test(cumulative)
add_xcsp_test(cumulative_var)
# The presolver is invisible to solution equivalence and to proof
# verification alike, so this one also asserts on its counters. The two
# zeroes are not padding: COMPARISON EDGES LIFTED 0 says all four edges
# arrived as two-term linears over the instance's own variables, which is
# the peephole's doing --- without it they would arrive as comparisons
# over invented auxiliaries instead --- and SKIPPED UNCITABLE ROW 0 says
# no donor of the right shape was dropped for want of a citable OPB row.
#
# These names are also the contract between ComponentStats::entries() and the
# generic loop in xcsp_glasgow_constraint_solver.cc: each is component_name()
# and an entry name upper-cased together, so a rename on either side fails here
# rather than in whatever is parsing the output. DIFFERENCE LOGIC PROPAGATOR
# INSTALLED is one of the two fields that were filled in and reported to nobody
# until the loop replaced the hand-written list, and is here so that stays
# fixed --- as differenceLogicPropagatorInstalled is in minizinc/CMakeLists.txt.
add_xcsp_test(difference_logic "--difference-logic"
    "^d DIFFERENCE LOGIC EDGES LIFTED 4$"
    "^d DIFFERENCE LOGIC COMPARISON EDGES LIFTED 0$"
    "^d DIFFERENCE LOGIC NODES 4$"
    "^d DIFFERENCE LOGIC SKIPPED NOT TWO TERMS 1$"
    "^d DIFFERENCE LOGIC SKIPPED UNCITABLE ROW 0$"
    "^d DIFFERENCE LOGIC PROPAGATOR INSTALLED 1$"
    "^d DIFFERENCE LOGIC SIMPLIFY RAN 1$")
add_xcsp_test(disjunctive)
add_xcsp_test(no_overlap_var)
add_xcsp_test(no_overlap_2d)
add_xcsp_test(no_overlap_2d_var)
add_xcsp_test(instantiation)
add_xcsp_test(intension_arithmetic)
add_xcsp_test(intension_basic)
add_xcsp_test(intension_boolean)
add_xcsp_test(intension_ordering)
add_xcsp_test(intension_reified)
add_xcsp_test(lex)
add_xcsp_test(lex_matrix)
add_xcsp_test(maximum)
add_xcsp_test(mdd)
add_xcsp_test(minimum)
add_xcsp_test(n_values)
add_xcsp_test(ordered_lengths)
add_xcsp_test(ordered_strict)
add_xcsp_test(precedence)
add_xcsp_test(regular)
add_xcsp_test(slide)
add_xcsp_test(sum_not_equals)
