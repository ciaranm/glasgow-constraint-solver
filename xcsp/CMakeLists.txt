include(FetchContent)

# The parser reads every integer as an int, and upstream's conversion does not
# check for overflow: 4294967297 is read as 1, silently, so an instance with a
# value past int32 gets a wrong answer. The patch makes the conversion throw
# std::out_of_range instead, refuses a tuple value of INT_MAX (the parser's
# wildcard sentinel, so it would be read as `*`), and stops a domain reaching
# INT_MAX from overflowing the loop that lists its values. The binary reports
# the refusals as unsupported. See dev_docs/xcsp.md, "Integer range".
FetchContent_Declare(xcsp3_cpp_parser
    GIT_REPOSITORY https://github.com/xcsp3team/XCSP3-CPP-Parser.git
    GIT_TAG 179670dd97cd2b87cdeb93aa7268b57bba719490
    PATCH_COMMAND ${CMAKE_COMMAND} -DPATCH_FILE=${CMAKE_CURRENT_SOURCE_DIR}/xcsp3_parser_integer_overflow.patch
        -P ${CMAKE_CURRENT_SOURCE_DIR}/apply_parser_patch.cmake
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

add_xcsp_test(all_different_except)
add_xcsp_test(all_different_except_values)
add_xcsp_test(all_different_matrix)
add_xcsp_test(all_equal)
add_xcsp_test(bin_packing)
add_xcsp_test(cardinality)
add_xcsp_test(cardinality_occvars)
add_xcsp_test(cardinality_intervals)
# A <values> list that repeats a value. XCSP3 calls it a set, but nothing on the
# way in checks it, and GlobalCardinality rejects it: the binding folds the repeat
# out and posts the occurrence equality it stood for (#922). ACE reads the same
# instance and agrees on all nine solutions, so the cache is a real cross-check
# rather than a record of what we happen to do.
add_xcsp_test(cardinality_repeated)
add_xcsp_test(channel_self)
add_xcsp_test(channel_two)
# The first list shorter than the second, where channel only says
# list1[i] = j -> list2[j] = i, and an entry of the second that nothing names
# is free, even outside the first's indices (#1047). ACE errors unless the
# first list's domain is exactly the second's indices, which is why _free has
# x over 0..3.
add_xcsp_test(channel_unequal)
add_xcsp_test(channel_unequal_free)
# The same variable twice in the first list, which is unsatisfiable (#1047).
add_xcsp_test(channel_aliased)
add_xcsp_test(circuit)
add_xcsp_test(circuit_size)
add_xcsp_test(circuit_size_var)
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
# Overlapping supports: wildcard rows covering each other, and an exact
# duplicate, through the shared-tuples path a group uses. Solutions that two
# rows match used to make the proof's solution lines fail (issue #1115).
add_xcsp_test(extension_overlap)
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
# A domain reaching INT_MAX, which the parser listed with an int loop that
# overflowed and never finished (the patch in this file fixes it). ACE cannot
# parse such a domain, so the cache is a hand count: x in {0, 1, INT_MAX} with
# x != 1.
add_xcsp_test(range_domain_int_max)

# Integers the parser cannot represent. Each used to wrap silently, giving a
# wrong answer, or to abort; each must now be reported as unsupported, with the
# reason. An uncaught exception, whose message could otherwise match, and any
# solution line both fail the test.
function(add_xcsp_refusal_test name message)
    add_test(NAME xcsp_${name} COMMAND $<TARGET_FILE:xcsp_glasgow_constraint_solver> --all ${CMAKE_SOURCE_DIR}/xcsp/tests/${name}.xml)
    set_tests_properties(xcsp_${name} PROPERTIES
        PASS_REGULAR_EXPRESSION "s UNSUPPORTED\nc [^\n]*${message}"
        FAIL_REGULAR_EXPRESSION "terminate called;ENUMSOL")
endfunction()
# 4294967296..4294967297 was read as 0..1.
add_xcsp_refusal_test(range_domain_past_int32 "an integer does not fit in an int")
# A support of (4294967297, 2) was read as (1, 2).
add_xcsp_refusal_test(range_tuple_past_int32 "an integer does not fit in an int")
# 2147483647 is the parser's wildcard, so a support of (2147483647, 2) was read
# as (*, 2).
add_xcsp_refusal_test(range_tuple_int_max "cannot be told apart from the wildcard")
# The parser's own std::stoi refusing a condition value, which used to abort.
add_xcsp_refusal_test(range_condition_past_int32 "stoi")
# Arithmetic over in-range values that does not fit, which used to abort.
add_xcsp_refusal_test(range_sum_overflow "does not fit in an Integer")
add_xcsp_test(slide)
add_xcsp_test(sum_not_equals)
# <sum> with ne against a nonzero constant and against a variable. Both used to
# lose solutions (#1032): ne went through an auxiliary for operand - sum whose
# range was sized from the list alone, so it could not hold every difference.
add_xcsp_test(sum_not_equals_negative)
add_xcsp_test(sum_not_equals_var)
