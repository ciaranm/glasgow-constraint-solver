# Integers at and past the edges of what the solver accepts
# (dev_docs/integer-ranges.md). These are hand-written JSON, because MiniZinc
# never emits an integer past long long. Such an integer used to be cast to long
# long and wrap silently, so `x <= 2^64 - 1` was read as `x <= -1` and lost
# solutions. Each must now be refused with an error naming the value as
# written: the pass expression is fzn-glasgow's own `error:` line, and an
# uncaught exception, whose message could otherwise match, fails the test.
gcs_fzn_json_test(minizinc-range-edges range_edges.fzn)
function(add_fzn_range_refusal_test name message)
    add_test(NAME minizinc-${name} COMMAND $<TARGET_FILE:fzn-glasgow> -a ${CMAKE_CURRENT_SOURCE_DIR}/${name}.fzn)
    set_tests_properties(minizinc-${name} PROPERTIES
        PASS_REGULAR_EXPRESSION "fzn-glasgow[^:]*: error: [^\n]*${message}"
        FAIL_REGULAR_EXPRESSION "terminate called")
endfunction()
add_fzn_range_refusal_test(range_int_past_long_long "the integer 18446744073709551615 does not fit in an Integer")
add_fzn_range_refusal_test(range_domain_2_63 "the integer 9223372036854775808 does not fit in an Integer")
add_fzn_range_refusal_test(range_integer_literal_too_long "the integer 1e\\+20 does not fit in an Integer")
add_fzn_range_refusal_test(range_float_where_int "expected an integer, but got 2.5")

# A var bool output array whose every element the flattener has fixed (#785).
# This has to be hand-written JSON: MiniZinc drops such an array from `output`
# unless something else keeps it alive, so a .mzn model cannot reach it. `ns` is
# the all-par array that used to print as 1 / 0; `es` keeps one live variable, so
# it prints correctly either way and shows the two disagreeing in one solution;
# `ds` is all-par ints, and is here so the fix cannot start calling those bools.
gcs_fzn_json_test(minizinc-parboolarrayoutput par_bool_array_output.fzn)
