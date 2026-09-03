add_executable(tables tables.cc)
target_link_libraries(tables PRIVATE glasgow_constraint_solver)


target_link_libraries(tables PRIVATE cxxopts)
target_link_libraries(tables PRIVATE gcs_fmt)

# One lane per algorithm: the library paths are covered by table_test, so what
# these add is that each algorithm solves this example correctly and writes a
# proof VeriPB accepts. tables_compact is the only place outside table_test that
# runs the compact algorithm at all -- this example's tables are all under
# min_tuples, so auto never switches on them.
#
# They do not pin the example's own forwarding of --table, and cannot: all three
# algorithms write byte-identical proofs by design, so run_test_and_verify.bash
# has nothing to see. Deleting the forwarding, so that --table compact parses and
# then selects auto, leaves all three lanes green (checked by mutation).
add_test(NAME tables COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:tables>)
# --basename because these share a binary with the lane above, and without
# distinct proof names a parallel ctest has them racing over one set of files
# (issue #562).
foreach(algorithm live compact)
    add_test(NAME tables_${algorithm}
        COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename tables_${algorithm}
        $<TARGET_FILE:tables> --table ${algorithm})
endforeach()

