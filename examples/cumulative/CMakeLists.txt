add_executable(cumulative cumulative.cc)
target_link_libraries(cumulative PRIVATE glasgow_constraint_solver)


target_link_libraries(cumulative PRIVATE cxxopts)

add_test(NAME cumulative COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:cumulative>)

# The encoding switch (#780). Distinct basenames so a parallel ctest does not
# race these over one set of proof files (#562), and names that avoid the
# `_startcheckpoint` suffix: that one belongs to the encoding *arms* registered
# in gcs/CMakeLists.txt, and `ctest -N -R startcheckpoint` counting exactly
# those is a sanity check worth keeping meaningful.
#
# The built-in five-task instance has constant lengths, heights and capacity
# and no optional task, so it is a shape the recovery reaches: this entry gets
# the strict encoding, with no per-time capacity row to fall back on, through a
# real example binary rather than a test fixture.
add_test(NAME cumulative_encoding_start_checkpoint COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash
    --basename cumulative_encoding_start_checkpoint $<TARGET_FILE:cumulative> --variant start-checkpoint)

# Both families in the model, and every recovered per-time row checked against
# the one the model still carries beside it.
add_test(NAME cumulative_encoding_both_recovering COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash
    --basename cumulative_encoding_both_recovering $<TARGET_FILE:cumulative> --variant both-recovering)

# The generated instance and the horizon override, which are how the two
# encodings get compared at a chosen n and H. Nothing else posts them, so
# without this entry they could rot unnoticed between measurements.
add_test(NAME cumulative_generated_instance COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash
    --basename cumulative_generated_instance $<TARGET_FILE:cumulative> --tasks 8 --seed 1 --horizon 20)

# The regime the start-checkpoint encoding exists for, which none of the
# entries above reach: a few tasks of long duration, so that each task's
# possible-active window --- and with it the time-indexed block --- is long
# while the instance stays trivial to solve. --max-start is what separates
# those two, and without an entry here nothing would notice if it stopped
# doing so. 3 tasks at duration up to 500 is 3,182 OPB lines against the
# built-in instance's 522, and still verifies in well under a second.
add_test(NAME cumulative_long_duration COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash
    --basename cumulative_long_duration $<TARGET_FILE:cumulative>
    --variant start-checkpoint --tasks 3 --seed 2 --max-length 500 --max-start 5 --horizon 508)
