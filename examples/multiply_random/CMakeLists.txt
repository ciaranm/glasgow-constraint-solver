add_executable(multiply_random multiply_random.cc)
target_link_libraries(multiply_random PUBLIC glasgow_constraint_solver)

target_link_libraries(multiply_random LINK_PUBLIC cxxopts)
target_link_libraries(multiply_random PRIVATE gcs_fmt)

# These arguments used to be passed after a bare `--`, which terminates cxxopts
# option parsing: --display-problem, -n and --stats were all silently discarded
# and the test only ever solved the default n=5 instance. Two further faults were
# hiding under that: the flag is spelled --display-problem, not
# --display_problem, and `--n 50` is not valid cxxopts syntax for a
# one-character option name (it needs `-n 50` or `--n=50`). n=50 is the size the
# registration always intended, and still runs in about 0.1s.
add_test(NAME multiply_random COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:multiply_random> --display-problem -n 50 --stats)
