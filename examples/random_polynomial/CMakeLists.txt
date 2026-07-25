add_executable(random_polynomial random_polynomial.cc)
target_link_libraries(random_polynomial PUBLIC glasgow_constraint_solver)

target_link_libraries(random_polynomial LINK_PUBLIC cxxopts)
target_link_libraries(random_polynomial PRIVATE gcs_fmt)

# Same silently-discarded-arguments bug as multiply_random -- see the comment in
# its CMakeLists.txt. Unlike that one, the size deliberately stays at the
# binary's default rather than moving to the n=50 the registration named: the
# instances are unseeded, and the runtime cliff is steep and close. Over 12
# sample runs of the whole check (solve plus VeriPB), n=5 stayed under 2.5s,
# while n=10 ranged from 0.1s to over 120s with three runs above 14s, and n=15
# took 90s. Raising this needs a seeded instance, not a bigger number.
add_test(NAME random_polynomial COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:random_polynomial> --display-problem --stats)
