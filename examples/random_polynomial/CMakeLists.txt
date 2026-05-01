add_executable(random_polynomial random_polynomial.cc)
target_link_libraries(random_polynomial PUBLIC glasgow_constraint_solver)

target_link_libraries(random_polynomial LINK_PUBLIC cxxopts)
target_link_libraries(random_polynomial PRIVATE gcs_fmt)

add_test(NAME random_polynomial COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:random_polynomial> -- --display_problem --n 50 --stats)
