add_executable(multiply_random multiply_random.cc)
target_link_libraries(multiply_random PUBLIC glasgow_constraint_solver)

target_link_libraries(multiply_random LINK_PUBLIC cxxopts)
target_link_libraries(multiply_random PRIVATE gcs_fmt)

add_test(NAME multiply_random COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:multiply_random> -- --display_problem --n 50 --stats)
