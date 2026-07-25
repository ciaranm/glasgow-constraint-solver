add_executable(regular_random regular_random.cc)
target_link_libraries(regular_random PRIVATE glasgow_constraint_solver)
target_link_libraries(regular_random PRIVATE cxxopts)

add_test(NAME regular_random COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename regular_random $<TARGET_FILE:regular_random>)
add_test(NAME regular_random-seeded COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename regular_random-seeded $<TARGET_FILE:regular_random> --seed -1115540197)
add_test(NAME regular_random-seeded-bacchus COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename regular_random-seeded-bacchus $<TARGET_FILE:regular_random> --seed -1115540197 --bacchus)
