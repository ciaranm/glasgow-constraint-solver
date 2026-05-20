add_executable(regular_random regular_random.cc)
target_link_libraries(regular_random PRIVATE glasgow_constraint_solver)
target_link_libraries(regular_random PRIVATE cxxopts)

add_test(NAME regular_random COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:regular_random>)
add_test(NAME regular_random-seeded COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:regular_random> --seed -1115540197)
add_test(NAME regular_random-seeded-bacchus COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:regular_random> --seed -1115540197 --bacchus)
set_tests_properties(regular_random regular_random-seeded regular_random-seeded-bacchus PROPERTIES RESOURCE_LOCK regular_random)
