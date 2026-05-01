add_executable(knapsack knapsack.cc)
target_link_libraries(knapsack PRIVATE glasgow_constraint_solver)


target_link_libraries(knapsack PRIVATE cxxopts)

add_test(NAME knapsack COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:knapsack>)
