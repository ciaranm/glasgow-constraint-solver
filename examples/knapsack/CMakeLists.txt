add_executable(knapsack knapsack.cc)
target_link_libraries(knapsack PUBLIC glasgow_constraint_solver)


target_link_libraries(knapsack LINK_PUBLIC cxxopts)

add_test(NAME knapsack COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:knapsack>)
