add_executable(circuit_random circuit_random.cc)
target_link_libraries(circuit_random PRIVATE glasgow_constraint_solver)

target_link_libraries(circuit_random PRIVATE cxxopts)

add_test(NAME circuit_random COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:circuit_random>)
