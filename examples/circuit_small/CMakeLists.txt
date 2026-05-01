add_executable(circuit_small circuit_small.cc)
target_link_libraries(circuit_small PRIVATE glasgow_constraint_solver)

target_link_libraries(circuit_small PRIVATE cxxopts)

add_test(NAME circuit_small COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:circuit_small>)
