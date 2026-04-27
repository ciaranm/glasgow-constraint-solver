add_executable(colour colour.cc)
target_link_libraries(colour PRIVATE glasgow_constraint_solver)


target_link_libraries(colour PRIVATE cxxopts)

add_test(NAME colour COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:colour>)
