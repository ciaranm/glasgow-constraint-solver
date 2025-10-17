add_executable(colour colour.cc)
target_link_libraries(colour PUBLIC glasgow_constraint_solver)


target_link_libraries(colour LINK_PUBLIC cxxopts)

add_test(NAME colour COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:colour>)
