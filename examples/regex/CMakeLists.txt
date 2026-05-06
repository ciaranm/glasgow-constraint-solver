add_executable(regex regex.cc)
target_link_libraries(regex PRIVATE glasgow_constraint_solver)


target_link_libraries(regex PRIVATE cxxopts)

add_test(NAME regex COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:regex>)