add_executable(magic_series magic_series.cc)
target_link_libraries(magic_series PUBLIC glasgow_constraint_solver)

target_link_libraries(magic_series LINK_PUBLIC cxxopts)

add_test(NAME magic_series-10 COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:magic_series> 10)
