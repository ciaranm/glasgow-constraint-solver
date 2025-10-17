add_executable(magic_square magic_square.cc)
target_link_libraries(magic_square PUBLIC glasgow_constraint_solver)

target_link_libraries(magic_square LINK_PUBLIC cxxopts)

add_test(NAME magic_square-3 COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:magic_square> 3)
