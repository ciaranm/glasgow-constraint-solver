add_executable(cake cake.cc)
target_link_libraries(cake PUBLIC glasgow_constraint_solver)


target_link_libraries(cake LINK_PUBLIC cxxopts)

add_test(NAME cake COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:cake>)
