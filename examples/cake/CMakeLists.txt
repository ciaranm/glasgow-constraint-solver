add_executable(cake cake.cc)
target_link_libraries(cake PUBLIC glasgow_constraint_solver)


target_link_libraries(cake LINK_PUBLIC cxxopts)
target_link_libraries(cake PRIVATE fmt::fmt)

add_test(NAME cake COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:cake>)
