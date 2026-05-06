add_executable(talent talent.cc)
target_link_libraries(talent PRIVATE glasgow_constraint_solver)


target_link_libraries(talent PRIVATE cxxopts)

add_test(NAME talent COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:talent>)
