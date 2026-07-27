add_executable(crystal_maze crystal_maze.cc)
target_link_libraries(crystal_maze PRIVATE glasgow_constraint_solver)


target_link_libraries(crystal_maze PRIVATE cxxopts)

add_test(NAME crystal_maze COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename crystal_maze $<TARGET_FILE:crystal_maze>)
add_test(NAME crystal_maze-abs COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename crystal_maze-abs $<TARGET_FILE:crystal_maze> --abs)
add_test(NAME crystal_maze-gac COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename crystal_maze-gac $<TARGET_FILE:crystal_maze> --gac)
add_test(NAME crystal_maze-abs-gac COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename crystal_maze-abs-gac $<TARGET_FILE:crystal_maze> --abs --gac)
