add_executable(crystal_maze crystal_maze.cc)
target_link_libraries(crystal_maze PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(crystal_maze LINK_PUBLIC ${Boost_LIBRARIES})

add_test(NAME crystal_maze COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:crystal_maze>)
add_test(NAME crystal_maze-abs COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:crystal_maze> --abs)
add_test(NAME crystal_maze-gac COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:crystal_maze> --gac)
add_test(NAME crystal_maze-abs-gac COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:crystal_maze> --abs --gac)
set_tests_properties(crystal_maze crystal_maze-abs crystal_maze-gac crystal_maze-abs-gac PROPERTIES RESOURCE_LOCK crystal_maze)
