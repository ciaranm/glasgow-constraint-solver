add_executable(crystal_maze crystal_maze.cc)
target_link_libraries(crystal_maze PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(crystal_maze LINK_PUBLIC ${Boost_LIBRARIES})
