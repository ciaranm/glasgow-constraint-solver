add_executable(black_hole black_hole.cc)
target_link_libraries(black_hole PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(black_hole LINK_PUBLIC ${Boost_LIBRARIES})