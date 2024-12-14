add_executable(skeleton_puzzle skeleton_puzzle.cc)
target_link_libraries(skeleton_puzzle PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(skeleton_puzzle LINK_PUBLIC ${Boost_LIBRARIES})