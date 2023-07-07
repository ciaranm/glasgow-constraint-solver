add_executable(at_most_1 at_most_1.cc)
target_link_libraries(at_most_1 PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(at_most_1 LINK_PUBLIC ${Boost_LIBRARIES})