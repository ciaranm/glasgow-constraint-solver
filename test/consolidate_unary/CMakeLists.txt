add_executable(consolidate_unary consolidate_unary.cc)
target_link_libraries(consolidate_unary PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(consolidate_unary LINK_PUBLIC ${Boost_LIBRARIES})