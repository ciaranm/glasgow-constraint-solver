add_executable(n_queens n_queens.cc)
target_link_libraries(n_queens PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(n_queens LINK_PUBLIC ${Boost_LIBRARIES})
