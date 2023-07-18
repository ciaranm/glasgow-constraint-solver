add_executable(break_in break_in.cc)
target_link_libraries(break_in PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(break_in LINK_PUBLIC ${Boost_LIBRARIES})