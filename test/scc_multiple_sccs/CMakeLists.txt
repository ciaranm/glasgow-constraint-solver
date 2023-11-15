add_executable(scc_multiple_sccs scc_multiple_sccs.cc)
target_link_libraries(scc_multiple_sccs PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(scc_multiple_sccs LINK_PUBLIC ${Boost_LIBRARIES})