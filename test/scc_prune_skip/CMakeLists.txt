add_executable(scc_prune_skip scc_prune_skip.cc)
target_link_libraries(scc_prune_skip PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(scc_prune_skip LINK_PUBLIC ${Boost_LIBRARIES})