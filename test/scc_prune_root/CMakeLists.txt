add_executable(scc_prune_root scc_prune_root.cc)
target_link_libraries(scc_prune_root PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(scc_prune_root LINK_PUBLIC ${Boost_LIBRARIES})