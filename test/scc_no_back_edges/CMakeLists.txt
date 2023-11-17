add_executable(scc_no_back_edges scc_no_back_edges.cc)
target_link_libraries(scc_no_back_edges PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(scc_no_back_edges LINK_PUBLIC ${Boost_LIBRARIES})